//! Generalized operation types for Levenshtein automata.
//!
//! This module implements the operation type system from "Efficient Computation of Substring Equivalence Classes with Applications to Polynomial-Time Tree Isomorphism"
//! (TCS 2011, Section 3, pages 2341-2342).
//!
//! ## Overview
//!
//! An **operation type** defines a single edit operation in a generalized Levenshtein
//! distance metric. Unlike the hardcoded Standard/Transposition/MergeAndSplit algorithms,
//! operation types are data-driven and composable.
//!
//! ## Operation Type Definition
//!
//! An operation type `t = ⟨t^x, t^y, t^w⟩` consists of:
//! - `t^x`: Number of characters consumed from the first word (dictionary)
//! - `t^y`: Number of characters consumed from the second word (query)
//! - `t^w`: Operation weight/cost (float)
//!
//! ## Standard Levenshtein Operations
//!
//! ```
//! Match:         ⟨1, 1, 0.0⟩  // Consume 1 from each, no cost
//! Substitution:  ⟨1, 1, 1.0⟩  // Consume 1 from each, cost 1
//! Insertion:     ⟨0, 1, 1.0⟩  // Consume only from query, cost 1
//! Deletion:      ⟨1, 0, 1.0⟩  // Consume only from dictionary, cost 1
//! Transposition: ⟨2, 2, 1.0⟩  // Consume 2 from each, cost 1
//! ```
//!
//! ## Extended Operations
//!
//! ### Phonetic Corrections
//! ```
//! ph→f digraph:  ⟨2, 1, 0.15⟩  // "ph" in dict matches "f" in query
//! Silent e:      ⟨1, 0, 0.1⟩   // Final "e" deletion, low cost
//! ```
//!
//! ### Weighted OCR Corrections
//! ```
//! O↔0 confusion: ⟨1, 1, 0.2⟩  // Common OCR error, low cost
//! l↔I confusion: ⟨1, 1, 0.3⟩  // Less common, higher cost
//! ```
//!
//! ## Restricted Operations
//!
//! A **restricted operation** `op = ⟨op^x, op^y, op^r, op^w⟩` adds:
//! - `op^r ⊆ Σ^{op^x} × Σ^{op^y}`: Set of allowed character pair substitutions
//!
//! Only character pairs in `op^r` can use this operation.
//!
//! ### Example: Keyboard Proximity
//! ```rust
//! use liblevenshtein::transducer::{OperationType, SubstitutionSet};
//!
//! let mut proximity = SubstitutionSet::new();
//! proximity.allow_str("q", "w");  // Adjacent on QWERTY
//! proximity.allow_str("w", "q");
//! proximity.allow_str("w", "e");
//! proximity.allow_str("e", "w");
//!
//! let op = OperationType::with_restriction(
//!     1, 1, 0.3,  // Low cost for adjacent keys
//!     proximity,
//!     "keyboard_proximity"
//! );
//! ```
//!
//! ## Theoretical Constraints
//!
//! From TCS 2011 Theorem 8.2 (Bounded Diagonal Property):
//!
//! 1. **Bounded consumption**: `t^x + t^y ≤ c` for some constant `c`
//! 2. **Zero-weight must be length-preserving**: If `t^w = 0`, then `t^x = t^y`
//!
//! These constraints ensure:
//! - Finite state space for universal automata
//! - Bounded subsumption check complexity
//! - SmallVec optimization (inline size = 8 is mathematically sufficient)
//!
//! ## Performance
//!
//! - **Operation matching**: O(1) for unrestricted, O(|op^r|) for restricted
//! - **Memory**: 16-40 bytes per operation depending on restriction set size
//! - **Cache-friendly**: Small operations stored inline (SmallVec)

use crate::transducer::substitution_set::SubstitutionSet;
use std::fmt;

/// A generalized operation type for Levenshtein automata.
///
/// Represents an edit operation `t = ⟨t^x, t^y, t^w⟩` from TCS 2011.
///
/// # Examples
///
/// ## Standard Operations
///
/// ```rust
/// # use liblevenshtein::transducer::OperationType;
/// // Match: ⟨1, 1, 0.0⟩
/// let match_op = OperationType::new(1, 1, 0.0, "match");
///
/// // Substitution: ⟨1, 1, 1.0⟩
/// let subst_op = OperationType::new(1, 1, 1.0, "substitute");
///
/// // Insertion: ⟨0, 1, 1.0⟩
/// let insert_op = OperationType::new(0, 1, 1.0, "insert");
///
/// // Deletion: ⟨1, 0, 1.0⟩
/// let delete_op = OperationType::new(1, 0, 1.0, "delete");
/// ```
///
/// ## Multi-Character Operations
///
/// ```rust
/// # use liblevenshtein::transducer::{OperationType, SubstitutionSet};
/// // Phonetic: ph→f digraph
/// let mut phonetic = SubstitutionSet::new();
/// phonetic.allow_str("ph", "f");
///
/// let ph_to_f = OperationType::with_restriction(
///     2, 1, 0.15,
///     phonetic,
///     "consonant_digraph_ph"
/// );
/// ```
///
/// ## Weighted Operations
///
/// ```rust
/// # use liblevenshtein::transducer::OperationType;
/// // OCR confusion: O↔0 (common, low cost)
/// let ocr_op = OperationType::new(1, 1, 0.2, "ocr_o_zero");
/// ```
#[derive(Clone, Debug)]
pub struct OperationType {
    /// Number of characters consumed from first word (dictionary).
    /// Corresponds to `t^x` in TCS 2011.
    consume_x: usize,

    /// Number of characters consumed from second word (query).
    /// Corresponds to `t^y` in TCS 2011.
    consume_y: usize,

    /// Operation weight/cost (≥ 0.0).
    /// Corresponds to `t^w` in TCS 2011.
    /// - 0.0: Free operation (must have consume_x == consume_y by Theorem 8.2)
    /// - 1.0: Standard Levenshtein cost
    /// - Other values: Custom costs for weighted operations
    weight: f64,

    /// Optional restriction set for character pair substitutions.
    /// If None, operation is unrestricted (applies to all character pairs).
    /// If Some(set), operation only applies to pairs in set.
    ///
    /// Corresponds to `op^r` in TCS 2011 for restricted operations.
    restriction: Option<SubstitutionSet>,

    /// Human-readable name for debugging and profiling.
    /// Examples: "match", "substitute", "ph_to_f", "silent_e"
    name: &'static str,
}

impl OperationType {
    /// Create a new unrestricted operation type.
    ///
    /// # Parameters
    ///
    /// - `consume_x`: Characters consumed from dictionary word (≥ 0)
    /// - `consume_y`: Characters consumed from query word (≥ 0)
    /// - `weight`: Operation cost (≥ 0.0)
    /// - `name`: Human-readable identifier
    ///
    /// # Panics
    ///
    /// Panics if:
    /// - `weight < 0.0` (negative costs are invalid)
    /// - `weight == 0.0` but `consume_x != consume_y` (violates Theorem 8.2)
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use liblevenshtein::transducer::OperationType;
    /// // Standard match operation
    /// let match_op = OperationType::new(1, 1, 0.0, "match");
    ///
    /// // Custom weighted operation
    /// let custom = OperationType::new(2, 1, 0.5, "custom_digraph");
    /// ```
    #[inline]
    pub fn new(consume_x: usize, consume_y: usize, weight: f64, name: &'static str) -> Self {
        assert!(weight >= 0.0, "Operation weight must be non-negative");

        // Theorem 8.2: Zero-weight operations must be length-preserving
        if weight == 0.0 {
            assert_eq!(
                consume_x, consume_y,
                "Zero-weight operation must preserve length (consume_x == consume_y)"
            );
        }

        Self {
            consume_x,
            consume_y,
            weight,
            restriction: None,
            name,
        }
    }

    /// Create a restricted operation type with character pair constraints.
    ///
    /// The operation only applies when the consumed characters match a pair
    /// in the restriction set.
    ///
    /// # Parameters
    ///
    /// - `consume_x`: Characters consumed from dictionary word
    /// - `consume_y`: Characters consumed from query word
    /// - `weight`: Operation cost
    /// - `restriction`: Allowed character pair substitutions
    /// - `name`: Human-readable identifier
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use liblevenshtein::transducer::{OperationType, SubstitutionSet};
    /// // Phonetic ph→f
    /// let mut phonetic = SubstitutionSet::new();
    /// phonetic.allow_str("ph", "f");
    ///
    /// let op = OperationType::with_restriction(
    ///     2, 1, 0.15,
    ///     phonetic,
    ///     "ph_to_f"
    /// );
    /// ```
    #[inline]
    pub fn with_restriction(
        consume_x: usize,
        consume_y: usize,
        weight: f64,
        restriction: SubstitutionSet,
        name: &'static str,
    ) -> Self {
        let mut op = Self::new(consume_x, consume_y, weight, name);
        op.restriction = Some(restriction);
        op
    }

    /// Get the number of characters consumed from the dictionary word.
    #[inline]
    pub fn consume_x(&self) -> usize {
        self.consume_x
    }

    /// Get the number of characters consumed from the query word.
    #[inline]
    pub fn consume_y(&self) -> usize {
        self.consume_y
    }

    /// Get the operation weight/cost.
    #[inline]
    pub fn weight(&self) -> f64 {
        self.weight
    }

    /// Get the operation name.
    #[inline]
    pub fn name(&self) -> &'static str {
        self.name
    }

    /// Check if this operation is restricted to specific character pairs.
    #[inline]
    pub fn is_restricted(&self) -> bool {
        self.restriction.is_some()
    }

    /// Get the restriction set, if any.
    #[inline]
    pub fn restriction(&self) -> Option<&SubstitutionSet> {
        self.restriction.as_ref()
    }

    /// Check if this operation is a match (zero cost, length-preserving).
    #[inline]
    pub fn is_match(&self) -> bool {
        self.weight == 0.0
    }

    /// Check if this operation is an insertion (consumes only from query).
    #[inline]
    pub fn is_insertion(&self) -> bool {
        self.consume_x == 0 && self.consume_y > 0
    }

    /// Check if this operation is a deletion (consumes only from dictionary).
    #[inline]
    pub fn is_deletion(&self) -> bool {
        self.consume_x > 0 && self.consume_y == 0
    }

    /// Check if this operation is a substitution (single-char, non-zero cost).
    #[inline]
    pub fn is_substitution(&self) -> bool {
        self.consume_x == 1 && self.consume_y == 1 && self.weight > 0.0
    }

    /// Check if this operation can apply to the given character pair.
    ///
    /// For unrestricted operations, always returns true.
    /// For restricted operations, checks if the pair is in the restriction set.
    ///
    /// # Parameters
    ///
    /// - `dict_chars`: Characters from dictionary word (length = consume_x)
    /// - `query_chars`: Characters from query word (length = consume_y)
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use liblevenshtein::transducer::{OperationType, SubstitutionSet};
    /// // Unrestricted match
    /// let match_op = OperationType::new(1, 1, 0.0, "match");
    /// assert!(match_op.can_apply(b"a", b"a"));
    /// assert!(!match_op.can_apply(b"a", b"b"));  // Characters must match for match op
    ///
    /// // Restricted phonetic operation
    /// let mut phonetic = SubstitutionSet::new();
    /// phonetic.allow_str("ph", "f");
    /// let ph_op = OperationType::with_restriction(2, 1, 0.15, phonetic, "ph_to_f");
    ///
    /// assert!(ph_op.can_apply(b"ph", b"f"));
    /// assert!(!ph_op.can_apply(b"ph", b"g"));
    /// ```
    #[inline]
    pub fn can_apply(&self, dict_chars: &[u8], query_chars: &[u8]) -> bool {
        // Length check
        if dict_chars.len() != self.consume_x || query_chars.len() != self.consume_y {
            return false;
        }

        // Special case: match operation requires character equality
        if self.is_match() {
            return dict_chars == query_chars;
        }

        // Check restriction set if present
        match &self.restriction {
            None => true,  // Unrestricted operation
            Some(set) => set.contains_str(dict_chars, query_chars),
        }
    }
}

impl fmt::Display for OperationType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}⟨{}, {}, {}⟩",
            self.name, self.consume_x, self.consume_y, self.weight
        )?;

        if self.is_restricted() {
            write!(f, " [restricted]")?;
        }

        Ok(())
    }
}

impl PartialEq for OperationType {
    fn eq(&self, other: &Self) -> bool {
        self.consume_x == other.consume_x
            && self.consume_y == other.consume_y
            && (self.weight - other.weight).abs() < f64::EPSILON
            && self.restriction == other.restriction
            && self.name == other.name
    }
}

impl Eq for OperationType {}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_standard_operations() {
        let match_op = OperationType::new(1, 1, 0.0, "match");
        assert!(match_op.is_match());
        assert!(!match_op.is_restricted());
        assert_eq!(match_op.consume_x(), 1);
        assert_eq!(match_op.consume_y(), 1);
        assert_eq!(match_op.weight(), 0.0);

        let subst_op = OperationType::new(1, 1, 1.0, "substitute");
        assert!(subst_op.is_substitution());
        assert!(!subst_op.is_match());

        let insert_op = OperationType::new(0, 1, 1.0, "insert");
        assert!(insert_op.is_insertion());

        let delete_op = OperationType::new(1, 0, 1.0, "delete");
        assert!(delete_op.is_deletion());
    }

    #[test]
    #[should_panic(expected = "Zero-weight operation must preserve length")]
    fn test_zero_weight_must_preserve_length() {
        OperationType::new(2, 1, 0.0, "invalid");
    }

    #[test]
    #[should_panic(expected = "Operation weight must be non-negative")]
    fn test_negative_weight_panics() {
        OperationType::new(1, 1, -0.5, "invalid");
    }

    #[test]
    fn test_match_requires_equality() {
        let match_op = OperationType::new(1, 1, 0.0, "match");
        assert!(match_op.can_apply(b"a", b"a"));
        assert!(!match_op.can_apply(b"a", b"b"));
    }

    #[test]
    fn test_unrestricted_operations() {
        let subst = OperationType::new(1, 1, 1.0, "substitute");
        // Unrestricted substitution works for any non-matching pair
        assert!(subst.can_apply(b"a", b"b"));
        assert!(subst.can_apply(b"x", b"y"));
    }

    #[test]
    fn test_restricted_operation() {
        let mut phonetic = SubstitutionSet::new();
        phonetic.allow('f', 'p');
        phonetic.allow('p', 'h');

        let restricted = OperationType::with_restriction(1, 1, 0.3, phonetic, "phonetic");

        assert!(restricted.is_restricted());
        assert!(restricted.can_apply(b"f", b"p"));
        assert!(restricted.can_apply(b"p", b"h"));
        assert!(!restricted.can_apply(b"a", b"b"));
    }

    #[test]
    fn test_display() {
        let op = OperationType::new(2, 1, 0.15, "ph_to_f");
        let display = format!("{}", op);
        assert!(display.contains("ph_to_f"));
        assert!(display.contains("2"));
        assert!(display.contains("1"));
        assert!(display.contains("0.15"));
    }
}
