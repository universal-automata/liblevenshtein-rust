//! Subsumption Relation for Universal Positions
//!
//! Implements the subsumption relation ≤^χ_s from Definition 11 (thesis pages 18-21).
//!
//! # Theory Background
//!
//! The subsumption relation is a partial order on positions that enables state minimization.
//! Position π₁ subsumes π₂ (written π₁ <^χ_s π₂) if π₂ represents a "better" state
//! (more errors available, close enough in position).
//!
//! ## Definition 11: Subsumption for Standard Levenshtein (χ = ε)
//!
//! ```text
//! i#e ≤^ε_s j#f  ⇔  f > e ∧ |j - i| ≤ f - e
//! ```
//!
//! **Intuition**: Position j#f subsumes i#e if:
//! 1. f > e (more errors available at j)
//! 2. |j - i| ≤ f - e (positions close enough given error difference)
//!
//! ## Subsumption for Transposition (χ = t)
//!
//! ```text
//! i#e   ≤^t_s j#f     ⇔  f > e ∧ |j - i| ≤ f - e
//! i#e_t ≤^t_s j#f     ⇔  f > e ∧ |j + 1 - i| ≤ f - e
//! i#e   ≤^t_s j#f_t   ⇔  false  (different types)
//! i#e_t ≤^t_s j#f_t   ⇔  false  (different types)
//! ```
//!
//! ## Subsumption for Merge/Split (χ = ms)
//!
//! ```text
//! i#e   ≤^ms_s j#f    ⇔  f > e ∧ |j - i| ≤ f - e
//! i#e_s ≤^ms_s j#f    ⇔  f > e ∧ |j - i| ≤ f - e
//! i#e   ≤^ms_s j#f_s  ⇔  false  (different types)
//! i#e_s ≤^ms_s j#f_s  ⇔  false  (different types)
//! ```
//!
//! # Examples
//!
//! ```ignore
//! use liblevenshtein::transducer::universal::{UniversalPosition, Standard, subsumes};
//!
//! let pos1 = UniversalPosition::<Standard>::new_i(3, 1, 3)?;  // I + 3#1
//! let pos2 = UniversalPosition::<Standard>::new_i(5, 2, 3)?;  // I + 5#2
//!
//! // Check: 3#1 ≤^ε_s 5#2
//! // f > e: 2 > 1 ✓
//! // |j - i| ≤ f - e: |5 - 3| = 2 ≤ 2 - 1 = 1? NO
//! assert!(!subsumes(&pos1, &pos2, 3));
//!
//! let pos3 = UniversalPosition::<Standard>::new_i(4, 1, 3)?;  // I + 4#1
//! let pos4 = UniversalPosition::<Standard>::new_i(5, 2, 3)?;  // I + 5#2
//!
//! // Check: 4#1 ≤^ε_s 5#2
//! // f > e: 2 > 1 ✓
//! // |j - i| ≤ f - e: |5 - 4| = 1 ≤ 2 - 1 = 1 ✓
//! assert!(subsumes(&pos3, &pos4, 3));
//! ```

use crate::transducer::universal::position::{
    MergeAndSplit, PositionVariant, Standard, Transposition, UniversalPosition,
};

/// Check if pos1 strictly subsumes pos2 (pos1 <^χ_s pos2)
///
/// # Arguments
///
/// - `pos1`: First position (potential subsumer)
/// - `pos2`: Second position (potentially subsumed)
/// - `max_distance`: Maximum edit distance n
///
/// # Returns
///
/// `true` if pos1 <^χ_s pos2 (pos2 is subsumed by pos1), `false` otherwise
///
/// # Theory
///
/// From Definition 11 (page 18):
/// - Both positions must have same parameter type (I or M)
/// - pos2 must have more errors available (f > e)
/// - Positions must be close enough (|j - i| ≤ f - e)
/// - For transposition/merge-split: special rules for type subscripts
///
/// # Example
///
/// ```ignore
/// let pos1 = UniversalPosition::<Standard>::new_i(4, 1, 3)?;
/// let pos2 = UniversalPosition::<Standard>::new_i(5, 2, 3)?;
/// assert!(subsumes(&pos1, &pos2, 3));  // 4#1 <^ε_s 5#2
/// ```
pub fn subsumes<V: PositionVariant>(
    pos1: &UniversalPosition<V>,
    pos2: &UniversalPosition<V>,
    max_distance: u8,
) -> bool {
    // Dispatch to variant-specific implementation
    subsumes_impl(pos1, pos2, max_distance)
}

/// Generic subsumption implementation (works for Standard variant)
///
/// For Standard variant, subsumption is straightforward:
/// i#e ≤^ε_s j#f ⇔ f > e ∧ |j - i| ≤ f - e
fn subsumes_impl<V: PositionVariant>(
    pos1: &UniversalPosition<V>,
    pos2: &UniversalPosition<V>,
    _max_distance: u8,
) -> bool {
    use UniversalPosition::*;

    match (pos1, pos2) {
        // I-type subsumption: both must be I-type
        (INonFinal { offset: i, errors: e, .. }, INonFinal { offset: j, errors: f, .. }) => {
            // Definition 11: f > e ∧ |j - i| ≤ f - e
            if *f <= *e {
                return false;  // Not strictly greater errors
            }

            let distance = (j - i).abs() as u8;
            let error_diff = f - e;

            distance <= error_diff
        }

        // M-type subsumption: both must be M-type
        (MFinal { offset: i, errors: e, .. }, MFinal { offset: j, errors: f, .. }) => {
            // Same formula as I-type: f > e ∧ |j - i| ≤ f - e
            if *f <= *e {
                return false;
            }

            let distance = (j - i).abs() as u8;
            let error_diff = f - e;

            distance <= error_diff
        }

        // Different parameter types: no subsumption
        _ => false,
    }
}

/// Subsumption for Transposition variant (future extension)
///
/// From Definition 11 extended for transposition:
/// - i#e_t ≤^t_s j#f ⇔ f > e ∧ |j + 1 - i| ≤ f - e
/// - Type subscripts must match (usual vs transposition state)
#[allow(dead_code)]
fn subsumes_transposition(
    pos1: &UniversalPosition<Transposition>,
    pos2: &UniversalPosition<Transposition>,
    _max_distance: u8,
) -> bool {
    use UniversalPosition::*;

    match (pos1, pos2) {
        (INonFinal { offset: i, errors: e, .. }, INonFinal { offset: j, errors: f, .. }) => {
            if *f <= *e {
                return false;
            }

            // For transposition state, offset adjustment: |j + 1 - i|
            // TODO: Check variant type when Transposition enum is used
            let distance = (j - i).abs() as u8;
            let error_diff = f - e;

            distance <= error_diff
        }

        (MFinal { offset: i, errors: e, .. }, MFinal { offset: j, errors: f, .. }) => {
            if *f <= *e {
                return false;
            }

            let distance = (j - i).abs() as u8;
            let error_diff = f - e;

            distance <= error_diff
        }

        _ => false,
    }
}

/// Subsumption for MergeAndSplit variant (future extension)
///
/// From Definition 11 extended for merge/split:
/// - Same rules as standard, but type subscripts must match
#[allow(dead_code)]
fn subsumes_merge_split(
    pos1: &UniversalPosition<MergeAndSplit>,
    pos2: &UniversalPosition<MergeAndSplit>,
    _max_distance: u8,
) -> bool {
    // Same implementation as standard for now
    // TODO: Check variant type when MergeAndSplit enum is used
    subsumes_impl(pos1, pos2, _max_distance)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_subsumption_basic_i_type() {
        // Test case: 1#1 ≤^ε_s 2#2
        // Invariant check: |1| = 1 ≤ 1 ✓, |2| = 2 ≤ 2 ✓
        let pos1 = UniversalPosition::<Standard>::new_i(1, 1, 3).unwrap();
        let pos2 = UniversalPosition::<Standard>::new_i(2, 2, 3).unwrap();

        // Check: f > e (2 > 1) ✓
        //        |j - i| ≤ f - e (|2 - 1| = 1 ≤ 2 - 1 = 1) ✓
        assert!(subsumes(&pos1, &pos2, 3));
    }

    #[test]
    fn test_subsumption_fails_distance_too_large() {
        // Test: 0#1 does NOT subsume 2#2
        // Invariant check: |0| = 0 ≤ 1 ✓, |2| = 2 ≤ 2 ✓
        let pos1 = UniversalPosition::<Standard>::new_i(0, 1, 3).unwrap();
        let pos2 = UniversalPosition::<Standard>::new_i(2, 2, 3).unwrap();

        // Check: f > e (2 > 1) ✓
        //        |j - i| ≤ f - e (|2 - 0| = 2 ≤ 2 - 1 = 1) ✗
        assert!(!subsumes(&pos1, &pos2, 3));
    }

    #[test]
    fn test_subsumption_fails_equal_errors() {
        // Positions with equal errors: no subsumption
        // Invariant check: |1| = 1 ≤ 1 ✓, |1| = 1 ≤ 1 ✓
        let pos1 = UniversalPosition::<Standard>::new_i(1, 1, 3).unwrap();
        let pos2 = UniversalPosition::<Standard>::new_i(1, 1, 3).unwrap();

        // f = e, so f > e fails
        assert!(!subsumes(&pos1, &pos2, 3));
    }

    #[test]
    fn test_subsumption_m_type() {
        // Test M-type positions
        let pos1 = UniversalPosition::<Standard>::new_m(-2, 0, 2).unwrap();
        let pos2 = UniversalPosition::<Standard>::new_m(-1, 1, 2).unwrap();

        // Check: f > e (1 > 0) ✓
        //        |j - i| ≤ f - e (|-1 - (-2)| = 1 ≤ 1 - 0 = 1) ✓
        assert!(subsumes(&pos1, &pos2, 2));
    }

    #[test]
    fn test_no_subsumption_across_types() {
        // I-type and M-type: no subsumption
        let i_pos = UniversalPosition::<Standard>::new_i(0, 0, 2).unwrap();
        let m_pos = UniversalPosition::<Standard>::new_m(0, 0, 2).unwrap();

        assert!(!subsumes(&i_pos, &m_pos, 2));
        assert!(!subsumes(&m_pos, &i_pos, 2));
    }
}
