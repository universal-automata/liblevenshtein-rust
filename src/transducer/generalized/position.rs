//! Generalized Position Types
//!
//! Implements universal positions adapted for runtime-configurable operations.
//! Based on Definition 15 from Mitankin's thesis (pages 30-33), but without
//! compile-time variant specialization.
//!
//! # Theory Background
//!
//! Generalized positions use parameters I (non-final) and M (final) with runtime operations:
//! - `I + t#k`: Non-final position, offset t from start, k errors consumed
//! - `M + t#k`: Final position, offset t from end, k errors consumed
//!
//! Unlike UniversalPosition, GeneralizedPosition does not use compile-time variants
//! (Standard, Transposition, MergeAndSplit). Instead, operations are determined at
//! runtime via the OperationSet parameter.
//!
//! ## Invariants (from Definition 15)
//!
//! **I-type (non-final)**:
//! ```text
//! I^ε_s = {I + t#k | |t| ≤ k ∧ -n ≤ t ≤ n ∧ 0 ≤ k ≤ n}
//! ```
//!
//! **M-type (final)**:
//! ```text
//! M^ε_s = {M + t#k | k ≥ -t - n ∧ -2n ≤ t ≤ 0 ∧ 0 ≤ k ≤ n}
//! ```
//!
//! # Examples
//!
//! ```ignore
//! use liblevenshtein::transducer::generalized::GeneralizedPosition;
//!
//! // Create I-type position: I + 0#0 (initial state)
//! let initial = GeneralizedPosition::new_i(0, 0, 2)?;
//!
//! // Create M-type position: M + (-1)#1 (one error, one char before end)
//! let final_pos = GeneralizedPosition::new_m(-1, 1, 2)?;
//! ```

use std::fmt;

/// Error type for invalid position creation
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PositionError {
    /// I-type position violates invariant |t| ≤ k ∧ -n ≤ t ≤ n ∧ 0 ≤ k ≤ n
    InvalidIPosition {
        /// The offset value that violated the invariant
        offset: i32,
        /// The error count that violated the invariant
        errors: u8,
        /// The maximum distance n
        max_distance: u8,
    },

    /// M-type position violates invariant k ≥ -t - n ∧ -2n ≤ t ≤ 0 ∧ 0 ≤ k ≤ n
    InvalidMPosition {
        /// The offset value that violated the invariant
        offset: i32,
        /// The error count that violated the invariant
        errors: u8,
        /// The maximum distance n
        max_distance: u8,
    },
}

impl fmt::Display for PositionError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            PositionError::InvalidIPosition { offset, errors, max_distance } => {
                write!(
                    f,
                    "Invalid I-position: I + {}#{} with n={}. \
                     Invariant: |t| ≤ k ∧ -n ≤ t ≤ n ∧ 0 ≤ k ≤ n",
                    offset, errors, max_distance
                )
            }
            PositionError::InvalidMPosition { offset, errors, max_distance } => {
                write!(
                    f,
                    "Invalid M-position: M + {}#{} with n={}. \
                     Invariant: k ≥ -t - n ∧ -2n ≤ t ≤ 0 ∧ 0 ≤ k ≤ n",
                    offset, errors, max_distance
                )
            }
        }
    }
}

impl std::error::Error for PositionError {}

/// Generalized position with parameter (I or M)
///
/// From Definition 15 (thesis pages 30-33), adapted for runtime operations.
///
/// Unlike `UniversalPosition<V>`, this type does not use compile-time variant
/// specialization. Operations are determined at runtime via `OperationSet`.
///
/// # Notation Mapping
///
/// Theory → Rust:
/// - `I + t#k` → `INonFinal { offset: t, errors: k }`
/// - `M + t#k` → `MFinal { offset: t, errors: k }`
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum GeneralizedPosition {
    /// I-type (non-final): I + offset#errors
    ///
    /// Represents position relative to start of word.
    ///
    /// Invariant: |offset| ≤ errors ∧ -n ≤ offset ≤ n ∧ 0 ≤ errors ≤ n
    INonFinal {
        /// Offset from parameter I (range: -n to n)
        offset: i32,

        /// Number of errors consumed (range: 0 to n)
        errors: u8,
    },

    /// M-type (final): M + offset#errors
    ///
    /// Represents position relative to end of word.
    ///
    /// Invariant: errors ≥ -offset - n ∧ -2n ≤ offset ≤ 0 ∧ 0 ≤ errors ≤ n
    MFinal {
        /// Offset from parameter M (range: -2n to 0)
        offset: i32,

        /// Number of errors consumed (range: 0 to n)
        errors: u8,
    },
}

// Custom Ord implementation to sort by (errors, offset) for efficient subsumption checks
impl PartialOrd for GeneralizedPosition {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for GeneralizedPosition {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        use std::cmp::Ordering;
        use GeneralizedPosition::*;

        // Sort by (errors, offset) to enable early termination in subsumption checks
        // Positions with fewer errors come first, making it easy to skip positions
        // that cannot participate in subsumption relationships
        match (self, other) {
            (INonFinal { errors: e1, offset: o1 }, INonFinal { errors: e2, offset: o2 }) |
            (MFinal { errors: e1, offset: o1 }, MFinal { errors: e2, offset: o2 }) => {
                match e1.cmp(e2) {
                    Ordering::Equal => o1.cmp(o2),
                    other => other,
                }
            }
            // I-type comes before M-type
            (INonFinal { .. }, MFinal { .. }) => Ordering::Less,
            (MFinal { .. }, INonFinal { .. }) => Ordering::Greater,
        }
    }
}

impl GeneralizedPosition {
    /// Create new I-type (non-final) position with invariant validation
    ///
    /// # Arguments
    ///
    /// - `offset`: Offset t from parameter I (must satisfy |t| ≤ k and -n ≤ t ≤ n)
    /// - `errors`: Number of errors k consumed (must satisfy 0 ≤ k ≤ n)
    /// - `max_distance`: Maximum edit distance n
    ///
    /// # Invariant
    ///
    /// `|offset| ≤ errors ∧ -n ≤ offset ≤ n ∧ 0 ≤ errors ≤ n`
    ///
    /// # Example
    ///
    /// ```ignore
    /// let pos = GeneralizedPosition::new_i(0, 0, 2)?;  // I + 0#0
    /// let pos = GeneralizedPosition::new_i(1, 1, 2)?;  // I + 1#1
    /// let pos = GeneralizedPosition::new_i(-2, 2, 2)?; // I + (-2)#2
    /// ```
    pub fn new_i(offset: i32, errors: u8, max_distance: u8) -> Result<Self, PositionError> {
        let n = max_distance as i32;

        // Check invariant: |offset| ≤ errors ∧ -n ≤ offset ≤ n ∧ 0 ≤ errors ≤ n
        if offset.abs() <= errors as i32
            && offset >= -n
            && offset <= n
            && errors <= max_distance
        {
            Ok(GeneralizedPosition::INonFinal { offset, errors })
        } else {
            Err(PositionError::InvalidIPosition {
                offset,
                errors,
                max_distance,
            })
        }
    }

    /// Create new M-type (final) position with invariant validation
    ///
    /// # Arguments
    ///
    /// - `offset`: Offset t from parameter M (must satisfy -2n ≤ t ≤ 0 and k ≥ -t - n)
    /// - `errors`: Number of errors k consumed (must satisfy 0 ≤ k ≤ n)
    /// - `max_distance`: Maximum edit distance n
    ///
    /// # Invariant
    ///
    /// `errors ≥ -offset - n ∧ -2n ≤ offset ≤ 0 ∧ 0 ≤ errors ≤ n`
    ///
    /// # Example
    ///
    /// ```ignore
    /// let pos = GeneralizedPosition::new_m(0, 0, 2)?;   // M + 0#0
    /// let pos = GeneralizedPosition::new_m(-1, 1, 2)?;  // M + (-1)#1
    /// let pos = GeneralizedPosition::new_m(-4, 2, 2)?;  // M + (-4)#2
    /// ```
    pub fn new_m(offset: i32, errors: u8, max_distance: u8) -> Result<Self, PositionError> {
        let n = max_distance as i32;

        // Check invariant: errors ≥ -offset - n ∧ -2n ≤ offset ≤ 0 ∧ 0 ≤ errors ≤ n
        if errors as i32 >= -offset - n
            && offset >= -2 * n
            && offset <= 0
            && errors <= max_distance
        {
            Ok(GeneralizedPosition::MFinal { offset, errors })
        } else {
            Err(PositionError::InvalidMPosition {
                offset,
                errors,
                max_distance,
            })
        }
    }

    /// Get the offset value
    pub fn offset(&self) -> i32 {
        match self {
            GeneralizedPosition::INonFinal { offset, .. } |
            GeneralizedPosition::MFinal { offset, .. } => *offset,
        }
    }

    /// Get the error count
    pub fn errors(&self) -> u8 {
        match self {
            GeneralizedPosition::INonFinal { errors, .. } |
            GeneralizedPosition::MFinal { errors, .. } => *errors,
        }
    }

    /// Check if this is an I-type (non-final) position
    pub fn is_non_final(&self) -> bool {
        matches!(self, GeneralizedPosition::INonFinal { .. })
    }

    /// Check if this is an M-type (final) position
    pub fn is_final(&self) -> bool {
        matches!(self, GeneralizedPosition::MFinal { .. })
    }
}

impl fmt::Display for GeneralizedPosition {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            GeneralizedPosition::INonFinal { offset, errors } => {
                write!(f, "I + {}#{}", offset, errors)
            }
            GeneralizedPosition::MFinal { offset, errors } => {
                write!(f, "M + {}#{}", offset, errors)
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_new_i_valid() {
        // I + 0#0 (initial state)
        let pos = GeneralizedPosition::new_i(0, 0, 2).unwrap();
        assert_eq!(pos.offset(), 0);
        assert_eq!(pos.errors(), 0);
        assert!(pos.is_non_final());

        // I + 1#1
        let pos = GeneralizedPosition::new_i(1, 1, 2).unwrap();
        assert_eq!(pos.offset(), 1);
        assert_eq!(pos.errors(), 1);

        // I + (-2)#2
        let pos = GeneralizedPosition::new_i(-2, 2, 2).unwrap();
        assert_eq!(pos.offset(), -2);
        assert_eq!(pos.errors(), 2);
    }

    #[test]
    fn test_new_i_invalid() {
        // |offset| > errors
        assert!(GeneralizedPosition::new_i(2, 1, 2).is_err());

        // offset > n
        assert!(GeneralizedPosition::new_i(3, 3, 2).is_err());

        // offset < -n
        assert!(GeneralizedPosition::new_i(-3, 3, 2).is_err());

        // errors > n
        assert!(GeneralizedPosition::new_i(0, 3, 2).is_err());
    }

    #[test]
    fn test_new_m_valid() {
        // M + 0#0
        let pos = GeneralizedPosition::new_m(0, 0, 2).unwrap();
        assert_eq!(pos.offset(), 0);
        assert_eq!(pos.errors(), 0);
        assert!(pos.is_final());

        // M + (-1)#1
        let pos = GeneralizedPosition::new_m(-1, 1, 2).unwrap();
        assert_eq!(pos.offset(), -1);
        assert_eq!(pos.errors(), 1);

        // M + (-4)#2
        let pos = GeneralizedPosition::new_m(-4, 2, 2).unwrap();
        assert_eq!(pos.offset(), -4);
        assert_eq!(pos.errors(), 2);
    }

    #[test]
    fn test_new_m_invalid() {
        // errors < -offset - n
        assert!(GeneralizedPosition::new_m(-4, 1, 2).is_err());

        // offset > 0
        assert!(GeneralizedPosition::new_m(1, 1, 2).is_err());

        // offset < -2n
        assert!(GeneralizedPosition::new_m(-5, 2, 2).is_err());

        // errors > n
        assert!(GeneralizedPosition::new_m(-1, 3, 2).is_err());
    }

    #[test]
    fn test_ordering() {
        let pos1 = GeneralizedPosition::new_i(0, 0, 2).unwrap();
        let pos2 = GeneralizedPosition::new_i(1, 1, 2).unwrap();
        let pos3 = GeneralizedPosition::new_i(-1, 1, 2).unwrap();
        let pos4 = GeneralizedPosition::new_m(0, 0, 2).unwrap();

        // Sort by errors first
        assert!(pos1 < pos2);
        assert!(pos1 < pos3);

        // Within same error level, sort by offset
        assert!(pos3 < pos2);

        // I-type comes before M-type
        assert!(pos1 < pos4);
        assert!(pos2 < pos4);
    }

    #[test]
    fn test_display() {
        let pos1 = GeneralizedPosition::new_i(1, 2, 3).unwrap();
        assert_eq!(format!("{}", pos1), "I + 1#2");

        let pos2 = GeneralizedPosition::new_m(-1, 1, 2).unwrap();
        assert_eq!(format!("{}", pos2), "M + -1#1");
    }
}
