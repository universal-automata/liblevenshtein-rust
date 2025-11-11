//! Universal Position Types
//!
//! Implements universal positions from Mitankin's thesis (Definition 15, pages 30-33).
//!
//! # Theory Background
//!
//! Universal positions use parameters I (non-final) and M (final) instead of concrete word indices:
//! - `I + t#k`: Non-final position, offset t from start, k errors consumed
//! - `M + t#k`: Final position, offset t from end, k errors consumed
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
//! use liblevenshtein::transducer::universal::{UniversalPosition, Standard};
//!
//! // Create I-type position: I + 0#0 (initial state)
//! let initial = UniversalPosition::<Standard>::new_i(0, 0, 2)?;
//!
//! // Create M-type position: M + (-1)#1 (one error, one char before end)
//! let final_pos = UniversalPosition::<Standard>::new_m(-1, 1, 2)?;
//! ```

use std::fmt;
use std::marker::PhantomData;

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

/// Trait for position variants (Standard, Transposition, MergeAndSplit)
///
/// This trait distinguishes between the three distance variants from the thesis:
/// - χ = ε (Standard Levenshtein)
/// - χ = t (with Transposition)
/// - χ = ms (with Merge/Split)
pub trait PositionVariant: Clone + fmt::Debug + PartialEq + Eq + std::hash::Hash {
    /// Human-readable variant name
    fn variant_name() -> &'static str;
}

/// Standard Levenshtein distance variant (χ = ε)
///
/// Operations: insertion, deletion, substitution
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Standard;

impl PositionVariant for Standard {
    fn variant_name() -> &'static str {
        "Standard"
    }
}

/// Transposition variant (χ = t)
///
/// Operations: insertion, deletion, substitution, **transposition**
///
/// Note: d^t_L does NOT satisfy triangle inequality (see thesis page 3)
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Transposition {
    /// Regular position (usual type)
    Usual,

    /// Transposition state (waiting to complete swap)
    /// Corresponds to i#e_t notation in thesis
    TranspositionState,
}

impl PositionVariant for Transposition {
    fn variant_name() -> &'static str {
        "Transposition"
    }
}

/// Merge/Split variant (χ = ms)
///
/// Operations: insertion, deletion, substitution, **merge** (2→1), **split** (1→2)
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum MergeAndSplit {
    /// Regular position (usual type)
    Usual,

    /// Split state (waiting to emit second character)
    /// Corresponds to i#e_s notation in thesis
    SplitState,
}

impl PositionVariant for MergeAndSplit {
    fn variant_name() -> &'static str {
        "MergeAndSplit"
    }
}

/// Universal position with parameter (I or M)
///
/// From Definition 15 (thesis pages 30-33).
///
/// # Type Parameters
///
/// - `V`: Position variant (Standard, Transposition, or MergeAndSplit)
///
/// # Notation Mapping
///
/// Theory → Rust:
/// - `I + t#k` → `INonFinal { offset: t, errors: k, .. }`
/// - `M + t#k` → `MFinal { offset: t, errors: k, .. }`
/// - `It + t#k` → `INonFinal { .., variant: Transposition::TranspositionState }`
/// - `Is + t#k` → `INonFinal { .., variant: MergeAndSplit::SplitState }`
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum UniversalPosition<V: PositionVariant> {
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

        /// Position variant (Standard/Transposition/MergeAndSplit)
        variant: PhantomData<V>,
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

        /// Position variant (Standard/Transposition/MergeAndSplit)
        variant: PhantomData<V>,
    },
}

impl<V: PositionVariant> UniversalPosition<V> {
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
    /// let pos = UniversalPosition::<Standard>::new_i(0, 0, 2)?;  // I + 0#0
    /// let pos = UniversalPosition::<Standard>::new_i(1, 1, 2)?;  // I + 1#1
    /// let pos = UniversalPosition::<Standard>::new_i(-2, 2, 2)?; // I + (-2)#2
    /// ```
    pub fn new_i(offset: i32, errors: u8, max_distance: u8) -> Result<Self, PositionError> {
        let n = max_distance as i32;

        // Check invariant: |offset| ≤ errors ∧ -n ≤ offset ≤ n ∧ 0 ≤ errors ≤ max_distance
        if offset.abs() as u8 > errors
            || offset < -n
            || offset > n
            || errors > max_distance
        {
            return Err(PositionError::InvalidIPosition {
                offset,
                errors,
                max_distance,
            });
        }

        Ok(Self::INonFinal {
            offset,
            errors,
            variant: PhantomData,
        })
    }

    /// Create new M-type (final) position with invariant validation
    ///
    /// # Arguments
    ///
    /// - `offset`: Offset t from parameter M (must satisfy -2n ≤ t ≤ 0)
    /// - `errors`: Number of errors k consumed (must satisfy k ≥ -t - n and 0 ≤ k ≤ n)
    /// - `max_distance`: Maximum edit distance n
    ///
    /// # Invariant
    ///
    /// `errors ≥ -offset - n ∧ -2n ≤ offset ≤ 0 ∧ 0 ≤ errors ≤ n`
    ///
    /// # Example
    ///
    /// ```ignore
    /// let pos = UniversalPosition::<Standard>::new_m(0, 0, 2)?;   // M + 0#0
    /// let pos = UniversalPosition::<Standard>::new_m(-1, 1, 2)?;  // M + (-1)#1
    /// let pos = UniversalPosition::<Standard>::new_m(-2, 0, 2)?;  // M + (-2)#0
    /// ```
    pub fn new_m(offset: i32, errors: u8, max_distance: u8) -> Result<Self, PositionError> {
        let n = max_distance as i32;

        // Check invariant: errors ≥ -offset - n ∧ -2n ≤ offset ≤ 0 ∧ 0 ≤ errors ≤ max_distance
        if (errors as i32) < -offset - n
            || offset < -2 * n
            || offset > 0
            || errors > max_distance
        {
            return Err(PositionError::InvalidMPosition {
                offset,
                errors,
                max_distance,
            });
        }

        Ok(Self::MFinal {
            offset,
            errors,
            variant: PhantomData,
        })
    }

    /// Get the offset value
    pub fn offset(&self) -> i32 {
        match self {
            Self::INonFinal { offset, .. } | Self::MFinal { offset, .. } => *offset,
        }
    }

    /// Get the error count
    pub fn errors(&self) -> u8 {
        match self {
            Self::INonFinal { errors, .. } | Self::MFinal { errors, .. } => *errors,
        }
    }

    /// Check if this is an I-type (non-final) position
    pub fn is_i_type(&self) -> bool {
        matches!(self, Self::INonFinal { .. })
    }

    /// Check if this is an M-type (final) position
    pub fn is_m_type(&self) -> bool {
        matches!(self, Self::MFinal { .. })
    }
}

impl<V: PositionVariant> fmt::Display for UniversalPosition<V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::INonFinal { offset, errors, .. } => {
                write!(f, "I + {}#{}", offset, errors)
            }
            Self::MFinal { offset, errors, .. } => {
                write!(f, "M + {}#{}", offset, errors)
            }
        }
    }
}
