//! Subsumption Relation for Generalized Positions
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
//! # Phase 1 Implementation
//!
//! Current implementation supports standard operations only (match, substitute, insert, delete).
//! This means we use the standard subsumption rule above.
//!
//! Future phases will add runtime OperationSet-specific subsumption rules.

use super::position::GeneralizedPosition;

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
///
/// # Phase 1: Standard Operations Only
///
/// This implementation uses the standard subsumption rule. Future phases
/// will extend this to support custom operation sets.
///
/// # Example
///
/// ```ignore
/// let pos1 = GeneralizedPosition::new_i(4, 1, 3)?;
/// let pos2 = GeneralizedPosition::new_i(5, 2, 3)?;
/// assert!(subsumes(&pos1, &pos2, 3));  // 4#1 <^ε_s 5#2
/// ```
#[inline(always)]
pub fn subsumes(
    pos1: &GeneralizedPosition,
    pos2: &GeneralizedPosition,
    max_distance: u8,
) -> bool {
    subsumes_standard(pos1, pos2, max_distance)
}

/// Standard subsumption rule implementation
///
/// From Definition 11 (page 18): i#e ≤^ε_s j#f ⇔ f > e ∧ |j - i| ≤ f - e
///
/// # Arguments
///
/// - `pos1`: Position i#e (potential subsumer)
/// - `pos2`: Position j#f (potentially subsumed)
/// - `_max_distance`: Maximum distance n (unused for standard, kept for consistency)
///
/// # Returns
///
/// `true` if pos1 <^ε_s pos2, `false` otherwise
///
/// # Conditions
///
/// 1. Both must be same type (I or M)
/// 2. pos2 has more errors: f > e
/// 3. Positions close enough: |j - i| ≤ f - e
fn subsumes_standard(
    pos1: &GeneralizedPosition,
    pos2: &GeneralizedPosition,
    _max_distance: u8,
) -> bool {
    use GeneralizedPosition::*;

    match (pos1, pos2) {
        // I-type subsumes I-type
        (
            INonFinal {
                offset: i,
                errors: e,
            },
            INonFinal {
                offset: j,
                errors: f,
            },
        ) => {
            // f > e (pos2 has more errors available)
            if *f <= *e {
                return false;
            }

            let error_diff = (*f - *e) as i32;
            let offset_diff = (*j - *i).abs();

            // |j - i| ≤ f - e
            offset_diff <= error_diff
        }

        // M-type subsumes M-type
        (
            MFinal {
                offset: i,
                errors: e,
            },
            MFinal {
                offset: j,
                errors: f,
            },
        ) => {
            // Same logic as I-type
            if *f <= *e {
                return false;
            }

            let error_diff = (*f - *e) as i32;
            let offset_diff = (*j - *i).abs();

            offset_diff <= error_diff
        }

        // Different types cannot subsume each other
        _ => false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_subsumes_i_type_standard() {
        // Test case: 1#2 <^ε_s 2#3
        // Valid positions: |1| ≤ 2 ✓ and |2| ≤ 3 ✓
        // f > e: 3 > 2 ✓
        // |j - i| ≤ f - e: |2 - 1| = 1 ≤ 3 - 2 = 1 ✓
        let pos1 = GeneralizedPosition::new_i(1, 2, 3).unwrap();
        let pos2 = GeneralizedPosition::new_i(2, 3, 3).unwrap();
        assert!(subsumes(&pos1, &pos2, 3));
    }

    #[test]
    fn test_not_subsumes_too_far() {
        // 0#2 should not subsume -2#3 (offset difference too large)
        // Valid positions: |0| ≤ 2 ✓ and |-2| ≤ 3 ✓
        // f > e: 3 > 2 ✓
        // |j - i| ≤ f - e: |-2 - 0| = 2 ≤ 3 - 2 = 1? NO
        let pos1 = GeneralizedPosition::new_i(0, 2, 3).unwrap();
        let pos2 = GeneralizedPosition::new_i(-2, 3, 3).unwrap();
        assert!(!subsumes(&pos1, &pos2, 3));
    }

    #[test]
    fn test_not_subsumes_same_errors() {
        // Cannot subsume if same error count
        let pos1 = GeneralizedPosition::new_i(0, 1, 3).unwrap();
        let pos2 = GeneralizedPosition::new_i(1, 1, 3).unwrap();
        assert!(!subsumes(&pos1, &pos2, 3));
    }

    #[test]
    fn test_subsumes_m_type_standard() {
        // M-type subsumption works the same way
        let pos1 = GeneralizedPosition::new_m(-1, 0, 2).unwrap();
        let pos2 = GeneralizedPosition::new_m(-2, 1, 2).unwrap();
        assert!(subsumes(&pos1, &pos2, 2));
    }

    #[test]
    fn test_not_subsumes_different_types() {
        // I-type cannot subsume M-type and vice versa
        let i_pos = GeneralizedPosition::new_i(0, 0, 2).unwrap();
        let m_pos = GeneralizedPosition::new_m(0, 0, 2).unwrap();
        assert!(!subsumes(&i_pos, &m_pos, 2));
        assert!(!subsumes(&m_pos, &i_pos, 2));
    }

    #[test]
    fn test_subsumes_reflexive_false() {
        // A position cannot subsume itself (requires f > e)
        let pos = GeneralizedPosition::new_i(0, 1, 3).unwrap();
        assert!(!subsumes(&pos, &pos, 3));
    }

    #[test]
    fn test_subsumes_boundary_case() {
        // Boundary case: |j - i| = f - e exactly
        let pos1 = GeneralizedPosition::new_i(0, 0, 3).unwrap();
        let pos2 = GeneralizedPosition::new_i(2, 2, 3).unwrap();
        // f > e: 2 > 0 ✓
        // |j - i| ≤ f - e: |2 - 0| = 2 ≤ 2 - 0 = 2 ✓
        assert!(subsumes(&pos1, &pos2, 3));
    }

    #[test]
    fn test_subsumes_negative_offsets() {
        // Test with negative offsets
        let pos1 = GeneralizedPosition::new_i(-1, 2, 3).unwrap();
        let pos2 = GeneralizedPosition::new_i(0, 3, 3).unwrap();
        // f > e: 3 > 2 ✓
        // |j - i| ≤ f - e: |0 - (-1)| = 1 ≤ 3 - 2 = 1 ✓
        assert!(subsumes(&pos1, &pos2, 3));
    }
}
