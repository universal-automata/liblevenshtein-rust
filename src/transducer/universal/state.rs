//! Universal State Type
//!
//! Implements universal states from Mitankin's thesis (Definition 15, pages 38-39).
//!
//! # Theory Background
//!
//! Universal states are sets of universal positions that maintain the anti-chain property:
//! no position subsumes another. This enables efficient state minimization.
//!
//! ## State Sets (Page 38)
//!
//! **Non-final states**:
//! ```text
//! I^χ_states = {Q | Q ⊆ I^χ_s ∧ ∀q₁,q₂ ∈ Q (q₁ ⊀^χ_s q₂)} \ {∅}
//! ```
//!
//! **Final states**:
//! ```text
//! M^χ_states = {Q | Q ⊆ M^χ_s ∧
//!               ∀q₁,q₂ ∈ Q (q₁ ⊀^χ_s q₂) ∧
//!               ∃q ∈ Q (q ≤^χ_s M#n) ∧
//!               ∃i ∈ [-n, 0] ∀q ∈ Q (M + i#0 ≤^χ_s q)} \ {∅}
//! ```
//!
//! **All states**:
//! ```text
//! Q^∀,χ_n = I^χ_states ∪ M^χ_states
//! ```
//!
//! ## Anti-chain Property
//!
//! For all positions p₁, p₂ in state Q:
//! - p₁ ⊀^χ_s p₂ (p₁ does not subsume p₂)
//! - p₂ ⊀^χ_s p₁ (p₂ does not subsume p₁)
//!
//! This is maintained by the ⊔ (join) operator when adding positions.
//!
//! # Examples
//!
//! ```ignore
//! use liblevenshtein::transducer::universal::{UniversalState, UniversalPosition, Standard};
//!
//! // Create initial state: {I + 0#0}
//! let initial = UniversalState::<Standard>::initial(2);
//! assert!(!initial.is_final());
//!
//! // Create state with multiple positions
//! let mut state = UniversalState::<Standard>::new(2);
//! state.add_position(UniversalPosition::new_i(0, 0, 2)?);
//! state.add_position(UniversalPosition::new_i(1, 1, 2)?);
//! ```

use std::collections::HashSet;
use std::fmt;

use crate::transducer::universal::position::{PositionVariant, UniversalPosition};
use crate::transducer::universal::subsumption::subsumes;

/// Universal state maintaining anti-chain property
///
/// A state is a set of universal positions where no position subsumes another.
/// This implements Q^∀,χ_n from the thesis (Definition 15, pages 38-39).
///
/// # Type Parameters
///
/// - `V`: Position variant (Standard, Transposition, or MergeAndSplit)
///
/// # Invariant
///
/// For all p₁, p₂ ∈ positions: p₁ ⊀^χ_s p₂ ∧ p₂ ⊀^χ_s p₁
///
/// This invariant is maintained by `add_position()` using the ⊔ operator.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct UniversalState<V: PositionVariant> {
    /// Set of positions (anti-chain)
    positions: HashSet<UniversalPosition<V>>,

    /// Maximum edit distance n
    max_distance: u8,
}

impl<V: PositionVariant> UniversalState<V> {
    /// Create new empty state
    ///
    /// # Arguments
    ///
    /// - `max_distance`: Maximum edit distance n
    ///
    /// # Example
    ///
    /// ```ignore
    /// let state = UniversalState::<Standard>::new(2);
    /// assert!(state.is_empty());
    /// ```
    pub fn new(max_distance: u8) -> Self {
        Self {
            positions: HashSet::new(),
            max_distance,
        }
    }

    /// Create initial state {I + 0#0}
    ///
    /// From thesis page 38: Initial state I^∀,χ = {I + 0#0}
    ///
    /// # Arguments
    ///
    /// - `max_distance`: Maximum edit distance n
    ///
    /// # Example
    ///
    /// ```ignore
    /// let initial = UniversalState::<Standard>::initial(2);
    /// assert_eq!(initial.len(), 1);
    /// assert!(!initial.is_final());
    /// ```
    pub fn initial(max_distance: u8) -> Self {
        let mut state = Self::new(max_distance);
        // I + 0#0 always satisfies invariant, so unwrap is safe
        let initial_pos = UniversalPosition::new_i(0, 0, max_distance)
            .expect("I + 0#0 should always be valid");
        state.positions.insert(initial_pos);
        state
    }

    /// Add position, maintaining anti-chain property (⊔ operator)
    ///
    /// Implements the subsumption closure from the thesis:
    /// 1. Remove all positions that subsume the new position (worse positions)
    /// 2. Add new position if it doesn't subsume any existing position
    ///
    /// This maintains the invariant ∀p₁,p₂ ∈ Q (p₁ ⊀^χ_s p₂).
    ///
    /// Note: If p1 <^χ_s p2, then p1 subsumes p2, meaning p2 is "better" (more errors).
    /// We keep the better positions and discard the worse ones.
    ///
    /// # Arguments
    ///
    /// - `pos`: Position to add
    ///
    /// # Example
    ///
    /// ```ignore
    /// let mut state = UniversalState::<Standard>::new(2);
    /// state.add_position(UniversalPosition::new_i(0, 0, 2)?);
    /// state.add_position(UniversalPosition::new_i(1, 1, 2)?);
    /// ```
    pub fn add_position(&mut self, pos: UniversalPosition<V>) {
        // Remove positions where p subsumes pos (p <^χ_s pos)
        // These are "worse" positions that should be discarded
        self.positions.retain(|p| !subsumes(p, &pos, self.max_distance));

        // Add new position only if pos doesn't subsume any existing position
        // If pos <^χ_s p for some p, then pos is "worse" and should be rejected
        if !self.positions.iter().any(|p| subsumes(&pos, p, self.max_distance)) {
            self.positions.insert(pos);
        }
    }

    /// Check if state is empty
    pub fn is_empty(&self) -> bool {
        self.positions.is_empty()
    }

    /// Get number of positions in state
    pub fn len(&self) -> usize {
        self.positions.len()
    }

    /// Get iterator over positions
    pub fn positions(&self) -> impl Iterator<Item = &UniversalPosition<V>> {
        self.positions.iter()
    }

    /// Check if state contains a position
    pub fn contains(&self, pos: &UniversalPosition<V>) -> bool {
        self.positions.contains(pos)
    }

    /// Check if state is final
    ///
    /// A state is final if it contains an M-type position that could accept.
    /// From the thesis, this means the state contains a position subsuming M + 0#k
    /// for some k ≤ n.
    ///
    /// For simplicity in Phase 1, we check if there exists an M-type position with offset ≤ 0.
    ///
    /// # Example
    ///
    /// ```ignore
    /// let mut state = UniversalState::<Standard>::new(2);
    /// state.add_position(UniversalPosition::new_m(0, 0, 2)?);
    /// assert!(state.is_final());
    /// ```
    pub fn is_final(&self) -> bool {
        self.positions.iter().any(|pos| match pos {
            UniversalPosition::MFinal { offset, .. } => *offset <= 0,
            _ => false,
        })
    }

    /// Get maximum distance
    pub fn max_distance(&self) -> u8 {
        self.max_distance
    }

    /// Check if this state contains only I-type positions
    pub fn is_i_state(&self) -> bool {
        !self.is_empty() && self.positions.iter().all(|p| p.is_i_type())
    }

    /// Check if this state contains only M-type positions
    pub fn is_m_state(&self) -> bool {
        !self.is_empty() && self.positions.iter().all(|p| p.is_m_type())
    }

    /// Check if this state contains mixed I and M positions
    pub fn is_mixed_state(&self) -> bool {
        if self.is_empty() {
            return false;
        }
        let has_i = self.positions.iter().any(|p| p.is_i_type());
        let has_m = self.positions.iter().any(|p| p.is_m_type());
        has_i && has_m
    }
}

impl<V: PositionVariant> fmt::Display for UniversalState<V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{{")?;
        let mut first = true;
        for pos in &self.positions {
            if !first {
                write!(f, ", ")?;
            }
            write!(f, "{}", pos)?;
            first = false;
        }
        write!(f, "}}")
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::transducer::universal::position::Standard;

    // =========================================================================
    // Basic State Tests
    // =========================================================================

    #[test]
    fn test_empty_state() {
        let state = UniversalState::<Standard>::new(2);
        assert!(state.is_empty());
        assert_eq!(state.len(), 0);
        assert!(!state.is_final());
        assert_eq!(state.max_distance(), 2);
    }

    #[test]
    fn test_initial_state() {
        let state = UniversalState::<Standard>::initial(2);
        assert!(!state.is_empty());
        assert_eq!(state.len(), 1);
        assert!(!state.is_final());

        let pos = UniversalPosition::new_i(0, 0, 2).unwrap();
        assert!(state.contains(&pos));
    }

    #[test]
    fn test_add_single_position() {
        let mut state = UniversalState::<Standard>::new(2);
        let pos = UniversalPosition::new_i(1, 1, 2).unwrap();

        state.add_position(pos.clone());
        assert_eq!(state.len(), 1);
        assert!(state.contains(&pos));
    }

    #[test]
    fn test_add_multiple_non_subsuming_positions() {
        let mut state = UniversalState::<Standard>::new(3);
        // Use positions that don't subsume each other:
        // 0#1 and -2#2
        // Check: does 0#1 subsume -2#2? f > e: 2 > 1 ✓, |-2 - 0| = 2 ≤ 2 - 1 = 1? NO
        // Check: does -2#2 subsume 0#1? f > e: 1 > 2? NO
        let pos1 = UniversalPosition::new_i(0, 1, 3).unwrap();
        let pos2 = UniversalPosition::new_i(-2, 2, 3).unwrap();

        state.add_position(pos1.clone());
        state.add_position(pos2.clone());

        // Both positions remain (not subsuming each other)
        assert_eq!(state.len(), 2);
        assert!(state.contains(&pos1));
        assert!(state.contains(&pos2));
    }

    // =========================================================================
    // Anti-chain / Subsumption Tests
    // =========================================================================

    #[test]
    fn test_add_position_removes_subsumed() {
        // Add 1#1, then add 2#2 which should remove 1#1 (since 1#1 <^ε_s 2#2)
        let mut state = UniversalState::<Standard>::new(3);
        let pos1 = UniversalPosition::new_i(1, 1, 3).unwrap();
        let pos2 = UniversalPosition::new_i(2, 2, 3).unwrap();

        state.add_position(pos1.clone());
        assert_eq!(state.len(), 1);

        state.add_position(pos2.clone());
        // pos1 should be removed because pos1 <^ε_s pos2
        assert_eq!(state.len(), 1);
        assert!(!state.contains(&pos1));
        assert!(state.contains(&pos2));
    }

    #[test]
    fn test_add_position_rejected_if_subsumed() {
        // Add 2#2, then try to add 1#1 which should be rejected
        let mut state = UniversalState::<Standard>::new(3);
        let pos1 = UniversalPosition::new_i(2, 2, 3).unwrap();
        let pos2 = UniversalPosition::new_i(1, 1, 3).unwrap();

        state.add_position(pos1.clone());
        assert_eq!(state.len(), 1);

        state.add_position(pos2.clone());
        // pos2 should not be added because pos2 <^ε_s pos1
        assert_eq!(state.len(), 1);
        assert!(state.contains(&pos1));
        assert!(!state.contains(&pos2));
    }

    #[test]
    fn test_anti_chain_maintained() {
        // Add multiple positions and verify no position subsumes another
        let mut state = UniversalState::<Standard>::new(3);

        // Use valid positions that don't subsume each other
        let pos1 = UniversalPosition::new_i(0, 1, 3).unwrap();
        let pos2 = UniversalPosition::new_i(-2, 2, 3).unwrap(); // Valid: |-2| = 2 ≤ 2
        let pos3 = UniversalPosition::new_i(-1, 1, 3).unwrap();

        state.add_position(pos1.clone());
        state.add_position(pos2.clone());
        state.add_position(pos3.clone());

        // Verify anti-chain: no position subsumes another
        let positions: Vec<_> = state.positions().collect();
        for (i, p1) in positions.iter().enumerate() {
            for (j, p2) in positions.iter().enumerate() {
                if i != j {
                    assert!(!subsumes(p1, p2, state.max_distance()));
                }
            }
        }
    }

    // =========================================================================
    // Final State Tests
    // =========================================================================

    #[test]
    fn test_final_state_with_m_zero() {
        let mut state = UniversalState::<Standard>::new(2);
        let pos = UniversalPosition::new_m(0, 0, 2).unwrap();

        state.add_position(pos);
        assert!(state.is_final());
    }

    #[test]
    fn test_final_state_with_m_negative() {
        let mut state = UniversalState::<Standard>::new(2);
        let pos = UniversalPosition::new_m(-1, 1, 2).unwrap();

        state.add_position(pos);
        assert!(state.is_final());
    }

    #[test]
    fn test_not_final_with_only_i_positions() {
        let mut state = UniversalState::<Standard>::new(2);
        let pos = UniversalPosition::new_i(0, 0, 2).unwrap();

        state.add_position(pos);
        assert!(!state.is_final());
    }

    // =========================================================================
    // State Type Tests
    // =========================================================================

    #[test]
    fn test_is_i_state() {
        let mut state = UniversalState::<Standard>::new(2);
        let pos1 = UniversalPosition::new_i(0, 0, 2).unwrap();
        let pos2 = UniversalPosition::new_i(1, 1, 2).unwrap();

        state.add_position(pos1);
        state.add_position(pos2);

        assert!(state.is_i_state());
        assert!(!state.is_m_state());
        assert!(!state.is_mixed_state());
    }

    #[test]
    fn test_is_m_state() {
        let mut state = UniversalState::<Standard>::new(2);
        let pos1 = UniversalPosition::new_m(0, 0, 2).unwrap();
        let pos2 = UniversalPosition::new_m(-1, 1, 2).unwrap();

        state.add_position(pos1);
        state.add_position(pos2);

        assert!(!state.is_i_state());
        assert!(state.is_m_state());
        assert!(!state.is_mixed_state());
    }

    #[test]
    fn test_is_mixed_state() {
        let mut state = UniversalState::<Standard>::new(2);
        let i_pos = UniversalPosition::new_i(0, 0, 2).unwrap();
        let m_pos = UniversalPosition::new_m(0, 0, 2).unwrap();

        state.add_position(i_pos);
        state.add_position(m_pos);

        assert!(!state.is_i_state());
        assert!(!state.is_m_state());
        assert!(state.is_mixed_state());
    }

    // =========================================================================
    // Iterator Tests
    // =========================================================================

    #[test]
    fn test_positions_iterator() {
        let mut state = UniversalState::<Standard>::new(3);
        // Use positions that don't subsume each other
        let pos1 = UniversalPosition::new_i(0, 1, 3).unwrap();
        let pos2 = UniversalPosition::new_i(-2, 2, 3).unwrap();

        state.add_position(pos1.clone());
        state.add_position(pos2.clone());

        let positions: HashSet<_> = state.positions().cloned().collect();
        assert_eq!(positions.len(), 2);
        assert!(positions.contains(&pos1));
        assert!(positions.contains(&pos2));
    }

    // =========================================================================
    // Display Tests
    // =========================================================================

    #[test]
    fn test_display_empty_state() {
        let state = UniversalState::<Standard>::new(2);
        assert_eq!(format!("{}", state), "{}");
    }

    #[test]
    fn test_display_single_position() {
        let mut state = UniversalState::<Standard>::new(2);
        let pos = UniversalPosition::new_i(0, 0, 2).unwrap();
        state.add_position(pos);

        let display = format!("{}", state);
        assert!(display.contains("I + 0#0"));
    }

    #[test]
    fn test_display_multiple_positions() {
        let mut state = UniversalState::<Standard>::new(3);
        // Use positions that don't subsume each other
        let pos1 = UniversalPosition::new_i(0, 1, 3).unwrap();
        let pos2 = UniversalPosition::new_i(-2, 2, 3).unwrap();

        state.add_position(pos1);
        state.add_position(pos2);

        let display = format!("{}", state);
        assert!(display.contains("I + 0#1"));
        assert!(display.contains("I + -2#2"));
    }

    // =========================================================================
    // Equality Tests
    // =========================================================================

    #[test]
    fn test_state_equality() {
        let mut state1 = UniversalState::<Standard>::new(2);
        let mut state2 = UniversalState::<Standard>::new(2);

        let pos = UniversalPosition::new_i(1, 1, 2).unwrap();
        state1.add_position(pos.clone());
        state2.add_position(pos);

        assert_eq!(state1, state2);
    }

    #[test]
    fn test_state_inequality_different_positions() {
        let mut state1 = UniversalState::<Standard>::new(2);
        let mut state2 = UniversalState::<Standard>::new(2);

        state1.add_position(UniversalPosition::new_i(0, 0, 2).unwrap());
        state2.add_position(UniversalPosition::new_i(1, 1, 2).unwrap());

        assert_ne!(state1, state2);
    }

    #[test]
    fn test_state_clone() {
        let mut state1 = UniversalState::<Standard>::new(2);
        state1.add_position(UniversalPosition::new_i(1, 1, 2).unwrap());

        let state2 = state1.clone();
        assert_eq!(state1, state2);
    }
}
