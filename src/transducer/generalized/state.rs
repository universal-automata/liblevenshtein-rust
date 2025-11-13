//! Generalized State Type
//!
//! Implements universal states adapted for runtime-configurable operations.
//! Based on Definition 15 from Mitankin's thesis (pages 38-39), but without
//! compile-time variant specialization.
//!
//! # Phase 1 Limitations
//!
//! Current implementation supports **standard operations only** (match, substitute, insert, delete).
//! Future phases will add:
//! - Runtime OperationSet parameter
//! - Multi-character operations
//! - Custom operation sets
//!
//! # Theory Background
//!
//! Universal states are sets of universal positions that maintain the anti-chain property:
//! no position subsumes another. This enables efficient state minimization.
//!
//! ## Anti-chain Property
//!
//! For all positions p₁, p₂ in state Q:
//! - p₁ ⊀^χ_s p₂ (p₁ does not subsume p₂)
//! - p₂ ⊀^χ_s p₁ (p₂ does not subsume p₁)
//!
//! This is maintained by the ⊔ (join) operator when adding positions.

use smallvec::SmallVec;
use std::fmt;

use super::bit_vector::CharacteristicVector;
use super::position::GeneralizedPosition;
use super::subsumption::subsumes;

/// Generalized state maintaining anti-chain property
///
///  state is a set of generalized positions where no position subsumes another.
///
/// # Invariant
///
/// For all p₁, p₂ ∈ positions: p₁ ⊀^χ_s p₂ ∧ p₂ ⊀^χ_s p₁
///
/// This invariant is maintained by `add_position()` using the ⊔ operator.
///
/// # SmallVec Optimization
///
/// Uses SmallVec with inline size of 8 to avoid heap allocations for typical states.
/// See universal/state.rs for theoretical justification via bounded diagonal property.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GeneralizedState {
    /// Set of positions (anti-chain), maintained in sorted order
    /// SmallVec avoids heap allocation for states with ≤8 positions
    positions: SmallVec<[GeneralizedPosition; 8]>,

    /// Maximum edit distance n
    max_distance: u8,
}

impl GeneralizedState {
    /// Create new empty state
    ///
    /// # Arguments
    ///
    /// - `max_distance`: Maximum edit distance n
    pub fn new(max_distance: u8) -> Self {
        Self {
            positions: SmallVec::new(),
            max_distance,
        }
    }

    /// Create initial state {I + 0#0}
    ///
    /// From thesis page 38: Initial state I^∀,χ = {I + 0#0}
    pub fn initial(max_distance: u8) -> Self {
        let mut state = Self::new(max_distance);
        // I + 0#0 always satisfies invariant, so unwrap is safe
        let initial_pos = GeneralizedPosition::new_i(0, 0, max_distance)
            .expect("I + 0#0 should always be valid");
        state.positions.push(initial_pos);
        state
    }

    /// Add position, maintaining anti-chain property (⊔ operator)
    ///
    /// Implements the subsumption closure from the thesis:
    /// 1. Remove all positions subsumed by the new position (worse positions)
    /// 2. Add new position if it's not subsumed by any existing position
    ///
    /// This maintains the invariant ∀p₁,p₂ ∈ Q (p₁ ⊀^χ_s p₂).
    pub fn add_position(&mut self, pos: GeneralizedPosition) {
        // Check if this position is subsumed by an existing one
        for existing in &self.positions {
            if subsumes(existing, &pos, self.max_distance) {
                return; // Already covered by existing position
            }
        }

        // Remove any positions that this new position subsumes
        self.positions
            .retain(|p| !subsumes(&pos, p, self.max_distance));

        // Insert in sorted position (binary search)
        let insert_pos = self
            .positions
            .binary_search(&pos)
            .unwrap_or_else(|pos| pos);
        self.positions.insert(insert_pos, pos);
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
    pub fn positions(&self) -> impl Iterator<Item = &GeneralizedPosition> {
        self.positions.iter()
    }

    /// Check if state is final
    ///
    /// A state is final if it contains an M-type position with offset ≤ 0.
    pub fn is_final(&self) -> bool {
        self.positions.iter().any(|pos| match pos {
            GeneralizedPosition::MFinal { offset, .. } => *offset <= 0,
            _ => false,
        })
    }

    /// Compute transition to successor state (δ^∀,χ_n)
    ///
    /// Phase 2: Supports runtime-configurable operations via OperationSet.
    ///
    /// # Arguments
    ///
    /// - `operations`: Set of operations defining the edit distance metric
    /// - `bit_vector`: Characteristic vector β(a, w) encoding matches for character a
    /// - `_input_length`: Reserved for diagonal crossing (future)
    ///
    /// # Returns
    ///
    /// Successor state, or `None` if no successors exist (undefined transition)
    pub fn transition(
        &self,
        operations: &crate::transducer::OperationSet,
        bit_vector: &CharacteristicVector,
        _input_length: usize,
    ) -> Option<Self> {
        // Special case: empty state has no successors
        if self.is_empty() {
            return None;
        }

        // Create new state for successors
        let mut next_state = Self::new(self.max_distance);

        // For each position in current state
        for pos in &self.positions {
            // Compute successors using runtime-configurable operations
            let successors = self.successors(pos, operations, bit_vector);

            // Add all successors to next state
            for succ in successors {
                next_state.add_position(succ);
            }
        }

        // Return None if no successors (undefined transition)
        if next_state.is_empty() {
            None
        } else {
            Some(next_state)
        }
    }

    /// Compute successors for a position using runtime-configurable operations
    ///
    /// Phase 2: Uses OperationSet to support custom edit distance metrics.
    fn successors(
        &self,
        pos: &GeneralizedPosition,
        operations: &crate::transducer::OperationSet,
        bit_vector: &CharacteristicVector,
    ) -> Vec<GeneralizedPosition> {
        match pos {
            GeneralizedPosition::INonFinal { offset, errors } => {
                self.successors_i_type(*offset, *errors, operations, bit_vector)
            }
            GeneralizedPosition::MFinal { offset, errors } => {
                self.successors_m_type(*offset, *errors, operations, bit_vector)
            }
        }
    }

    /// Compute successors for I-type positions with runtime-configurable operations
    ///
    /// Based on Universal automaton's δ^D,ε_e with I^ε conversion.
    ///
    /// # I^ε Conversion
    ///
    /// Universal positions use δ^D,ε_e which operates on raw offsets,
    /// then converts via I^ε({i#e}) = {I + (i-1)#e}.
    ///
    /// This means:
    /// - MATCH: t+1#e → I^ε → I+t#e (offset stays same)
    /// - DELETE: t#e+1 → I^ε → I+(t-1)#(e+1) (offset decreases)
    /// - INSERT: (t+1)#(e+1) → I^ε → I+t#(e+1) (offset stays same)
    /// - SUBSTITUTE: (t+1)#(e+1) → I^ε → I+t#(e+1) (offset stays same)
    fn successors_i_type(
        &self,
        offset: i32,
        errors: u8,
        operations: &crate::transducer::OperationSet,
        bit_vector: &CharacteristicVector,
    ) -> Vec<GeneralizedPosition> {
        let mut successors = Vec::new();
        let n = self.max_distance as i32;

        // Bit vector index for current position: offset + n
        let match_index = (offset + n) as usize;

        // Case 1: Position within visible window
        if match_index < bit_vector.len() {
            let has_match = bit_vector.is_match(match_index);

            // Iterate over all operations
            for op in operations.operations() {
                // Only handle single-char operations for now (Phase 2c will add multi-char)
                if op.consume_x() > 1 || op.consume_y() > 1 {
                    continue;
                }

                // Classify operation type and generate successors
                if op.is_match() {
                    // Match operation: ⟨1, 1, 0.0⟩
                    if has_match {
                        // δ^D,ε_e: (t+1)#e → I^ε → I+t#e
                        if let Ok(succ) = GeneralizedPosition::new_i(offset, errors, self.max_distance) {
                            successors.push(succ);
                            // Match takes precedence - early return
                            return successors;
                        }
                    }
                } else if op.is_deletion() {
                    // Delete operation: ⟨1, 0, w⟩
                    if errors < self.max_distance {
                        let new_errors = errors + op.weight() as u8;
                        if new_errors <= self.max_distance {
                            // δ^D,ε_e: t#(e+w) → I^ε → I+(t-1)#(e+w)
                            if let Ok(succ) = GeneralizedPosition::new_i(offset - 1, new_errors, self.max_distance) {
                                successors.push(succ);
                            }
                        }
                    }
                } else if op.is_insertion() || op.is_substitution() {
                    // Insert ⟨0, 1, w⟩ or Substitute ⟨1, 1, w⟩
                    if errors < self.max_distance {
                        let new_errors = errors + op.weight() as u8;
                        if new_errors <= self.max_distance {
                            // δ^D,ε_e: (t+1)#(e+w) → I^ε → I+t#(e+w)
                            if let Ok(succ) = GeneralizedPosition::new_i(offset, new_errors, self.max_distance) {
                                successors.push(succ);
                            }
                        }
                    }
                }
            }

            // SKIP-TO-MATCH optimization (Phase 2c: generalize for multi-char)
            if !has_match && errors < self.max_distance {
                for idx in (match_index + 1)..bit_vector.len() {
                    if bit_vector.is_match(idx) {
                        let skip_distance = (idx - match_index) as i32;
                        let new_errors = errors + skip_distance as u8;
                        if new_errors <= self.max_distance {
                            if let Ok(succ) = GeneralizedPosition::new_i(offset + skip_distance, new_errors, self.max_distance) {
                                successors.push(succ);
                            }
                        }
                        break;
                    }
                }
            }

            return successors;
        }

        // Case 2: Position beyond visible window
        // This happens when input is longer than word (e.g., "test" vs "tests")
        // We still need to generate error transitions to account for extra input
        if errors >= self.max_distance {
            return successors; // No error budget left
        }

        // Special case: empty bit vector
        if bit_vector.is_empty() {
            if let Ok(succ) = GeneralizedPosition::new_i(offset - 1, errors + 1, self.max_distance) {
                successors.push(succ);
            }
            return successors;
        }

        // Generate generic error transitions for positions outside window
        // DELETE: skip word character
        if let Ok(succ) = GeneralizedPosition::new_i(offset - 1, errors + 1, self.max_distance) {
            successors.push(succ);
        }

        // INSERT/SUBSTITUTE: advance input
        if let Ok(succ) = GeneralizedPosition::new_i(offset, errors + 1, self.max_distance) {
            successors.push(succ);
        }

        successors
    }

    /// Compute successors for M-type positions with runtime-configurable operations
    ///
    /// Similar logic to I-type, but positions are relative to end of word.
    fn successors_m_type(
        &self,
        offset: i32,
        errors: u8,
        operations: &crate::transducer::OperationSet,
        bit_vector: &CharacteristicVector,
    ) -> Vec<GeneralizedPosition> {
        let mut successors = Vec::new();

        // For M-type, bit vector index is computed differently
        // M + offset#errors at input k corresponds to word position m + offset
        // where m is the word length (not known here, so we use simplified logic)
        let bit_index = offset + bit_vector.len() as i32;
        let has_match = bit_index >= 0
            && (bit_index as usize) < bit_vector.len()
            && bit_vector.is_match(bit_index as usize);

        // Iterate over all operations
        for op in operations.operations() {
            // Skip multi-char operations for now (Phase 2c will add multi-char)
            if op.consume_x() > 1 || op.consume_y() > 1 {
                continue;
            }

            // Classify operation type and generate successors
            if op.is_match() && has_match {
                // Match operation: ⟨1, 1, 0.0⟩
                if let Ok(succ) = GeneralizedPosition::new_m(offset + 1, errors, self.max_distance) {
                    successors.push(succ);
                }
            } else if op.is_deletion() && errors < self.max_distance {
                // Delete operation: ⟨1, 0, w⟩
                let new_errors = errors + op.weight() as u8;
                if new_errors <= self.max_distance {
                    if let Ok(succ) = GeneralizedPosition::new_m(offset, new_errors, self.max_distance) {
                        successors.push(succ);
                    }
                }
            } else if (op.is_insertion() || op.is_substitution()) && errors < self.max_distance {
                // Insert ⟨0, 1, w⟩ or Substitute ⟨1, 1, w⟩
                let new_errors = errors + op.weight() as u8;
                if new_errors <= self.max_distance {
                    if let Ok(succ) = GeneralizedPosition::new_m(offset + 1, new_errors, self.max_distance) {
                        successors.push(succ);
                    }
                }
            }
        }

        successors
    }
}

impl fmt::Display for GeneralizedState {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{{")?;
        for (i, pos) in self.positions.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            write!(f, "{}", pos)?;
        }
        write!(f, "}}")
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_initial_state() {
        let state = GeneralizedState::initial(2);
        assert_eq!(state.len(), 1);
        assert!(!state.is_final());
        assert!(!state.is_empty());
    }

    #[test]
    fn test_add_position_no_subsumption() {
        let mut state = GeneralizedState::new(2);
        // Add positions that don't subsume each other
        // I + 0#1 does not subsume I + (-1)#1 (same errors, different offsets)
        // Valid positions: |0| ≤ 1 ✓ and |-1| ≤ 1 ✓
        state.add_position(GeneralizedPosition::new_i(0, 1, 2).unwrap());
        state.add_position(GeneralizedPosition::new_i(-1, 1, 2).unwrap());
        assert_eq!(state.len(), 2);
    }

    #[test]
    fn test_final_state() {
        let mut state = GeneralizedState::new(2);
        state.add_position(GeneralizedPosition::new_m(0, 0, 2).unwrap());
        assert!(state.is_final());
    }

    #[test]
    fn test_display() {
        let mut state = GeneralizedState::new(2);
        state.add_position(GeneralizedPosition::new_i(0, 1, 2).unwrap());
        state.add_position(GeneralizedPosition::new_i(-1, 1, 2).unwrap());
        let display = format!("{}", state);
        assert!(display.contains("I + 0#1") || display.contains("I + -1#1"));
        assert!(display.contains("I + -1#1") || display.contains("I + 0#1"));
    }
}
