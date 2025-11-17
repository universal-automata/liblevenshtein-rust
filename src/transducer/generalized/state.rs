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

    /// Previous input character for split/transpose validation (Phase 3b)
    /// Needed for two-step phonetic operations that validate across input positions
    previous_input_char: Option<char>,
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
            previous_input_char: None,
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
        full_word: &str,
        word_slice: &str,
        input_char: char,
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
            // Phase 3b: Pass full_word and word_slice for phonetic operations
            let successors = self.successors(pos, operations, bit_vector, full_word, word_slice, input_char);

            // Add all successors to next state
            for succ in successors {
                next_state.add_position(succ);
            }
        }

        // Return None if no successors (undefined transition)
        if next_state.is_empty() {
            None
        } else {
            // Phase 3b: Store current char for next iteration (needed for split/transpose)
            next_state.previous_input_char = Some(input_char);
            Some(next_state)
        }
    }

    /// Compute successors for a position using runtime-configurable operations
    ///
    /// Phase 2: Uses OperationSet to support custom edit distance metrics.
    /// Phase 3b: Accepts full_word, word_slice, and input_char for phonetic operations.
    fn successors(
        &self,
        pos: &GeneralizedPosition,
        operations: &crate::transducer::OperationSet,
        bit_vector: &CharacteristicVector,
        full_word: &str,
        word_slice: &str,
        input_char: char,
    ) -> Vec<GeneralizedPosition> {
        match pos {
            GeneralizedPosition::INonFinal { offset, errors } => {
                self.successors_i_type(*offset, *errors, operations, bit_vector, full_word, word_slice, input_char)
            }
            GeneralizedPosition::MFinal { offset, errors } => {
                self.successors_m_type(*offset, *errors, operations, bit_vector, full_word, word_slice, input_char)
            }
            // Phase 2d: Multi-character operation intermediate states
            GeneralizedPosition::ITransposing { offset, errors } => {
                // Complete transposition for I-type positions
                // Phase 3b: Pass full_word, word_slice, input_char for phonetic validation
                self.successors_i_transposing(*offset, *errors, operations, bit_vector, full_word, word_slice, input_char)
            }
            GeneralizedPosition::MTransposing { offset, errors } => {
                // Complete transposition for M-type positions
                // Phase 3b: Pass full_word, word_slice, input_char for phonetic validation
                self.successors_m_transposing(*offset, *errors, operations, bit_vector, full_word, word_slice, input_char)
            }
            // Phase 2d.5: Splitting positions
            GeneralizedPosition::ISplitting { offset, errors, entry_char } => {
                // Complete split for I-type positions
                // Phase 3b: Pass full_word, word_slice, input_char for phonetic validation
                self.successors_i_splitting(*offset, *errors, *entry_char, operations, bit_vector, full_word, word_slice, input_char)
            }
            GeneralizedPosition::MSplitting { offset, errors, entry_char } => {
                // Complete split for M-type positions
                // Phase 3b: Pass full_word, word_slice, input_char for phonetic validation
                self.successors_m_splitting(*offset, *errors, *entry_char, operations, bit_vector, full_word, word_slice, input_char)
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
        full_word: &str,
        word_slice: &str,
        input_char: char,
    ) -> Vec<GeneralizedPosition> {
        let mut successors = Vec::new();
        let n = self.max_distance as i32;

        // Bit vector index for current position: offset + n
        let match_index = (offset + n) as usize;

        // Case 1: Position within visible window
        if match_index < bit_vector.len() {
            let has_match = bit_vector.is_match(match_index);

            // Iterate over all operations (handle standard single-character operations)
            for op in operations.operations() {
                // Skip multi-char operations in this loop (handled separately below)
                if op.consume_x() > 1 || op.consume_y() > 1 {
                    continue;
                }

                // Classify operation type and generate successors
                if op.is_match() {
                    // Match operation: ⟨1, 1, 0.0⟩
                    if has_match {
                        // Phase 3: For match, check can_apply() with actual characters
                        let word_chars: Vec<char> = word_slice.chars().collect();
                        if match_index < word_chars.len() {
                            let word_char_str = word_chars[match_index].to_string();
                            let input_char_str = input_char.to_string();
                            if op.can_apply(word_char_str.as_bytes(), input_char_str.as_bytes()) {
                                // δ^D,ε_e: (t+1)#e → I^ε → I+t#e
                                if let Ok(succ) = GeneralizedPosition::new_i(offset, errors, self.max_distance) {
                                    successors.push(succ);
                                    // Phase 3b: Don't return early - allow multi-character operations to compete
                                }
                            }
                        }
                    }
                } else if op.is_deletion() {
                    // Delete operation: ⟨1, 0, w⟩
                    // Phase 3: For deletion, check can_apply() with word character and empty input
                    if errors < self.max_distance {
                        let new_errors = errors + op.weight() as u8;
                        if new_errors <= self.max_distance {
                            let word_chars: Vec<char> = word_slice.chars().collect();
                            if match_index < word_chars.len() {
                                let word_char_str = word_chars[match_index].to_string();
                                if op.can_apply(word_char_str.as_bytes(), &[]) {
                                    // δ^D,ε_e: t#(e+w) → I^ε → I+(t-1)#(e+w)
                                    if let Ok(succ) = GeneralizedPosition::new_i(offset - 1, new_errors, self.max_distance) {
                                        successors.push(succ);
                                    }
                                }
                            }
                        }
                    }
                } else if op.is_insertion() {
                    // Insert ⟨0, 1, w⟩
                    // Phase 3: For insertion, check can_apply() with empty word and input character
                    if errors < self.max_distance {
                        let new_errors = errors + op.weight() as u8;
                        if new_errors <= self.max_distance {
                            let input_char_str = input_char.to_string();
                            if op.can_apply(&[], input_char_str.as_bytes()) {
                                // δ^D,ε_e: (t+1)#(e+w) → I^ε → I+t#(e+w)
                                if let Ok(succ) = GeneralizedPosition::new_i(offset, new_errors, self.max_distance) {
                                    successors.push(succ);
                                }
                            }
                        }
                    }
                } else if op.is_substitution() {
                    // Substitute ⟨1, 1, w⟩
                    // Phase 3: For substitution, check can_apply() with word and input characters
                    if errors < self.max_distance {
                        let new_errors = errors + op.weight() as u8;
                        if new_errors <= self.max_distance {
                            let word_chars: Vec<char> = word_slice.chars().collect();
                            if match_index < word_chars.len() {
                                let word_char_str = word_chars[match_index].to_string();
                                let input_char_str = input_char.to_string();
                                if op.can_apply(word_char_str.as_bytes(), input_char_str.as_bytes()) {
                                    // δ^D,ε_e: (t+1)#(e+w) → I^ε → I+t#(e+w)
                                    if let Ok(succ) = GeneralizedPosition::new_i(offset, new_errors, self.max_distance) {
                                        successors.push(succ);
                                    }
                                }
                            }
                        }
                    }
                }
            }

            // Phase 2d/3b: Multi-character operations - TRANSPOSITION ⟨2,2,1⟩
            // Phase 3b: Support phonetic ⟨2,2⟩ operations (e.g., "qu"↔"kw")
            let transpose_ops: Vec<_> = operations.operations().iter()
                .filter(|op| op.consume_x() == 2 && op.consume_y() == 2)
                .collect();

            if !transpose_ops.is_empty() && errors < self.max_distance {
                let word_chars: Vec<char> = word_slice.chars().collect();
                let next_match_index = (offset + n + 1) as usize;

                // Check if we have enough word characters for transpose
                if next_match_index < word_chars.len() && word_chars[next_match_index] != '$' {
                    // Check standard operations (bit_vector match at next position)
                    let standard_match = next_match_index < bit_vector.len()
                        && bit_vector.is_match(next_match_index);

                    // For phonetic operations, speculatively enter transpose state
                    let has_phonetic_transpose = transpose_ops.iter().any(|op| op.weight() < 1.0);

                    // Enter transpose state if either standard or phonetic operations could apply
                    if standard_match {
                        // Standard transpose: enter with errors+1 (will decrement at completion)
                        if let Ok(trans) = GeneralizedPosition::new_i_transposing(
                            offset - 1,
                            errors + 1,
                            self.max_distance
                        ) {
                            successors.push(trans);
                        }
                    } else if has_phonetic_transpose {
                        // Phonetic transpose: enter with errors+0 (fractional weight)
                        if let Ok(trans) = GeneralizedPosition::new_i_transposing(
                            offset - 1,
                            errors,
                            self.max_distance
                        ) {
                            successors.push(trans);
                        }
                    }
                }
            }

            // Phase 2d/3: Multi-character operations - MERGE ⟨2,1⟩
            // Merge: consume 2 word chars, match 1 input char (direct operation)
            // Phase 3: Supports phonetic operations like "ch"→"k", "ph"→"f"
            if errors < self.max_distance {
                let word_chars: Vec<char> = word_slice.chars().collect();

                // Check if we have enough word characters (need 2 consecutive chars)
                // Skip padding chars '$'
                if match_index + 1 < word_chars.len()
                    && word_chars[match_index] != '$'
                    && word_chars[match_index + 1] != '$' {
                    // Extract 2 word characters
                    let word_2chars: String = word_chars[match_index..match_index+2].iter().collect();
                    let input_1char = input_char.to_string();

                    // Check all ⟨2,1⟩ operations
                    for op in operations.operations() {
                        if op.consume_x() == 2 && op.consume_y() == 1 {
                            // Phase 3: Use can_apply() for phonetic operations
                            // Don't check bit_vector - phonetic ops don't require char matches
                            if op.can_apply(word_2chars.as_bytes(), input_1char.as_bytes()) {
                                let weight_as_errors = op.weight() as u8;
                                let new_errors = errors + weight_as_errors;

                                if new_errors <= self.max_distance {
                                    // Direct transition: offset+1, errors+weight
                                    // Note: For fractional weights (e.g., 0.15), weight truncates to 0
                                    // This creates positions with offset > errors (e.g., offset=1, errors=0)
                                    // which is allowed by the relaxed invariant in new_i()
                                    if let Ok(merge) = GeneralizedPosition::new_i(
                                        offset + 1,
                                        new_errors,
                                        self.max_distance
                                    ) {
                                        successors.push(merge);
                                        break; // Only add one merge successor per position
                                    }
                                }
                            }
                        }
                    }
                }
            }

            // Phase 2d/3b: Multi-character operations - SPLIT ⟨1,2,1⟩
            // Split: consume 1 word char, match 2 input chars (two-step operation)
            // Phase 3b: Support phonetic ⟨1,2⟩ operations (e.g., "k"→"ch")
            let split_ops: Vec<_> = operations.operations().iter()
                .filter(|op| op.consume_x() == 1 && op.consume_y() == 2)
                .collect();

            // Phase 3b: Check if we should enter split state
            // For standard splits: errors < max_distance required
            // For phonetic splits with fractional weight: allowed even at max_distance (cost=0)
            let has_phonetic_split = split_ops.iter().any(|op| op.weight() < 1.0);
            let can_enter_split = errors < self.max_distance || has_phonetic_split;

            if !split_ops.is_empty() && can_enter_split {
                let word_chars: Vec<char> = word_slice.chars().collect();

                // Check if we can enter split state
                if match_index < word_chars.len() && word_chars[match_index] != '$' {
                    // Check standard operations (bit_vector match)
                    let standard_match = match_index < bit_vector.len() && bit_vector.is_match(match_index);

                    // For phonetic operations, check if THIS word character can be split
                    // We need at least one split operation that can apply to this word char
                    // AND the current input char must match the first char of the split target
                    let word_1char = word_chars[match_index].to_string();
                    let can_phonetic_split = split_ops.iter().any(|op| {
                        if op.weight() < 1.0 && op.consume_x() == 1 {
                            // Check TWO conditions:
                            // 1. This word character can be split (source check)
                            // 2. Current input character matches first char of target (prevents wrong split entry)
                            // This fixes the double-split bug where t→th was entered when reading 'a' instead of 't'
                            op.can_apply_to_source(word_1char.as_bytes())
                                && op.matches_first_target_char(word_1char.as_bytes(), input_char)
                        } else {
                            false
                        }
                    });

                    // Enter split state - prioritize phonetic over standard
                    // When both conditions are true, phonetic split takes precedence (errors+0 vs errors+1)
                    if can_phonetic_split {
                        // Phonetic split: enter with errors+0 (fractional weight truncates to 0)
                        // Allowed even at max_distance since cost=0
                        if let Ok(split) = GeneralizedPosition::new_i_splitting(
                            offset - 1,
                            errors,
                            self.max_distance,
                            input_char  // Store the character read when entering this split state
                        ) {
                            successors.push(split);
                        }
                    } else if standard_match && errors < self.max_distance {
                        // Standard split: enter with errors+1 (will decrement at completion)
                        // Only used when phonetic split doesn't apply
                        if let Ok(split) = GeneralizedPosition::new_i_splitting(
                            offset - 1,
                            errors + 1,
                            self.max_distance,
                            input_char  // Store the character read when entering this split state
                        ) {
                            successors.push(split);
                        }
                    }
                }
            }

            // SKIP-TO-MATCH optimization (Phase 2c: generalize for multi-char)
            // Scans FORWARD through word to find next match position
            // NOT equivalent to N DELETEs (DELETE moves backward, skip moves forward)
            // Cost: number of word characters skipped over
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
        full_word: &str,
        word_slice: &str,
        input_char: char,
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
                // Phase 3: Check can_apply() with actual characters
                let word_chars: Vec<char> = word_slice.chars().collect();
                if bit_index >= 0 && (bit_index as usize) < word_chars.len() {
                    let word_char_str = word_chars[bit_index as usize].to_string();
                    let input_char_str = input_char.to_string();
                    if op.can_apply(word_char_str.as_bytes(), input_char_str.as_bytes()) {
                        if let Ok(succ) = GeneralizedPosition::new_m(offset + 1, errors, self.max_distance) {
                            successors.push(succ);
                        }
                    }
                }
            } else if op.is_deletion() && errors < self.max_distance {
                // Delete operation: ⟨1, 0, w⟩
                // Phase 3: Check can_apply() with word character and empty input
                let new_errors = errors + op.weight() as u8;
                if new_errors <= self.max_distance {
                    let word_chars: Vec<char> = word_slice.chars().collect();
                    if bit_index >= 0 && (bit_index as usize) < word_chars.len() {
                        let word_char_str = word_chars[bit_index as usize].to_string();
                        if op.can_apply(word_char_str.as_bytes(), &[]) {
                            if let Ok(succ) = GeneralizedPosition::new_m(offset, new_errors, self.max_distance) {
                                successors.push(succ);
                            }
                        }
                    }
                }
            } else if op.is_insertion() && errors < self.max_distance {
                // Insert ⟨0, 1, w⟩
                // Phase 3: Check can_apply() with empty word and input character
                let new_errors = errors + op.weight() as u8;
                if new_errors <= self.max_distance {
                    let input_char_str = input_char.to_string();
                    if op.can_apply(&[], input_char_str.as_bytes()) {
                        if let Ok(succ) = GeneralizedPosition::new_m(offset + 1, new_errors, self.max_distance) {
                            successors.push(succ);
                        }
                    }
                }
            } else if op.is_substitution() && errors < self.max_distance {
                // Substitute ⟨1, 1, w⟩
                // Phase 3: Check can_apply() with word and input characters
                let new_errors = errors + op.weight() as u8;
                if new_errors <= self.max_distance {
                    let word_chars: Vec<char> = word_slice.chars().collect();
                    if bit_index >= 0 && (bit_index as usize) < word_chars.len() {
                        let word_char_str = word_chars[bit_index as usize].to_string();
                        let input_char_str = input_char.to_string();
                        if op.can_apply(word_char_str.as_bytes(), input_char_str.as_bytes()) {
                            if let Ok(succ) = GeneralizedPosition::new_m(offset + 1, new_errors, self.max_distance) {
                                successors.push(succ);
                            }
                        }
                    }
                }
            }
        }

        // Phase 2d/3b: Multi-character operations - TRANSPOSITION ⟨2,2,1⟩
        // Phase 3b: Support phonetic ⟨2,2⟩ operations (e.g., "qu"↔"kw")
        let transpose_ops: Vec<_> = operations.operations().iter()
            .filter(|op| op.consume_x() == 2 && op.consume_y() == 2)
            .collect();

        if !transpose_ops.is_empty() && errors < self.max_distance {
            let next_match_index = (offset + bit_vector.len() as i32 + 1) as usize;
            let word_chars: Vec<char> = word_slice.chars().collect();

            // Check if we have enough word characters for transpose
            if next_match_index < word_chars.len() && word_chars[next_match_index] != '$' {
                let next_bit_index = offset + bit_vector.len() as i32 + 1;

                // Check standard operations (bit_vector match at next position)
                let standard_match = next_bit_index >= 0
                    && (next_bit_index as usize) < bit_vector.len()
                    && bit_vector.is_match(next_bit_index as usize);

                // For phonetic operations, speculatively enter transpose state
                let has_phonetic_transpose = transpose_ops.iter().any(|op| op.weight() < 1.0);

                // Enter transpose state if either standard or phonetic operations could apply
                if standard_match {
                    // Standard transpose: enter with errors+1 (will decrement at completion)
                    if let Ok(trans) = GeneralizedPosition::new_m_transposing(
                        offset - 1,
                        errors + 1,
                        self.max_distance
                    ) {
                        successors.push(trans);
                    }
                } else if has_phonetic_transpose {
                    // Phonetic transpose: enter with errors+0 (fractional weight)
                    if let Ok(trans) = GeneralizedPosition::new_m_transposing(
                        offset - 1,
                        errors,
                        self.max_distance
                    ) {
                        successors.push(trans);
                    }
                }
            }
        }

        // Phase 2d/3: Multi-character operations - MERGE ⟨2,1⟩
        // Merge: consume 2 word chars, match 1 input char (direct operation)
        // Phase 3: Supports phonetic operations like "ch"→"k", "ph"→"f"
        if errors < self.max_distance {
            let word_chars: Vec<char> = word_slice.chars().collect();
            let next_match_index_i32 = offset + bit_vector.len() as i32 + 1;

            // Check if index is valid (non-negative) before converting to usize
            // M-type positions can have negative offsets, so this prevents overflow
            if next_match_index_i32 >= 0 {
                let next_match_index = next_match_index_i32 as usize;

                // Check if we have enough word characters (need 2 consecutive chars)
                // Skip padding chars '$'
                if next_match_index + 1 < word_chars.len()
                    && word_chars[next_match_index] != '$'
                    && word_chars[next_match_index + 1] != '$' {
                // Extract 2 word characters
                let word_2chars: String = word_chars[next_match_index..next_match_index+2].iter().collect();
                let input_1char = input_char.to_string();

                // Check all ⟨2,1⟩ operations
                for op in operations.operations() {
                    if op.consume_x() == 2 && op.consume_y() == 1 {
                        // Phase 3: Use can_apply() for phonetic operations
                        if op.can_apply(word_2chars.as_bytes(), input_1char.as_bytes()) {
                            let weight_as_errors = op.weight() as u8;
                            let new_errors = errors + weight_as_errors;

                            if new_errors <= self.max_distance {
                                // Direct transition: offset+1, errors+weight
                                if let Ok(merge) = GeneralizedPosition::new_m(
                                    offset + 1,
                                    new_errors,
                                    self.max_distance
                                ) {
                                    successors.push(merge);
                                    break; // Only add one merge successor per position
                                }
                            }
                        }
                    }
                }
                }
            }
        }

        // Phase 2d/3b: Multi-character operations - SPLIT ⟨1,2,1⟩
        // Split: consume 1 input char, match 2 word chars (two-step operation)
        // Phase 3b: Support phonetic ⟨1,2⟩ operations (e.g., "k"→"ch")
        let split_ops: Vec<_> = operations.operations().iter()
            .filter(|op| op.consume_x() == 1 && op.consume_y() == 2)
            .collect();

        // Phase 3b: Check if we should enter split state
        // For standard splits: errors < max_distance required
        // For phonetic splits with fractional weight: allowed even at max_distance (cost=0)
        let has_phonetic_split = split_ops.iter().any(|op| op.weight() < 1.0);
        let can_enter_split = errors < self.max_distance || has_phonetic_split;

        if !split_ops.is_empty() && can_enter_split {
            let next_match_index = (offset + bit_vector.len() as i32) as usize;
            let word_chars: Vec<char> = word_slice.chars().collect();

            // Check if we can enter split state
            if next_match_index < word_chars.len() && word_chars[next_match_index] != '$' {
                // Check standard operations (bit_vector match)
                let standard_match = bit_index >= 0 && (bit_index as usize) < bit_vector.len()
                    && bit_vector.is_match(bit_index as usize);

                // For phonetic operations, check if THIS word character can be split
                // AND the current input char must match the first char of the split target
                let word_1char = word_chars[next_match_index].to_string();
                let can_phonetic_split = split_ops.iter().any(|op| {
                    if op.weight() < 1.0 && op.consume_x() == 1 {
                        // Check TWO conditions:
                        // 1. This word character can be split (source check)
                        // 2. Current input character matches first char of target (prevents wrong split entry)
                        op.can_apply_to_source(word_1char.as_bytes())
                            && op.matches_first_target_char(word_1char.as_bytes(), input_char)
                    } else {
                        false
                    }
                });

                // Enter split state - prioritize phonetic over standard
                // When both conditions are true, phonetic split takes precedence (errors+0 vs errors+1)
                if can_phonetic_split {
                    // Phonetic split: enter with errors+0 (fractional weight truncates to 0)
                    // Allowed even at max_distance since cost=0
                    if let Ok(split) = GeneralizedPosition::new_m_splitting(
                        offset - 1,
                        errors,
                        self.max_distance,
                        input_char  // Store the character read when entering this split state
                    ) {
                        successors.push(split);
                    }
                } else if standard_match && errors < self.max_distance {
                    // Standard split: enter with errors+1 (will decrement at completion)
                    // Only used when phonetic split doesn't apply
                    if let Ok(split) = GeneralizedPosition::new_m_splitting(
                        offset - 1,
                        errors + 1,
                        self.max_distance,
                        input_char  // Store the character read when entering this split state
                    ) {
                        successors.push(split);
                    }
                }
            }
        }

        successors
    }

    /// Compute successors for I-type transposing positions
    ///
    /// Complete the transposition operation: consume the second input character,
    /// match against current word position, and return to usual state.
    ///
    /// # Transposition Complete Logic
    ///
    /// From transposing state I+(offset)#(errors)_t:
    /// - Check bit_vector[offset + n] (current position)
    /// - If match, create I+(offset+1)#(errors-1) (jump 2 word positions, decrement error)
    fn successors_i_transposing(
        &self,
        offset: i32,
        errors: u8,
        operations: &crate::transducer::OperationSet,
        bit_vector: &CharacteristicVector,
        full_word: &str,
        word_slice: &str,
        input_char: char,
    ) -> Vec<GeneralizedPosition> {
        let mut successors = Vec::new();
        let n = self.max_distance as i32;
        let match_index = (offset + n) as usize;

        // Phase 3b: Complete transpose with phonetic validation
        // Extract 2 word characters that are being transposed
        let word_chars: Vec<char> = word_slice.chars().collect();
        if match_index + 1 >= word_chars.len()
            || word_chars[match_index] == '$'
            || word_chars[match_index + 1] == '$'
        {
            return successors;
        }
        let word_2chars: String = word_chars[match_index..match_index + 2].iter().collect();

        // Get both input characters (previous + current)
        let prev_char = self.previous_input_char.unwrap_or('\0');
        let curr_char = input_char;
        let input_2chars = format!("{}{}", prev_char, curr_char);

        // Check standard operations first (bit_vector match)
        // Only use standard path if we have errors to decrement
        if errors > 0 && match_index < bit_vector.len() && bit_vector.is_match(match_index) {
            // Complete transposition: offset+1 (jump 2 word positions), errors-1
            if let Ok(succ) = GeneralizedPosition::new_i(
                offset + 1,
                errors - 1,  // Decrement error (was incremented on enter)
                self.max_distance
            ) {
                successors.push(succ);
                return successors;  // Return early - one successor per position
            }
        }

        // Check phonetic transpose operations ⟨2,2⟩
        for op in operations.operations() {
            if op.consume_x() == 2 && op.consume_y() == 2 {
                if op.can_apply(word_2chars.as_bytes(), input_2chars.as_bytes()) {
                    // Complete phonetic transpose (cost was already applied on enter)
                    if let Ok(succ) = GeneralizedPosition::new_i(
                        offset + 1,  // Jump 2 word positions
                        errors,      // Keep same errors (cost was already applied)
                        self.max_distance
                    ) {
                        successors.push(succ);
                        break;  // Only add one transpose successor per position
                    }
                }
            }
        }

        successors
    }

    /// Compute successors for M-type transposing positions
    ///
    /// Complete the transposition operation for M-type (final) positions.
    ///
    /// # Transposition Complete Logic
    ///
    /// From transposing state M+(offset)#(errors)_t:
    /// - Check bit_vector at appropriate index
    /// - If match, create M+(offset+1)#(errors-1)
    fn successors_m_transposing(
        &self,
        offset: i32,
        errors: u8,
        operations: &crate::transducer::OperationSet,
        bit_vector: &CharacteristicVector,
        full_word: &str,
        word_slice: &str,
        input_char: char,
    ) -> Vec<GeneralizedPosition> {
        let mut successors = Vec::new();
        let bit_index = offset + bit_vector.len() as i32;

        // Phase 3b: Complete transpose with phonetic validation
        // Extract 2 word characters that are being transposed
        let next_match_index = (offset + bit_vector.len() as i32) as usize;
        let word_chars: Vec<char> = word_slice.chars().collect();
        if next_match_index + 1 >= word_chars.len()
            || word_chars[next_match_index] == '$'
            || word_chars[next_match_index + 1] == '$'
        {
            return successors;
        }
        let word_2chars: String = word_chars[next_match_index..next_match_index + 2].iter().collect();

        // Get both input characters (previous + current)
        let prev_char = self.previous_input_char.unwrap_or('\0');
        let curr_char = input_char;
        let input_2chars = format!("{}{}", prev_char, curr_char);

        // Check standard operations first (bit_vector match)
        // Only use standard path if we have errors to decrement
        if errors > 0
            && bit_index >= 0
            && (bit_index as usize) < bit_vector.len()
            && bit_vector.is_match(bit_index as usize)
        {
            // Complete transposition: offset+1, errors-1
            if let Ok(succ) = GeneralizedPosition::new_m(
                offset + 1,
                errors - 1,  // Decrement error
                self.max_distance
            ) {
                successors.push(succ);
                return successors;  // Return early - one successor per position
            }
        }

        // Check phonetic transpose operations ⟨2,2⟩
        for op in operations.operations() {
            if op.consume_x() == 2 && op.consume_y() == 2 {
                if op.can_apply(word_2chars.as_bytes(), input_2chars.as_bytes()) {
                    // Complete phonetic transpose (cost was already applied on enter)
                    if let Ok(succ) = GeneralizedPosition::new_m(
                        offset + 1,  // Jump 2 word positions
                        errors,      // Keep same errors (cost was already applied)
                        self.max_distance
                    ) {
                        successors.push(succ);
                        break;  // Only add one transpose successor per position
                    }
                }
            }
        }

        successors
    }

    /// Compute successors for I-type splitting positions
    ///
    /// Complete the split operation: consume the second input character,
    /// match against current word position, and return to usual state.
    ///
    /// # Split Complete Logic
    ///
    /// From splitting state I+(offset)#(errors)_s:
    /// - Check bit_vector[offset + n] (current position for second word char)
    /// - If match, create I+(offset+0)#(errors-1) (advance 1 word position, decrement error)
    fn successors_i_splitting(
        &self,
        offset: i32,
        errors: u8,
        entry_char: char,
        operations: &crate::transducer::OperationSet,
        bit_vector: &CharacteristicVector,
        full_word: &str,
        word_slice: &str,
        input_char: char,
    ) -> Vec<GeneralizedPosition> {
        let mut successors = Vec::new();
        let n = self.max_distance as i32;
        let match_index_i32 = offset + n;

        // Phase 3b: Complete split with phonetic validation
        // Extract word character that was split
        let word_chars: Vec<char> = word_slice.chars().collect();

        // Phase 3b fix: Handle negative match_index or empty word_slice by using full_word
        let word_1char = if match_index_i32 < 0 || word_chars.is_empty() {
            // Need to use full_word instead of word_slice
            let full_word_chars: Vec<char> = full_word.chars().collect();
            // Calculate absolute position in full word
            // When entering split, we did offset-1, so the word char being split is at offset+n+1
            let word_pos = (offset + n + 1) as usize;

            if word_pos < full_word_chars.len() && full_word_chars[word_pos] != '$' {
                full_word_chars[word_pos].to_string()
            } else {
                // Past word end - no character to validate
                return successors;
            }
        } else {
            // Normal case: extract from subword
            let match_index = match_index_i32 as usize;
            if match_index >= word_chars.len() || word_chars[match_index] == '$' {
                return successors;
            }
            word_chars[match_index].to_string()
        };

        // Get both input characters (entry_char + current)
        // Use entry_char (the char read when entering this split state) instead of state-level previous_input_char
        let prev_char = entry_char;
        let curr_char = input_char;
        let input_2chars = format!("{}{}", prev_char, curr_char);

        // Phase 3b: Check PHONETIC split operations FIRST ⟨1,2⟩ (more specific)
        for op in operations.operations() {
            if op.consume_x() == 1 && op.consume_y() == 2 {
                if op.can_apply(word_1char.as_bytes(), input_2chars.as_bytes()) {
                    // Complete phonetic split (cost was already applied on enter)
                    // Split consumes 1 word char, so advance offset by 1
                    let new_offset = offset + 1;

                    // Check if we've reached or passed the end of the word
                    // If so, create M-type position; otherwise I-type
                    let word_len = word_chars.len();
                    let result_match_index = (new_offset + n) as usize;

                    if result_match_index >= word_len {
                        // Past word end -> M-type position
                        // M-type offset is relative to word end
                        let m_offset = new_offset - (word_len as i32 - n);
                        if let Ok(succ) = GeneralizedPosition::new_m(m_offset, errors, self.max_distance) {
                            successors.push(succ);
                            return successors;  // Early return after phonetic split
                        }
                    } else {
                        // Still within word -> I-type position
                        if let Ok(succ) = GeneralizedPosition::new_i(new_offset, errors, self.max_distance) {
                            successors.push(succ);
                            return successors;  // Early return after phonetic split
                        }
                    }
                }
            }
        }

        // FALLBACK: Check standard operations (bit_vector match)
        // Only reached if no phonetic operation applied
        if errors > 0 && match_index_i32 >= 0 {
            let match_idx = match_index_i32 as usize;
            if match_idx < bit_vector.len() && bit_vector.is_match(match_idx) {
                // Complete split: offset+0 (advance 1 word position), errors-1
                if let Ok(succ) = GeneralizedPosition::new_i(
                    offset,      // +0 (stays same!)
                    errors - 1,  // Decrement error (was incremented on enter)
                    self.max_distance
                ) {
                    successors.push(succ);
                }
            }
        }

        successors
    }

    /// Compute successors for M-type splitting positions
    ///
    /// Complete the split operation for M-type (final) positions.
    ///
    /// # Split Complete Logic
    ///
    /// From splitting state M+(offset)#(errors)_s:
    /// - Check bit_vector at appropriate index
    /// - If match, create M+(offset+0)#(errors-1)
    fn successors_m_splitting(
        &self,
        offset: i32,
        errors: u8,
        entry_char: char,
        operations: &crate::transducer::OperationSet,
        bit_vector: &CharacteristicVector,
        full_word: &str,
        word_slice: &str,
        input_char: char,
    ) -> Vec<GeneralizedPosition> {
        let mut successors = Vec::new();
        let bit_index = offset + bit_vector.len() as i32;

        // Phase 3b: Complete split with phonetic validation
        // Extract word character that was split
        let next_match_index_i32 = offset + bit_vector.len() as i32;
        let word_chars: Vec<char> = word_slice.chars().collect();

        // Phase 3b fix: Handle negative or out-of-bounds index by using full_word
        let word_1char = if next_match_index_i32 < 0 || word_chars.is_empty() {
            // Need to use full_word instead of word_slice
            let full_word_chars: Vec<char> = full_word.chars().collect();

            // For M-type, calculate absolute position
            // When entering split, we did offset-1, so add +1 to get the word char being split
            let word_len = full_word_chars.len();
            let word_pos = (word_len as i32 + offset + 1) as usize;

            if word_pos < full_word_chars.len() && full_word_chars[word_pos] != '$' {
                full_word_chars[word_pos].to_string()
            } else {
                // Past word end - no character to validate
                return successors;
            }
        } else {
            // Normal case: extract from subword
            let next_match_index = next_match_index_i32 as usize;
            if next_match_index >= word_chars.len() || word_chars[next_match_index] == '$' {
                return successors;
            }
            word_chars[next_match_index].to_string()
        };

        // Get both input characters (entry_char + current)
        // Use entry_char (the char read when entering this split state) instead of state-level previous_input_char
        let prev_char = entry_char;
        let curr_char = input_char;
        let input_2chars = format!("{}{}", prev_char, curr_char);

        // Phase 3b: Check PHONETIC split operations FIRST ⟨1,2⟩ (more specific)
        for op in operations.operations() {
            if op.consume_x() == 1 && op.consume_y() == 2 {
                if op.can_apply(word_1char.as_bytes(), input_2chars.as_bytes()) {
                    // Complete phonetic split (cost was already applied on enter)
                    // Split consumes 1 word char, so advance offset by 1
                    let new_offset = offset + 1;
                    if let Ok(succ) = GeneralizedPosition::new_m(
                        new_offset,  // Keep same (net +1 due to entry offset-1)
                        errors,      // Keep same errors (cost was already applied)
                        self.max_distance
                    ) {
                        successors.push(succ);
                        return successors;  // Early return after phonetic split
                    }
                }
            }
        }

        // FALLBACK: Check standard operations (bit_vector match)
        // Only reached if no phonetic operation applied
        if errors > 0
            && bit_index >= 0
            && (bit_index as usize) < bit_vector.len()
            && bit_vector.is_match(bit_index as usize)
        {
            // Complete split: offset+0, errors-1
            if let Ok(succ) = GeneralizedPosition::new_m(
                offset,      // +0 (stays same!)
                errors - 1,  // Decrement error
                self.max_distance
            ) {
                successors.push(succ);
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
