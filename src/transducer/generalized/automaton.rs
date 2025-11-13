//! Generalized Levenshtein Automaton
//!
//! Implements a Levenshtein automaton with runtime-configurable operations.
//!
//! # Design Philosophy
//!
//! `GeneralizedAutomaton` complements `UniversalAutomaton` by trading compile-time
//! specialization for runtime flexibility:
//!
//! - **UniversalAutomaton**: Compile-time operations (Standard, Transposition, MergeAndSplit)
//!   - Zero runtime overhead
//!   - Fixed operation sets
//!   - Perfect for standard Levenshtein variants
//!
//! - **GeneralizedAutomaton**: Runtime operations (Phase 1: standard only)
//!   - Small runtime overhead (+10-20% estimate)
//!   - Future: Custom operation sets
//!   - Perfect for phonetic corrections and custom metrics
//!
//! # Phase 1 Implementation
//!
//! Current implementation supports **standard operations only** (match, substitute, insert, delete).
//! Future phases will add:
//! - Runtime OperationSet parameter
//! - Multi-character operations
//! - Custom operation sets
//!
//! # Theory Background
//!
//! ## Definition 15: Universal Levenshtein Automaton (Page 30)
//!
//! ```text
//! A^∀,χ_n = ⟨Σ^∀_n, Q^∀,χ_n, I^∀,χ, F^∀,χ_n, δ^∀,χ_n⟩
//! ```
//!
//! Where:
//! - **Σ^∀_n**: Bit vectors of length ≤ 2n + 2
//! - **Q^∀,χ_n**: State space (I^χ_states ∪ M^χ_states)
//! - **I^∀,χ**: Initial state {I#0}
//! - **F^∀,χ_n**: Final states (states with M-type positions)
//! - **δ^∀,χ_n**: Transition function
//!
//! ## Acceptance Condition (Page 48)
//!
//! Given a word w and input x, the automaton accepts if:
//! 1. Encode the pair as h_n(w, x) = β(x₁, s_n(w,1))...β(x_t, s_n(w,t))
//! 2. Process the bit vector sequence: δ^∀,χ_n*(I^∀,χ, h_n(w, x))
//! 3. Check if the resulting state is final (contains M-type positions)
//!
//! # Examples
//!
//! ```ignore
//! use liblevenshtein::transducer::generalized::GeneralizedAutomaton;
//!
//! // Create automaton for maximum distance n=2
//! let automaton = GeneralizedAutomaton::new(2);
//!
//! // Check if "test" accepts "text" (distance 1)
//! assert!(automaton.accepts("test", "text"));
//!
//! // Check if "test" accepts "hello" (distance > 2)
//! assert!(!automaton.accepts("test", "hello"));
//! ```

use super::bit_vector::CharacteristicVector;
use super::state::GeneralizedState;
use crate::transducer::OperationSet;

/// Generalized Levenshtein Automaton A^∀,χ_n
///
/// A parameter-free automaton that recognizes the Levenshtein neighborhood
/// L^χ_{Lev}(n, w) for any word w without modification.
///
/// # Phase 2: Runtime-Configurable Operations
///
/// Supports custom operation sets including:
/// - Standard operations (match, substitute, insert, delete)
/// - Transposition
/// - Multi-character operations (phonetic corrections, merge/split)
/// - Weighted operations with custom costs
///
/// # Examples
///
/// ```ignore
/// use liblevenshtein::transducer::generalized::GeneralizedAutomaton;
/// use liblevenshtein::transducer::OperationSet;
///
/// // Standard Levenshtein
/// let automaton = GeneralizedAutomaton::new(2);
///
/// // With transposition
/// let automaton = GeneralizedAutomaton::with_operations(
///     2,
///     OperationSet::with_transposition()
/// );
///
/// // Check if "test" accepts "text" (distance 1)
/// assert!(automaton.accepts("test", "text"));
/// ```
#[derive(Debug, Clone)]
pub struct GeneralizedAutomaton {
    /// Maximum edit distance n
    max_distance: u8,

    /// Set of operations defining the edit distance metric
    operations: OperationSet,
}

impl GeneralizedAutomaton {
    /// Create a new Generalized Levenshtein Automaton with standard operations
    ///
    /// Uses the standard operation set (match, substitute, insert, delete).
    ///
    /// # Arguments
    ///
    /// - `max_distance`: Maximum edit distance n (typically 1, 2, or 3)
    ///
    /// # Returns
    ///
    /// A new `GeneralizedAutomaton` instance with standard operations
    ///
    /// # Examples
    ///
    /// ```ignore
    /// let automaton = GeneralizedAutomaton::new(2);
    /// ```
    #[must_use]
    pub fn new(max_distance: u8) -> Self {
        Self {
            max_distance,
            operations: OperationSet::standard(),
        }
    }

    /// Create a new Generalized Levenshtein Automaton with custom operations
    ///
    /// # Arguments
    ///
    /// - `max_distance`: Maximum edit distance n (typically 1, 2, or 3)
    /// - `operations`: Set of operations defining the edit distance metric
    ///
    /// # Returns
    ///
    /// A new `GeneralizedAutomaton` instance with custom operations
    ///
    /// # Examples
    ///
    /// ```ignore
    /// // Automaton with transposition support
    /// let automaton = GeneralizedAutomaton::with_operations(
    ///     2,
    ///     OperationSet::with_transposition()
    /// );
    ///
    /// // Automaton with custom phonetic operations
    /// let mut ops = OperationSet::standard();
    /// ops.add_merge("ph", "f", 0);  // "ph" → "f" with no cost
    /// let automaton = GeneralizedAutomaton::with_operations(2, ops);
    /// ```
    #[must_use]
    pub fn with_operations(max_distance: u8, operations: OperationSet) -> Self {
        Self {
            max_distance,
            operations,
        }
    }

    /// Get the maximum edit distance n
    #[must_use]
    pub fn max_distance(&self) -> u8 {
        self.max_distance
    }

    /// Create the initial state I^∀,χ = {I#0}
    ///
    /// From thesis page 38: The initial state contains a single I-type position
    /// with offset 0 and 0 errors.
    ///
    /// # Returns
    ///
    /// Initial state {I#0}
    fn initial_state(&self) -> GeneralizedState {
        GeneralizedState::initial(self.max_distance)
    }

    /// Check if a state is accepting according to Levenshtein distance criterion
    ///
    /// From thesis page 24 (Proposition 11): A position i#e is accepting if:
    /// ```text
    /// p - i ≤ n - e
    /// ```
    /// Where p is word length, i is position, n is max distance, e is errors.
    ///
    /// This translates to: remaining characters ≤ remaining error budget.
    ///
    /// # Arguments
    ///
    /// - `state`: State to check after processing all input
    /// - `word_len`: Length of dictionary word
    /// - `input_len`: Length of input string processed
    ///
    /// # Returns
    ///
    /// `true` if state is accepting (within distance n), `false` otherwise
    #[must_use]
    fn is_accepting(&self, state: &GeneralizedState, word_len: usize, input_len: usize) -> bool {
        use crate::transducer::generalized::GeneralizedPosition;

        let n = self.max_distance as i32;

        state.positions().any(|pos| {
            match pos {
                GeneralizedPosition::MFinal { offset, errors } => {
                    // M-type positions are past the word end
                    // They're accepting if offset ≤ 0 and errors ≤ n
                    *offset <= 0 && *errors <= self.max_distance
                }
                GeneralizedPosition::INonFinal { .. } => {
                    // I-type positions: check if we can reach word end with remaining errors
                    // Current word position in the word = input_len + offset
                    let current_word_pos = input_len as i32 + pos.offset();

                    // Check bounds
                    if current_word_pos < 0 {
                        return false; // Before word start
                    }

                    // Remaining characters to match = word_len - current_word_pos
                    let remaining_chars = word_len as i32 - current_word_pos;

                    // Remaining error budget = max_distance - errors_used
                    let remaining_errors = n - (pos.errors() as i32);

                    // Accept if we can delete/skip remaining characters with available errors
                    // Proposition 11: p - i ≤ n - e
                    // where p = word_len, i = current_word_pos, e = errors used, n = max_distance
                    remaining_chars >= 0 && remaining_chars <= remaining_errors
                }
            }
        })
    }

    /// Check if word w accepts input x within the maximum distance
    ///
    /// From thesis page 51-52: Encodes the pair (w, x) as h_n(w, x) and
    /// processes it through the automaton.
    ///
    /// # Arguments
    ///
    /// - `word`: Dictionary word w
    /// - `input`: Input string x to match against
    ///
    /// # Returns
    ///
    /// `true` if Lev(w, x) ≤ n, `false` otherwise
    ///
    /// # Algorithm
    ///
    /// 1. Start with initial state I^∀,χ = {I#0}
    /// 2. For each character x_i in input:
    ///    - Compute relevant subword s_n(w, i)
    ///    - Compute characteristic vector β(x_i, s_n(w, i))
    ///    - Apply transition: state := δ^∀,χ_n(state, β)
    /// 3. Check if final state is accepting
    ///
    /// # Phase 1 Note
    ///
    /// Uses standard operations only (match, substitute, insert, delete).
    ///
    /// # Examples
    ///
    /// ```ignore
    /// let automaton = GeneralizedAutomaton::new(2);
    ///
    /// // Distance 1: one substitution
    /// assert!(automaton.accepts("test", "text"));
    ///
    /// // Distance 0: identical
    /// assert!(automaton.accepts("test", "test"));
    ///
    /// // Distance 3: too far
    /// assert!(!automaton.accepts("test", "hello"));
    /// ```
    pub fn accepts(&self, word: &str, input: &str) -> bool {
        // Special case 1: Empty input (outside domain of h_n from thesis page 51)
        // From Levenshtein definition: d(w, ε) = |w|
        // Accept if |w| ≤ n
        if input.is_empty() {
            return word.len() <= self.max_distance as usize;
        }

        // Special case 2: Input too long (encoding h_n undefined)
        // From thesis page 51: h_n(w, x) defined only if |x| ≤ |w| + n
        if input.len() > word.len() + self.max_distance as usize {
            return false;
        }

        // Start with initial state {I#0}
        let mut state = self.initial_state();

        // Process each character of input
        // This generates the bit vector sequence h_n(w, x) = β(x₁, s_n(w,1))...β(x_t, s_n(w,t))
        for (i, input_char) in input.chars().enumerate() {
            // Compute relevant subword s_n(w, i+1)
            // From thesis page 51: s_n(w, i) = w_{i-n}...w_{min(|w|, i+n+1)}
            let subword = self.relevant_subword(word, i + 1);

            // Compute characteristic vector β(x_i, s_n(w, i))
            let bit_vector = CharacteristicVector::new(input_char, &subword);

            // Apply transition: state := δ^∀,χ_n(state, β)
            // Pass input position (1-indexed) as k parameter for diagonal crossing
            if let Some(next_state) = state.transition(&self.operations, &bit_vector, i + 1) {
                state = next_state;
            } else {
                // Transition failed, reject
                return false;
            }
        }

        // Check acceptance using Proposition 11 criterion (thesis page 24)
        // A position i#e is accepting if: p - i ≤ n - e
        // (remaining characters ≤ remaining error budget)
        self.is_accepting(&state, word.len(), input.len())
    }

    /// Compute relevant subword s_n(w, i)
    ///
    /// From thesis page 51:
    /// ```text
    /// s_n(w, i) = w_{i-n}w_{i-n+1}...w_v
    /// where v = min(|w|, i + n + 1)
    /// ```
    ///
    /// Pad with '$' for positions before start of word.
    ///
    /// # Arguments
    ///
    /// - `word`: Dictionary word w
    /// - `position`: Position i (1-indexed)
    ///
    /// # Returns
    ///
    /// Relevant subword around position i
    fn relevant_subword(&self, word: &str, position: usize) -> String {
        let n = self.max_distance as i32;
        let i = position as i32;

        // From thesis page 51: s_n(w, i) = w_{i-n}...w_v where v = min(|w|, i + n + 1)
        // The notation w_a...w_b means positions from a through b inclusive (1-indexed)
        let start = i - n;
        let v = std::cmp::min(word.len() as i32, i + n + 1);

        let mut result = String::new();

        // Note: positions are 1-indexed in the thesis, but Rust uses 0-indexing
        // The range should be inclusive of v (start..=v would work, but v might be past word end)
        for pos in start..=v {
            if pos < 1 {
                // Before the start of the word - pad with '$'
                result.push('$');
            } else if pos <= word.len() as i32 {
                // Convert 1-indexed position to 0-indexed
                let idx = (pos - 1) as usize;
                if let Some(ch) = word.chars().nth(idx) {
                    result.push(ch);
                }
            }
            // If pos > word.len(), we're past the end - don't add anything
        }

        result
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_new() {
        let automaton = GeneralizedAutomaton::new(2);
        assert_eq!(automaton.max_distance(), 2);
    }

    #[test]
    fn test_debug_identical() {
        let automaton = GeneralizedAutomaton::new(2);
        let word = "test";
        let input = "test";

        // Manual step-through
        let mut state = automaton.initial_state();
        eprintln!("\nDEBUG: Initial state = {}", state);

        for (i, ch) in input.chars().enumerate() {
            eprintln!("\nDEBUG: Processing char {} ('{}') at input position {}", i+1, ch, i);

            let subword = automaton.relevant_subword(word, i + 1);
            eprintln!("DEBUG: Relevant subword = '{}'", subword);

            let bit_vector = CharacteristicVector::new(ch, &subword);
            eprintln!("DEBUG: Bit vector length = {}", bit_vector.len());

            match state.transition(&automaton.operations, &bit_vector, i + 1) {
                Some(next) => {
                    eprintln!("DEBUG: Next state = {}", next);
                    state = next;
                }
                None => {
                    panic!("Transition failed at position {}", i);
                }
            }
        }

        eprintln!("\nDEBUG: Final state = {}", state);
        eprintln!("DEBUG: Word length = {}, Input length = {}", word.len(), input.len());

        // Check acceptance
        let is_accepting = automaton.is_accepting(&state, word.len(), input.len());
        eprintln!("DEBUG: is_accepting = {}", is_accepting);

        if !is_accepting {
            eprintln!("\nDEBUG: Checking each position:");
            for pos in state.positions() {
                let current_word_pos = input.len() as i32 + pos.offset();
                let remaining_chars = word.len() as i32 - current_word_pos;
                let remaining_errors = automaton.max_distance() as i32 - pos.errors() as i32;
                eprintln!("  Position {}: current_word_pos={}, remaining_chars={}, remaining_errors={}, accepting={}",
                         pos, current_word_pos, remaining_chars, remaining_errors,
                         remaining_chars >= 0 && remaining_chars <= remaining_errors);
            }
        }

        assert!(is_accepting, "Should accept identical strings");
    }

    #[test]
    fn test_accepts_identical() {
        let automaton = GeneralizedAutomaton::new(2);
        assert!(automaton.accepts("test", "test"));
        assert!(automaton.accepts("", ""));
        assert!(automaton.accepts("hello", "hello"));
    }

    #[test]
    fn test_accepts_one_substitution() {
        let automaton = GeneralizedAutomaton::new(2);
        assert!(automaton.accepts("test", "text")); // t->x
        assert!(automaton.accepts("hello", "hallo")); // e->a
    }

    #[test]
    fn test_debug_one_insertion() {
        let automaton = GeneralizedAutomaton::new(2);
        let word = "test";
        let input = "tests";

        eprintln!("\nDEBUG: Testing insertion word='{}', input='{}', max_distance={}", word, input, automaton.max_distance());

        let mut state = automaton.initial_state();
        eprintln!("Initial state: {}", state);

        for (i, ch) in input.chars().enumerate() {
            eprintln!("\n--- Processing char {} ('{}') at position {} ---", i+1, ch, i+1);

            let subword = automaton.relevant_subword(word, i + 1);
            eprintln!("Relevant subword: '{}'", subword);

            let bit_vector = CharacteristicVector::new(ch, &subword);
            eprintln!("Bit vector length: {}", bit_vector.len());

            match state.transition(&automaton.operations, &bit_vector, i + 1) {
                Some(next) => {
                    eprintln!("Next state: {}", next);
                    state = next;
                }
                None => {
                    eprintln!("Transition failed!");
                    panic!("Should not fail at position {}", i+1);
                }
            }
        }

        eprintln!("\n--- Final state check ---");
        eprintln!("Final state: {}", state);
        eprintln!("Word length: {}", word.len());
        eprintln!("Input length: {}", input.len());

        let n = automaton.max_distance() as i32;
        for pos in state.positions() {
            let current_word_pos = input.len() as i32 + pos.offset();
            let remaining_chars = word.len() as i32 - current_word_pos;
            let remaining_errors = n - (pos.errors() as i32);

            eprintln!("\nPosition: {}", pos);
            eprintln!("  current_word_pos = {} + {} = {}", input.len(), pos.offset(), current_word_pos);
            eprintln!("  remaining_chars = {} - {} = {}", word.len(), current_word_pos, remaining_chars);
            eprintln!("  remaining_errors = {} - {} = {}", n, pos.errors(), remaining_errors);
            eprintln!("  Accept? {} >= 0 && {} <= {} = {}",
                     remaining_chars, remaining_chars, remaining_errors,
                     remaining_chars >= 0 && remaining_chars <= remaining_errors);
        }

        let is_accepting = automaton.is_accepting(&state, word.len(), input.len());
        eprintln!("\nFinal is_accepting result: {}", is_accepting);

        assert!(is_accepting, "Should accept insertion");
    }

    #[test]
    fn test_accepts_one_insertion() {
        let automaton = GeneralizedAutomaton::new(2);
        assert!(automaton.accepts("test", "tests")); // +s at end
        assert!(automaton.accepts("test", "ttest")); // +t at start
    }

    #[test]
    fn test_accepts_one_deletion() {
        let automaton = GeneralizedAutomaton::new(2);
        assert!(automaton.accepts("tests", "test")); // -s at end
        assert!(automaton.accepts("ttest", "test")); // -t at start
    }

    #[test]
    fn test_rejects_too_far() {
        let automaton = GeneralizedAutomaton::new(2);
        assert!(!automaton.accepts("test", "hello")); // distance 4
        assert!(!automaton.accepts("abc", "xyz")); // distance 3
    }

    #[test]
    fn test_empty_input() {
        let automaton = GeneralizedAutomaton::new(2);
        assert!(automaton.accepts("", "")); // distance 0
        assert!(automaton.accepts("ab", "")); // distance 2
        assert!(!automaton.accepts("abc", "")); // distance 3 > 2
    }

    #[test]
    fn test_empty_word() {
        let automaton = GeneralizedAutomaton::new(2);
        assert!(automaton.accepts("", "ab")); // distance 2
        assert!(!automaton.accepts("", "abc")); // distance 3 > 2
    }

    #[test]
    fn test_max_distance_zero() {
        let automaton = GeneralizedAutomaton::new(0);
        assert!(automaton.accepts("test", "test")); // exact match
        assert!(!automaton.accepts("test", "text")); // any difference rejected
    }

    #[test]
    fn test_debug_deletion_middle() {
        let automaton = GeneralizedAutomaton::new(1);
        let word = "test";
        let input = "tst";  // Missing 'e' in middle

        eprintln!("\nDEBUG: Testing deletion in middle: word='{}', input='{}', max_distance={}",
                  word, input, automaton.max_distance());
        eprintln!("Expected: true (1 deletion)");

        // Manual step-through
        let mut state = automaton.initial_state();
        eprintln!("\nInitial state: {}", state);

        for (i, ch) in input.chars().enumerate() {
            eprintln!("\n--- Processing char {} ('{}') at position {} ---", i+1, ch, i+1);

            let subword = automaton.relevant_subword(word, i + 1);
            eprintln!("Relevant subword: '{}'", subword);

            let bit_vector = CharacteristicVector::new(ch, &subword);
            eprintln!("Bit vector length: {}", bit_vector.len());

            match state.transition(&automaton.operations, &bit_vector, i + 1) {
                Some(next) => {
                    eprintln!("Next state: {}", next);
                    state = next;
                }
                None => {
                    eprintln!("Transition failed - no successor state!");
                    panic!("Should not fail at position {}", i+1);
                }
            }
        }

        eprintln!("\n--- Final state check ---");
        eprintln!("Final state: {}", state);
        eprintln!("Word length: {}", word.len());
        eprintln!("Input length: {}", input.len());

        // Check is_accepting manually for each position
        let n = automaton.max_distance() as i32;
        eprintln!("\nChecking acceptance for each position:");

        use crate::transducer::generalized::GeneralizedPosition;
        for pos in state.positions() {
            match pos {
                GeneralizedPosition::MFinal { offset, errors } => {
                    eprintln!("\nM-type position: offset={}, errors={}", offset, errors);
                    eprintln!("  M-type accepting? offset <= 0 && errors <= {}: {} <= 0 && {} <= {} = {}",
                             n, offset, errors, n, *offset <= 0 && *errors <= n as u8);
                }
                GeneralizedPosition::INonFinal { offset, errors } => {
                    let current_word_pos = input.len() as i32 + offset;
                    let remaining_chars = word.len() as i32 - current_word_pos;
                    let remaining_errors = n - (*errors as i32);

                    eprintln!("\nI-type position: offset={}, errors={}", offset, errors);
                    eprintln!("  current_word_pos = {} + {} = {}", input.len(), offset, current_word_pos);
                    eprintln!("  remaining_chars = {} - {} = {}", word.len(), current_word_pos, remaining_chars);
                    eprintln!("  remaining_errors = {} - {} = {}", n, errors, remaining_errors);
                    eprintln!("  Accept? {} >= 0 && {} <= {} = {}",
                             remaining_chars, remaining_chars, remaining_errors,
                             remaining_chars >= 0 && remaining_chars <= remaining_errors);
                }
            }
        }

        let result = automaton.accepts(word, input);
        eprintln!("\n=== Final result: {} ===", result);
        eprintln!("Expected: true");

        assert!(result, "Should accept deletion in middle");
    }

    #[test]
    fn test_max_distance_one() {
        let automaton = GeneralizedAutomaton::new(1);
        assert!(automaton.accepts("test", "text")); // 1 substitution
        assert!(automaton.accepts("test", "tst")); // 1 deletion
        assert!(!automaton.accepts("test", "tx")); // distance 2
    }
}
