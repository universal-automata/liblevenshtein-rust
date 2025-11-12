# Phase 4: Automaton Construction - Progress Report

## Overview

Phase 4 implements the complete Universal Levenshtein Automaton A^∀,χ_n structure, including initialization, state transitions, bit vector encoding, and word acceptance checking. Most components are implemented correctly, but the acceptance condition requires further work.

## Implementation Summary

### Files Created

1. **NEW**: `src/transducer/universal/automaton.rs` (477 lines)
2. **MODIFIED**: `src/transducer/universal/mod.rs` (added automaton module export)
3. **NEW**: `docs/research/universal-levenshtein/PHASE4_BUG_ANALYSIS.md`

### What Was Implemented

#### 1. UniversalAutomaton Structure (lines 62-94)

```rust
pub struct UniversalAutomaton<V: PositionVariant> {
    max_distance: u8,
    _phantom: std::marker::PhantomData<V>,
}
```

**Features**:
- Generic over position variant (Standard, Transposition, MergeAndSplit)
- Stores maximum distance n
- Stateless design (no precomputed state graph)

#### 2. Initial State Generation (lines 120-130)

From thesis page 38: `I^∀,χ = {I#0}`

```rust
fn initial_state(&self) -> UniversalState<V> {
    let mut state = UniversalState::new(self.max_distance);
    // I#0: I-type position with offset 0, errors 0
    if let Ok(pos) = UniversalPosition::new_i(0, 0, self.max_distance) {
        state.add_position(pos);
    }
    state
}
```

#### 3. Final State Check (lines 132-146)

From thesis page 38: `F^∀,χ_n = M^χ_states`

```rust
fn is_final(&self, state: &UniversalState<V>) -> bool {
    state.positions().any(|pos| pos.is_m_type())
}
```

**NOTE**: This implementation is incomplete - see PHASE4_BUG_ANALYSIS.md for details.

#### 4. Relevant Subword Computation (lines 202-240)

From thesis page 51: `s_n(w, i) = w_{i-n}...w_v where v = min(|w|, i+n+1)`

```rust
fn relevant_subword(&self, word: &str, position: usize) -> String {
    let n = self.max_distance as i32;
    let i = position as i32;

    let start = i - n;
    let v = std::cmp::min(word.len() as i32, i + n + 1);

    let mut result = String::new();

    for pos in start..=v {
        if pos < 1 {
            result.push('$');  // Padding
        } else if pos <= word.len() as i32 {
            let idx = (pos - 1) as usize;
            if let Some(ch) = word.chars().nth(idx) {
                result.push(ch);
            }
        }
    }

    result
}
```

**Key Features**:
- 1-indexed positions (thesis convention)
- Padding with '$' for positions before word start
- Window size: exactly 2n+2 characters (unless limited by word length)
- Inclusive range [i-n, v] where v = min(|w|, i+n+1)

#### 5. Word Acceptance (lines 148-200)

From thesis page 51-52: h_n(w, x) encoding and acceptance

```rust
pub fn accepts(&self, word: &str, input: &str) -> bool {
    let mut state = self.initial_state();

    for (i, input_char) in input.chars().enumerate() {
        let subword = self.relevant_subword(word, i + 1);
        let bit_vector = CharacteristicVector::new(input_char, &subword);

        if let Some(next_state) = state.transition(&bit_vector, i + 1) {
            state = next_state;
        } else {
            return false;
        }
    }

    self.is_final(&state)
}
```

**Algorithm**:
1. Start with initial state {I#0}
2. For each character x_i in input:
   - Compute relevant subword s_n(w, i)
   - Compute characteristic vector β(x_i, s_n(w, i))
   - Apply transition δ^∀,χ_n(state, β)
3. Check if final state contains M-type positions

**ISSUE**: Acceptance condition is incomplete - see bug analysis.

### 2. Comprehensive Test Suite (18 tests, lines 257-477)

#### Basic Automaton Tests (6 tests)
1. **test_new_automaton** - Create automaton with max distance
2. **test_initial_state** - Initial state is {I#0}
3. **test_is_final_i_type_state** - I-type states not final
4. **test_is_final_m_type_state** - M-type states are final
5. **test_is_final_mixed_state** - Mixed states are final

#### Relevant Subword Tests (4 tests)
6. **test_relevant_subword_start** - Position 1, includes padding
7. **test_relevant_subword_middle** - Position 3, full window
8. **test_relevant_subword_end** - Position 4, truncated window
9. **test_relevant_subword_n1** - Different max distance (n=1)

#### Acceptance Tests (8 tests) - **Currently Failing**
10. **test_accepts_identical** - Same word and input (distance 0)
11. **test_accepts_substitution** - One substitution
12. **test_accepts_insertion** - One insertion
13. **test_accepts_deletion** - One deletion
14. **test_rejects_too_far** - Distance exceeds max
15. **test_accepts_empty_to_empty** - Both empty strings
16. **test_accepts_empty_word** - Empty word, short input
17. **test_accepts_to_empty** - Non-empty word, empty input

#### Additional Tests (not shown in excerpt)
- test_rejects_empty_word_too_far
- test_rejects_to_empty_too_far
- test_accepts_multiple_edits
- test_accepts_n1
- test_accepts_longer_words

### Test Results

**Passing**: 144 / 154 tests (includes all previous phases)
- 6 automaton structure tests ✓
- 4 relevant subword tests ✓
- 0 acceptance tests ✓ (10 failing)

**Failing**: 10 acceptance tests
- All tests in `test_accepts_*` category failing
- Root cause: Incorrect acceptance condition

## Known Issues

### Issue 1: Acceptance Condition Implementation

**Problem**: Current `is_final()` only checks for M-type positions, but:
1. Empty word case not handled (I#0 should be accepting)
2. I-type positions within n deletions of word end should be accepting
3. May need end-of-word transitions to consume remaining characters

**Impact**: All acceptance tests fail

**Analysis**: See `PHASE4_BUG_ANALYSIS.md` for detailed investigation

### Issue 2: Transition Failures

**Problem**: Some transitions fail after 2-3 steps even for identical strings

**Debug Output** (test_accepts_identical):
```
Step 1: subword="$$test" (6 chars), next_state: 3 positions ✓
Step 2: subword="$test" (5 chars), next_state: 3 positions ✓
Step 3: subword="test" (4 chars), transition FAILED ✗
```

**Hypothesis**: Bit vector length or diagonal crossing causing empty successor states

## Theoretical Foundations

### Definition 15 (Thesis Page 30): Universal Automaton

```
A^∀,χ_n = ⟨Σ^∀_n, Q^∀,χ_n, I^∀,χ, F^∀,χ_n, δ^∀,χ_n⟩
```

Where:
- **Σ^∀_n**: Bit vectors of length ≤ 2n + 2
- **Q^∀,χ_n**: State space I^χ_states ∪ M^χ_states
- **I^∀,χ**: Initial state {I#0}
- **F^∀,χ_n**: Final states M^χ_states
- **δ^∀,χ_n**: Transition function (implemented in Phase 2 Week 5)

### Function s_n (Thesis Page 51): Relevant Subword

```
s_n(w, i) = w_{i-n}w_{i-n+1}...w_v
where v = min(|w|, i + n + 1)
```

**Purpose**: Extract window of at most 2n+2 characters around position i.

### Function h_n (Thesis Page 51): Word Pair Encoding

```
h_n(w, x₁x₂...x_t) = β(x₁, s_n(w,1))β(x₂, s_n(w,2))...β(x_t, s_n(w,t))

Valid only if t ≤ |w| + n
```

**Purpose**: Encode pair (w, x) as bit vector sequence for automaton processing.

## Integration with Previous Phases

### Phase 1 Integration ✓
- Uses `UniversalPosition<V>` for I-type and M-type positions
- Uses `UniversalState<V>` for state management
- Respects position invariants

### Phase 2 Week 3 Integration ✓
- Uses `CharacteristicVector` for bit vector encoding
- Encodes character matches in subword windows

### Phase 2 Week 5 Integration ✓
- Uses `UniversalState::transition()` for state transitions
- Passes `input_length` parameter for diagonal crossing
- Leverages all successor functions (δ^ε_p, δ^t_p, δ^s_p)

### Phase 3 Integration ✓
- Uses diagonal crossing functions (rm, f_n, m_n)
- Handles I ↔ M type conversion automatically in transitions

## Complexity Analysis

### Relevant Subword
- **Time**: O(n) to extract window (at most 2n+2 characters)
- **Space**: O(n) for subword string

### Accepts Function
- **Time**: O(|input| × |Q| × S) where:
  - |input| iterations for each character
  - |Q| positions in state (bounded by configuration space size)
  - S operations per position successor
- **Space**: O(|Q|) for state storage

### Overall Automaton
- **Space**: O(1) - no precomputed state graph (stateless design)
- **Time per query**: O(|input| × |Q| × S)

## Examples from Usage

### Example 1: Create Automaton

```rust
use liblevenshtein::transducer::universal::{UniversalAutomaton, Standard};

let automaton = UniversalAutomaton::<Standard>::new(2);
assert_eq!(automaton.max_distance(), 2);
```

### Example 2: Check Acceptance (once fixed)

```rust
let automaton = UniversalAutomaton::<Standard>::new(2);

// Distance 0
assert!(automaton.accepts("test", "test"));

// Distance 1
assert!(automaton.accepts("test", "text"));  // substitution
assert!(automaton.accepts("test", "teast")); // insertion
assert!(automaton.accepts("test", "tet"));   // deletion

// Distance > 2
assert!(!automaton.accepts("test", "hello"));
```

### Example 3: Relevant Subword

```rust
let automaton = UniversalAutomaton::<Standard>::new(2);

// Position 1 (n=2): window [-1, 4] = $$test (2 padding + 4 word chars)
let subword = automaton.relevant_subword("test", 1);
assert_eq!(subword, "$$test");

// Position 3 (n=2): window [1, 6] but clamp to [1, 4] = test
let subword = automaton.relevant_subword("test", 3);
assert_eq!(subword, "test");
```

## What's Next

### Immediate (Fix Phase 4)
1. **Fix acceptance condition**:
   - Handle empty word case
   - Check I-type positions for word end proximity
   - Possibly add end-of-word transitions
2. **Debug transition failures**:
   - Investigate why transitions fail after 2-3 steps
   - Check bit vector/position compatibility
3. **Verify all tests pass**

### Future (Phase 5+)
1. **Performance Optimization**:
   - Profile acceptance queries
   - Optimize hot paths in transition
   - Consider caching frequent computations
2. **Dictionary Integration**:
   - Integrate with existing dictionary structures
   - Implement fuzzy search API
3. **Advanced Features**:
   - Transposition variant (χ = t)
   - Merge/split variant (χ = ms)
   - State graph precomputation (optional)

## Summary

Phase 4 successfully implements most of the Universal Levenshtein Automaton:

✓ Automaton structure (UniversalAutomaton<V>)
✓ Initial state generation ({I#0})
✓ Relevant subword computation (s_n function)
✓ Bit vector encoding per input character
✓ State transition loop (uses Phase 2 Week 5 transition)
✓ 144 tests passing (including all previous phases)

❌ Acceptance condition incomplete (10 tests failing)
❌ Transitions failing for some inputs (needs investigation)

The foundation is solid and most components are correct. The remaining work is to fix the acceptance logic and debug the transition failures. Once these are resolved, Phase 4 will be complete.

---

**Completion Date**: 2025-11-11 (in progress)
**Tests Passing**: 144 / 154
**Status**: 🚧 INCOMPLETE (acceptance condition needs fix)

