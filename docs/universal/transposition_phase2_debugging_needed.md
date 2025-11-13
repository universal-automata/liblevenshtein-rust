# Transposition Implementation - Debugging Required

**Date**: 2025-11-13
**Status**: Phase 2 infrastructure complete, logic needs debugging

## Summary

Phase 2 successfully implemented the infrastructure for transposition with trait-based dispatch. However, acceptance tests are failing, indicating the transposition logic needs correction.

## What Works

1. **Infrastructure** ✅
   - `PositionVariant` trait extended with `compute_i_successors()` and `compute_m_successors()`
   - Trait implementations for Standard, Transposition, and MergeAndSplit variants
   - Generic `successors()` method uses trait dispatch
   - All 156 original tests pass

2. **Backward Compatibility** ✅
   - Standard variant maintains zero overhead
   - Existing functionality unaffected

## What Needs Debugging

### Test Results

**Failing**: 9 out of 12 transposition tests
**Passing**: 3 tests (distance zero, rejects non-adjacent, with standard operations at distance 2)

**Failing tests**:
- `test_transposition_adjacent_swap_start`: "test" → "etst"
- `test_transposition_adjacent_swap_middle`: "test" → "tset"
- `test_transposition_adjacent_swap_end`: "test" → "tets"
- `test_transposition_two_chars`: "ab" → "ba"
- `test_transposition_vs_standard`
- `test_transposition_longer_words`
- `test_transposition_multiple_swaps`
- `test_transposition_with_repeated_chars`
- `test_transposition_empty_and_single_char` (partial failure)

### Potential Issues

1. **Transposition Logic Interpretation**

   Current implementation (position.rs:202-323):
   ```rust
   TranspositionState::Usual => {
       // Get standard successors
       let mut successors = UniversalPosition::<Self>::successors_i_type_standard(...);

       // Add transposition initiation if NO match
       if !bit_vector.is_match(match_index) && errors < max_distance {
           // Enter transposition: (i+1)#(e+1)_t
           successors.push(new_i_with_state(offset + 1, errors + 1, ..., Transposing));
       }
   }

   TranspositionState::Transposing => {
       // Complete transposition if match
       if bit_vector.is_match(match_index) {
           vec![new_i_with_state(offset + 1, errors, ..., Usual)]
       } else {
           vec![]
       }
   }
   ```

   **Hypothesis 1**: Transposition should trigger on mismatch where the *next* character would match the *previous* input character. The current logic might not be checking this correctly.

   **Hypothesis 2**: The bit vector indexing might be off. When checking for transposition:
   - At input position k, word position i
   - We're checking if word[i+1] matches input[k-1] (the previous input character)
   - The bit vector β(x_k, s_n(w,k)) encodes matches for current input char x_k

2. **Bit Vector Semantics**

   The characteristic vector β(x, w') tells us if character x matches positions in window w'.

   For transposition at position k:
   - Input so far: ...x_{k-1} x_k ...
   - Word window: ... w_i w_{i+1} ...
   - Standard: tries to match x_k with w_i
   - Transposition: tries to match x_k with w_{i-1} and x_{k-1} with w_i

   **Issue**: The current bit vector only encodes matches for the *current* input character. To check transposition, we'd need access to the *previous* input character, which isn't available in the successor function signature.

3. **State Machine Flow**

   **Current implementation**:
   1. Usual state, no match → enter Transposing state
   2. Transposing state, match → complete transposition, return to Usual

   **Potential issue**: The transition might need to verify that:
   - Current input char matches previous word char (swap detection)
   - Previous input char would match current word char (swap confirmation)

   But we don't have access to previous input/word characters in the successor function.

## Root Cause Analysis

The fundamental issue is that **transposition is a 2-character operation** that depends on matching:
- Current input char x_k with previous word char w_{i-1}
- Previous input char x_{k-1} with current word char w_i

However, the Universal automaton processes **one character at a time** using bit vectors that only encode matches for the *current* input character.

### How Standard Damerau-Levenshtein Handles This

Traditional Damerau-Levenshtein keeps a full DP matrix where you can look back at diagonal-2 cells. The Universal automaton's parameter-free approach needs a different strategy.

### Mitankin's Solution (Thesis Definition 7)

From the thesis (page 16):

**For transposition state i#e_t**:
```
δ^D,t_e(i#e_t, b) = {(i+2)#e} if b[1] = 1, else ∅
```

Key insight: `b[1]` refers to position 1 in the bit vector, which corresponds to index `n+offset+1` in our implementation.

**Hypothesis**: The transposition state tracks that we've seen a mismatch and advances the position by 1. Then, when processing the *next* input character, if `b[1] = 1` (match at offset+1), we confirm the transposition.

## Debugging Strategy

### Step 1: Manual Trace

Walk through "ab" → "ba" with n=1:

**Initial**: State = {I+0#0_usual}

**Process 'b' (input[0])**:
- Bit vector β('b', "ab") = [0, 1] (no match at position 0, match at position 1)
- Position I+0#0_usual, bit_vector[n+0] = bit_vector[1] = 1 → MATCH
- Standard successor: I+0#0_usual (advance input, stay at word position 0)
- No transposition (match found)

**Hmm, that's wrong** - we should process the first character 'b' against word 'ab', and it doesn't match 'a' at position 0.

Let me reconsider: The bit vector β(x_k, s_n(w,k)) is constructed for input character x_k and the relevant subword s_n(w,k).

For "ab" with input "ba":
- k=0, x_0='b', word="ab", subword s_1("ab",0) = ""a"b" (positions -1 to 1)
  - But position -1 is out of bounds, so effective subword is "ab"
  - β('b', "ab") should mark where 'b' appears: position 1
  - As a bit vector: [0, 1] where index i corresponds to word position relative to window

**This needs careful analysis of the bit vector construction and indexing.**

### Step 2: Add Debug Logging

Instrument the transposition successor functions to log:
- Current offset, errors, variant_state
- Bit vector contents
- Match index calculation
- Which branch is taken

### Step 3: Compare with Standard Implementation

Run both Standard and Transposition variants on same inputs and compare state transitions.

### Step 4: Consult Thesis Examples

Find worked examples in Mitankin's thesis and trace through them step-by-step.

## Immediate Next Steps

1. **Add comprehensive logging** to transposition successor methods
2. **Manual trace** simple cases like "ab" → "ba"
3. **Review bit vector construction** in `bit_vector.rs`
4. **Re-read Mitankin's Definition 7** carefully
5. **Consider consulting the original paper's proofs** for transposition correctness

## Files to Review

- `src/transducer/universal/position.rs:202-323` - Transposition implementation
- `src/transducer/universal/bit_vector.rs` - Characteristic vector construction
- `src/transducer/universal/automaton.rs` - State transitions and acceptance
- Mitankin's thesis - Definition 7 (page 16), Definition 15-18 (pages 30-48)

## Hypothesis for Fix

After reviewing the logic more carefully, I believe the issue might be:

1. **Transposition initiation condition**: Should check if entering transposition state is valid
2. **Bit vector indexing**: The match_index calculation might be off by 1
3. **State conversion**: The I^ε conversion might need adjustment for transposition states

## Time Estimate

- Debugging and fixing: 2-4 hours
- Additional testing: 1 hour
- **Total**: 3-5 hours

## References

- Mitankin's thesis: "Efficient Computation of Substring Equivalence Classes" (TCS 2011)
- Current implementation: `src/transducer/universal/position.rs`
- Test failures: `src/transducer/universal/automaton.rs:588-716`
