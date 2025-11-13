# Merge/Split Operations Analysis - Phase 3

**Date**: 2025-11-13
**Status**: Research Phase

## Overview

Analyzing merge and split operations from the lazy automaton (`src/transducer/transition.rs:380-495`) to design the Universal automaton implementation.

## Lazy Automaton Semantics

### Operation Definitions

**Merge Operation**: Two input characters combine into one word character
- **Cost**: 1 error
- **Effect**: Advance input position by +2, advance word position by +1
- **Notation**: ⟨2,1,1⟩ (2 from input, 1 from word, cost 1)

**Split Operation**: One input character expands into two word characters
- **Cost**: 1 error
- **Effect**: Advance input position by +1, advance word position by +2
- **Notation**: ⟨1,2,1⟩ (1 from input, 2 from word, cost 1)
- **Two-step process**: Enter split state, then complete split

### Split State Machine

Unlike transposition (which has intermediate state), split is also stateful:

1. **Enter Split** (`transition.rs:415, 430, 449, 469`):
   - Condition: `!s` (not in special state) and `i < query_length`
   - Creates: `Position::new_special(i, e + 1)`
   - Stays at same input position `i`, increments error
   - Sets `is_special = true` (split state)

2. **Complete Split** (`transition.rs:459, 475, 490`):
   - Condition: `s` (in special state)
   - Creates: `Position::new(i + 1, e)`
   - Advances input by +1, keeps same error count
   - Returns to `is_special = false`

**Key Insight**: Split is similar to transposition's two-step process!
- Enter: `i#e` → `i#(e+1)_s` (same i, increment error)
- Complete: `i#(e+1)_s` → `(i+1)#e` (advance i by 1, decrement error)

Wait - this doesn't match the ⟨1,2,1⟩ notation! Let me re-analyze...

### Re-Analysis of Split

Looking more carefully at line 459:
```rust
// In special state (completing split)
next.push(Position::new(i + 1, e));
```

The split completes by advancing `i` by 1, but what about the word?

The key is that split is entered when checking `cv[h]` (current word position), and completed when checking `cv[h]` again at the NEXT input character. The bit vector advancement handles the "consume 2 word characters" part!

**Corrected Understanding**:
- **Enter Split**: At input `k`, word position `i`, reading word char 1 of 2
  - State: `i#e` → `i#(e+1)_s`
  - Bit vector: Stays at same position (will re-check)
- **Complete Split**: At next input `k+1`, still at word position `i`, reading word char 2 of 2
  - State: `i#(e+1)_s` → `(i+1)#e`
  - Bit vector: Advances normally (has now consumed 2 word chars across 2 inputs)

So split allows consuming 2 consecutive word characters for 1 input character!

### Merge Operation

From lines 420, 454:
```rust
// Merge operation: skip 2 query chars (only if we have 2 chars available)
if i + 2 <= query_length {
    next.push(Position::new(i + 2, e + 1));
}
```

**Merge** is simpler - it's a direct operation:
- No special state needed
- Jump from `i#e` → `(i+2)#(e+1)` in one step
- Consumes 2 input chars, 1 word char
- Like a "double deletion" but matches 1 word char

### Additive Nature

Just like transposition, merge/split includes ALL standard operations (`transition.rs:412-421, 446-455`):
- Insertion: `i#e` → `i#(e+1)`
- Deletion (via epsilon closure): `i#e` → `(i+1)#(e+1)`
- Substitution: `i#e` → `(i+1)#(e+1)`
- Plus merge and split

## Universal Automaton Mapping

### Offset Calculations for Merge

**Merge**: `i#e` → `(i+2)#(e+1)`

At input `k`, position `I+offset#e`:
- Current word position: `i = offset + k`
- Target at next input `k+1`: `i+2` at input position `k+1`
- Need: `offset' + (k+1) = i+2 = (offset+k)+2`
- Therefore: **`offset' = offset + 1`**

### Offset Calculations for Split

**Enter Split**: `i#e` → `i#(e+1)_s`

At input `k`, position `I+offset#e`:
- Current word position: `i = offset + k`
- Target at next input `k+1`: still at `i` (same word position)
- Need: `offset' + (k+1) = i = offset+k`
- Therefore: **`offset' = offset - 1`**

**Complete Split**: `i#(e+1)_s` → `(i+1)#e`

At input `k`, position `I+offset#(e+1)_s`:
- Current word position: `i = offset + k`
- Target at next input `k+1`: `i+1`
- Need: `offset' + (k+1) = i+1 = (offset+k)+1`
- Therefore: **`offset' = offset`**

### Comparison with Transposition

| Operation | Enter | Complete |
|-----------|-------|----------|
| **Transposition** | `offset - 1` | `offset + 1` |
| **Split** | `offset - 1` | `offset + 0` |
| **Merge** | N/A (direct) | `offset + 1` |

Interesting patterns:
- Both transposition and split ENTER with `offset - 1` (stay at same word position)
- Transposition complete jumps by +2 words, split complete stays at +1 word
- Merge is like transposition complete but without intermediate state

## Implementation Plan

### MergeSplitState Enum

```rust
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum MergeSplitState {
    Usual,      // Normal state
    Splitting,  // In the middle of split operation
}
```

### Successor Generation

**For I-type positions**:

1. **Standard Operations** (same as before)
   - Match, insertion, substitution, deletion

2. **Merge Operation** (when not splitting)
   ```rust
   // Merge: consume 2 inputs, 1 word char
   if !is_splitting && next_match_index < bit_vector.len()
       && bit_vector.is_match(next_match_index) && errors < max_distance {
       // i#e → (i+2)#(e+1)
       // offset' = offset + 1
       successors.push(UniversalPosition::new_i_with_state(
           offset + 1,
           errors + 1,
           max_distance,
           MergeSplitState::Usual,
       ));
   }
   ```

3. **Split Entry** (when not splitting)
   ```rust
   // Split entry: one input becomes two word chars
   if !is_splitting && match_index < bit_vector.len()
       && bit_vector.is_match(match_index) && errors < max_distance {
       // i#e → i#(e+1)_s
       // offset' = offset - 1
       successors.push(UniversalPosition::new_i_with_state(
           offset - 1,
           errors + 1,
           max_distance,
           MergeSplitState::Splitting,
       ));
   }
   ```

4. **Split Completion** (when splitting)
   ```rust
   if is_splitting && match_index < bit_vector.len() && bit_vector.is_match(match_index) {
       // i#(e+1)_s → (i+1)#e
       // offset' = offset + 0
       successors.push(UniversalPosition::new_i_with_state(
           offset,
           errors - 1,
           max_distance,
           MergeSplitState::Usual,
       ));
   }
   ```

## Questions to Validate

1. Does the lazy automaton allow split at ANY position or only at specific boundaries?
   - Answer: Lines 414, 428, 448, 468 check `i < query_length`, so yes, allowed anywhere

2. Can merge and split be combined in the same transition?
   - Answer: No - merge is only added when `!s` (not splitting), lines 419, 453

3. What happens at word boundaries during split?
   - Answer: Lines 461-476 handle `h + 1 == w` boundary case, split still works

4. Can split complete even at max_distance?
   - Answer: YES! Line 489-490 allows split completion even at `e == max_distance`

## Next Steps

1. Implement `MergeSplitState` enum
2. Update `MergeAndSplit` trait with complete logic
3. Create comprehensive test cases
4. Cross-validate against lazy automaton

## References

- Lazy automaton: `src/transducer/transition.rs:380-495`
- Transposition Phase 2: `docs/universal/transposition_phase2_summary.md`
