# Transposition Logic - Hypothesis 2

**Date**: 2025-11-13
**Status**: Analyzing bit vector indexing semantics

## Problem

Tests are still failing after initial fix. Need to reconsider the interpretation of `b[k]` indexing from Mitankin's thesis.

## Mitankin's Definition 7 (Page 16)

For transposition variant χ = t with error limit e:

**Usual State**:
```
δ^D,t_e(i#e, b) = δ^D_e(i#e, b) ∪ {(i+1)#(e+1)_t} if b[1] = 0 ∧ e < n, else δ^D_e(i#e, b)
```

**Transposing State**:
```
δ^D,t_e(i#e_t, b) = {(i+2)#e} if b[1] = 1, else ∅
```

## Bit Vector Indexing Analysis

The characteristic vector β(x, w') encodes matches at each position. The notation `b[k]` refers to index `k` in the bit vector.

### Standard Interpretation

For position `i#e`:
- offset = `i - e`
- The bit vector is indexed from 0
- Position `b[0]` corresponds to word position `i - e`
- Position `b[k]` corresponds to word position `i - e + k`

In our implementation:
- We construct the bit vector for the substring window around the current position
- `match_index = n + offset` checks position `b[n+offset]`
- For position `i#e` with `offset = i-e`, this checks `b[n + i - e]`

### The `b[1]` Check

When Mitankin writes `b[1]`, this means "check position 1 in the bit vector".

For position `i#e`:
- offset = `i - e`
- `b[0]` maps to index `n + offset` in our implementation
- `b[1]` maps to index `n + offset + 1` in our implementation

### Current Implementation Issues

**I-type Usual State (line 221)**: ✅ CORRECT
```rust
let next_match_index = (max_distance as i32 + offset + 1) as usize;
if next_match_index < bit_vector.len()
    && !bit_vector.is_match(next_match_index)  // Checks b[1] = 0
```

**I-type Transposing State (line 242)**: ❓ NEEDS REVIEW
```rust
let match_index = (max_distance as i32 + offset) as usize;
if match_index < bit_vector.len() && bit_vector.is_match(match_index)  // Checks b[0] = 1???
```

**M-type Usual State (line 282)**: ❌ WRONG
```rust
let match_index = (max_distance as i32 + offset) as usize;
if match_index < bit_vector.len()
    && !bit_vector.is_match(match_index)  // Should check b[1] = 0, not b[0] = 0
```

**M-type Transposing State (line 303)**: ❓ NEEDS REVIEW
```rust
let match_index = (max_distance as i32 + offset) as usize;
if match_index < bit_vector.len() && bit_vector.is_match(match_index)  // Checks b[0] = 1???
```

## New Hypothesis

The issue is with the **Transposing state** interpretation. When we enter the Transposing state, we create a position with offset+1 and errors+1:

```rust
// From Usual state (line 228-233):
UniversalPosition::new_i_with_state(
    offset + 1,      // NEW offset
    errors + 1,      // NEW errors
    max_distance,
    TranspositionState::Transposing,
)
```

So when we're in the Transposing state with this new position:
- The position is conceptually `(i+1)#(e+1)_t`
- The stored offset is `(i+1) - (e+1) = i - e`
- This is the SAME as the original offset!

Wait, that can't be right. Let me reconsider...

Actually, in the I^ε conversion:
- Position `i#e` is stored as `I+offset` where `offset = i - 1`
- No wait, looking at the code again...

Let me trace through "ab" → "ba" manually:

### Manual Trace: "ab" → "ba" with n=1

**Initial State**: {I+0#0_usual}
- offset = 0, errors = 0, state = Usual

**Process input[0] = 'b'**:
- Word = "ab"
- Bit vector β('b', "ab") = [?, ?] - marks where 'b' appears
- 'b' is at position 1 in "ab", so bit_vector[1] = 1
- For position I+0#0:
  - match_index = n + offset = 1 + 0 = 1
  - bit_vector[1] = 1 → MATCH
  - Standard successor: stays at I+0#0 (no advancement because it's a match in window)

Hmm, I need to better understand the bit vector construction and window semantics.

## Root Cause Hypothesis

The fundamental issue might be that **I don't fully understand the bit vector window and indexing semantics**. I need to:

1. Review how the bit vector is constructed in `bit_vector.rs`
2. Understand what `s_n(w, k)` (the subword window) actually contains
3. Map the thesis notation `b[k]` to the correct implementation index

## Next Steps

1. Read `src/transducer/universal/bit_vector.rs` to understand construction
2. Add extensive debug logging to print:
   - Current position (offset, errors, state)
   - Bit vector contents
   - Which indices are being checked
   - Match results
3. Manually trace "ab" → "ba" with actual bit vector values
4. Compare with thesis definitions to find the mapping error

## Possible Bug Patterns

1. **Offset confusion**: The stored offset vs. the actual position index
2. **Window semantics**: The bit vector might be constructed for a shifted window
3. **b[0] vs b[1]**: Currently checking different indices in different states
4. **I^ε conversion**: The conversion formula might affect how we interpret offsets

The most suspicious issue is that in **Transposing state**, I'm checking `b[0]` when the thesis says `b[1]`. This suggests the Transposing state might also need to check `match_index + 1`.
