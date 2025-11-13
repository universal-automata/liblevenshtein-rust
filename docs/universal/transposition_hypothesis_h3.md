# Transposition Logic - Hypothesis 3: Invert the Condition

**Date**: 2025-11-13
**Status**: New hypothesis based on transposition semantics

## Key Insight

The transposition should be entered when we detect a potential character swap. This happens when:
1. Current input character does NOT match current word position (b[0] = 0)
2. Current input character DOES match next word position (b[1] = 1)

This suggests characters at positions i and i+1 might be swapped in the input.

## Hypothesis

**Current implementation checks**: `!bit_vector.is_match(next_match_index)` → enter if b[1] = 0
**New hypothesis**: Should check `bit_vector.is_match(next_match_index)` → enter if b[1] = 1

## Rationale

For "ab" → "ba":
- Input[0] = 'b', Word = "ab"
- Position I+0#0 (word position 0)
- b[0] = ('b' == 'a') = 0 (no match at current position)
- b[1] = ('b' == 'b') = 1 (match at next position!)
- Interpretation: Input has 'b', but word expects 'a' at position 0 and 'b' at position 1
- Hypothesis: Positions 0-1 might be swapped!
- Action: Enter transposing state

Then at Input[1] = 'a':
- In Transposing state at position (word position increased)
- Check if 'a' matches the PREVIOUS word position (completing the swap)
- If yes → transposition confirmed!

## Proposed Fix

Change line 223 in position.rs from:
```rust
&& !bit_vector.is_match(next_match_index)
```

To:
```rust
&& bit_vector.is_match(next_match_index)
```

Also need to review the Transposing state logic to ensure it correctly completes the transposition.

## Alternative Interpretation

Maybe Definition 7's `b[1]` doesn't mean what I think it means. Let me consider:
- The bit vector is indexed relative to the position's window
- For position i#e, maybe b[0] corresponds to word[i-1], b[1] to word[i], etc.?
- This would explain why "b[1] = 0" makes sense

But this contradicts the standard successor implementation which clearly shows:
```rust
// position.rs:736
let match_index = (max_distance as i32 + offset) as usize;
// This checks b[n+offset] which should be b[0] for the current position
```

## Next Step

Try inverting the condition and test if it fixes the failing tests.
