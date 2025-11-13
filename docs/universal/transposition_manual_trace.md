# Transposition Manual Trace - "ab" → "ba"

**Date**: 2025-11-13
**Status**: Debugging with concrete trace

## Setup

- Word w = "ab" (length 2)
- Input x = "ba" (length 2)
- Max distance n = 1

## Bit Vector Construction

The relevant subword function creates:
```rust
// For position i (1-indexed), n=1:
// start = i - n
// end = min(|w|, i + n)
// Characters from position start to end (1-indexed, inclusive)
```

### For "ab" with n=1:

**Input[0] = 'b', position i=1**:
- `s_1("ab", 1)` = characters from position (1-1=0) to min(2, 1+1=2) = positions 0 to 2
- Position 0 → '$' (padding)
- Position 1 → 'a' (w[0])
- Position 2 → 'b' (w[1])
- Subword: "$ab"
- β('b', "$ab") = [0, 0, 1] (only position 2 matches)

**Input[1] = 'a', position i=2**:
- `s_1("ab", 2)` = characters from position (2-1=1) to min(2, 2+1=3) = positions 1 to 2
- Position 1 → 'a' (w[0])
- Position 2 → 'b' (w[1])
- Subword: "ab"
- β('a', "ab") = [1, 0] (only position 0 matches - 'a')

## State Machine Trace

### Initial State

State = {I+0#0_usual}
- offset = 0
- errors = 0
- variant_state = Usual

### Process input[0] = 'b'

**Bit vector**: β('b', "$ab") = [0, 0, 1]
- Length = 3

**Position I+0#0_usual** (offset=0, errors=0):

Check match at index n+offset = 1+0 = 1:
- bit_vector[1] = 0 (NO MATCH)

**Standard successors** (from `successors_i_type_standard`):
1. Deletion: I+0#1 (stay at word position 0, +1 error)
2. Substitution: I+1#1 (advance word position to 1, +1 error)
3. Insertion: I+0#1 (advance input, stay at word position, +1 error) - wait, this doesn't make sense...

Let me review the standard successor logic...

Actually, looking at the existing code, the standard successors for I-type check `bit_vector[n+offset]`:
- If match: add I+offset#errors (match, no error increase)
- Always add: I+offset#(errors+1) (deletion)
- Always add: I+(offset+1)#(errors+1) (substitution)
- If offset > -(n as i32): add I+(offset-1)#(errors+1) (insertion)

**Standard successors for I+0#0**:
- bit_vector[1] = 0 → NO MATCH successor
- Deletion: I+0#1
- Substitution: I+1#1
- Insertion (offset > -1): I+(-1)#1

**Transposition check** (Usual state):
- Check next_match_index = n + offset + 1 = 1 + 0 + 1 = 2
- bit_vector[2] = 1 (MATCH!)
- errors < max_distance (0 < 1) ✓
- But wait - we should enter transposition when b[1] = 0 (NO match), not when b[1] = 1!

## ERROR FOUND!

The condition `!bit_vector.is_match(next_match_index)` should be checking if b[1] = 0.

Looking at Mitankin's Definition 7:
```
δ^D,t_e(i#e, b) = δ^D_e(i#e, b) ∪ {(i+1)#(e+1)_t} if b[1] = 0 ∧ e < n
```

This means: "Enter transposition state if b[1] = 0 (no match at position 1)".

In our case:
- Position I+0#0 corresponds to word position i = offset + errors = 0 (in 0-indexed), or position 1 in thesis notation
- The bit vector b = [0, 0, 1] has b[0] = 0, b[1] = 0, b[2] = 1
- So b[1] = 0 → YES, we should enter transposition!

But next_match_index = 2, and bit_vector[2] = 1, so the condition `!bit_vector.is_match(2)` = false.

## The Real Problem

**The bit vector indexing in thesis vs. implementation**:

In Mitankin's thesis, `b[k]` means "the k-th bit in the characteristic vector" (0-indexed into the vector itself).

In our implementation:
- The bit vector is constructed from the relevant subword
- For position i#e with offset = i-e
- We check `bit_vector[n+offset+k]` to get what corresponds to thesis notation `b[k]`

**For position I+0#0**:
- offset = 0, errors = 0
- In thesis notation, this is position i#e where offset = i-e, so if offset=0 and e=0, then i=0 (but thesis uses 1-indexed, so this is position 1 in thesis)
- The bit vector b corresponds to matches in the subword around this position
- `b[0]` in thesis = bit_vector[n+offset] = bit_vector[1+0] = bit_vector[1]
- `b[1]` in thesis = bit_vector[n+offset+1] = bit_vector[1+0+1] = bit_vector[2]

So the mapping is correct! Let me reconsider...

Wait, I need to understand what `b[1]` represents semantically.

## Understanding `b[k]` Semantics

Looking at the relevant subword for position i=1, n=1:
- Subword = "$ab" (positions 0, 1, 2 in the subword string)
- Bit vector β('b', "$ab") = [0, 0, 1]
  - Index 0: '$' ≠ 'b' → 0
  - Index 1: 'a' ≠ 'b' → 0
  - Index 2: 'b' = 'b' → 1

The subword represents word positions relative to the current position:
- Index 0 in subword → word position i-n = 1-1 = 0 (padded as '$')
- Index 1 in subword → word position i-n+1 = 0+1 = 1 (word[0] = 'a')
- Index 2 in subword → word position i-n+2 = 0+2 = 2 (word[1] = 'b')

Now, for position `i#e`:
- Current word position is `i`
- `b[0]` checks if input character matches word[i]
- `b[1]` checks if input character matches word[i+1]

For position 1#0 (I+0#0):
- Current word position is 1 (thesis notation, 1-indexed)
- `b[0]` checks if 'b' matches word[1] = 'a' → NO
- `b[1]` checks if 'b' matches word[2] = 'b' → YES!

So `b[1] = 1`, not `b[1] = 0`.

According to Definition 7, we enter transposition when `b[1] = 0`. Since `b[1] = 1`, we should NOT enter transposition here.

This is correct! The transposition check is working as intended for this case.

## Continue Trace

Since we don't enter transposition from I+0#0, the successors are just the standard ones:
- I+0#1 (deletion)
- I+1#1 (substitution)
- I+(-1)#1 (insertion)

### Process input[1] = 'a'

**New state** = {I+0#1, I+1#1, I+(-1)#1}

**Bit vector**: β('a', "ab") = [1, 0]

Let's trace each position:

**Position I+0#1** (offset=0, errors=1):
- match_index = n + offset = 1 + 0 = 1
- bit_vector[1] = 0 (NO MATCH - but wait, the bit vector only has length 2!)

Ah! The bit vector length depends on the subword, which changes based on input position.

For input position i=2, the subword is "ab" (length 2), so the bit vector has length 2.
- Index 0 → word position 1 = 'a'
- Index 1 → word position 2 = 'b'

For position I+0#1:
- offset = 0, errors = 1
- This represents word position i = offset + errors = 0 + 1 = 1 (0-indexed), or position 1 (thesis 1-indexed)
- match_index = n + offset = 1 + 0 = 1
- bit_vector[1] = 0 (checks word[2] = 'b', input = 'a', no match)

Standard successors from I+0#1:
- No match successor (bit_vector[1] = 0)
- Deletion: I+0#2 (but errors would be 2 > max_distance, so rejected)
- Substitution: I+1#2 (rejected)
- Insertion: I+(-1)#2 (rejected)

**Position I+1#1** (offset=1, errors=1):
- match_index = n + offset = 1 + 1 = 2
- bit_vector[2] is out of bounds! (bit_vector.len() = 2)

This means the match check should be guarded. But wait, the bit vector should have sufficient length...

## Issue with Bit Vector Length

I think the problem is that the bit vector length depends on the subword length, which varies based on input position and word boundaries.

Let me re-read how the subword is constructed and verify the indexing...

Actually, looking at line 222-223 in position.rs:
```rust
if next_match_index < bit_vector.len()
    && !bit_vector.is_match(next_match_index)
```

The bounds check is there! So if the index is out of bounds, we don't enter transposition.

Let me reconsider the problem from a different angle.

## Alternative Hypothesis

Maybe the issue is that I'm misunderstanding what "entering transposition state" means.

Looking at Definition 7 again:
- From Usual state i#e, if b[1] = 0, we can transition to (i+1)#(e+1)_t
- From Transposing state i#e_t, if b[1] = 1, we transition to (i+2)#e

The transposition operation swaps two adjacent characters. The state machine:
1. Usual state at position i: sees input char x_k doesn't match word[i+1] (b[1] = 0)
2. Enter Transposing state at position i+1: now at next input char x_{k+1}, check if it matches word[i] (retroactively checking the swap)
3. If match (b[1] = 1 in new context), complete transposition and go to position i+2

But this doesn't match my current implementation! In my implementation:
- From Usual i#e, I create Transposing (i+1)#(e+1)
- The offset stored is (i+1)-(e+1) = i-e (same as original)

Wait, that's wrong. Let me recompute:
- Original position: i#e, offset = i-e
- New position: (i+1)#(e+1), offset = (i+1)-(e+1) = i-e

So the offset doesn't change! That seems suspicious.

Let me look at the I^ε conversion formula from the thesis...

## I^ε Conversion (Thesis Definition 15)

From the thesis:
```
I^ε({i#e}) = {I+(i-1)#e}
```

So for position i#e, we store it as I+(i-1)#e. This means:
- stored_offset = i - 1
- But we've been using stored_offset = i - e...

Wait, that's for the ε (standard) variant. Let me check if transposition uses a different conversion...

Actually, looking at the implementation, I see that for I-type positions:
- We store offset = i - errors (not i - 1)
- So position i#e is stored with offset = i - e

But the thesis Definition 15 says I^ε({i#e}) = {I+(i-1)#e}, which suggests stored_offset = i-1 for the parameter-free (ε) variant.

I think there's confusion between the different notations. Let me look at the implementation of `new_i` to understand what offset represents...

## Conclusion

I need to deeply understand the position representation and bit vector indexing before I can fix the transposition logic. The issue is complex and involves:
1. Understanding the I^ε conversion formula
2. Understanding what offset represents in stored positions
3. Understanding the bit vector window and how indices map to word positions
4. Understanding what b[k] represents semantically for transposition

This requires consulting the thesis more carefully and possibly adding comprehensive debug logging to trace through a simple example.
