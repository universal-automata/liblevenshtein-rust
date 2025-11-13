# Hypothesis H4: Understanding Bit Vector Semantics

**Date**: 2025-11-13
**Status**: In progress

## Key Insight

The lazy automaton uses **offset-adjusted** bit vectors where `cv[0]` always corresponds to current word position `i`, but the Universal automaton uses **absolute indexing** relative to the subword window.

## Bit Vector Structure in Universal Automaton

For input at position `i` (1-indexed), the bit vector β(x_i, s_n(w, i)) is computed over:

```
s_n(w, i) = w_{i-n} w_{i-n+1} ... w_v  where v = min(|w|, i+n+1)
```

With padding: `w_{-n+1} = ... = w_0 = $`

### Example: "ab" → "ba" with n=1

**Input position i=1, character 'b'**:
- Subword: s_1(w, 1) = w_{0} w_{1} w_{2} = [a, b, EOW]
- But with padding: s_1(w, 1) = w_{-1+1} w_0 w_1 w_2 = [$, a, b]
- Bit vector: β('b', [$, a, b]) = [0, 0, 1]

**Checking from position I+0#0 (offset=0, word_pos=0+1=0...wait**

Actually, let me reconsider the indexing. Looking at line 35:
```
s_n(w, i) = w_{i-n} w_{i-n+1} ... w_v where v = min(|w|, i + n + 1)
```

For i=1, n=1:
- Start: i-n = 1-1 = 0
- End: min(|w|, i+n+1) = min(2, 1+1+1) = min(2, 3) = 2
- So: s_1(w, 1) = w_0 w_1 w_2, but |w|=2, so w_2 doesn't exist
- With 0-indexing: w_0='a', w_1='b'
- But i-n=0 might be negative with larger n, that's why we need padding

Let me look at the actual `relevant_subword` implementation:

## relevant_subword Function (bit_vector.rs:328-355)

```rust
fn relevant_subword(word: &str, position: usize, max_distance: u8) -> String {
    let n = max_distance as i32;
    let p = word.len() as i32;
    let i = position as i32;  // 1-indexed!

    // Start index: i - n (can be negative, hence need padding)
    let start = i - n;
    // End index: min(p, i + n + 1)
    let end = p.min(i + n + 1);
```

So for i=1 (first input char), n=1, word="ab" (p=2):
- start = 1 - 1 = 0
- end = min(2, 1 + 1 + 1) = min(2, 3) = 2
- If start < 0: add (0-start) padding chars
- Extract word[max(0,start)..end]

For our case: start=0, so NO padding needed!
- Subword = word[0..2] = "ab"
- β('b', "ab") = [0, 1]

**This is the answer!** The bit vector for input[0]='b' is [0, 1]:
- bit[0] = ('b' == 'a') = 0
- bit[1] = ('b' == 'b') = 1

## Position I+offset#errors at Input Position k

When position I+offset#errors processes input at position k (0-indexed):
- Word position: i = k + offset (relative to actual word)
- But the bit vector corresponds to input position k+1 (1-indexed in subword calculation!)

Wait, this is confusing. Let me trace through the actual accepts() function to see how input positions map to bit vectors.

## Next Steps

1. Check how the Universal automaton's `accepts()` function iterates through input
2. Verify the mapping between input position k and bit vector index
3. Document the correct relationship between position offset and bit vector indices
4. Fix the transposition logic based on correct understanding

## Hypothesis

The issue might be that we're 1-indexed in theory but 0-indexed in implementation, causing off-by-one errors in bit vector lookups.
