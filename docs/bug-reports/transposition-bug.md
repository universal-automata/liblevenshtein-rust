# Transposition Bug Analysis

## Summary

**Bug**: Query "ab" fails to find dictionary term "ba" at distance 1 using the Transposition algorithm.

**Root Cause**: Position (1,1,false) incorrectly subsumes position (0,1,true) during state construction, preventing the transposition path from being explored.

## Detailed Analysis

### The Expected Behavior

For query "ab" and dictionary "ba" with transposition algorithm:
1. Distance should be 1 (single transposition: swap 'a' and 'b')
2. The automaton should find "ba" as a match

### The Actual Behavior

The automaton returns no matches.

### Root Cause Investigation

#### Step 1: Initial State Transitions

Starting from root with query "ab":
- Initial state: (0,0,false)
- Process dictionary edge 'b'
- Characteristic vector for 'b' vs "ab" at offset 0: [false, true]
  - 'b' doesn't match query[0]='a'
  - 'b' matches query[1]='b'
  - Match found at index 1!

#### Step 2: Position Generation

When match is at index 1 (lines 226-231 in transition.rs), we generate:
1. (0,1,false) - insertion
2. **(0,1,true) - special transposition start** ← KEY POSITION
3. (1,1,false) - substitution
4. (2,1,false) - transposition complete

#### Step 3: State Construction with Subsumption

Positions are inserted into the state via `State::insert()`:

```
Insert (0,1,false):
  State: [(0,1,false)]

Insert (0,1,true):
  State: [(0,1,false), (0,1,true)]  ← Both coexist ✓

Insert (1,1,false):
  State: [(0,1,false), (1,1,false)]  ← (0,1,true) DISAPPEARED! ❌
```

**BUG LOCATION**: When inserting (1,1,false), it removes (0,1,true) via the subsumption check at line 91 of state.rs:

```rust
self.positions.retain(|p| !position.subsumes(p, algorithm, query_length));
```

This means (1,1,false) subsumes (0,1,true)!

#### Step 4: Subsumption Analysis

Testing: Does (1,1,false) subsume (0,1,true)?

Inputs:
- lhs (self): i=1, e=1, s=false
- rhs (other): j=0, f=1, t=true
- algorithm: Transposition
- query_length: 2

Subsumption logic (position.rs lines 116-124):

```rust
if t {  // rhs is special
    let adjusted_diff = if j < i {
        i.saturating_sub(j).saturating_sub(1)  // 1 - 0 - 1 = 0
    } else {
        j.saturating_sub(i) + 1
    };
    return adjusted_diff <= (f - e);  // 0 <= (1 - 1) = 0 <= 0 → TRUE ✓
}
```

**Result**: Returns `true` - (1,1,false) subsumes (0,1,true)

### Why This Is Wrong

The special position (0,1,true) represents a **transposition-in-progress** state. It's fundamentally different from a normal position at (1,1,false):

- **(0,1,true)**: "We've seen query[0]='a', dict has 'b', this could be the START of a transposition"
- **(1,1,false)**: "We've matched/substituted one character normally"

These represent DIFFERENT computational paths in the automaton. The special position needs to:
1. Wait for the next dictionary character
2. Check if it matches query[0] (completing the transposition)

If we remove (0,1,true), we lose the ability to explore the transposition path!

### Comparison with Java Implementation

Java code (SubsumesFunction.java lines 74-93):

```java
if (t) {
    return (j < i ? i - j - 1 : j - i + 1) <= (f - e);
}
```

The Rust implementation is IDENTICAL to Java. So either:
1. The Java implementation has the same bug, OR
2. There's additional context/logic we're missing

### C++ Implementation Note

The C++ code (subsumes.cpp line 24) has a typo:

```cpp
bool t = lhs->is_special();  // BUG: should be rhs->is_special()
```

This is clearly wrong - it checks lhs twice instead of checking rhs. This bug would prevent the problematic subsumption from occurring, potentially masking the issue!

## Hypothesis

The transposition subsumption formula may be mathematically correct for general cases, but it fails to account for the semantic difference between:
- A normal position that has consumed k characters with e errors
- A special position representing a transposition-in-progress state

**Proposed Fix**: Special positions should NEVER be subsumed by normal positions when using the Transposition algorithm, regardless of the distance formula. They represent fundamentally different states.

## Test Case

```rust
use liblevenshtein::prelude::*;

let dict = DoubleArrayTrie::from_terms(vec!["ba".to_string()]);
let transducer = Transducer::new(dict, Algorithm::Transposition);
let results: Vec<_> = transducer.query("ab", 1).collect();

// Expected: ["ba"]
// Actual: []
assert_eq!(results, vec!["ba"]);  // FAILS
```

## Next Steps

1. Review Java implementation behavior with this specific test case
2. Determine if Java has the same bug or if there's additional logic
3. Implement fix: Prevent normal positions from subsuming special positions
4. Add regression test for "ab" -> "ba" case
5. Re-run full test suite to ensure no regressions

## Potential Fix

In `position.rs`, modify the transposition subsumption logic:

```rust
Algorithm::Transposition => {
    // ... existing s checks ...

    if t {
        // CRITICAL: Special positions (transposition-in-progress) represent
        // fundamentally different computational paths than normal positions.
        // A normal position should NEVER subsume a special position, as this
        // would prematurely terminate exploration of valid transposition paths.
        //
        // Example: Query "ab", dict "ba"
        //   (1,1,false) should NOT subsume (0,1,true)
        //   The special position is needed to complete the transposition!
        if !s {
            return false;  // Normal position cannot subsume special position
        }

        // rhs is special: adjusted formula (only applies when lhs is also special)
        let adjusted_diff = if j < i {
            i.saturating_sub(j).saturating_sub(1)
        } else {
            j.saturating_sub(i) + 1
        };
        return adjusted_diff <= (f - e);
    }

    // Neither special: standard formula
    let index_diff = i.abs_diff(j);
    let error_diff = f - e;
    index_diff <= error_diff
}
```

This ensures that special transposition positions can only be subsumed by other special positions, preserving the transposition exploration path.
