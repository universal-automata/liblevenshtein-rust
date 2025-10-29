# Subsumption Logic Analysis

## Overview

This document analyzes the subsumption logic used in the Levenshtein automaton implementation, comparing the Rust and C++ approaches and identifying optimization opportunities.

## Background

Subsumption is a critical optimization for Levenshtein automata. A position `p1` at `(i, e)` **subsumes** position `p2` at `(j, f)` if all candidates reachable from `p2` are also reachable from `p1`. This allows us to prune redundant positions from states, reducing the state space and improving performance.

## Algorithm-Specific Subsumption Formulas

###  1. Standard Algorithm
`p1` subsumes `p2` if:
- `e ≤ f` (fewer or equal errors)
- `|i - j| ≤ (f - e)` (index difference bounded by error difference)

### 2. Transposition Algorithm
More complex due to special positions tracking transposition states:
- If both `p1` and `p2` are special: `i == j`
- If `p1` special, `p2` not: `i == j`
- If `p2` special (not `p1`): `adjusted_diff ≤ (f - e)` where:
  - `adjusted_diff = (j < i) ? (i - j - 1) : (j - i + 1)`
- Neither special: standard formula `|i - j| ≤ (f - e)`

### 3. MergeAndSplit Algorithm
- If `p1` special but not `p2`: cannot subsume (return false)
- Otherwise: standard formula `|i - j| ≤ (f - e)`

## Implementation Comparison

### C++ Approach: Batch Unsubsumption

**Process:**
1. Merge all positions from transitions into `next_state` without checking subsumption
2. Call `unsubsume(next_state, query_length)` to remove redundant positions
3. Sort the state

**Unsubsume Implementation (unsubsume.cpp:10-38):**
```cpp
void UnsubsumeFn::operator()(State *state, std::size_t query_length) {
  StateIterator outer_iter = state->begin();
  StateIterator iter_end = state->end();
  while (outer_iter != iter_end) {
    Position *outer = *outer_iter;
    std::size_t outer_errors = outer->num_errors();

    // Skip positions with more errors (optimization)
    StateIterator inner_iter(state, outer, &outer_iter);
    ++inner_iter;
    while (inner_iter != iter_end) {
      Position *inner = *inner_iter;
      if (outer_errors < inner->num_errors()) {
        break;
      }
      ++inner_iter;
    }

    // Remove subsumed positions
    while (inner_iter != iter_end) {
      Position *inner = *inner_iter;
      if (subsumes(outer, inner, query_length)) {
        inner_iter.remove();
      }
      ++inner_iter;
    }

    ++outer_iter;
  }
}
```

**Complexity:** O(n²) where n is the number of positions in the state

### Rust Approach: Online Subsumption

**Process (state.rs:54-71):**
```rust
pub fn insert(&mut self, position: Position, algorithm: Algorithm) {
    // Check if this position is subsumed by an existing one
    for existing in &self.positions {
        if existing.subsumes(&position, algorithm) {
            return; // Early exit - O(n) in best case
        }
    }

    // Remove any positions that this new position subsumes
    self.positions.retain(|p| !position.subsumes(p, algorithm)); // O(n)

    // Insert in sorted position
    let insert_pos = self
        .positions
        .binary_search(&position)
        .unwrap_or_else(|pos| pos);  // O(log n)
    self.positions.insert(insert_pos, position);  // O(n)
}
```

**Complexity:** O(n) per insertion for typical cases, O(kn) total for k insertions

## Theoretical Analysis

### C++ Batch Approach

**Advantages:**
- Simple to implement
- Works with any position insertion strategy
- Clear separation of concerns

**Disadvantages:**
- Always O(n²) regardless of subsumption patterns
- Stores all positions temporarily before filtering
- Requires extra memory for positions that will be discarded
- Must sort after unsubsumption

**Best Case:** O(n²) - when no positions subsume each other
**Worst Case:** O(n²) - when all positions subsume each other
**Average Case:** O(n²)

### Rust Online Approach

**Advantages:**
- Early termination when position is subsumed (common case)
- Never stores positions that will be discarded
- Maintains sorted order incrementally
- Memory efficient - only keeps necessary positions

**Disadvantages:**
- Repeated subsumption checks during insertions
- O(n) cost per insertion in worst case

**Best Case:** O(k) - when all positions are subsumed (early exit)
**Worst Case:** O(kn) - when no positions subsume each other
**Average Case:** O(kn) where k < n typically due to subsumption

## Practical Considerations

### State Sizes in Practice

From profiling data (pool.rs tests):
- Most states have 2-5 positions
- States with ≤8 positions are the common case (hence SmallVec optimization)
- Maximum observed state size: ~10-15 positions for max_distance ≤ 3

**Implication:** For small n (typical case), the difference between O(n²) and O(kn) is minimal. However, the constant factors and early termination matter more.

### Subsumption Patterns

**Common patterns observed:**
1. **High subsumption**: Position `(0, 0)` in initial state subsumes many positions with higher errors
2. **Moderate subsumption**: Positions at lower error levels often subsume positions at higher error levels
3. **Low subsumption**: When max_distance is high and query_length is long, fewer positions subsume each other

**Rust advantage:** Early exit optimization in `insert()` is particularly effective for high subsumption scenarios.

## Benchmarking Strategy

### Test Cases

1. **Varying Position Counts:** 10, 50, 100, 200 positions
2. **Varying Max Distance:** 0, 2, 5, 10, 50, 100, usize::MAX/2
3. **All Three Algorithms:** Standard, Transposition, MergeAndSplit
4. **Best/Worst Cases:**
   - Best: All positions subsumed by first
   - Worst: No positions subsume each other
   - Average: Random positions with typical subsumption patterns

### Metrics to Measure

1. **Time per insertion**
2. **Total time for state construction**
3. **Memory usage**
4. **Cache efficiency**
5. **Algorithm-specific differences**

## Optimization Opportunities

### Potential Optimizations for Rust

1. **Early Termination in retain():**
   - Currently `retain()` checks all positions
   - Could break early if we know no more positions can be subsumed

2. **Sorted Insertion with Subsumption:**
   - Leverage sorted order to skip impossible subsumptions
   - Positions with lower errors come first
   - Can skip checking positions with much higher errors

3. **Batch Hints:**
   - When inserting many positions (e.g., from epsilon closure), could use hybrid approach
   - Collect small batches and process together

4. **SIMD Subsumption Checks:**
   - For large states, could use SIMD to check multiple subsumptions in parallel
   - Most beneficial for Standard algorithm (simple comparison)

5. **Position Metadata:**
   - Cache min/max error bounds in state for faster filtering
   - Skip subsumption checks when bounds don't overlap

### Potential Optimizations for C++ Approach

1. **Sort Before Unsubsume:**
   - Sort positions by (num_errors, term_index) first
   - Enables early breaks in inner loop

2. **Incremental Unsubsumption:**
   - Unsubsume during merge instead of after
   - Similar to Rust approach

## Next Steps

1. ✅ Run comprehensive benchmarks
2. ⏳ Generate flame graphs for both approaches
3. ⏳ Analyze results
4. ⏳ Implement optimizations for winner
5. ⏳ Verify correctness with property tests
