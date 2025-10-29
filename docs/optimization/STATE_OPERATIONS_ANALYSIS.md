# State Operations Analysis

## Overview

This document analyzes the performance characteristics of state operations beyond the core `insert()` function (which was already optimized in the subsumption analysis).

## Implementation Location

**File**: `src/transducer/state.rs`

### Core Data Structure

```rust
pub struct State {
    positions: SmallVec<[Position; 8]>,
}
```

- Uses SmallVec for stack allocation of small states
- Positions maintained in sorted order
- Subsumption checked during insertion

---

## State Operations Inventory

### 1. Creation Operations

#### `State::new()` - lines 26-31
```rust
pub fn new() -> Self {
    Self {
        positions: SmallVec::new(),
    }
}
```
**Complexity**: O(1)
**Usage**: Initial state creation
**Performance**: Optimal - just allocates SmallVec

#### `State::single(position)` - lines 33-38
```rust
pub fn single(position: Position) -> Self {
    let mut positions = SmallVec::new();
    positions.push(position);
    Self { positions }
}
```
**Complexity**: O(1)
**Usage**: Create state with one position
**Performance**: Optimal - one allocation + one push

#### `State::from_positions(positions)` - lines 43-49
```rust
pub fn from_positions(mut positions: Vec<Position>) -> Self {
    positions.sort();
    positions.dedup();
    Self {
        positions: SmallVec::from_vec(positions),
    }
}
```
**Complexity**: O(n log n) for sort
**Usage**: Batch state creation
**Performance**: Standard sort/dedup, reasonable for batch ops

---

### 2. Mutation Operations

#### `State::insert()` - lines 82-99
**Status**: ✅ Already optimized (see SUBSUMPTION_OPTIMIZATION_REPORT.md)
**Performance**: O(kn) where k << n, 3.3x faster than alternatives

#### `State::merge()` - lines 102-106
```rust
pub fn merge(&mut self, other: &State, algorithm: Algorithm) {
    for position in &other.positions {
        self.insert(*position, algorithm);
    }
}
```
**Complexity**: O(m × kn) where m = positions in other state
**Usage**: Combine two states
**Performance**: Depends on insert() which is already optimal
**Potential Concern**: Multiple insert() calls could be batched

#### `State::clear()` - lines 147-149
```rust
pub fn clear(&mut self) {
    self.positions.clear();
}
```
**Complexity**: O(1)
**Usage**: StatePool reuse
**Performance**: Optimal - just resets length

#### `State::copy_from()` - lines 162-168
```rust
pub fn copy_from(&mut self, other: &State) {
    self.positions.clear();
    self.positions.reserve(other.positions.len());
    for pos in &other.positions {
        self.positions.push(*pos); // Copy, not clone
    }
}
```
**Complexity**: O(n)
**Usage**: StatePool reuse with copy
**Performance**: Good - uses reserve + copy
**Potential Optimization**: Could use slice copy instead of loop

---

### 3. Query Operations

#### `State::head()` - lines 109-111
```rust
pub fn head(&self) -> Option<&Position> {
    self.positions.first()
}
```
**Complexity**: O(1)
**Performance**: Optimal

#### `State::positions()` - lines 115-117
```rust
pub fn positions(&self) -> &[Position] {
    &self.positions
}
```
**Complexity**: O(1)
**Performance**: Optimal - just returns slice reference

#### `State::is_empty()` - lines 121-123
```rust
pub fn is_empty(&self) -> bool {
    self.positions.is_empty()
}
```
**Complexity**: O(1)
**Performance**: Optimal

#### `State::len()` - lines 127-129
```rust
pub fn len(&self) -> usize {
    self.positions.len()
}
```
**Complexity**: O(1)
**Performance**: Optimal

#### `State::iter()` - lines 132-134
```rust
pub fn iter(&self) -> impl Iterator<Item = &Position> {
    self.positions.iter()
}
```
**Complexity**: O(1) to create iterator
**Performance**: Optimal - zero-cost abstraction

---

### 4. Distance Computation Operations

#### `State::min_distance()` - lines 174-186
```rust
pub fn min_distance(&self) -> Option<usize> {
    self.positions.first().map(|first| {
        // Fast path: if we only have one position, return it immediately
        if self.positions.len() == 1 {
            return first.num_errors;
        }

        // Otherwise, find the minimum
        self.positions.iter().map(|p| p.num_errors).min().unwrap()
    })
}
```
**Complexity**:
- Best case (n=1): O(1)
- General case: O(n)

**Usage**: Find minimum error count in state
**Performance**: Good - has fast path for single position
**Potential Optimization**: Could cache min_errors if frequently called

#### `State::infer_distance()` - lines 193-210
```rust
pub fn infer_distance(&self, query_length: usize) -> Option<usize> {
    // Fast path: single position (common case)
    if self.positions.len() == 1 {
        let p = &self.positions[0];
        let remaining = query_length.saturating_sub(p.term_index);
        return Some(p.num_errors + remaining);
    }

    // General case: find minimum across all positions
    self.positions
        .iter()
        .map(|p| {
            let remaining = query_length.saturating_sub(p.term_index);
            p.num_errors + remaining
        })
        .min()
}
```
**Complexity**:
- Best case (n=1): O(1)
- General case: O(n)

**Usage**: Calculate final edit distance at end of dictionary term
**Performance**: Good - has fast path, uses iterator min()
**Optimization**: Well-designed with fast path

#### `State::infer_prefix_distance()` - lines 220-237
```rust
pub fn infer_prefix_distance(&self, query_length: usize) -> Option<usize> {
    // Fast path: single position
    if self.positions.len() == 1 {
        let p = &self.positions[0];
        return if p.term_index >= query_length {
            Some(p.num_errors)
        } else {
            None
        };
    }

    // General case: find minimum among positions that consumed the full query
    self.positions
        .iter()
        .filter(|p| p.term_index >= query_length)
        .map(|p| p.num_errors)
        .min()
}
```
**Complexity**:
- Best case (n=1): O(1)
- General case: O(n)

**Usage**: Calculate distance for prefix matching
**Performance**: Good - has fast path, uses filter + min()
**Optimization**: Well-designed

---

## Performance Characteristics Summary

### Optimal Operations (No optimization needed)

1. ✅ `new()` - O(1)
2. ✅ `single()` - O(1)
3. ✅ `insert()` - Already optimized (subsumption analysis)
4. ✅ `clear()` - O(1)
5. ✅ `head()` - O(1)
6. ✅ `positions()` - O(1)
7. ✅ `is_empty()` - O(1)
8. ✅ `len()` - O(1)
9. ✅ `iter()` - O(1) to create

### Good Operations (Fast paths implemented)

1. ✅ `min_distance()` - O(1) for n=1, O(n) otherwise
2. ✅ `infer_distance()` - O(1) for n=1, O(n) otherwise
3. ✅ `infer_prefix_distance()` - O(1) for n=1, O(n) otherwise

### Potentially Optimizable Operations

1. **`copy_from()`** - lines 162-168
   - Current: Loop with push() - O(n)
   - Optimization: Use slice copy - still O(n) but better constants
   - Expected improvement: ~10-20% faster
   - Worth it? Only if profiling shows this is hot

2. **`merge()`** - lines 102-106
   - Current: Multiple insert() calls
   - Optimization: Batch insert with one-time sort/dedup
   - Expected improvement: Reduces subsumption checks
   - Worth it? Only if merge() is frequently called

3. **`from_positions()`** - lines 43-49
   - Current: Sort + dedup + SmallVec conversion
   - Optimization: Could avoid intermediate Vec
   - Worth it? Rarely called, low priority

---

## Usage Pattern Analysis

### Typical State Lifecycle

```
1. Create initial state: State::single(Position::new(0, 0))
2. Transition states: transition_state() [already benchmarked at ~75ns]
3. Query distance: infer_distance() or infer_prefix_distance()
4. Cleanup: Drop (automatic)
```

### StatePool Pattern

```
1. Allocate state from pool
2. clear() existing state
3. copy_from() or manual population via insert()
4. Use state
5. Return to pool
```

The StatePool pattern is used in `transition_state_pooled()` for allocation reuse.

---

## Benchmark Plan

### Test Dimensions

1. **State sizes**: 1, 3, 5, 10, 20 positions
2. **Operations to benchmark**:
   - `min_distance()` - single vs multiple positions
   - `infer_distance()` - single vs multiple positions
   - `infer_prefix_distance()` - single vs multiple positions
   - `copy_from()` - measure memcpy overhead
   - `merge()` - measure vs hypothetical batch insert
3. **Comparison benchmarks**:
   - `copy_from()` loop vs slice copy
   - `merge()` multiple insert vs batch
   - `min_distance()` with cached vs computed

### Specific Benchmarks

1. **bench_state_queries()** - min_distance, infer_distance, infer_prefix_distance
2. **bench_state_copy()** - copy_from performance
3. **bench_state_merge()** - merge vs batch insert
4. **bench_distance_computation()** - various state sizes

---

## Expected Bottlenecks

Based on transition benchmark results (~75ns full state transition), the state operations are likely **not** bottlenecks because:

1. Most operations are O(1) or O(n) with small n (typically 2-5 positions)
2. Fast paths implemented for n=1 (common case)
3. The critical path (transition_state) is already ~75ns total

### Potential Hot Spots

If profiling a full dictionary query:

1. **infer_distance()** - Called for every accepted dictionary term
   - Frequency: High (once per match)
   - Cost: O(n), typically 2-5 positions
   - Expected: 5-20ns based on state size

2. **copy_from()** in StatePool - If used frequently
   - Frequency: Medium (depends on pool usage)
   - Cost: O(n), simple copy
   - Expected: 10-30ns for typical states

3. **merge()** - If used (not clear from codebase)
   - Frequency: Unknown, possibly low
   - Cost: O(m × kn)
   - Expected: Depends on usage pattern

---

## Optimization Priorities

### High Priority (If profiling shows hot)

1. **None identified yet** - Need profiling data

### Medium Priority (Potential micro-optimizations)

1. **copy_from() slice copy**
   - Replace loop with slice copy
   - Expected: ~10-20% improvement
   - Implementation: Simple, low risk

2. **Cached min_distance**
   - Store min_errors in State
   - Update on insert()
   - Expected: O(n) → O(1)
   - Trade-off: Adds 8 bytes to State, complicates insert()

### Low Priority (Unlikely to matter)

1. **Batch merge()**
2. **Optimized from_positions()**
3. **SIMD distance computation** (overkill for n<10)

---

## Predicted Conclusion

Based on the transition benchmark results showing ~75ns full state transitions, and given that:

1. State query operations are O(1) or O(n) with small n
2. Most operations have fast paths for n=1
3. The critical path is already very fast

**Prediction**: State operations are already well-optimized and are **not** bottlenecks.

The likely final conclusion will be:

> **"State operations are already efficient. The O(1) operations are optimal, and the O(n) operations have appropriate fast paths. No optimization is needed unless profiling identifies specific hot spots."**

---

## Next Steps

1. ✅ Analyze state operations (this document)
2. ⏳ Create benchmark suite for state operations
3. ⏳ Run benchmarks
4. ⏳ Analyze results
5. ⏳ Implement optimizations if justified
6. ⏳ Measure improvements

---

## References

- State implementation: `src/transducer/state.rs`
- Subsumption optimization: `SUBSUMPTION_OPTIMIZATION_REPORT.md`
- Transition optimization: `TRANSITION_OPTIMIZATION_REPORT.md`
- Position implementation: `src/transducer/position.rs`
