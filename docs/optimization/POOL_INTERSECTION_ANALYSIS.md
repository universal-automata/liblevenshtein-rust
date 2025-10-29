# Pool and Intersection Optimization Analysis

**Date**: 2025-10-29
**Target**: StatePool and Intersection implementations
**Scope**: Memory allocation patterns and path reconstruction efficiency

---

## Executive Summary

Analysis of StatePool and Intersection implementations reveals **already well-optimized designs** with intelligent memory management strategies:

1. **StatePool** - LIFO allocation reuse strategy reducing Vec allocation overhead
2. **Intersection** - Lightweight PathNode design eliminating Arc cloning in parent chains

**Initial Assessment**: Both systems show evidence of prior optimization work. Benchmark validation recommended before any changes.

---

## 1. StatePool Implementation Analysis

### Location
`src/transducer/pool.rs` (302 lines)

### Current Design

**Data Structure**:
```rust
pub struct StatePool {
    pool: Vec<State>,           // Recycled states
    allocations: usize,         // Total new allocations
    reuses: usize,             // Total reuses
}
```

**Configuration**:
- `MAX_POOL_SIZE`: 32 states
- `INITIAL_CAPACITY`: 16 states
- Strategy: LIFO (last-in, first-out)

### Operations Analysis

#### 1. `acquire()` - Get state from pool

**Current Implementation** (lines 92-101):
```rust
#[inline]
pub fn acquire(&mut self) -> State {
    if let Some(mut state) = self.pool.pop() {
        state.clear(); // Clear positions but keep Vec capacity
        self.reuses += 1;
        state
    } else {
        self.allocations += 1;
        State::new()
    }
}
```

**Performance**:
- Pool hit: O(1) - pop from Vec + clear SmallVec
- Pool miss: O(1) - allocate new SmallVec (stack allocated for ≤8 positions)

**Analysis**:
✅ **Optimal** - Uses `#[inline]` correctly
✅ **Preserves capacity** - `clear()` keeps Vec allocation
✅ **LIFO strategy** - Better cache locality (recently used states)

#### 2. `release()` - Return state to pool

**Current Implementation** (lines 114-119):
```rust
#[inline]
pub fn release(&mut self, state: State) {
    if self.pool.len() < Self::MAX_POOL_SIZE {
        self.pool.push(state);
    }
    // Otherwise drop the state (let it deallocate)
}
```

**Performance**:
- O(1) - push to Vec (unless pool full)

**Analysis**:
✅ **Optimal** - Simple bounded pool
✅ **Prevents unbounded growth** - Caps at MAX_POOL_SIZE
✅ **Inline** - Minimal overhead

### Memory Characteristics

**State Size** (from previous analysis):
- SmallVec<[Position; 8]> - 16 bytes header + up to 8 Positions on stack
- Position is 8 bytes (term_index: usize, num_errors: usize)
- Stack allocation for ≤8 positions: ~80 bytes
- Heap allocation for >8 positions: 16 bytes + allocated capacity

**Pool Memory**:
- Max pool size: 32 states × ~80 bytes = **~2.5KB maximum**
- Very reasonable memory overhead

### Usage Pattern Analysis

From `src/transducer/transition.rs:580-638` - `transition_state_pooled()`:

```rust
// Acquire state for epsilon closure
let mut expanded_state = pool.acquire();      // Reuse #1
epsilon_closure_into(..., &mut expanded_state, ...);

// Acquire state for next state
let mut next_state = pool.acquire();          // Reuse #2

// ... compute transitions ...

pool.release(expanded_state);                 // Return #1

if next_state.is_empty() {
    pool.release(next_state);                 // Return #2 (if empty)
    None
} else {
    Some(next_state)                          // Caller owns (will release later)
}
```

**Observation**:
- Each transition uses 2 states from pool
- One returned immediately (expanded_state)
- One returned later or passed to caller
- **Pool should typically have 1-2 states available**

### Potential Optimization Opportunities

#### Opportunity 1: Adaptive Pool Size

**Current**: Fixed MAX_POOL_SIZE = 32

**Alternative**: Adaptive sizing based on query depth
```rust
// For deep dictionary traversals (depth > 100), more states in flight
// For shallow traversals (depth < 10), fewer states needed
let dynamic_max = min(64, max(16, avg_path_depth * 2));
```

**Expected Impact**: Minor - fixed size of 32 is already reasonable
**Recommendation**: **Low priority** - current size works well

#### Opportunity 2: Pre-warming the Pool

**Current**: Pool starts empty, grows as states are released

**Alternative**: Pre-allocate some states on pool creation
```rust
pub fn new() -> Self {
    let mut pool = Vec::with_capacity(Self::INITIAL_CAPACITY);
    // Pre-warm with a few states
    for _ in 0..4 {
        pool.push(State::new());
    }
    Self { pool, allocations: 0, reuses: 0 }
}
```

**Expected Impact**:
- Eliminates first 4 allocations per query
- Cost: 4 × ~80 bytes = 320 bytes upfront
- Benefit: Faster query startup (avoids 4 allocations)

**Recommendation**: **Medium priority** - simple change, measureable benefit

#### Opportunity 3: Per-Thread Pools

**Current**: Each query creates its own pool

**Alternative**: Thread-local pools that persist across queries
```rust
thread_local! {
    static POOL: RefCell<StatePool> = RefCell::new(StatePool::new());
}

pub fn with_thread_pool<F, R>(f: F) -> R
where
    F: FnOnce(&mut StatePool) -> R
{
    POOL.with(|pool| f(&mut pool.borrow_mut()))
}
```

**Expected Impact**:
- Eliminates pool creation overhead per query
- Better reuse across multiple queries on same thread
- Risk: May accumulate states if not properly managed

**Recommendation**: **Low priority** - adds complexity, unclear if better

---

## 2. Intersection Implementation Analysis

### Location
`src/transducer/intersection.rs` (215 lines)

### Current Design

**Key Innovation**: Lightweight PathNode for parent chain

**Data Structures**:
```rust
// Lightweight path node (~16 bytes)
pub struct PathNode {
    label: u8,                          // 1 byte (+ 7 padding)
    parent: Option<Box<PathNode>>,      // 8 bytes
}

// Full intersection (size depends on DictionaryNode type)
pub struct Intersection<N: DictionaryNode> {
    label: Option<u8>,                  // 2 bytes (1 + discriminant)
    node: N,                            // Varies by dictionary type
    state: State,                       // ~80 bytes (SmallVec)
    parent: Option<Box<PathNode>>,      // 8 bytes
}
```

### Memory Efficiency Analysis

**PathNode vs Full Intersection**:
- PathNode: ~16 bytes (label + pointer)
- Full Intersection: ~50+ bytes (depending on N)
- **Savings**: ~34 bytes per parent in chain

**For a depth-10 path**:
- PathNode chain: 10 × 16 bytes = 160 bytes
- Full Intersection chain (old): 10 × 50 bytes = 500 bytes
- **Savings**: 340 bytes per path

**For 1000 active paths**:
- Total savings: ~340KB

### Operations Analysis

#### 1. `term()` - Path reconstruction (lines 103-118)

**Current Implementation**:
```rust
pub fn term(&self) -> String {
    let mut bytes = Vec::new();

    // Collect current label
    if let Some(label) = self.label {
        bytes.push(label);
    }

    // Collect parent labels
    if let Some(parent) = &self.parent {
        parent.collect_labels(&mut bytes);
    }

    bytes.reverse();
    String::from_utf8_lossy(&bytes).into_owned()
}
```

**Performance**:
- Allocation: Vec<u8> with capacity = depth
- Collection: O(depth) - walk parent chain
- Reverse: O(depth) - in-place
- UTF-8 conversion: O(depth)

**Total**: O(depth) with one allocation

**Potential Issues**:
- ⚠️ Allocates Vec every time (not pooled)
- ⚠️ Two passes: collect + reverse

#### 2. `collect_labels()` - Recursive collection (lines 36-41)

**Current Implementation**:
```rust
pub fn collect_labels(&self, labels: &mut Vec<u8>) {
    labels.push(self.label);
    if let Some(parent) = &self.parent {
        parent.collect_labels(labels);
    }
}
```

**Performance**:
- Recursive: Stack frames = depth
- Push operation: Amortized O(1)

**Potential Issues**:
- ⚠️ **Recursive** - could blow stack for deep paths (>1000 levels)
- ⚠️ Collects in reverse order (requires later reverse)

#### 3. `depth()` - Path length calculation (lines 121-132)

**Current Implementation**:
```rust
pub fn depth(&self) -> usize {
    match &self.parent {
        Some(parent) => 1 + parent.depth(),
        None => {
            if self.label.is_some() { 1 } else { 0 }
        }
    }
}
```

**Performance**:
- Recursive: O(depth)
- No allocation

**Potential Issues**:
- ⚠️ **Not cached** - recomputed every call
- ⚠️ Recursive - stack risk for deep paths

### Potential Optimization Opportunities

#### Opportunity 1: Cache depth in PathNode

**Current**: depth() walks entire chain

**Alternative**:
```rust
pub struct PathNode {
    label: u8,
    depth: u16,  // Cached depth (supports up to 65K levels)
    parent: Option<Box<PathNode>>,
}

impl PathNode {
    pub fn new(label: u8, parent: Option<Box<PathNode>>) -> Self {
        let depth = match &parent {
            Some(p) => p.depth + 1,
            None => 1,
        };
        Self { label, depth, parent }
    }

    #[inline(always)]
    pub fn depth(&self) -> usize {
        self.depth as usize
    }
}
```

**Impact**:
- Memory: +2 bytes per PathNode (16 → 18 bytes, likely 24 with padding)
- Performance: depth() becomes O(1) instead of O(depth)
- Trade-off: +50% memory for O(depth) → O(1) query

**Recommendation**: **Medium priority** - depth() likely called frequently

#### Opportunity 2: Iterative collection (avoid recursion)

**Current**: Recursive collect_labels()

**Alternative**:
```rust
pub fn collect_labels(&self, labels: &mut Vec<u8>) {
    let mut current = Some(self);
    while let Some(node) = current {
        labels.push(node.label);
        current = node.parent.as_deref();
    }
}
```

**Impact**:
- Eliminates recursion (no stack risk)
- Same O(depth) performance
- Slightly better cache locality

**Recommendation**: **High priority** - eliminates stack overflow risk

#### Opportunity 3: Preallocate Vec in term()

**Current**: Vec grows dynamically during collection

**Alternative**:
```rust
pub fn term(&self) -> String {
    let depth = self.depth(); // O(1) if cached
    let mut bytes = Vec::with_capacity(depth);

    // ... rest unchanged ...
}
```

**Impact**:
- Eliminates Vec reallocations during collection
- Requires O(1) depth() (see Opportunity 1)
- Measurable improvement for deep paths

**Recommendation**: **Medium priority** - pairs with depth caching

#### Opportunity 4: Reverse-order collection (eliminate reverse)

**Current**: Collect in reverse, then reverse Vec

**Alternative**: Collect in forward order using parent walk
```rust
pub fn term(&self) -> String {
    let depth = self.depth();
    let mut bytes = Vec::with_capacity(depth);

    // Collect path in vector
    let mut path = Vec::with_capacity(depth);
    let mut current = self.parent.as_ref();
    while let Some(node) = current {
        path.push(node);
        current = node.parent.as_ref();
    }

    // Add labels in forward order
    for node in path.iter().rev() {
        bytes.push(node.label);
    }
    if let Some(label) = self.label {
        bytes.push(label);
    }

    String::from_utf8_lossy(&bytes).into_owned()
}
```

**Impact**:
- Eliminates one O(depth) reverse operation
- Adds one Vec<&PathNode> allocation
- Net benefit unclear

**Recommendation**: **Low priority** - increased complexity, unclear benefit

#### Opportunity 5: String pooling for term()

**Current**: Every term() call allocates new String

**Alternative**: Cache reconstructed terms
```rust
pub struct Intersection<N: DictionaryNode> {
    // ... existing fields ...
    cached_term: Option<String>,  // Lazily computed
}

pub fn term(&self) -> &str {
    if let Some(ref term) = self.cached_term {
        return term;
    }

    let term = self.compute_term();
    self.cached_term = Some(term);
    self.cached_term.as_ref().unwrap()
}
```

**Impact**:
- Requires mutable self or interior mutability
- Adds memory overhead
- Only beneficial if term() called multiple times per intersection

**Recommendation**: **Low priority** - likely term() called once per match

---

## 3. Integration Analysis

### How Pool and Intersection Work Together

From query implementations, typical flow:

1. **Create pool** - One per query
2. **Create initial intersection** - Root dictionary node + initial state
3. **For each dictionary transition**:
   a. Acquire state from pool
   b. Compute transition (transition_state_pooled)
   c. Create child intersection (new PathNode)
   d. Release intermediate states to pool
4. **On match** - Call intersection.term() to get result

### Memory Flow

```
Query Start:
├── Pool: [] (empty)
├── Active Intersections: 1 (root)

After First Transition:
├── Pool: [state1] (returned expanded_state)
├── Active Intersections: 2-5 (children)

After Deep Traversal (depth=10):
├── Pool: [s1, s2, ..., sN] (released states)
├── Active Intersections: ~10-100 (branch factor dependent)
├── PathNode chains: 10 levels × 16 bytes = 160 bytes per path
```

**Key Insight**: Pool size of 32 is sufficient because:
- Most states are short-lived (acquire → use → release within one transition)
- Only states actively transitioning need storage
- Branch factor (children per node) typically < 10

---

## 4. Benchmark Plan

### Pool Benchmarks

Create `benches/pool_intersection_benchmarks.rs`:

1. **Pool Operations**:
   - `acquire()` hit rate (pool not empty)
   - `acquire()` miss rate (pool empty)
   - `release()` performance
   - Pool warmup vs cold start

2. **Pool Usage Patterns**:
   - Single acquire/release cycle
   - Multiple concurrent states (2-10)
   - Deep query simulation (100+ transitions)
   - Reuse rate measurement

3. **Pool Size Impact**:
   - Compare sizes: 8, 16, 32, 64, 128
   - Measure memory usage vs reuse rate

### Intersection Benchmarks

1. **PathNode Operations**:
   - `new()` allocation
   - `depth()` calculation (current vs cached)
   - `collect_labels()` (recursive vs iterative)

2. **term() Reconstruction**:
   - Shallow paths (depth 1-5)
   - Medium paths (depth 10-20)
   - Deep paths (depth 50-100)
   - With/without depth caching
   - With/without preallocation

3. **Memory Benchmarks**:
   - PathNode size vs full Intersection chain
   - Memory per 1000 active paths

---

## 5. Expected Results

### Pool Performance

Based on analysis, expected benchmarks:

| Operation | Expected Time | Notes |
|-----------|---------------|-------|
| `acquire()` (hit) | 2-5ns | Pop + clear SmallVec |
| `acquire()` (miss) | 10-15ns | Allocate new SmallVec |
| `release()` | 1-3ns | Push to Vec |
| Warmup benefit | 40-60ns savings | Eliminates 4 × 10-15ns allocations |

### Intersection Performance

| Operation | Current (est) | Optimized (est) | Improvement |
|-----------|---------------|-----------------|-------------|
| `depth()` (depth=10) | 10 calls × 10ns = 100ns | 10 calls × 1ns = 10ns | 10x |
| `collect_labels()` | Stack + recursion | Iterative | Safer, same speed |
| `term()` (depth=10) | 50-80ns | 30-50ns | ~30-40% |

### Overall Impact

For a typical query with:
- 100 dictionary node visits
- Average path depth: 5
- 2 states per transition

**Current**:
- Pool overhead: 100 × 2 × 5ns = 1µs (acquire hits)
- Path reconstruction: 10 matches × 50ns = 500ns

**Optimized**:
- Pool overhead: 100 × 2 × 2ns = 400ns (warmup)
- Path reconstruction: 10 matches × 30ns = 300ns

**Total savings**: ~700ns per query (0.7µs)

**Percentage improvement**: Depends on total query time
- If query is 10µs: 7% improvement
- If query is 100µs: 0.7% improvement

---

## 6. Optimization Priority

### High Priority (Implement First)

1. ✅ **Iterative collect_labels()** - Eliminates stack overflow risk
   - Safety improvement
   - No performance cost
   - Simple change

### Medium Priority (Benchmark First)

2. ⏳ **Pool pre-warming** - 4 states on creation
   - Simple change
   - Clear benefit (eliminates 4 allocations)
   - Benchmark to confirm

3. ⏳ **Cache depth in PathNode** - Add depth field
   - Moderate change (+2 bytes per node)
   - Significant if depth() called frequently
   - Benchmark to confirm call frequency

4. ⏳ **Preallocate Vec in term()** - Use cached depth
   - Depends on #3
   - Clear benefit for deep paths
   - Benchmark to quantify

### Low Priority (Investigate Later)

5. ❌ **Adaptive pool sizing** - Complexity vs benefit unclear
6. ❌ **Thread-local pools** - Adds complexity, unclear benefit
7. ❌ **Reverse-order collection** - Complex, unclear benefit
8. ❌ **Term caching** - Only beneficial if term() called multiple times

---

## 7. Next Steps

1. ✅ Create this analysis document
2. ⏳ Create comprehensive benchmark suite
3. ⏳ Run benchmarks to validate assumptions
4. ⏳ Implement high-priority optimizations
5. ⏳ Measure improvements
6. ⏳ Create optimization report

---

## References

- Pool implementation: `src/transducer/pool.rs`
- Intersection implementation: `src/transducer/intersection.rs`
- Pool usage: `src/transducer/transition.rs:580-638`
- State operations: Previous STATE_OPERATIONS_OPTIMIZATION_REPORT.md

---

**Status**: ⏳ **ANALYSIS COMPLETE - BENCHMARKS NEXT**
