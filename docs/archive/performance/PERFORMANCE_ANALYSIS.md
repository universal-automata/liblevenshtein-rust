# Performance Analysis: Filtering & Prefix Matching

## Executive Summary

Flame graph analysis reveals that **`queue_children()` consumes 37.91% of total execution time**, making it the primary optimization target. Key bottlenecks identified:

1. Edge iteration from PathMap (10.99%)
2. SmallVec collection operations (8.81%)
3. Bit mask testing (4.91%)
4. Epsilon closure computation (2.72%)
5. Box allocations (1.93%)
6. Arc reference counting overhead (1.74%)

## Benchmark Results

### Prefix vs Exact Matching

| Query Length | Exact (µs) | Prefix (µs) | Overhead |
|-------------|-----------|-------------|----------|
| 3 chars | 14.0 | 41.1 | 2.9x |
| 5 chars | 17.4 | 51.9 | 3.0x |
| 7 chars | 15.1 | 50.1 | 3.3x |
| 10 chars | 15.3 | 48.9 | 3.2x |

**Analysis**: Prefix matching is ~3x slower than exact matching due to increased traversal (exploring longer paths).

### Edit Distance Impact

| Distance | Time (µs) |
|----------|-----------|
| 0 | 46.6 |
| 1 | 78.2 |
| 2 | 95.5 |
| 3 | 111.7 |

**Analysis**: Linear scaling with edit distance (expected). Each additional distance level adds ~16-18µs.

### Filtering Strategies

| Strategy | Time (µs) | Speedup |
|----------|-----------|---------|
| Post-filter | 79.0 | 1.0x (baseline) |
| Pre-filter (sub-trie) | 44.2 | 1.79x |

**Analysis**: Sub-trie construction provides 1.79x speedup for 33% filtering rate.

### Filter Complexity

| Filter Type | Time (µs) |
|------------|-----------|
| Simple (HashSet lookup) | 229.6 |
| Medium (string ops) | 131.6 |
| Complex (multiple conditions) | 226.2 |

**Analysis**: Counter-intuitive result - simple filter is slower! This is because:
- Simple filter returns MORE candidates (passes filter more often)
- More results = more work collecting/processing
- Medium filter is most selective (fewest results)

### Combined Operations

| Operation | Time (µs) |
|-----------|-----------|
| Prefix only | 124.8 |
| Prefix + filter | 218.4 |
| Prefix + distance + filter | 218.1 |
| Prefix + distance + multi-filter | 224.8 |

**Analysis**: Filtering adds ~75% overhead. Multiple filters add minimal incremental cost.

### Scalability

| Dictionary Size | Time (µs) | Throughput (Melem/s) |
|----------------|-----------|----------------------|
| 1,000 | 1.76 | 569 |
| 5,000 | 29.9 | 167 |
| 10,000 | 53.7 | 186 |
| 20,000 | 66.6 | 300 |

**Analysis**: Near-linear scaling up to 20K terms. Throughput improves at larger sizes (better amortization of fixed costs).

## Flame Graph Analysis

### Hotspot #1: `queue_children()` - 37.91%

**Function**: `OrderedQueryIterator::queue_children`

**Breakdown**:
- Edge iteration (PathMap zipper): 10.99%
- SmallVec collection: 8.81%
- Bit mask testing: 4.91%
- Transition computation: 3.61%
- Epsilon closure: 2.72%
- Box allocations: 1.93%
- Arc drops: 1.74%

**Root Cause**: This function is called for EVERY node visited during traversal. For a query with distance=1 on a 10K dictionary, this could be thousands of calls.

**Code Path**:
```
queue_children()
  ├─> node.edges()          // 10.99% - PathMap lock + zipper iteration
  │    └─> with_zipper()     // 10.25% - RwLock acquisition + zipper setup
  │         └─> SmallVec collect  // 8.81% - collecting edges
  │              └─> filter iteration  // 4.91% - bit mask tests
  ├─> transition_state_pooled()  // 3.61%
  │    └─> epsilon_closure_into()  // 2.72%
  ├─> Box::new()             // 1.93% - heap allocation
  └─> Arc drop               // 1.74% - reference counting
```

### Hotspot #2: PathMap Edge Iteration - 10.99%

**Function**: `<PathMapNode as DictionaryNode>::edges`

**Issues**:
1. RwLock acquisition on every node (atomic operations)
2. Zipper creation overhead
3. SmallVec collection from iterator
4. Bit mask testing for each potential edge (256 iterations max)

**Assembly observations**:
- `lock cmpxchg` instruction (0.07% just for atomic)
- Multiple function calls not inlined
- Allocation for SmallVec when edges > inline capacity

### Hotspot #3: SmallVec Operations - 8.81%

**Function**: SmallVec collection and push operations

**Issues**:
1. Collection from filtered iterator
2. Push operations (with capacity checks)
3. Spilling to heap when > inline capacity

**Current inline capacity**: Unknown (need to check source)

### Hotspot #4: Epsilon Closure - 2.72%

**Function**: `epsilon_closure_into`

**Issues**:
1. State copying
2. Position iteration and insertion
3. SmallVec push operations

**Note**: Already optimized with pooling, but still hot.

## Optimization Opportunities

### High Impact (>5% improvement potential)

#### 1. Edge Iteration Caching
**Current**: Every `queue_children` call acquires PathMap lock and creates zipper
**Proposed**: Cache edge results at node level (if PathMap supports it)
**Potential**: 10.99% → ~2-3% (7-8% improvement)
**Complexity**: Medium (requires PathMap changes or wrapper)

#### 2. Pre-allocate Intersection Vectors
**Current**: VecDeque grows dynamically for each distance bucket
**Proposed**: Pre-allocate based on typical traversal width
**Potential**: 1.93% → ~0.5% (1.4% improvement)
**Complexity**: Low

#### 3. Inline Hot Paths
**Current**: Many small functions not inlined (visible in assembly)
**Proposed**: Add `#[inline(always)]` to hot path functions
**Potential**: 2-3% improvement (reduced call overhead)
**Complexity**: Low

#### 4. Optimize SmallVec Capacity
**Current**: Unknown inline capacity
**Proposed**: Tune inline capacity based on actual edge counts
**Potential**: 2-3% improvement (fewer heap spills)
**Complexity**: Low

### Medium Impact (2-5% improvement potential)

#### 5. Reduce Arc Overhead
**Current**: PathMapNode uses Arc, causing ref count overhead
**Proposed**: Consider lifetime-based borrowing where possible
**Potential**: 1.74% improvement
**Complexity**: High (requires API changes)

#### 6. Batch Epsilon Closure
**Current**: Computed for each transition
**Proposed**: Batch compute for multiple transitions
**Potential**: 1-2% improvement
**Complexity**: Medium

### Low Impact (<2% improvement potential)

#### 7. Optimize Bit Mask Testing
**Current**: Filter iteration tests bits sequentially
**Proposed**: Use BMI2 instructions (pdep/pext) if available
**Potential**: 1-2% improvement
**Complexity**: Medium (needs CPU feature detection)

## Recommended Optimization Plan

### Phase 1: Low-Hanging Fruit (Quick Wins)
1. ✅ Add `#[inline(always)]` to hot functions
2. ✅ Pre-allocate intersection vectors with sensible capacity
3. ✅ Tune SmallVec inline capacities

**Expected**: 5-7% improvement, ~2 hours work

### Phase 2: Medium Effort
4. ✅ Optimize epsilon closure batching
5. ✅ Investigate edge iterator optimizations

**Expected**: 3-5% improvement, ~1 day work

### Phase 3: Long-Term
6. Consider PathMap API enhancements for caching
7. Explore alternative edge storage formats

**Expected**: 10-15% improvement, ~1 week work

## Testing Strategy

1. Run benchmarks before and after each optimization
2. Verify correctness with full test suite
3. Generate new flame graphs to verify hotspot reduction
4. Measure real-world impact on code completion scenario

## Conclusion

The prefix matching and filtering implementation is correct but has optimization opportunities:

- **Primary bottleneck**: `queue_children` function (37.91%)
- **Quick wins available**: Inlining, pre-allocation, capacity tuning
- **Long-term potential**: PathMap edge iteration optimization
- **Current performance**: Acceptable for <10K dictionaries, optimization recommended for >10K

**Priority**: Implement Phase 1 optimizations immediately for 5-7% improvement with minimal risk.
