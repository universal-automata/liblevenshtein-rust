# Fuzzy Map Baseline Performance Analysis

## Executive Summary

**Date**: 2025-10-29
**Status**: ⚠️ **PERFORMANCE REGRESSION DETECTED**

The addition of fuzzy map support (generic `PathMapDictionary<V>`) has introduced **3-13% performance regressions** in query operations across multiple benchmarks. This is likely due to:

1. Additional trait bounds and monomorphization overhead
2. Potential changes to memory layout from generic parameters
3. Indirect performance impact from type parameter propagation

## Baseline Benchmarks Completed

### ✅ `benchmarks.rs` - Core Operations
**Result**: Compiled and ran successfully

Key findings:
- Query operations: ~300-500μs for distance 2, dictionary size 500-1000
- Distance computation: 99ns-1.5μs depending on string lengths
- Dictionary operations: 157-236ns per operation
- No obvious regression (no prior baseline to compare)

### ✅ `query_iterator_benchmarks.rs` - Query Performance
**Result**: **PERFORMANCE REGRESSION DETECTED**

Critical regressions:
| Benchmark | Regression | Impact |
|-----------|-----------|--------|
| `ordered_vs_unordered/ordered/1` | +10.6% | 51.4μs (was 46.4μs) |
| `ordered_vs_unordered/ordered/2` | +6.96% | 242μs (was 226μs) |
| `ordered_query_dict_size_scaling/1000` | +13.7% | 249μs (was 219μs) |
| `ordered_query_dict_size_scaling/5000` | +10.3% | 478μs (was 434μs) |
| `ordered_query_algorithms/standard` | +7.14% | 147μs (was 137μs) |
| `large_distance_queries/50` | +51.5% | 9.65μs (was 6.37μs) |

Pattern: **Ordered queries and larger dictionaries show the worst degradation**

### ✅ `backend_comparison.rs` - Compilation Fixed
**Result**: Compilation successful (not benchmarked yet)

## Type Inference Issues Fixed

Adding the generic type parameter `V: DictionaryValue = ()` broke type inference in 9 benchmark locations:

### Files Fixed:
1. `benches/benchmarks.rs` - 3 instances (lines 60, 113, 226)
2. `benches/backend_comparison.rs` - 6 instances (lines 75, 146, 225, 304, 382, 459)

### Pattern Applied:
```rust
// Before (broken):
let dict = PathMapDictionary::from_terms(vec![...]);

// After (fixed):
let dict: PathMapDictionary<()> = PathMapDictionary::from_terms(vec![...]);
```

## Performance Regression Analysis

### Hypothesis 1: Monomorphization Overhead
The generic parameter `V` forces Rust to generate separate code for each value type:
- `PathMapDictionary<()>` (unit type - no values)
- `PathMapDictionary<u32>` (scope IDs)
- `PathMapDictionary<Vec<String>>` (metadata lists)

**Impact**: Increased binary size, potential instruction cache misses

### Hypothesis 2: Memory Layout Changes
The `PathMap<V>` structure now includes value storage:
```rust
pub struct PathMap<V: DictionaryValue = ()> {
    root: Arc<PathMapNode<V>>,  // Changed from PathMapNode
    term_count: Arc<AtomicUsize>,
}
```

**Impact**: Different alignment, padding, cache line utilization

### Hypothesis 3: Trait Bound Overhead
All node operations now require `V: DictionaryValue` bounds:
```rust
impl<V: DictionaryValue> PathMapNode<V> {
    // Trait dispatch may add indirection
}
```

**Impact**: Virtual dispatch overhead, reduced inlining opportunities

## Recommended Actions

### Phase 1 Continuation (Current)
1. ✅ Fix remaining benchmark compilation errors
2. ⏳ Run `backend_comparison.rs` to establish full baseline
3. ⏳ Document all regression measurements
4. ⏳ Investigate root cause of regression

### Phase 1.5 (NEW): Regression Investigation & Mitigation
**CRITICAL - Must address before proceeding to Phase 2**

1. **Profile PathMapDictionary<()> operations** using perf/flamegraph
   - Compare against pre-generic version (git checkout previous commit)
   - Identify hotspots introduced by generics

2. **Optimize value access paths**
   - Consider `#[inline(always)]` for value-related methods
   - Investigate zero-cost abstraction violations

3. **Benchmark monomorphization impact**
   - Compare binary sizes
   - Measure instruction cache effects

4. **Potential Optimizations**:
   - Use `MaybeUninit<V>` for unit type to eliminate storage
   - Add `#[repr(C)]` or `#[repr(align(...))]` for consistent layout
   - Implement specialized fast paths for `PathMapDictionary<()>`

### Phase 2 onwards (BLOCKED until regression resolved)
Cannot proceed with fuzzy map benchmarking until baseline performance is acceptable.

## Test Configuration

### Environment
- Platform: Linux 6.17.3-arch2-1
- CPU: target-cpu=native optimizations enabled
- Rust: cargo bench (release profile with debuginfo)
- Criterion: 100 samples per benchmark

### Benchmark Parameters
- Dictionary sizes: 100, 500, 1000, 5000 terms
- Edit distances: 0-10, 99
- Query lengths: 1-21 characters
- Algorithms: Standard, Transposition, MergeAndSplit

## Next Steps

1. **Immediate**: Complete Phase 1.5 regression investigation
2. **Short-term**: Implement performance optimizations
3. **Validation**: Re-run baselines to confirm no regression
4. **Proceed**: Only then move to Phase 2 (fuzzy map benchmarks)

## References

- Baseline files:
  - `baseline_benchmarks.txt` - Core operations
  - `query_iterator_baseline.txt` - Query performance (with regressions)

- Source files modified:
  - `benches/benchmarks.rs` (type annotations)
  - `benches/backend_comparison.rs` (type annotations)
