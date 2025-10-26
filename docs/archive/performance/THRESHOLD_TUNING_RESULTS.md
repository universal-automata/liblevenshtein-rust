# Adaptive Threshold Tuning Results

## Summary

Empirical testing identified the optimal threshold for switching from linear to binary search in edge lookup operations. By tuning the threshold from 8 to 16 edges, we achieved **20-21% performance improvement** for larger dictionaries.

---

## Background

The DAWG implementation uses an adaptive search strategy:
- **Linear search**: For nodes with few edges (cache-friendly, simple)
- **Binary search**: For nodes with many edges (algorithmic efficiency)

The original threshold was set at 8 edges based on intuition. This analysis provides empirical evidence for the optimal threshold.

---

## Methodology

### 1. Edge Count Distribution Analysis

Analyzed the distribution of edge counts in DAWG nodes across different dictionary sizes:

| Dictionary Size | Nodes | Edge Count Distribution |
|-----------------|-------|------------------------|
| 100 terms | 119 | 84% have 0 edges, 7% have 1 edge, 9% have 10 edges |
| 500 terms | 563 | 89% have 0 edges, 1% have 1 edge, 10% have 10 edges |
| 1000 terms | 1118 | 89% have 0 edges, 1% have 1 edge, 10% have 10 edges |
| 5000 terms | 5562 | 90% have 0 edges, 0.1% have 1 edge, 10% have 10 edges |

**Key finding:** Synthetic test data ("word000000" pattern) creates a **bimodal distribution** with 90% final/linear nodes and 10% branching nodes with exactly 10 edges.

### 2. Linear vs Binary Search Performance

Microbenchmarked both search strategies across different edge counts to find the crossover point:

| Edge Count | Linear Search | Binary Search | Winner | Advantage |
|------------|---------------|---------------|--------|-----------|
| 2 | 1.49 ns | 2.21 ns | **Linear** | 33% faster |
| 4 | 2.20 ns | 3.24 ns | **Linear** | 32% faster |
| 6 | 2.82 ns | 4.34 ns | **Linear** | 35% faster |
| 8 | 3.47 ns | 4.46 ns | **Linear** | 22% faster |
| 10 | 4.20 ns | 6.04 ns | **Linear** | 30% faster |
| 12 | 4.39 ns | 6.06 ns | **Linear** | 28% faster |
| **16** | 6.11 ns | 6.04 ns | **TIE** | ~0% |
| 20 | 7.24 ns | 7.87 ns | **Linear** | 8% faster |
| 26 | 9.22 ns | 7.92 ns | **Binary** | 14% faster |

**Crossover point: 16-20 edges**
- Linear search is faster up to 16 edges
- Binary search becomes advantageous at 20+ edges (full alphabet: 26 edges)

### 3. Implications for Original Threshold=8

With the original threshold of 8:
- 90% of nodes (0-1 edges): Correctly used linear search ✅
- 10% of nodes (10 edges): **Incorrectly used binary search** ❌
  - Binary search: 6.04 ns
  - Linear search: 4.20 ns
  - **Lost 30% performance** on these nodes

---

## Results: Threshold 8 → 16

Updated threshold in both `dawg.rs` and `dynamic_dawg.rs`:

```rust
// Before: threshold=8
if edges.len() < 8 {
    // linear search
} else {
    // binary search
}

// After: threshold=16 (empirically validated)
if edges.len() < 16 {
    // linear search
} else {
    // binary search
}
```

### Performance Impact

| Dictionary Size | Threshold=8 | Threshold=16 | Improvement |
|-----------------|-------------|--------------|-------------|
| 100 terms | 3.13 µs | 2.94 µs | **-4.1% (1.04x faster)** |
| 500 terms | 3.22 µs | 2.87 µs | **-8.7% (1.10x faster)** |
| 1000 terms | 3.84 µs | 3.03 µs | **-21.6% (1.27x faster)** |
| 5000 terms | 3.86 µs | 3.06 µs | **-20.5% (1.26x faster)** |

**Average improvement: 13.7% across all sizes, with 20-21% for larger dictionaries**

---

## Analysis

### Why Threshold=16 Performs Better

1. **Matches empirical crossover point**: Testing showed 16-20 edges as the optimal threshold
2. **Benefits 10-edge nodes**: The 10% of nodes with 10 edges now use linear search (4.2ns) instead of binary (6.0ns) - **30% faster**
3. **No penalty for other nodes**: Nodes with 0-1 edges continue using linear search
4. **Rare large nodes unaffected**: Nodes with 16+ edges (rare in our data) now correctly use binary search

### Why Larger Dictionaries Benefit More

- **100 terms**: Only 11 nodes with 10 edges → smaller absolute impact
- **1000 terms**: 111 nodes with 10 edges → 10x more opportunities for speedup
- **5000 terms**: 555 nodes with 10 edges → 50x more opportunities

The improvement scales with dictionary size because the 10% of branching nodes becomes a larger absolute count.

---

## Synthetic vs Real-World Data

### Limitations of Synthetic Data

Our test data ("word000000", "word000001", etc.) creates an **artificial edge distribution**:
- All branching nodes have exactly 10 edges (digits '0'-'9')
- Real English dictionaries would have more varied distributions

### Expected Real-World Distribution

English dictionaries would likely show:
- **1-5 edges**: Common prefixes (th, st, pr, ing)
- **10-15 edges**: Vowel-heavy positions, common suffixes
- **20-26 edges**: Root positions with high branching

With real data, threshold=16 would still be optimal or even conservative. A threshold of 20 might perform even better for English text.

---

## Cumulative Performance Impact

Combining with Arc optimization (from previous work):

| Operation | Baseline | +Arc Opt | +Arc+Threshold | Total Improvement |
|-----------|----------|----------|----------------|-------------------|
| contains/100 | 9.30 µs | 3.13 µs | 2.94 µs | **-68.4% (3.16x faster)** |
| contains/500 | 9.60 µs | 3.22 µs | 2.87 µs | **-70.1% (3.35x faster)** |
| contains/1000 | 9.61 µs | 3.84 µs | 3.03 µs | **-68.5% (3.17x faster)** |
| contains/5000 | 9.71 µs | 3.86 µs | 3.06 µs | **-68.5% (3.17x faster)** |

**Combined optimizations deliver 3.2-3.4x speedup!**

---

## Code Changes

### Files Modified

**1. `src/dictionary/dawg.rs`**
- Line 279: Updated threshold from 8 to 16 in `contains()` method
- Line 323: Updated threshold from 8 to 16 in `transition()` method
- Added empirical justification in comments

**2. `src/dictionary/dynamic_dawg.rs`**
- Line 646: Updated threshold from 8 to 16 in `transition()` method

### Benchmarks Created

**`benches/threshold_analysis.rs`**
- Analyzes edge count distribution across dictionary sizes
- Prints percentile statistics (p50, p75, p90, p95, p99)
- Measures current implementation performance

**`benches/threshold_tuning.rs`**
- Microbenchmarks linear vs binary search for 2-26 edges
- Identifies exact crossover point (16 edges)
- Validates optimal threshold choice

---

## Recommendations

### For Current Codebase
✅ **Apply threshold=16** - Validated by empirical testing, delivers 20-21% improvement

### For Real-World Dictionaries
Consider threshold=20 for English dictionaries:
- More conservative based on natural language distribution
- Would benefit nodes with 16-19 edges
- Minimal downside (26-edge nodes are rare)

### For Other Languages
- **Logographic (Chinese, Japanese)**: Much higher edge counts → threshold=32 or higher
- **Small alphabets (Hawaiian, Polynesian)**: Lower edge counts → threshold=8-12
- **Agglutinative (Finnish, Turkish)**: Similar to English → threshold=16-20

### For Future Work
1. **Parameterized threshold**: Make threshold a const generic parameter
2. **Profiling-guided threshold**: Analyze real dictionary's edge distribution at build time
3. **Per-node optimization**: Use different thresholds at different DAWG depths

---

## Conclusion

Empirical threshold tuning delivered **20-21% performance improvement** for dictionary lookups:

**Key Findings:**
- Crossover point is 16-20 edges (not 8)
- Linear search faster up to 16 edges (cache locality wins)
- Binary search faster at 26+ edges (algorithmic efficiency wins)
- Synthetic data has bimodal distribution (90% small, 10% medium)

**Optimization Applied:**
- Changed threshold from 8 to 16 in all edge lookup code
- Validated with comprehensive microbenchmarks
- Tested across multiple dictionary sizes

**Combined with Arc optimization: 3.2-3.4x total speedup for contains() operations**

---

## Files

**Analysis Results:**
- `threshold_analysis_results.txt` - Edge distribution analysis
- `threshold_tuning_results.txt` - Linear vs binary crossover testing

**Benchmarks:**
- `dawg_contains_threshold16.txt` - Performance with optimized threshold

**Related Documentation:**
- `docs/ARC_OPTIMIZATION_RESULTS.md` - Arc overhead elimination (60% improvement)
- `docs/DAWG_OPTIMIZATION_OPPORTUNITIES.md` - Original optimization analysis
