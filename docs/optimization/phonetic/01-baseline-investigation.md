# Phase 1: Baseline Investigation

**Date**: 2025-11-18 23:20
**System**: Intel Xeon E5-2699 v3 @ 2.30GHz (taskset -c 0)
**Compiler**: RUSTFLAGS="-C target-cpu=native", bench profile

## Objective

Establish precise baseline measurements and formulate testable hypotheses for the observed performance degradation in large inputs.

## Baseline Measurements

### Throughput by Input Size

| Input Size (phones) | Total Time (ns) | Std Dev | Time per Phone (ns) | Ratio vs Baseline |
|---------------------|-----------------|---------|---------------------|-------------------|
| 5 | 1,132 | ±40 | 226 | 1.00× (baseline) |
| 10 | 2,677 | ±98 | 268 | 1.19× |
| 20 | 8,425 | ±309 | 421 | 1.86× |
| 50 | 42,997 | ±1,673 | **860** | **3.80×** ⚠️ |

### Performance Degradation Analysis

**Expected Behavior**: O(n) linear scaling → ~226 ns/phone across all sizes
**Actual Behavior**: Superlinear degradation as input size increases

**Degradation Curve**:
```
5 phones:  226 ns/phone (baseline)
10 phones: 268 ns/phone (+19%)
20 phones: 421 ns/phone (+86%)
50 phones: 860 ns/phone (+280%) ⚠️
```

**Critical Finding**: Performance degrades by **280%** at 50 phones compared to 5-phone baseline.

**Scaling Characteristic**:
- If truly O(n), 50-phone should take ~11,300 ns (50 × 226 ns)
- Actual: 42,997 ns (~3.8× expected)
- Indicates O(n²) or worse behavior, OR significant constant overhead

## Hypothesis Formation

### H1: Vec Reallocation Overhead (HIGH PRIORITY)

**Theory**: Frequent Vec reallocations during `apply_rule_at()` and `apply_rules_seq()`

**Evidence**:
- `apply_rule_at()` creates new Vec for every rule application
- No pre-allocation with capacity hints
- Multiple pattern sizes (1-2 phones) → unpredictable result sizes

**Code Location**: `src/phonetic/application.rs:177-187`
```rust
let mut result = Vec::with_capacity(s.len() + MAX_EXPANSION_FACTOR);
result.extend_from_slice(&s[..pos]);
result.extend_from_slice(&rule.replacement);
result.extend_from_slice(&s[(pos + rule.pattern.len())..]);
```

**Expected Impact**: O(n) allocations × reallocation cost → O(n²) behavior

**Testable Prediction**:
- Profiling should show significant time in `Vec::reserve()` or `alloc::realloc()`
- Memory allocator overhead should dominate for large inputs

---

### H2: Quadratic Pattern Matching (MEDIUM PRIORITY)

**Theory**: Nested loops in pattern matching lead to O(n²) behavior

**Evidence**:
- `apply_rules_seq()` iterates through all rules for each application
- `find_first_match()` scans entire string for each rule
- Pattern matching at every position

**Code Location**: `src/phonetic/application.rs:203-227`
```rust
loop {
    for rule in rules {  // O(r) rules
        if let Some(pos) = find_first_match(rule, &current) {  // O(n) scan
            // Apply rule
        }
    }
}
```

**Expected Impact**: For each application, O(r × n) work → total O(f × r × n) where f = applications

**Testable Prediction**:
- Profiling should show significant time in `find_first_match()` or `pattern_matches_at()`
- Time should scale with both input length AND fuel

---

### H3: Cache Inefficiency (LOW PRIORITY)

**Theory**: Large phonetic vectors exceed cache size, causing cache misses

**Evidence**:
- Phone enum: likely 2-4 bytes each
- 50 phones: 100-200 bytes (well within L1 cache)
- Unlikely to be primary cause

**Expected Impact**: Minimal for sizes tested (50 phones << L1 cache size)

**Testable Prediction**:
- `perf stat` should show low cache miss rate for 50-phone case
- Cache miss rate should not increase significantly vs 5-phone case

---

### H4: Slice Copying Overhead (MEDIUM PRIORITY)

**Theory**: Frequent slice copying in `apply_rule_at()` creates overhead

**Evidence**:
- Three slice copies per rule application:
  - `&s[..pos]` (prefix)
  - `&rule.replacement` (replacement)
  - `&s[(pos + rule.pattern.len())..]` (suffix)
- Copies scale with input size

**Expected Impact**: O(n) copying per application → total O(f × n)

**Testable Prediction**:
- Profiling should show significant time in `extend_from_slice()`
- Time proportional to number of bytes copied

---

## Hypotheses Priority Ranking

**Based on Likelihood and Expected Impact**:

1. **H1 (Vec Reallocation)**: HIGHEST PRIORITY
   - Most likely cause of superlinear degradation
   - Easy to test and optimize
   - Expected improvement: 2-4× speedup

2. **H2 (Quadratic Pattern Matching)**: HIGH PRIORITY
   - Complex interaction between rules, fuel, and input length
   - Could explain 3.8× degradation
   - Expected improvement: 2-3× speedup

3. **H4 (Slice Copying)**: MEDIUM PRIORITY
   - Linear overhead but significant for large inputs
   - Harder to optimize (fundamental to algorithm)
   - Expected improvement: 1.5-2× speedup

4. **H3 (Cache Inefficiency)**: LOW PRIORITY
   - Unlikely given input sizes tested
   - Test last if other hypotheses don't explain degradation

---

## Next Steps

### Immediate Actions (Phase 2):

1. **Code Analysis**: Examine source code for H1 and H2
   - Count allocations in `apply_rules_seq()` and `apply_rule_at()`
   - Trace execution flow for 50-phone input

2. **Targeted Profiling** (only when ready to analyze immediately):
   - Generate flamegraph for 50-phone case
   - Look for allocation hot spots (H1)
   - Look for pattern matching loops (H2)

3. **Perf Stat Analysis**:
   - Run `perf stat` to check cache miss rates (H3)
   - Measure instructions per cycle (IPC)
   - Check branch misprediction rate

### Validation Approach:

**For each hypothesis**:
1. Gather supporting data (profiling, code analysis)
2. Implement targeted optimization
3. Measure impact with isolated benchmark
4. Accept or reject hypothesis based on data

---

## Baseline Summary

**Confirmed Issue**: 3.80× performance degradation at 50 phones vs expected linear scaling

**Leading Hypotheses**:
- H1: Vec reallocation overhead (highest priority)
- H2: Quadratic pattern matching (high priority)

**Expected Root Cause**: Combination of H1 and H2

**Target Improvement**: Reduce 50-phone time from 42,997 ns to ~11,300 ns (3.8× speedup)

**Next Phase**: Code analysis and targeted profiling to validate H1 and H2

---

**Baseline Established**: ✅
**Hypotheses Formulated**: ✅
**Ready for Phase 2**: ✅
