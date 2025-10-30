# Phase 3 SIMD Reassessment

**Date**: 2025-10-30
**Status**: Research Complete - Decision Required

---

## Executive Summary

After prototyping with `pulp` and researching SIMD Levenshtein implementations, I've discovered that achieving significant SIMD speedups (20-30x) requires more sophisticated techniques than initially anticipated. This document presents the findings and recommendations.

---

## Research Findings

### 1. Successful SIMD Implementation: triple_accel

**Library**: [triple_accel](https://github.com/Daniel-Liu-c0deb0t/triple_accel)
**Performance**: **20-30x speedup** over scalar implementations
**Techniques**:
- AVX2 (256-bit) and SSE4.1 (128-bit) implementations
- Runtime CPU detection with automatic fallback
- Optimized for integer operations (not floats)

### 2. SIMD Opportunities for Levenshtein Distance

Based on research from [Levenshtein Distance with SIMD](https://turnerj.com/blog/levenshtein-distance-with-simd), there are **three main areas** where SIMD helps:

#### a) **Prefix/Suffix Comparison** ✅ Already Optimized
- Compare 16-32 characters at once with AVX2
- **Status**: We already do this with `strip_common_affixes()`
- **Impact**: Major - eliminates unnecessary DP computation

#### b) **Row Initialization** 🟡 Potential Gain
- Fill DP row with initial values using SIMD
- Instead of: `for i in 0..n { row[i] = i; }`
- Use SIMD: Fill 8 usizes at once with AVX2
- **Impact**: Minor - only happens once per call
- **Complexity**: Low - straightforward vectorization

#### c) **Branchless Minimum** 🟡 Potential Gain
- Use SIMD min instructions instead of `a.min(b).min(c)`
- Eliminates branch prediction overhead
- **Impact**: Moderate - happens for every DP cell
- **Complexity**: Medium - requires proper SIMD types

#### d) **Anti-Diagonal Processing** 🔴 Complex
- Process anti-diagonals of DP matrix in parallel
- Eliminates dependencies between cells
- **Impact**: High - true parallelism (8x potential)
- **Complexity**: Very High - complete algorithm restructuring

---

## The pulp Problem

After prototyping, I discovered **pulp is not ideal** for our use case:

### Issues with pulp:
1. **Float-focused**: Most operations optimized for f32/f64
2. **Limited integer support**: Awkward API for u32/usize operations
3. **Abstraction overhead**: Less control than raw intrinsics
4. **Documentation gaps**: Integer SIMD operations poorly documented

### What pulp does well:
- ✅ Safe, stable Rust
- ✅ Runtime CPU detection
- ✅ Cross-platform (x86, ARM)
- ✅ Great for float-heavy workloads

### What we need:
- Integer vector operations (u32/usize)
- Min operations on integer vectors
- Load/store for integer arrays
- Compare-and-select for character matching

---

## Alternatives Reconsidered

### Option A: Raw `std::arch` Intrinsics ⭐⭐⭐⭐⭐

**What**: Use raw x86 SIMD intrinsics directly

**Example**:
```rust
#[cfg(target_arch = "x86_64")]
use std::arch::x86_64::*;

unsafe {
    let a = _mm256_loadu_si256(ptr as *const __m256i);
    let b = _mm256_loadu_si256(ptr2 as *const __m256i);
    let min_result = _mm256_min_epu32(a, b);
}
```

**Pros**:
- ✅ **Maximum performance** (what triple_accel uses)
- ✅ **Full control** over every instruction
- ✅ **No dependencies** (built-in to std)
- ✅ **Well-documented** (Intel intrinsics guide)
- ✅ **Proven approach** (triple_accel: 20-30x speedup)

**Cons**:
- ⚠️ **Requires unsafe code**
- ⚠️ **Platform-specific** (separate AVX2, SSE, ARM implementations)
- ⚠️ **Complex** (manual alignment, pointer arithmetic)
- ⚠️ **More error-prone**

**Recommendation**: **Best option for maximum performance**

---

### Option B: Use/Study triple_accel ⭐⭐⭐⭐

**What**: Learn from or integrate with triple_accel library

**Pros**:
- ✅ **Proven performance** (20-30x speedup)
- ✅ **Already implemented** Levenshtein + Damerau-Levenshtein
- ✅ **Runtime dispatch** with fallbacks
- ✅ **Open source** (MIT license) - can study implementation

**Cons**:
- ⚠️ **Dependency** on external crate
- ⚠️ **May not support merge-and-split** distance
- ⚠️ **Different API** than our current interface
- ⚠️ **Need to validate** against our requirements

**Recommendation**: **Study their implementation, possibly adopt patterns**

---

### Option C: Limited pulp Implementation ⭐⭐

**What**: Continue with pulp for simple optimizations only

**Realistically achievable**:
- Row initialization speedup (~1.1-1.2x)
- Cleaner runtime CPU detection

**Performance expectation**: **1.2-1.5x** (not the 2-4x initially hoped)

**Why so limited?**:
- pulp's integer SIMD support is minimal
- Can't efficiently do the DP inner loop
- Most gains already captured in Phase 2

**Recommendation**: **Not worth the complexity for limited gains**

---

### Option D: Ship Phase 2, Revisit SIMD Later ⭐⭐⭐⭐⭐

**What**: Ship current Phase 2 optimizations, tackle SIMD separately

**Benefits**:
- ✅ **Immediate value** (15-39% improvement from Phase 2)
- ✅ **Production-tested** (all tests passing)
- ✅ **Low risk** (safe Rust, backward compatible)
- ✅ **More time** to properly implement SIMD later

**Timeline if proceeding with SIMD later**:
- 1-2 days: Study triple_accel implementation
- 2-3 days: Implement AVX2 version with std::arch
- 1-2 days: Implement SSE4.1 fallback
- 1-2 days: Testing and validation
- **Total**: 5-9 days for proper SIMD implementation

**Recommendation**: **Best pragmatic choice**

---

## Decision Matrix

| Approach | Performance | Complexity | Time | Risk | Recommendation |
|----------|------------|------------|------|------|----------------|
| **A. std::arch intrinsics** | ⭐⭐⭐⭐⭐ (20-30x) | High | 5-9 days | Medium | ⭐⭐⭐⭐⭐ |
| **B. triple_accel patterns** | ⭐⭐⭐⭐⭐ (20-30x) | Medium | 3-5 days | Low | ⭐⭐⭐⭐ |
| **C. Limited pulp** | ⭐⭐ (1.2-1.5x) | Medium | 2-3 days | Medium | ⭐⭐ |
| **D. Ship Phase 2 now** | ⭐⭐⭐ (current) | Low | 0 days | Low | ⭐⭐⭐⭐⭐ |

---

## Technical Deep Dive: Why DP is Hard to Vectorize

### The Dependency Problem

```rust
// Standard DP recurrence
curr_row[j] = min3(
    prev_row[j] + 1,      // deletion
    curr_row[j-1] + 1,    // insertion ← depends on curr_row[j-1]!
    prev_row[j-1] + cost  // substitution
);
```

The **insertion cost depends on curr_row[j-1]**, which must be computed first. This creates a **sequential dependency** that prevents naive vectorization.

### Solution 1: Anti-Diagonal Processing (Complex)

Process cells along anti-diagonals, where all cells can be computed in parallel:

```
Matrix indices:
(0,0)
(0,1) (1,0)
(0,2) (1,1) (2,0)
(0,3) (1,2) (2,1) (3,0)
...
```

Cells on the same anti-diagonal have no dependencies and can be SIMD-parallelized.

**Challenge**: Complex indexing, memory access patterns, edge cases

**Used by**: triple_accel (likely)

### Solution 2: Banded Processing (Simpler)

Only vectorize operations that don't have dependencies:
- Deletion costs: `prev_row[j] + 1` ✅ Can vectorize
- Substitution costs: `prev_row[j-1] + cost` ✅ Can vectorize
- Insertion costs: `curr_row[j-1] + 1` ❌ Keep scalar

**Performance**: ~2-3x speedup (not 20-30x)

**Used by**: Simpler SIMD implementations

---

## Recommendations

### Immediate Recommendation: **Ship Phase 2 Now** (Option D)

**Rationale**:
1. Phase 2 provides **15-39% improvement** - significant and production-ready
2. SIMD for Levenshtein is **more complex than anticipated**
3. Proper SIMD needs **5-9 days** of focused work
4. Should use **std::arch intrinsics** (not pulp) for maximum performance
5. Can implement SIMD as **separate future effort**

**Action Items**:
1. ✅ Commit Phase 2 changes
2. ✅ Tag release: `v0.3.1-phase2-optimizations`
3. 📋 Create issue: "Phase 3: SIMD Optimization with std::arch"
4. 📋 Document: Link to triple_accel as reference implementation

---

### If Proceeding with SIMD: **Use std::arch + Study triple_accel**

**Approach**:
1. **Study** triple_accel source code for anti-diagonal approach
2. **Implement** AVX2 version with `std::arch::x86_64` intrinsics
3. **Add** SSE4.1 fallback for older CPUs
4. **Feature flag**: Make SIMD optional (`simd` feature)
5. **Benchmark** thoroughly on multiple CPUs

**Timeline**: 5-9 days
**Expected performance**: 10-30x speedup (depending on string length)

---

## Revised Phase 3 Plan (If Proceeding)

### Phase 3.1: Study and Design (1-2 days)
- Analyze triple_accel implementation
- Understand anti-diagonal approach
- Design data structures for SIMD
- Plan memory layout

### Phase 3.2: Implement AVX2 (2-3 days)
- Use `std::arch::x86_64` intrinsics
- Implement anti-diagonal DP with `__m256i`
- Handle edge cases and alignment
- Runtime CPU detection

### Phase 3.3: Implement SSE4.1 Fallback (1-2 days)
- 128-bit vectors for older CPUs
- Same algorithm, different vector width
- Test on systems without AVX2

### Phase 3.4: Testing and Validation (1-2 days)
- Property-based testing with proptest
- Benchmark on multiple CPUs
- Validate correctness
- Performance regression tests

### Phase 3.5: Documentation (0.5-1 day)
- Document SIMD implementation
- Add usage examples
- Update benchmarks
- Write PHASE3_RESULTS.md

**Total**: 5-9 days for production-ready SIMD

---

## Key Learnings

1. **pulp is great for floats, not ideal for integer DP algorithms**
2. **Levenshtein SIMD requires anti-diagonal processing for best performance**
3. **triple_accel proves 20-30x is achievable with proper implementation**
4. **std::arch intrinsics are the way to go for maximum performance**
5. **SIMD for DP is a substantial undertaking, not a quick optimization**

---

## Conclusion

**Recommendation**: **Ship Phase 2 now, implement SIMD later with std::arch**

Phase 2 delivered solid, production-ready improvements (15-39% faster). SIMD optimization is worthwhile but requires:
- More sophisticated techniques (anti-diagonal processing)
- Raw SIMD intrinsics (std::arch, not pulp)
- Significant development time (5-9 days)

**The pragmatic approach**: Deploy Phase 2 gains immediately, tackle SIMD as a dedicated future effort with proper planning and reference implementations.

---

## Next Steps

### If Shipping Phase 2 Now:
1. Remove pulp dependency (optional, or keep for future use)
2. Commit Phase 2 changes
3. Create GitHub issue for SIMD implementation
4. Document triple_accel as reference for future work

### If Proceeding with SIMD:
1. Study triple_accel implementation in detail
2. Start Phase 3.1: Design anti-diagonal approach
3. Budget 5-9 days for complete implementation
4. Use std::arch intrinsics, not pulp

---

*Research Date: 2025-10-30*
*Status: Awaiting Decision*
*Recommendation: Ship Phase 2, implement SIMD later*
