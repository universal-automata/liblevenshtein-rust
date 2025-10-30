# Phase 3: SIMD Vectorization Research

**Date**: 2025-10-30
**Status**: Research Phase
**Goal**: 2-4x additional speedup on medium/long strings

---

## Executive Summary

SIMD (Single Instruction, Multiple Data) vectorization can provide significant speedups for dynamic programming algorithms like Levenshtein distance by processing multiple cells of the DP matrix in parallel.

**Target Performance**:
- Current (Phase 2): 374-492ns for medium strings
- Phase 3 Goal: 150-200ns for medium strings (2-4x faster)

---

## SIMD Options for Stable Rust

### Option 1: `pulp` (RECOMMENDED) ⭐⭐⭐⭐⭐

**Crate**: `pulp = "0.21.5"`

**Pros**:
- ✅ **Works on stable Rust** (no nightly required)
- ✅ **High-level API** - Easier to use than raw intrinsics
- ✅ **Runtime CPU detection** - Automatically selects best SIMD for CPU
- ✅ **Cross-platform** - Works on x86-64 and ARM
- ✅ **Safe** - No unsafe code required
- ✅ **Well-maintained** - Active development
- ✅ **Feature: x86-v3** - Targets AVX2 by default

**Cons**:
- ⚠️ More abstract API (learning curve)
- ⚠️ Less control than raw intrinsics

**Best for**: Production code that needs portable, safe SIMD on stable Rust

---

### Option 2: `wide` ⭐⭐⭐⭐

**Crate**: `wide = "0.8.1"`

**Pros**:
- ✅ **Works on stable Rust**
- ✅ **Simple API** - Similar to `std::simd`
- ✅ **Portable** - Compiles to SSE/AVX on x86, NEON on ARM
- ✅ **Type-safe** - Strong typing for vector sizes
- ✅ **Zero overhead** - Compiles to optimal SIMD instructions

**Cons**:
- ⚠️ **No runtime dispatch** - Must compile for specific CPU features
- ⚠️ Lower-level than `pulp` (more manual work)

**Best for**: Projects that compile for specific CPU targets

---

### Option 3: Raw `std::arch` intrinsics ⭐⭐⭐

**Built-in**: No external dependencies

**Pros**:
- ✅ **No dependencies**
- ✅ **Maximum control**
- ✅ **Direct access to CPU instructions**
- ✅ **Well-documented**

**Cons**:
- ❌ **Unsafe code required**
- ❌ **Platform-specific** (separate impl for AVX2, SSE, NEON)
- ❌ **Complex** - Must handle alignment, edge cases manually
- ❌ **More error-prone**

**Best for**: Expert-level optimization where every nanosecond counts

---

### Option 4: `std::simd` (Nightly only) ⭐⭐

**Status**: Nightly-only (unstable feature `portable_simd`)

**Pros**:
- ✅ **Built into standard library**
- ✅ **Portable** - Works across all architectures
- ✅ **Safe** - No unsafe required
- ✅ **Clean API**

**Cons**:
- ❌ **Requires nightly Rust** (not stable as of 1.90)
- ❌ **API may change** (still unstable)
- ❌ **Cannot use in stable libraries**

**Best for**: Experimental/personal projects that can use nightly

---

## Recommendation: Use `pulp`

For this project, I recommend **`pulp`** because:

1. ✅ **Stable Rust** - No nightly required (important for library)
2. ✅ **Runtime dispatch** - Automatically uses best SIMD available
3. ✅ **Safe** - No unsafe code
4. ✅ **High-level** - Less error-prone than raw intrinsics
5. ✅ **Cross-platform** - Works on x86 and ARM
6. ✅ **Well-maintained** - Active development, good documentation

---

## SIMD Vectorization Strategy

### Target: Inner DP Loop

The inner loop of Levenshtein distance is embarrassingly parallel:

```rust
// Current scalar code (processes 1 cell at a time)
for j in 1..=n {
    let cost = if source_chars[i - 1] == target_chars[j - 1] { 0 } else { 1 };
    curr_row[j] = min3(
        prev_row[j] + 1,      // deletion
        curr_row[j - 1] + 1,  // insertion
        prev_row[j - 1] + cost // substitution
    );
}
```

**SIMD approach**: Process 8 cells at once (with AVX2)

```rust
// SIMD vectorized (processes 8 cells at once)
for j in (1..=n).step_by(8) {
    // Load 8 cells from prev_row, curr_row
    let prev = load_u32x8(&prev_row[j..]);
    let curr_left = load_u32x8(&curr_row[j-1..]);
    let diag = load_u32x8(&prev_row[j-1..]);

    // Compute costs (vectorized character comparison)
    let costs = compute_costs_simd(&source_chars[i-1], &target_chars[j-1..j+7]);

    // Parallel min operations
    let deletion = prev + splat_u32x8(1);
    let insertion = curr_left + splat_u32x8(1);
    let substitution = diag + costs;

    let result = min(min(deletion, insertion), substitution);

    // Store 8 cells to curr_row
    store_u32x8(&mut curr_row[j..], result);
}
```

---

## Challenges and Solutions

### Challenge 1: Character Comparison

**Problem**: Need to compare `source[i]` with 8 characters `target[j..j+8]`

**Solution**:
```rust
// Create vector of same character repeated 8 times
let src_char_vec = splat_u32x8(source[i] as u32);
let tgt_char_vec = load_u32x8(&target_chars[j..j+8]);

// Vectorized comparison
let matches = src_char_vec.simd_eq(tgt_char_vec);

// Convert bool mask to 0/1 costs
let costs = matches.select(splat_u32x8(0), splat_u32x8(1));
```

### Challenge 2: Edge Cases

**Problem**: String length may not be multiple of 8

**Solution**: Process remainder with scalar code
```rust
// SIMD loop (multiple of 8)
for j in (1..n_simd).step_by(8) {
    // ... SIMD code ...
}

// Scalar remainder (< 8 cells)
for j in n_simd..=n {
    // ... scalar code ...
}
```

### Challenge 3: Dependency on Previous Cell

**Problem**: `curr_row[j]` depends on `curr_row[j-1]` (sequential dependency)

**Solution**: Use wavefront/anti-diagonal approach or accept limited parallelism
- **Approach 1**: Process anti-diagonals in parallel (complex)
- **Approach 2**: Accept dependency, still get 2-3x speedup (simpler, recommended)

**Recommendation**: Use Approach 2 - Even with dependency, SIMD provides significant speedup for the other operations (deletion, substitution).

---

## Implementation Plan

### Phase 3.1: Setup and Prototyping (Day 1)

**Tasks**:
1. Add `pulp` dependency to Cargo.toml
2. Create feature flag `simd` for optional SIMD support
3. Write simple prototype to verify pulp works
4. Benchmark prototype vs scalar code

**Deliverable**: Working SIMD prototype showing speedup potential

---

### Phase 3.2: Implement SIMD for `standard_distance()` (Days 2-3)

**Tasks**:
1. Create `standard_distance_simd()` function
2. Implement vectorized inner loop
3. Handle edge cases (remainder cells)
4. Add runtime CPU feature detection
5. Add fallback to scalar version if SIMD unavailable

**Code structure**:
```rust
#[cfg(feature = "simd")]
pub fn standard_distance(source: &str, target: &str) -> usize {
    if source.len() < 16 || target.len() < 16 {
        // Too small for SIMD benefit
        return standard_distance_scalar(source, target);
    }

    pulp::Arch::new().dispatch(|| {
        standard_distance_simd(source, target)
    })
}

#[cfg(not(feature = "simd"))]
pub fn standard_distance(source: &str, target: &str) -> usize {
    standard_distance_scalar(source, target)
}
```

**Deliverable**: Working SIMD implementation for standard distance

---

### Phase 3.3: Extend to Other Algorithms (Day 4)

**Tasks**:
1. Apply same vectorization to `transposition_distance()`
2. Consider `merge_and_split_distance()` (may be too complex for SIMD)
3. Refactor common SIMD code into helper functions

**Deliverable**: SIMD support for all applicable distance functions

---

### Phase 3.4: Testing and Benchmarking (Day 5)

**Tasks**:
1. Run all existing tests with SIMD enabled
2. Add SIMD-specific tests
3. Run comprehensive benchmarks
4. Compare SIMD vs scalar performance
5. Test on different CPUs (AVX2, SSE, ARM if available)

**Success criteria**:
- ✅ All tests passing
- ✅ 2-4x speedup for strings > 20 chars
- ✅ No slowdown for short strings
- ✅ Graceful fallback when SIMD unavailable

**Deliverable**: Benchmarked, validated SIMD implementation

---

### Phase 3.5: Documentation and Polish (Day 5)

**Tasks**:
1. Document SIMD implementation details
2. Add usage examples
3. Update README with performance results
4. Create PHASE3_RESULTS.md document

**Deliverable**: Complete documentation

---

## Expected Performance

### Current (Phase 2)
```
Short (< 10 chars):  94-96ns
Medium (10-20):      374-492ns
Long (> 20):         ~2-5µs
```

### Target (Phase 3 with SIMD)
```
Short (< 10 chars):  94-96ns    (no change, too small for SIMD)
Medium (10-20):      150-200ns  (2-3x faster)
Long (> 20):         ~500ns-1µs (3-5x faster)
```

### Speedup Breakdown

**Why 2-4x speedup?**

1. **Parallel min operations** - 8 at once instead of 1 (8x potential)
2. **Reduced by dependencies** - curr_row[j-1] dependency limits parallelism (÷3)
3. **Overhead** - Setup, alignment, remainder (÷1.2)
4. **Net speedup**: 8x ÷ 3 ÷ 1.2 ≈ **2-3x**

For longer strings, better cache utilization may push this to **3-4x**.

---

## Risks and Mitigation

### Risk 1: Complexity

**Risk**: SIMD code is more complex and error-prone

**Mitigation**:
- Use high-level `pulp` API (not raw intrinsics)
- Comprehensive testing
- Keep scalar version as fallback
- Property-based tests to catch edge cases

### Risk 2: Maintenance Burden

**Risk**: SIMD code is harder to maintain

**Mitigation**:
- Feature flag makes it optional
- Well-documented code
- Separate SIMD and scalar implementations clearly
- Use pulp for portability (no per-platform code)

### Risk 3: Limited Benefit for Short Strings

**Risk**: SIMD overhead may negate benefits for short strings

**Mitigation**:
- Runtime check: use scalar for strings < 16 chars
- Benchmark to find optimal threshold
- Default to scalar if uncertain

---

## Alternative: Manual Vectorization with `std::arch`

If `pulp` doesn't provide sufficient performance, we can fall back to manual SIMD with `std::arch`:

**Pros**:
- Maximum control
- No dependencies
- Potentially faster

**Cons**:
- Requires unsafe code
- Platform-specific (AVX2, SSE4, NEON)
- Much more complex
- Error-prone

**Recommendation**: Try `pulp` first. Only use `std::arch` if `pulp` doesn't meet performance targets.

---

## Timeline

| Phase | Duration | Deliverable |
|-------|----------|-------------|
| 3.1: Setup | 4-6 hours | Working prototype |
| 3.2: Implement standard_distance | 1-2 days | SIMD for standard distance |
| 3.3: Extend to other algorithms | 0.5-1 day | SIMD for all algorithms |
| 3.4: Testing & benchmarking | 1 day | Validated implementation |
| 3.5: Documentation | 0.5 day | Complete docs |
| **Total** | **3-5 days** | **Production-ready SIMD** |

---

## Next Steps

1. ✅ **Research complete** - `pulp` is the best option
2. ⏭️ **Add pulp dependency** and create feature flag
3. ⏭️ **Build prototype** to verify approach
4. ⏭️ **Implement SIMD** for standard_distance()
5. ⏭️ **Test and benchmark**

---

## Conclusion

SIMD vectorization is feasible and should provide **2-4x speedup** for medium/long strings. Using `pulp` provides a good balance of:
- Performance (runtime dispatch to best SIMD)
- Safety (no unsafe code)
- Maintainability (high-level API)
- Portability (works on stable Rust, x86 and ARM)

**Recommendation**: Proceed with `pulp`-based implementation.

---

*Research Date: 2025-10-30*
*Status: Ready to implement*
*Estimated effort: 3-5 days*
