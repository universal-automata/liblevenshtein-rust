# Distance Functions: Optimization Roadmap

**Date**: 2025-10-30
**Status**: ✅ Phase 2 Complete - 15-39% Improvement Achieved
**Current Performance**: 94ns (short), 374-492ns (medium)

---

## Executive Summary

Based on comprehensive benchmarking, profiling, and research, this document outlines the optimization strategy for Levenshtein distance functions. Priority is given to high-impact, low-effort improvements.

---

## Phase 2: Quick Wins (Estimated: 1-2 days, 10-20% speedup)

### 1. Use FxHash for Cache Keys ⭐⭐⭐⭐⭐

**Current**: Default hasher (SipHash for security)
**Proposed**: FxHash (faster for small keys)

**Rationale**:
- SipHash: ~20-30ns per hash (DoS-resistant but slow)
- FxHash: ~5-10ns per hash (non-cryptographic, fast)
- Cache keys are trusted internal data (no DoS risk)

**Implementation**:
```rust
use std::hash::BuildHasherDefault;
use rustc_hash::FxHasher;

type FastHashMap<K, V> = HashMap<K, V, BuildHasherDefault<FxHasher>>;
```

**Expected gain**: 10-15ns per cached operation (~10-15% for recursive)

**Files to modify**:
- `src/distance/mod.rs`: Change `HashMap` to use `FxHasher`
- `Cargo.toml`: Add `rustc-hash = "1.1"` dependency

---

### 2. Inline Hot Path Functions ⭐⭐⭐⭐

**Current**: Compiler decides inlining
**Proposed**: Force inline for small, hot functions

**Targets**:
```rust
#[inline(always)]
fn substring_from(s: &str, char_offset: usize) -> &str { ... }

#[inline(always)]
fn SymmetricPair::new(a: &str, b: &str) -> Self { ... }
```

**Rationale**:
- These functions are called in every recursive step
- Very small (< 10 instructions)
- Inlining eliminates call overhead (~2-3ns each)

**Expected gain**: 5-10ns per operation (~5-10%)

**Files to modify**:
- `src/distance/mod.rs`: Add `#[inline(always)]` annotations

---

### 3. Use SmallVec for Character Buffers ⭐⭐⭐⭐

**Current**: `Vec<char>` allocation for each string
**Proposed**: `SmallVec<[char; 32]>` (stack allocation for small strings)

**Rationale**:
- Most strings are < 32 chars (fits on stack)
- Avoids heap allocation (~20-30ns overhead)
- Zero cost for short strings, small overhead for long strings

**Implementation**:
```rust
use smallvec::SmallVec;

// Instead of:
let source_chars: Vec<char> = source.chars().collect();

// Use:
let source_chars: SmallVec<[char; 32]> = source.chars().collect();
```

**Expected gain**: 20-30ns for short strings (~20-30%)

**Note**: `smallvec` is already a dependency!

**Files to modify**:
- `src/distance/mod.rs`: Replace `Vec<char>` with `SmallVec<[char; 32]>`

---

### 4. Enable Common Suffix Elimination ⭐⭐⭐

**Current**: Code exists but commented out
**Proposed**: Integrate `strip_common_affixes()` into recursive functions

**Rationale**:
- Already implemented (no new code needed)
- Significant speedup for strings with common suffixes
- Low risk (already tested in C++ version)

**Expected gain**: 10-50% for strings with common suffixes (variable)

**Files to modify**:
- `src/distance/mod.rs`: Uncomment and integrate suffix stripping

---

## Phase 3: SIMD Vectorization (Estimated: 3-5 days, 2-4x speedup for medium/long strings)

### Overview

**Target**: Inner loop of DP matrix computation
**Approach**: Compute 4-16 cells in parallel using SIMD instructions

### Implementation Strategy

#### Step 1: Research and Prototype (1 day)

**Options**:
1. **`std::simd`** (Rust standard library, nightly)
   - Portable across platforms
   - Requires nightly compiler
   - Clean API

2. **`packed_simd2`** (crate, stable)
   - Works on stable Rust
   - Similar API to `std::simd`
   - Well-maintained

3. **Raw intrinsics** (`std::arch`)
   - Maximum control
   - Platform-specific (AVX2, SSE, NEON)
   - Complex, error-prone

**Recommendation**: Start with `packed_simd2` (stable + portable)

#### Step 2: Vectorize Inner Loop (2-3 days)

**Current scalar code**:
```rust
for j in 1..=n {
    let cost = if source_chars[i - 1] == target_chars[j - 1] { 0 } else { 1 };
    curr_row[j] = (prev_row[j] + 1)              // deletion
        .min(curr_row[j - 1] + 1)                // insertion
        .min(prev_row[j - 1] + cost);            // substitution
}
```

**Vectorized code** (process 8 cells at once with AVX2):
```rust
use packed_simd::u32x8;

// Process 8 cells in parallel
for j in (1..=n).step_by(8) {
    let prev = u32x8::from_slice_unaligned(&prev_row[j..j+8]);
    let curr = u32x8::from_slice_unaligned(&curr_row[j-1..j+7]);
    let diag = u32x8::from_slice_unaligned(&prev_row[j-1..j+7]);

    let cost_vec = /* compute match/mismatch cost vector */;

    // Parallel min operations
    let result = (prev + 1).min(curr + 1).min(diag + cost_vec);

    result.write_to_slice_unaligned(&mut curr_row[j..j+8]);
}
```

**Challenges**:
- Character comparison vectorization
- Edge case handling (string ends)
- Alignment and padding

**Expected speedup**: 2-4x for strings > 20 chars

#### Step 3: Benchmark and Validate (1 day)

- Run comprehensive benchmarks
- Verify correctness with property tests
- Compare SIMD vs scalar performance
- Add feature flag for SIMD (optional opt-in)

**Feature flag approach**:
```toml
[features]
simd = ["packed_simd2"]
```

---

## Phase 4: Cache Optimization (Estimated: 2-3 days, improves memory usage)

### 1. Implement LRU Eviction ⭐⭐⭐⭐

**Problem**: Unbounded cache growth
**Solution**: Least Recently Used (LRU) eviction policy

**Implementation options**:

1. **`lru` crate** (simple, battle-tested)
```rust
use lru::LruCache;

pub struct MemoCache {
    cache: RwLock<LruCache<SymmetricPair, usize>>,
}
```

2. **Custom LRU** (more control)
- `HashMap` + doubly-linked list
- More complex but more flexible

**Recommendation**: Use `lru` crate

**Expected benefit**: Bounded memory usage, no performance regression

---

### 2. Add Cache Statistics ⭐⭐⭐

**Goal**: Monitor cache effectiveness

**Metrics to track**:
- Hit rate (cache hits / total queries)
- Miss rate
- Eviction count
- Current size

**Implementation**:
```rust
pub struct CacheStats {
    pub hits: AtomicUsize,
    pub misses: AtomicUsize,
    pub evictions: AtomicUsize,
}

impl MemoCache {
    pub fn stats(&self) -> CacheStats { ... }
    pub fn hit_rate(&self) -> f64 { ... }
}
```

**Usage**:
```rust
let cache = create_memo_cache();
// ... perform queries ...
println!("Hit rate: {:.2}%", cache.hit_rate() * 100.0);
```

---

### 3. Tune Cache Size ⭐⭐

**Current**: Unbounded (grows indefinitely)
**Proposed**: Configurable max size (default: 1000 entries)

**Implementation**:
```rust
pub fn create_memo_cache_with_capacity(capacity: usize) -> MemoCache {
    MemoCache::with_capacity(capacity)
}
```

**Tuning guidance**:
- Small (100): Low memory, higher miss rate
- Medium (1000): Balanced (recommended default)
- Large (10000): High memory, very high hit rate

---

## Phase 5: Advanced Optimizations (Estimated: 1-2 weeks, variable gains)

### 1. Profile-Guided Optimization (PGO) ⭐⭐⭐

**Approach**: Use actual usage patterns to guide compiler optimizations

**Steps**:
1. Build with instrumentation: `cargo pgo build`
2. Run representative workload to collect profiles
3. Rebuild with PGO data: `cargo pgo optimize`

**Expected gain**: 5-15% across the board

**Effort**: Low (mostly automated)

---

### 2. Algorithmic Alternatives ⭐⭐

**Ukkonen's Algorithm**:
- Optimal for small edit distances (k << min(m,n))
- Computes only "band" around diagonal
- Complexity: O(k × min(m,n)) instead of O(m×n)

**When beneficial**:
- Queries with small max_distance (k ≤ 5)
- Automaton can guide k parameter

**Implementation**:
```rust
pub fn ukkonen_distance(source: &str, target: &str, max_k: usize) -> Option<usize>
```

**Expected gain**: 2-10x for small k values

---

### 3. Block Processing for Long Strings ⭐

**Problem**: Cache locality degrades for very long strings
**Solution**: Process DP matrix in blocks (cache-oblivious algorithm)

**Only beneficial for**: Strings > 1000 chars (rare in fuzzy search)

**Effort**: High, benefit: Marginal for typical use case

---

## Phase 6: Cross-Validation (Estimated: 3-4 days)

### Build Test Harness

**Goal**: Verify exact equivalence with C++ implementation

**Approach**:
1. Build C++ liblevenshtein with test interface
2. Generate comprehensive test corpus (10k string pairs)
3. Run both implementations, compare results
4. Document any differences

**Test corpus**:
- Random strings (various lengths)
- Common prefixes/suffixes
- Unicode characters
- Edge cases

**Validation criteria**:
- 100% exact match on all test cases
- Performance within 20% (expected)

---

## Optimization Priority Matrix

| Optimization | Effort | Expected Gain | Priority | Phase |
|--------------|--------|---------------|----------|-------|
| **FxHash** | 1 hour | 10-15% recursive | ⭐⭐⭐⭐⭐ | 2 |
| **SmallVec** | 2 hours | 20-30% short strings | ⭐⭐⭐⭐⭐ | 2 |
| **Inline annotations** | 1 hour | 5-10% | ⭐⭐⭐⭐ | 2 |
| **Suffix elimination** | 2 hours | 10-50% (variable) | ⭐⭐⭐⭐ | 2 |
| **SIMD vectorization** | 3-5 days | 2-4x medium/long | ⭐⭐⭐⭐ | 3 |
| **LRU eviction** | 1 day | Better memory | ⭐⭐⭐⭐ | 4 |
| **Cache statistics** | 4 hours | Monitoring | ⭐⭐⭐ | 4 |
| **PGO** | 1 day | 5-15% | ⭐⭐⭐ | 5 |
| **Ukkonen's** | 3-5 days | 2-10x (k small) | ⭐⭐ | 5 |
| **Block processing** | 1 week | Marginal | ⭐ | 5 |

---

## Realistic Timeline

### Week 1: Quick Wins
- Day 1-2: Implement FxHash, SmallVec, inlining, suffix elimination
- Day 3: Benchmark and validate
- Day 4-5: Tune and document

**Deliverable**: 30-50% speedup for typical workloads

### Week 2: SIMD
- Day 1: Research and prototype
- Day 2-4: Implement vectorized inner loop
- Day 5: Benchmark, validate, document

**Deliverable**: 2-4x speedup for medium/long strings

### Week 3: Cache + Advanced
- Day 1-2: LRU eviction and statistics
- Day 3: PGO optimization
- Day 4-5: Documentation and final benchmarks

**Deliverable**: Production-ready optimized implementation

---

## Expected Final Performance

### Current (Baseline)
```
Short strings:   99 ns
Medium strings: 740 ns
Long strings:    ~5 µs
```

### After Quick Wins (Phase 2)
```
Short strings:   70 ns  (-30%)
Medium strings: 520 ns  (-30%)
Long strings:    ~3.5 µs (-30%)
```

### After SIMD (Phase 3)
```
Short strings:   70 ns  (no change, too small for SIMD)
Medium strings: 200 ns  (-70% from baseline!)
Long strings:    ~1 µs   (-80% from baseline!)
```

### After Full Optimization
```
Short strings:   60 ns  (-40% from baseline)
Medium strings: 150 ns  (-80% from baseline)
Long strings:   ~800 ns  (-84% from baseline)
```

**Target**: Competitive with hand-tuned assembly implementations!

---

## Risk Assessment

### Low Risk (Safe to implement)
- ✅ FxHash: Drop-in replacement
- ✅ SmallVec: Already tested extensively
- ✅ Inline annotations: Compiler hint only
- ✅ Suffix elimination: Already in C++

### Medium Risk (Needs careful validation)
- ⚠️ SIMD: Requires extensive testing
- ⚠️ LRU eviction: Could impact performance if not done right

### High Risk (Proceed with caution)
- ❌ Algorithmic changes: Could break existing behavior
- ❌ Unsafe code: Only if absolutely necessary (avoid!)

---

## Success Criteria

### Performance
- [ ] 30% speedup from quick wins
- [ ] 2-4x speedup for medium/long strings (SIMD)
- [ ] No regression for short strings
- [ ] Consistent performance across platforms

### Quality
- [ ] All tests still passing
- [ ] No new bugs introduced
- [ ] Property tests validate correctness
- [ ] Cross-validation with C++ passes

### Documentation
- [ ] Benchmark results documented
- [ ] Optimization techniques explained
- [ ] Usage recommendations updated
- [ ] Performance characteristics well-understood

---

## Conclusion

The optimization roadmap is clear and achievable:

1. **Phase 2 (Quick Wins)**: Low-hanging fruit, 30-50% improvement
2. **Phase 3 (SIMD)**: Major speedup for medium/long strings
3. **Phase 4 (Cache)**: Better memory usage
4. **Phase 5 (Advanced)**: Marginal gains, optional

**Recommended approach**: Implement Phase 2 first, then reassess whether Phase 3-5 are needed based on actual performance requirements.

**Current status**: Production-ready baseline established. Ready to optimize! 🚀

---

*Generated: 2025-10-30*
*Based on: Comprehensive benchmarking, profiling, and research*
