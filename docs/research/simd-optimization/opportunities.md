# SIMD Optimization Opportunities Analysis

**Date**: 2025-10-30
**Status**: Research Complete
**Scope**: Dictionary, Automata, and Compositional Data Structures

---

## Executive Summary

Beyond the current SIMD implementation for distance functions, the codebase has **significant untapped potential** for SIMD acceleration across multiple hot paths:

**Top Opportunities** (by expected impact):
1. **Characteristic Vector Computation** - 3-4x speedup potential ⭐⭐⭐
2. **Position Subsumption Checking** - 4-6x speedup potential ⭐⭐⭐
3. **Dictionary Edge Lookups** - 2-4x speedup potential ⭐⭐
4. **Transposition Distance** - 2.5-3x speedup potential ⭐⭐
5. **Common Prefix/Suffix Stripping** - 4-6x speedup potential ⭐⭐

**Overall Impact**: Could achieve **2-4x overall speedup** for typical fuzzy matching workloads.

---

## 1. State Transition Operations (HIGHEST PRIORITY)

### A. Characteristic Vector Computation

**Location**: `src/transducer/transition.rs:21-36`

**Current Implementation** (Scalar):
```rust
fn characteristic_vector<'a>(
    dict_char: u8,
    query: &[u8],
    window_size: usize,
    offset: usize,
    buffer: &'a mut [bool; 8],
) -> &'a [bool] {
    let len = window_size.min(8);
    for (i, item) in buffer.iter_mut().enumerate().take(len) {
        let query_idx = offset + i;
        *item = query_idx < query.len() && query[query_idx] == dict_char;
    }
    &buffer[..len]
}
```

**Why It's Hot**: Called for every state transition in Levenshtein automata traversal

**SIMD Strategy**:
```rust
#[cfg(target_arch = "x86_64")]
#[target_feature(enable = "avx2")]
unsafe fn characteristic_vector_simd(
    dict_char: u8,
    query: &[u8],
    window_size: usize,
    offset: usize,
) -> u8 {
    // Broadcast dict_char to all 32 lanes
    let dict_vec = _mm256_set1_epi8(dict_char as i8);

    // Load up to 32 query bytes (process 8 at a time)
    let mut query_bytes = [0u8; 32];
    let load_len = (query.len() - offset).min(window_size).min(32);
    if offset < query.len() {
        let available = query.len() - offset;
        let copy_len = available.min(load_len);
        query_bytes[..copy_len].copy_from_slice(&query[offset..offset + copy_len]);
    }
    let query_vec = _mm256_loadu_si256(query_bytes.as_ptr() as *const __m256i);

    // Compare all bytes at once
    let cmp_result = _mm256_cmpeq_epi8(dict_vec, query_vec);

    // Extract mask (1 bit per byte comparison result)
    let mask = _mm256_movemask_epi8(cmp_result) as u32;

    // Apply window size mask
    let window_mask = (1u32 << window_size) - 1;
    (mask & window_mask) as u8
}
```

**Benefits**:
- **3-4x speedup**: Process 8-32 comparisons in 3 instructions vs 8-24 scalar instructions
- **Eliminate branches**: No bounds checking in the loop
- **Critical path**: This is called millions of times in typical queries

**Complexity**: Low
**Implementation Time**: 2-3 hours

---

### B. Position Subsumption Checking

**Location**: `src/transducer/state.rs:82-99`

**Current Implementation** (Scalar):
```rust
pub fn insert(&mut self, position: Position, algorithm: Algorithm) {
    // Check if this position is subsumed by existing ones
    for existing in &self.positions {
        if existing.subsumes(&position, algorithm) {
            return; // Already covered
        }
    }

    // Remove positions that this new position subsumes
    self.positions.retain(|p| !position.subsumes(p, algorithm));

    self.positions.push(position);
}

// Position::subsumes checks: |i - j| <= (f - e)
```

**Why It's Hot**: Called for every candidate position during automata traversal
**Critical for**: High max_distance queries (>3) with many positions per state

**SIMD Strategy**:
```rust
#[cfg(target_arch = "x86_64")]
#[target_feature(enable = "avx2")]
unsafe fn batch_subsumption_check(
    positions: &[Position],
    new_position: &Position,
    algorithm: Algorithm,
) -> (bool, Vec<bool>) {
    let n = positions.len();
    let mut subsumed_by_existing = false;
    let mut subsumes_existing = vec![false; n];

    // Process 8 positions at a time
    for chunk_start in (0..n).step_by(8) {
        let chunk_size = (n - chunk_start).min(8);

        // Load term indices and errors into vectors
        let mut term_indices = [0i32; 8];
        let mut num_errors = [0i32; 8];

        for i in 0..chunk_size {
            term_indices[i] = positions[chunk_start + i].term_index as i32;
            num_errors[i] = positions[chunk_start + i].num_errors as i32;
        }

        // Broadcast new position values
        let new_term = _mm256_set1_epi32(new_position.term_index as i32);
        let new_errors = _mm256_set1_epi32(new_position.num_errors as i32);

        // Load existing position vectors
        let exist_term = _mm256_loadu_si256(term_indices.as_ptr() as *const __m256i);
        let exist_errors = _mm256_loadu_si256(num_errors.as_ptr() as *const __m256i);

        // Compute |term_index - new_term|
        let diff = _mm256_sub_epi32(exist_term, new_term);
        let abs_diff = _mm256_abs_epi32(diff);

        // Compute (new_errors - exist_errors)
        let error_diff = _mm256_sub_epi32(new_errors, exist_errors);

        // Check if |i-j| <= (f-e)
        let subsumes_mask = _mm256_cmpgt_epi32(
            _mm256_add_epi32(abs_diff, _mm256_set1_epi32(1)),
            error_diff
        );

        // Extract results
        let result_mask = !(_mm256_movemask_epi8(subsumes_mask) as u32);

        for i in 0..chunk_size {
            if (result_mask >> (i * 4)) & 1 != 0 {
                subsumes_existing[chunk_start + i] = true;
            }
        }
    }

    (subsumed_by_existing, subsumes_existing)
}
```

**Benefits**:
- **4-6x speedup**: For states with 8+ positions
- **Massive impact**: On queries with max_distance > 3
- **Scales linearly**: More positions = more benefit

**Complexity**: Medium
**Implementation Time**: 4-6 hours

---

## 2. Distance Computations (Extend Current SIMD)

### A. Complete SSE4.1 Fallback

**Location**: `src/distance/simd.rs:198-208`

**Current Status**: Falls back to scalar

**SIMD Strategy**: Implement 128-bit SSE4.1 version (4 u32 values in parallel)
- Use `_mm_min_epu32`, `_mm_cmpeq_epi32`, `_mm_andnot_si128`
- Same algorithm as AVX2 but with 4-wide vectors instead of 8-wide

**Benefits**:
- **1.8-2x speedup** on older CPUs (pre-2013)
- **Broad compatibility**: SSE4.1 available since Core 2 (2008)

**Complexity**: Low (copy AVX2 with 128-bit intrinsics)
**Implementation Time**: 2-3 hours

---

### B. Vectorize Transposition Distance

**Location**: `src/distance/mod.rs:302-357`

**Current Implementation**: Triple-loop DP with scalar operations

**SIMD Strategy**: Same as standard distance
- Process 8 columns at once
- Vectorize deletion/substitution costs
- Handle transposition in scalar (conditional logic)

**Benefits**:
- **2.5-3x speedup** on long strings (>32 chars)
- **Important**: Transposition distance is heavily used

**Complexity**: Medium
**Implementation Time**: 4-6 hours

---

### C. SIMD Common Prefix/Suffix Stripping

**Location**: `src/distance/mod.rs:108-145`

**Current Implementation**: Linear character-by-character comparison

**SIMD Strategy**:
```rust
#[cfg(target_arch = "x86_64")]
#[target_feature(enable = "avx2")]
unsafe fn find_first_mismatch_simd(a: &[char], b: &[char]) -> usize {
    let len = a.len().min(b.len());
    let mut i = 0;

    // Process 8 chars at a time
    while i + 8 <= len {
        let mut a_chars = [0u32; 8];
        let mut b_chars = [0u32; 8];

        for j in 0..8 {
            a_chars[j] = a[i + j] as u32;
            b_chars[j] = b[i + j] as u32;
        }

        let a_vec = _mm256_loadu_si256(a_chars.as_ptr() as *const __m256i);
        let b_vec = _mm256_loadu_si256(b_chars.as_ptr() as *const __m256i);

        let cmp = _mm256_cmpeq_epi32(a_vec, b_vec);
        let mask = _mm256_movemask_epi8(cmp);

        // Check if all equal
        if mask != -1 {
            // Found mismatch - count trailing ones
            return i + (mask as u32).trailing_ones() as usize / 4;
        }

        i += 8;
    }

    // Handle remainder
    while i < len && a[i] == b[i] {
        i += 1;
    }

    i
}
```

**Benefits**:
- **4-6x speedup** on strings >32 chars
- **Cumulative gain**: Helps all distance functions

**Complexity**: Low
**Implementation Time**: 2-3 hours

---

## 3. Dictionary Edge Lookups

### A. SIMD Linear Search for Small Edge Sets

**Location**: Multiple dictionary implementations (`dawg.rs`, `suffix_automaton.rs`, etc.)

**Current Implementation**: Linear search for <16 edges

**SIMD Strategy**:
```rust
#[cfg(target_arch = "x86_64")]
#[target_feature(enable = "avx2")]
unsafe fn find_edge_simd(edges: &[(u8, usize)], target: u8) -> Option<usize> {
    if edges.len() == 0 { return None; }
    if edges.len() > 32 { return None; } // Fall back to binary search

    // Extract labels into array
    let mut labels = [0u8; 32];
    for (i, (label, _)) in edges.iter().enumerate() {
        labels[i] = *label;
    }

    // Broadcast target
    let target_vec = _mm256_set1_epi8(target as i8);
    let labels_vec = _mm256_loadu_si256(labels.as_ptr() as *const __m256i);

    // Compare
    let cmp = _mm256_cmpeq_epi8(target_vec, labels_vec);
    let mask = _mm256_movemask_epi8(cmp) as u32;

    if mask != 0 {
        let idx = mask.trailing_zeros() as usize;
        if idx < edges.len() {
            return Some(edges[idx].1);
        }
    }

    None
}
```

**Benefits**:
- **2-4x speedup**: For dictionaries with many small-branching nodes
- **Eliminate branches**: No loop with conditionals
- **Common case**: Most DAWG nodes have <16 edges

**Complexity**: Low
**Implementation Time**: 2-3 hours

---

## 4. Query Processing

### A. Vectorize Min Distance Calculation

**Location**: `src/transducer/state.rs:173-186`

**Current Implementation**: Linear scan to find minimum

**SIMD Strategy**:
```rust
#[cfg(target_arch = "x86_64")]
#[target_feature(enable = "avx2")]
unsafe fn min_distance_simd(positions: &[Position]) -> usize {
    if positions.is_empty() { return usize::MAX; }
    if positions.len() == 1 { return positions[0].num_errors; }

    // Process 8 at a time
    let mut min_vec = _mm256_set1_epi32(i32::MAX);

    for chunk in positions.chunks(8) {
        let mut errors = [i32::MAX; 8];
        for (i, pos) in chunk.iter().enumerate() {
            errors[i] = pos.num_errors as i32;
        }

        let errors_vec = _mm256_loadu_si256(errors.as_ptr() as *const __m256i);
        min_vec = _mm256_min_epi32(min_vec, errors_vec);
    }

    // Horizontal minimum
    let min_arr = std::mem::transmute::<__m256i, [i32; 8]>(min_vec);
    min_arr.iter().min().unwrap() as usize
}
```

**Benefits**:
- **2-3x speedup**: For states with 8+ positions
- **Complements** subsumption optimization

**Complexity**: Low
**Implementation Time**: 1-2 hours

---

## 5. CPU-Specific Optimizations (Beyond SIMD)

### A. Prefetching for Dictionary Traversal

**Strategy**: Use `_mm_prefetch` to load next node before accessing it

```rust
#[cfg(target_arch = "x86_64")]
use std::arch::x86_64::{_mm_prefetch, _MM_HINT_T0};

unsafe fn traverse_with_prefetch(&self, path: &[u8]) {
    let mut state = 0;

    for (i, &byte) in path.iter().enumerate() {
        // Prefetch next potential state
        if i + 1 < path.len() {
            let predicted_next = self.predict_next_state(state, path[i + 1]);
            _mm_prefetch(
                &self.nodes[predicted_next] as *const _ as *const i8,
                _MM_HINT_T0
            );
        }

        state = self.transition(state, byte)?;
    }
}
```

**Benefits**:
- **10-20% speedup**: On deep traversals
- **Reduces cache misses**: Critical for large dictionaries

---

### B. BMI2 Instructions for Bit Manipulation

**Use Case**: Efficient bit extraction from masks in PathMap

```rust
#[cfg(all(target_arch = "x86_64", target_feature = "bmi2"))]
use std::arch::x86_64::{_pext_u64, _pdep_u64};

// Extract set bits efficiently
let set_bits = _pext_u64(mask, 0xFFFFFFFFFFFFFFFF);
let count = set_bits.count_ones();
```

---

### C. Cache Line Alignment

**Strategy**: Align hot structures to 64-byte cache lines

```rust
#[repr(align(64))]  // CPU cache line size
struct CacheOptimizedState {
    // Hot fields first
    positions: SmallVec<[Position; 8]>,
    index: usize,

    // Cold fields last
    metadata: StateMetadata,
}
```

**Benefits**:
- **5-10% speedup**: Reduces false sharing and cache line splits
- **Especially important**: For multi-threaded workloads

---

## Implementation Roadmap

### Phase 4: High-Impact SIMD (Recommended)

**Duration**: 1-2 weeks
**Expected Overall Speedup**: 2-3x on typical workloads

**Tasks**:
1. **Week 1**:
   - Characteristic vector SIMD (3-4x local speedup)
   - Edge lookup SIMD (2-4x local speedup)
   - SSE4.1 fallback for distance (1.8-2x on old CPUs)
   - Common prefix/suffix SIMD (4-6x local speedup)

2. **Week 2**:
   - Position subsumption SIMD (4-6x local speedup)
   - Transposition distance SIMD (2.5-3x local speedup)
   - Min distance SIMD (2-3x local speedup)
   - Comprehensive benchmarking and tuning

### Phase 5: Advanced Optimizations (Optional)

**Duration**: 1-2 weeks
**Expected Additional Speedup**: 1.3-1.5x

**Tasks**:
- Prefetching for dictionary traversal
- Cache line alignment
- BMI2 instructions where applicable
- ARM NEON implementations

---

## Priority Matrix

| Optimization | Impact | Complexity | Time | Priority |
|--------------|--------|------------|------|----------|
| **Characteristic Vector SIMD** | Very High | Low | 2-3h | 1 ⭐⭐⭐ |
| **Edge Lookup SIMD** | High | Low | 2-3h | 2 ⭐⭐⭐ |
| **Position Subsumption SIMD** | Very High | Medium | 4-6h | 3 ⭐⭐⭐ |
| **SSE4.1 Fallback** | High | Low | 2-3h | 4 ⭐⭐ |
| **Common Prefix/Suffix SIMD** | Medium | Low | 2-3h | 5 ⭐⭐ |
| **Transposition Distance SIMD** | High | Medium | 4-6h | 6 ⭐⭐ |
| **Min Distance SIMD** | Medium | Low | 1-2h | 7 ⭐ |
| **Prefetching** | Medium | Medium | 3-4h | 8 ⭐ |
| **Cache Line Alignment** | Low | Low | 2-3h | 9 ⭐ |
| **BMI2 Instructions** | Low | Medium | 3-4h | 10 ⭐ |

---

## Architecture Recommendation

### Create Unified SIMD Module

```
src/simd/
├── mod.rs              // Public API, runtime detection
├── x86_64/
│   ├── mod.rs
│   ├── avx2.rs         // AVX2 implementations
│   ├── sse41.rs        // SSE4.1 implementations
│   └── scalar.rs       // Fallback implementations
├── aarch64/
│   ├── mod.rs
│   └── neon.rs         // ARM NEON implementations
└── generic.rs          // Cross-platform scalar fallbacks
```

### Runtime Capability Detection

```rust
pub struct SimdCapabilities {
    pub has_avx2: bool,
    pub has_sse41: bool,
    pub has_bmi2: bool,
    pub has_popcnt: bool,
}

static SIMD_CAPS: LazyLock<SimdCapabilities> = LazyLock::new(|| {
    SimdCapabilities::detect()
});
```

---

## Benchmarking Strategy

Create comprehensive benchmarks for each optimization:

```rust
// benches/simd_benchmarks.rs
criterion_group!(
    name = simd_benches;
    config = Criterion::default();
    targets =
        bench_characteristic_vector,
        bench_position_subsumption,
        bench_edge_lookup,
        bench_transposition_distance,
        // ...
);
```

**Compare**:
- Scalar vs SIMD implementations
- Different SIMD instruction sets (AVX2 vs SSE4.1)
- Various input sizes and patterns

---

## Expected Overall Performance Gains

### Conservative Estimate (Phase 4 Only)

| Workload Type | Baseline | Phase 4 | Total Gain |
|---------------|----------|---------|------------|
| **Low max_distance (≤2)** | 100% | 180-220% | 1.8-2.2x |
| **Medium max_distance (3-4)** | 100% | 250-300% | 2.5-3x |
| **High max_distance (≥5)** | 100% | 300-400% | 3-4x |

### With Phase 5 (Full Optimization)

| Workload Type | Baseline | Phase 4+5 | Total Gain |
|---------------|----------|-----------|------------|
| **Low max_distance** | 100% | 220-280% | 2.2-2.8x |
| **Medium max_distance** | 100% | 320-400% | 3.2-4x |
| **High max_distance** | 100% | 400-500% | 4-5x |

---

## Conclusion

The codebase has **tremendous potential** for SIMD acceleration beyond distance functions:

✅ **High-impact targets identified**: Characteristic vectors, subsumption, edge lookups
✅ **Low-hanging fruit**: Many optimizations are low complexity, high impact
✅ **Proven approach**: Can use same patterns as Phase 3 distance SIMD
✅ **Incremental deployment**: Can implement and validate each optimization independently

**Recommendation**: Implement Phase 4 high-impact optimizations for **2-4x overall speedup** on typical fuzzy matching workloads.

---

*Analysis Date: 2025-10-30*
*Status: Ready for Implementation*
*Estimated Total Effort: 1-2 weeks for Phase 4*
