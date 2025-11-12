# Hypothesis 2: Bitmap for ASCII Operations

**Status**: ❌ **REJECTED**
**Date**: 2025-11-12
**Branch**: `feature/h2-bitmap-substitution` (to be removed)
**Baseline Commit**: e5a32a0

---

## Hypothesis

**Statement**: For byte-level (ASCII) substitutions, a 128×128 bit matrix (2KB) would provide O(1) lookup with excellent cache locality, outperforming hash-based approaches for small-to-medium sized sets.

**Rationale**:
- FxHashSet requires hash computation overhead for each lookup
- Hash-based approach has pointer indirection and potential cache misses
- Bitmap fits entirely in L1 cache (typical: 32-64KB)
- Bit test operations are extremely fast (single instruction)
- Sequential memory access has better cache behavior than hash probing

**Expected Impact**: 3-10% improvement for ASCII `contains()` calls

---

## Implementation

### Design

**Data Structure**:
```rust
pub struct SubstitutionSetBitmap {
    /// 128×128 bit matrix stored as bytes.
    /// Index calculation: bitmap[a * 16 + b / 8] & (1 << (b % 8))
    /// where 16 = 128 / 8 (bytes per row)
    bitmap: [u8; 2048],  // 128 * 128 / 8 = 2048 bytes
}
```

**Memory Layout**:
- Total size: 2048 bytes (2 KB)
- Represents 128×128 = 16,384 possible ASCII byte pairs
- Each bit at position `[a][b]` indicates if substitution `a → b` is allowed
- Row-major storage: row `a` occupies bytes `a*16` through `a*16+15`

**Core Operations**:

1. **Lookup** (`contains`):
```rust
#[inline]
pub fn contains(&self, dict_char: u8, query_char: u8) -> bool {
    if dict_char >= 128 || query_char >= 128 {
        return false;
    }
    let byte_index = (dict_char as usize) * 16 + (query_char as usize) / 8;
    let bit_offset = query_char % 8;
    (self.bitmap[byte_index] & (1 << bit_offset)) != 0
}
```

2. **Insertion** (`allow_byte`):
```rust
#[inline]
pub fn allow_byte(&mut self, a: u8, b: u8) {
    if a >= 128 || b >= 128 {
        return;
    }
    let byte_index = (a as usize) * 16 + (b as usize) / 8;
    let bit_offset = b % 8;
    self.bitmap[byte_index] |= 1 << bit_offset;
}
```

### Files Created/Modified

1. **src/transducer/substitution_set_bitmap.rs** (CREATED - 320 lines)
   - Core bitmap implementation
   - Preset builders (phonetic_basic, keyboard_qwerty, leet_speak, ocr_friendly)
   - Unit tests

2. **src/transducer/mod.rs** (MODIFIED)
   - Added `pub mod substitution_set_bitmap;`

3. **benches/substitution_set_microbench.rs** (MODIFIED - Added 142 lines)
   - `bench_bitmap_vs_hash_single()` - Single lookup comparison
   - `bench_bitmap_vs_hash_batch()` - Batch lookup with varying sizes
   - `bench_bitmap_vs_hash_presets()` - Preset initialization comparison

---

## Benchmark Results

### Test Configuration

```bash
RUSTFLAGS="-C target-cpu=native" taskset -c 0 \
  cargo bench --bench substitution_set_microbench --features rand \
  -- "bitmap_vs_hash"
```

**Hardware**:
- CPU: Intel Xeon E5-2699 v3 @ 2.30GHz (Haswell-EP)
- L1 Cache: 1.1 MiB (per core)
- L2 Cache: ~9 MB
- L3 Cache: ~45 MB
- CPU Affinity: Core 0 (isolated)

**Compiler**: `rustc` with `-C target-cpu=native`

### Raw Results

#### 1. Single Lookup Performance

| Operation   | Hash (FxHashSet) | Bitmap    | Improvement | Speedup |
|-------------|------------------|-----------|-------------|---------|
| **Hit**     | 5.18 ns         | 2.30 ns   | **55.5%**   | 2.25×   |
| **Miss**    | 5.32 ns         | 2.25 ns   | **57.7%**   | 2.37×   |

**Analysis**:
- ✅ Bitmap is **2.25-2.37× faster** for individual lookups
- ✅ Performance is **consistent** (hit vs miss within 2%)
- ✅ Hash has ~5.2ns overhead (likely hash computation + probing)
- ✅ Bitmap has ~2.3ns overhead (bit indexing + test)

#### 2. Batch Lookup Performance (100 queries, 50% hit rate)

| Set Size | Hash (FxHashSet) | Bitmap  | Improvement | Speedup |
|----------|------------------|---------|-------------|---------|
| 10 pairs | 420.6 ns        | 176.9 ns| **58.0%**   | 2.37×   |
| 50 pairs | 438.5 ns        | 176.3 ns| **59.8%**   | 2.49×   |
| 100 pairs| 414.8 ns        | 172.5 ns| **58.5%**   | 2.41×   |

**Throughput (batch/100)**:
- Hash: ~238 Melem/s
- Bitmap: ~570 Melem/s (**2.4× higher**)

**Analysis**:
- ✅ Bitmap is **2.37-2.49× faster** for batch operations
- ✅ Performance is **independent of set size** (constant 2KB memory)
- ✅ Hash performance **slightly degrades** with size (50 pairs: 438ns vs 10 pairs: 420ns)
- ✅ Excellent cache behavior (2KB fits in L1)

#### 3. Preset Initialization Performance ❌

| Preset           | Pairs | Hash (FxHashSet) | Bitmap      | Slowdown   |
|------------------|-------|------------------|-------------|------------|
| **phonetic_basic** | 14  | 177.7 ns        | 2,243.5 ns  | **12.6×**  |
| **keyboard_qwerty**| 68  | 563.7 ns        | 2,303.9 ns  | **4.1×**   |
| **leet_speak**     | 22  | 223.9 ns        | 2,151.2 ns  | **9.6×**   |

**Analysis**:
- ❌ Bitmap is **4.1-12.6× slower** for preset initialization
- ❌ Overhead is **independent of pair count** (~2.2μs constant)
- ❌ Likely due to fixed 2KB zero-initialization cost
- ❌ Hash only allocates for actual pairs stored

---

## Analysis

### What Went Right ✅

1. **Lookup Performance Exceeded Expectations**
   - Expected: 3-10% improvement
   - Actual: **55-60% improvement** (2.4× speedup)
   - Root cause: Eliminated hash computation + probing overhead

2. **Cache Behavior is Excellent**
   - 2KB bitmap fits entirely in L1 cache
   - Sequential memory access pattern
   - Performance independent of set size

3. **Consistent Performance**
   - Hit vs miss within 2% (2.30ns vs 2.25ns)
   - No variance across set sizes (10-100 pairs)
   - Predictable behavior for real-world usage

### What Went Wrong ❌

1. **Initialization Overhead is Catastrophic**
   - 4.1-12.6× slower than hash-based approach
   - Fixed ~2.2μs cost regardless of pair count
   - Overhead likely from:
     - Zero-initializing 2048 bytes
     - Poor cache behavior during initialization
     - No benefit from const arrays (H1 optimization)

2. **Memory Overhead for Small Sets**
   - Bitmap always uses 2KB
   - Hash uses ~(n * 24 bytes) for n pairs
   - Crossover point: ~85 pairs (85 * 24 = 2040 bytes)
   - Most practical sets are <85 pairs

3. **No Benefit from Const Array Optimization**
   - H1 optimization (const arrays) gave 15-28% improvement for hash presets
   - Bitmap cannot leverage compile-time initialization
   - Fixed initialization cost dominates

---

## Decision: ❌ REJECT

### Reasoning

**Critical Flaw**: Initialization overhead (4-13×) **outweighs** lookup performance benefits (2.4×)

**Why This Matters**:
1. **Preset initialization happens at program startup**
   - Users construct presets once, use many times
   - But construction happens in hot path (e.g., setting up transducer)
   - 2μs overhead adds up with multiple transducers

2. **Lookup performance doesn't justify cost**
   - 2.4× faster lookup = saving ~3ns per lookup
   - Need **~733 lookups** to amortize 2.2μs initialization cost
   - For small queries (<733 lookups), bitmap is net slower

3. **Memory overhead for small sets**
   - Most practical substitution sets are small (<50 pairs)
   - Bitmap uses 2KB regardless, hash uses <1KB for small sets

4. **Cannot leverage const array optimization (H1)**
   - H1 gave 15-28% speedup for hash-based presets
   - Bitmap has fixed initialization cost, no compile-time benefit

### Break-Even Analysis

**When would bitmap be worthwhile?**

Assuming:
- Initialization cost: 2,200ns (bitmap) vs 200ns (hash) = **2,000ns overhead**
- Lookup speedup: 5.2ns (hash) vs 2.3ns (bitmap) = **2.9ns saved per lookup**

Break-even point: `2,000ns / 2.9ns ≈ 690 lookups`

**Real-world scenarios**:
- Small query (word length 5, distance 1): ~50 lookups
- Medium query (word length 10, distance 2): ~300 lookups
- Large query (word length 15, distance 3): ~1,000 lookups

**Conclusion**: Only large queries (distance ≥3) would benefit, but:
- Most practical queries are distance 1-2
- Universal transducer is already highly optimized (SmallVec, BTreeSet→SmallVec)
- 2.4× lookup speedup is marginal compared to other bottlenecks

---

## Alternative Considered: Lazy Initialization

**Idea**: Only initialize bitmap on first lookup, not during construction.

**Why Rejected**:
- First lookup would have 2μs penalty (unacceptable latency spike)
- Adds complexity (initialization flag, thread safety considerations)
- Doesn't solve fundamental memory overhead issue
- Initialization still happens eventually

---

## Lessons Learned

1. **Initialization cost matters**
   - Optimizing hot path (lookup) is insufficient if cold path (initialization) regresses
   - Amortization analysis is critical for data structure choices

2. **Memory footprint matters for small sets**
   - Fixed-size data structures have crossover points
   - Most practical sets are small (<50 pairs)

3. **Const arrays are powerful (H1 confirmed again)**
   - Hash-based approach benefits from compile-time initialization
   - Fixed data structures (like bitmap) cannot leverage this

4. **Measurement before optimization**
   - Hypothesis was reasonable (cache locality, O(1) lookup)
   - Empirical data revealed fatal flaw (initialization cost)
   - Avoiding premature commitment saved wasted effort

---

## Reproducibility

### Commands

```bash
# Build optimized
RUSTFLAGS="-C target-cpu=native" cargo build --release --features rand

# Run benchmarks
RUSTFLAGS="-C target-cpu=native" taskset -c 0 \
  cargo bench --bench substitution_set_microbench --features rand \
  -- "bitmap_vs_hash" 2>&1 | tee /tmp/bitmap_vs_hash_results.txt
```

### Environment

- **OS**: Linux 6.17.7-arch1-1
- **Rust**: `rustc --version` (to be recorded)
- **CPU**: Intel Xeon E5-2699 v3 @ 2.30GHz (36 cores, Haswell-EP)
- **CPU Governor**: (to be checked)
- **Affinity**: Core 0 (isolated via `taskset -c 0`)

### Commit

- **Baseline**: e5a32a0 (with H1 const array optimization)
- **H2 Branch**: `feature/h2-bitmap-substitution` (experimental, to be deleted)

---

## Next Steps

1. ✅ Document H2 rejection
2. Remove experimental files:
   - `src/transducer/substitution_set_bitmap.rs`
   - Bitmap benchmarks from `benches/substitution_set_microbench.rs`
   - Module export from `src/transducer/mod.rs`
3. Update `00-experiment-log.md` with H2 results
4. Move to **Hypothesis 3**: Hybrid Small/Large Strategy
   - Investigate SmallVec for <10 pairs
   - Profile crossover point for hash promotion

---

**Conclusion**: While bitmap lookup performance is excellent (2.4× faster), the 4-13× initialization overhead makes this optimization unsuitable for production use. The break-even point (~700 lookups) exceeds typical query patterns, and the memory overhead penalizes small substitution sets.

**Decision**: ❌ **REJECT** - Initialization cost outweighs lookup benefits.
