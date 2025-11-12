# SubstitutionSet Optimization - Experiment Log

**Date Started**: 2025-11-12
**Objective**: Systematically identify and optimize performance bottlenecks in SubstitutionSet/SubstitutionSetChar operations
**Hardware**: Intel Xeon E5-2699 v3 @ 2.30GHz (36 cores, 72 threads), 252 GB RAM
**Baseline Commit**: e5a32a0 (docs: Update universal-levenshtein README with SmallVec implementation status)

## Scientific Method

This optimization follows rigorous scientific methodology:
1. **Hypothesis**: Formulate specific, testable hypotheses about potential optimizations
2. **Experiment**: Implement the optimization in isolation
3. **Measurement**: Benchmark against baseline with statistical rigor (Criterion)
4. **Analysis**: Evaluate results, determine if hypothesis is confirmed
5. **Decision**: Keep if improvement is significant, discard otherwise
6. **Documentation**: Record all results for reproducibility

## Phase 1: Baseline Establishment

### 1.1 Benchmark Suite Creation

**Created Benchmarks**:
- `benches/substitution_set_microbench.rs` - Micro-benchmarks for isolated operations
  - `contains()` with varying set sizes (1-500 pairs)
  - Hit/miss ratio tests (10%, 50%, 90% hit rates)
  - Insertion performance (`allow_byte`, `allow`)
  - Preset builder initialization (4 byte presets, 4 char presets)
  - Single lookup profiling (hit vs miss)

- `benches/substitution_integration_bench.rs` - Real-world query scenarios
  - Unrestricted (baseline) query performance
  - Phonetic preset performance
  - Keyboard preset performance
  - Custom small substitution sets
  - Policy overhead comparison across distances

**Test Configuration**:
- CPU Affinity: Core 0 (micro-benchmarks), Core 1 (integration benchmarks)
- Compiler Flags: `RUSTFLAGS="-C target-cpu=native"`
- Features: `--features rand` (for micro-benchmarks)

### 1.2 Baseline Measurements

**Micro-Benchmark Run**:
```bash
RUSTFLAGS="-C target-cpu=native" taskset -c 0 cargo bench \
  --bench substitution_set_microbench --features rand \
  2>&1 | tee /tmp/substitution_set_baseline.txt
```

**Integration Benchmark Run**:
```bash
RUSTFLAGS="-C target-cpu=native" taskset -c 1 cargo bench \
  --bench substitution_integration_bench \
  2>&1 | tee /tmp/substitution_integration_baseline.txt
```

**Status**: RUNNING (started 2025-11-12)

### 1.3 Baseline Results

_(To be filled after benchmarks complete)_

## Phase 2: Profiling and Analysis

### 2.1 Flamegraph Generation

_(Planned)_

```bash
# Contains() hot path profiling
RUSTFLAGS="-C target-cpu=native" taskset -c 0 cargo flamegraph \
  --bench substitution_set_microbench --features rand \
  -- --bench "single_lookup/hit"
```

### 2.2 Perf stat Analysis

_(Planned)_

```bash
taskset -c 0 perf stat -e cycles,instructions,cache-references,cache-misses,branches,branch-misses \
  -- cargo bench --bench substitution_set_microbench --features rand \
  -- --bench "single_lookup"
```

### 2.3 Bottleneck Identification

_(To be filled after profiling)_

## Phase 3: Optimization Experiments

### Hypothesis 1: Const Arrays for Presets ✅ **CONFIRMED**

**Hypothesis**: Preset substitution sets (phonetic, keyboard, etc.) have known,
fixed contents at compile time. Using const arrays would eliminate runtime hash
computations and char-to-byte conversions during initialization.

**Expected Impact**: 5-15% improvement for preset initialization

**Actual Impact**: **15-28% improvement** (exceeded expectations!)

**Implementation**:
- Created `substitution_set_const.rs` with const array-based presets
- Attempted PHF implementation but PHF v0.11 doesn't support tuple keys
- Used const arrays with direct byte insertion (`allow_byte()` vs `allow()`)
- Pre-allocated exact capacity from const array length

**Results** (2025-11-12):
- phonetic_basic: 196ns → 158ns (**-19.2%**, p<0.05) ✅
- keyboard_qwerty: 587ns → 495ns (**-15.6%**, p<0.05) ✅
- leet_speak: 245ns → 200ns (**-18.1%**, p<0.05) ✅
- ocr_friendly: 224ns → 160ns (**-28.2%**, p<0.05) ✅

**Decision**: **KEEP** - All presets exceed 2% threshold significantly

**Documentation**: See `02-hypothesis1-const-arrays.md` for full analysis

**Status**: ✅ COMPLETED - Approved for production integration

---

### Hypothesis 2: Bitmap for ASCII Operations (MEDIUM-HIGH PRIORITY)

**Hypothesis**: For byte-level (ASCII) substitutions, a 128×128 bit matrix (2KB)
would provide O(1) lookup with excellent cache locality, outperforming hash-based
approaches for small-to-medium sized sets.

**Expected Impact**: 3-10% improvement for ASCII contains() calls

**Implementation Strategy**:
- Implement 128×128 bit array (16384 bits = 2KB)
- Use bit indexing: `bitmap[a * 128 + b]`
- Compare cache behavior vs FxHashSet

**Status**: PENDING

---

### Hypothesis 3: Hybrid Small/Large Strategy (MEDIUM PRIORITY)

**Hypothesis**: Small substitution sets (<10 pairs) would benefit from linear scan
over hash lookup overhead. Hybrid approach: SmallVec for <10 pairs, FxHashSet for ≥10.

**Expected Impact**: 2-5% improvement for small custom sets

**Implementation Strategy**:
- SmallVec<[(u8, u8); 10]> for small sets
- Automatic promotion to FxHashSet at threshold
- Benchmark crossover point

**Status**: PENDING

---

### Hypothesis 4: SIMD Lookup for Small Sets (LOW PRIORITY)

**Hypothesis**: For very small sets (≤8 pairs), SIMD parallel comparison could
outperform both linear scan and hashing.

**Expected Impact**: 1-3% improvement for tiny sets

**Status**: DEFERRED (low priority)

---

### Hypothesis 5: Custom Hasher Optimization (LOW PRIORITY)

**Hypothesis**: FxHasher is general-purpose. A specialized hasher for (u8, u8) pairs
could reduce collisions and improve performance.

**Expected Impact**: 1-2% improvement

**Status**: DEFERRED (diminishing returns)

## Phase 4: Integration and Final Benchmarks

_(To be filled after experiments complete)_

## Phase 5: Results Summary

_(To be filled after all experiments complete)_

## Reproducibility

**Environment**:
- OS: Linux 6.17.7-arch1-1
- Rust Version: (to be recorded)
- Cargo Version: (to be recorded)
- CPU Frequency Governor: (to be checked)

**Reproduction Commands**:
```bash
# Clone repository
git clone https://github.com/anthropics/liblevenshtein-rust
cd liblevenshtein-rust
git checkout <commit-hash>

# Run benchmarks
RUSTFLAGS="-C target-cpu=native" taskset -c 0 \
  cargo bench --bench substitution_set_microbench --features rand

RUSTFLAGS="-C target-cpu=native" taskset -c 1 \
  cargo bench --bench substitution_integration_bench
```

## Notes

- All benchmarks run with CPU affinity to minimize variance
- Criterion provides statistical analysis (confidence intervals, outlier detection)
- Each optimization implemented on separate branch for easy rollback
- Only optimizations showing >2% improvement with statistical significance will be kept

---

**Last Updated**: 2025-11-12
**Experiment Owner**: Claude Code (Anthropic AI Assistant)
