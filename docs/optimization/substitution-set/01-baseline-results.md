# SubstitutionSet Baseline Performance Results

**Date**: 2025-11-12
**Hardware**: Intel Xeon E5-2699 v3 @ 2.30GHz (CPU Core 0 & 1, performance governor)
**Rust**: 1.91.0
**Commit**: e5a32a0

## Executive Summary

Baseline measurements show that FxHashSet-based SubstitutionSet implementation performs excellently:
- **Single lookup**: ~5.0ns (hash lookup is extremely fast)
- **Batch operations**: ~4.0ns per lookup with overhead
- **Policy overhead**: +10-20% for restricted policies (acceptable)
- **Preset initialization**: 200ns-1µs (not a bottleneck)

**Optimization Priority**: Focus on preset initialization (perfect hashing) as primary optimization target.

---

## Micro-Benchmark Results

### 1. Contains() Performance by Set Size

Testing 100 lookups (50% hit rate) across varying set sizes:

| Set Size | Time (ns) | Throughput (Melem/s) | Per-Lookup (ns) |
|----------|-----------|----------------------|-----------------|
| 1        | 407.38    | 245.47              | 4.07            |
| 5        | 411.14    | 243.23              | 4.11            |
| 10       | 413.05    | 242.10              | 4.13            |
| 20       | 430.16    | 232.47              | 4.30            |
| 50       | 431.69    | 231.65              | 4.32            |
| 100      | 402.83    | 248.24              | 4.03            |
| 200      | 421.07    | 237.49              | 4.21            |
| 500      | 448.15    | 223.14              | 4.48            |

**Analysis**:
- Performance relatively flat across sizes (4.0-4.5ns per lookup)
- Slight degradation at size=500 (448ns vs 407ns for size=1) = +10%
- Excellent hash distribution (no major collisions)
- FxHashSet scales well for this use case

### 2. Hit Rate Impact (1000 lookups, set size=50)

| Hit Rate | Time (µs) | Throughput (Melem/s) | Per-Lookup (ns) |
|----------|-----------|----------------------|-----------------|
| 10%      | 4.025     | 248.44              | 4.025           |
| 50%      | 4.525     | 220.97              | 4.525           |
| 90%      | 4.787     | 208.88              | 4.787           |

**Analysis**:
- Hit rate affects performance: 10% → 90% hit = +19% latency
- Cache effects: More hits = more data access = slightly slower
- Difference is modest (0.76ns per lookup)

### 3. Insertion Performance

#### Byte-level (SubstitutionSet):

| Pairs | Time (µs) | Throughput (Melem/s) | Per-Insert (ns) |
|-------|-----------|----------------------|-----------------|
| 10    | 0.269     | 37.15               | 26.9            |
| 50    | 1.024     | 48.82               | 20.5            |
| 100   | 1.901     | 52.60               | 19.0            |
| 500   | 7.707     | 64.88               | 15.4            |

**Analysis**:
- Insertion gets more efficient with larger batches (cache warming)
- 500 inserts: 15.4ns per insert (excellent)

#### Char-level (SubstitutionSetChar):

| Pairs | Time (µs) | Throughput (Melem/s) | Per-Insert (ns) |
|-------|-----------|----------------------|-----------------|
| 10    | 0.327     | 30.55               | 32.7            |
| 50    | 1.127     | 44.38               | 22.5            |
| 100   | 2.050     | 48.78               | 20.5            |
| 500   | 11.282    | 44.32               | 22.6            |

**Analysis**:
- Char operations ~20-30% slower than byte operations (expected)
- Unicode handling adds overhead but still performant

### 4. Preset Initialization

#### Byte-level Presets:

| Preset          | Time (ns) | Description                    |
|-----------------|-----------|--------------------------------|
| phonetic_basic  | 209.66    | Common phonetic substitutions  |
| leet_speak      | 286.13    | 1337 speak mappings            |
| ocr_friendly    | 267.40    | OCR confusion pairs            |
| keyboard_qwerty | 645.64    | QWERTY adjacent key typos      |

**Analysis**:
- Keyboard preset is 3x slower (larger set: ~80 pairs vs ~20-30)
- All presets initialize in <1µs (fast)
- **Optimization opportunity**: Perfect hashing could eliminate hash computation

#### Char-level Presets:

| Preset                    | Time (µs) | Description                |
|---------------------------|-----------|----------------------------|
| greek_case_insensitive    | 0.493     | Greek letter mappings      |
| japanese_hiragana_katakana| 0.369     | Japanese kana mappings     |
| cyrillic_case_insensitive | 0.636     | Cyrillic letter mappings   |
| diacritics_latin          | 1.024     | Diacritic removal          |

**Analysis**:
- Char presets 2-5x slower than byte presets (Unicode overhead)
- Still sub-microsecond performance
- Diacritics preset largest (1µs)

### 5. Single Lookup Profiling

| Operation | Time (ns) | Notes                          |
|-----------|-----------|--------------------------------|
| Hit       | 5.054     | Lookup found in set            |
| Miss      | 5.178     | Lookup not found (early exit)  |

**Analysis**:
- Absolute minimum latency: ~5ns per lookup
- Miss slightly slower (+2.5%) due to full scan confirmation
- This represents raw FxHashSet performance

---

## Integration Benchmark Results

### 1. Unrestricted Query Performance (Baseline)

Testing real fuzzy queries with varying edit distances:

| Query        | Distance | Time (µs) | Description                |
|--------------|----------|-----------|----------------------------|
| aple         | 1        | 10.45     | Simple 1-edit query        |
| appl         | 1        | 11.17     | 1-edit, multiple results   |
| banan        | 1        | 16.86     | Longer term, 1-edit        |
| famly        | 1        | 16.80     | 1-edit query               |
| computr      | 1        | 21.11     | Long term, 1-edit          |
| aplpy        | 2        | 58.00     | 2-edit query               |
| beutiful     | 2        | 79.60     | 2-edit, long term          |
| buisness     | 2        | 65.67     | 2-edit, medium term        |
| govrment     | 2        | 55.22     | 2-edit, no results         |
| intresting   | 3        | 178.89    | 3-edit, long term          |

**Analysis**:
- Distance scaling: d=1→d=2 ≈ 3-4x slower, d=2→d=3 ≈ 2x slower
- Query length impacts performance significantly
- Exponential growth in state space with distance

### 2. Policy Overhead Comparison

Query: "computer" (exact match in dictionary)

#### Distance = 1:

| Policy         | Time (µs) | Overhead vs Baseline |
|----------------|-----------|----------------------|
| Unrestricted   | 20.93     | -                    |
| Phonetic       | 22.94     | +9.6%                |
| Custom (small) | 22.91     | +9.5%                |

#### Distance = 2:

| Policy         | Time (µs) | Overhead vs Baseline |
|----------------|-----------|----------------------|
| Unrestricted   | 86.15     | -                    |
| Phonetic       | 93.27     | +8.3%                |
| Custom (small) | 85.82     | -0.4%                |

#### Distance = 3:

| Policy         | Time (µs) | Overhead vs Baseline |
|----------------|-----------|----------------------|
| Unrestricted   | 186.77    | -                    |
| Phonetic       | 223.75    | +19.8%               |
| Custom (small) | 214.40    | +14.8%               |

**Analysis**:
- Policy overhead increases with edit distance
- At d=3, phonetic adds ~37µs overhead (~20%)
- Small custom set performs slightly better than phonetic (fewer checks)
- Overhead is acceptable for most use cases

### 3. Preset Policy Performance

#### Phonetic Preset Queries:

| Query   | Distance | Time (µs) | Notes                        |
|---------|----------|-----------|------------------------------|
| aple    | 1        | 25.16     | vs 10.45µs unrestricted      |
| senter  | 2        | 133.61    | c/s substitution             |
| kollege | 2        | 93.55     | c/k substitution             |
| foto    | 2        | 83.35     | f/ph substitution (no match) |
| nite    | 2        | 68.14     | ight/ite (no match)          |
| kwick   | 2        | 73.54     | qu/k (no match)              |

**Analysis**:
- Phonetic preset adds 10-40µs overhead depending on query
- Overhead acceptable for phonetic search use cases

#### Keyboard Preset Queries:

| Query    | Distance | Time (µs) | Notes                       |
|----------|----------|-----------|-----------------------------|
| aoole    | 2        | 111.70    | p/o adjacent key            |
| bannna   | 2        | 90.99     | a/n adjacent key            |
| vook     | 1        | 45.97     | b/v adjacent key            |
| cimputer | 2        | 136.96    | o/i adjacent key            |
| familh   | 1        | 28.44     | y/h adjacent key            |

**Analysis**:
- Keyboard preset overhead similar to phonetic
- Useful for typo correction scenarios

---

## Bottleneck Analysis

### Current Performance Characteristics:

1. **Single lookup: ~5ns** - Extremely fast, hard to optimize further
2. **Preset initialization: 200-640ns** - Could benefit from perfect hashing
3. **Policy overhead: +10-20%** - Acceptable, but could be reduced
4. **Hash computation: ~2-3ns** - Part of the 5ns total

### Optimization Opportunities (Ranked):

1. **HIGH**: Perfect hash for presets - Eliminate 200-640ns initialization cost
2. **MEDIUM**: Bitmap for ASCII - Potentially faster than hash for byte-level (5ns → 3ns?)
3. **MEDIUM**: Hybrid small/large - Linear scan for <10 pairs might be faster
4. **LOW**: Custom hasher - Minimal gains (~1-2%)

### What NOT to Optimize:

- Single lookup performance (5ns) - Already excellent
- Insertion performance - Not a hot path
- Policy overhead at d=1 - Minimal impact

---

## Reproducibility

### Environment:
```
OS: Linux 6.17.7-arch1-1
Rust: 1.91.0 (f8297e351 2025-10-28)
Cargo: 1.91.0 (ea2d97820 2025-10-10)
CPU Governor: performance
CPU Affinity: Core 0 (micro), Core 1 (integration)
RUSTFLAGS: -C target-cpu=native
```

### Commands:
```bash
# Micro-benchmarks
RUSTFLAGS="-C target-cpu=native" taskset -c 0 \
  cargo bench --bench substitution_set_microbench --features rand

# Integration benchmarks
RUSTFLAGS="-C target-cpu=native" taskset -c 1 \
  cargo bench --bench substitution_integration_bench
```

### Raw Output:
- Micro-benchmarks: `/tmp/substitution_set_baseline.txt`
- Integration: `/tmp/substitution_integration_baseline.txt`

---

## Next Steps

1. **Generate flamegraphs** - Identify exact hotspots in contains() and preset init
2. **Run perf stat** - Analyze cache misses, branch mispredictions
3. **Implement Hypothesis 1** - Perfect hash for presets (HIGH priority)
4. **Measure improvements** - Compare against this baseline

---

**Generated**: 2025-11-12
**Baseline Commit**: e5a32a0
