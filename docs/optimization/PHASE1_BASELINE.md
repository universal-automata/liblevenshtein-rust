# Phase 1: Baseline Establishment & Hypothesis Formation

**Date**: November 17-18, 2025
**System**: Intel Xeon E5-2699 v3 @ 2.30GHz (36 cores), 252 GB RAM
**CPU Affinity**: Pinned to core 0 using `taskset -c 0`
**CPU Governor**: performance (verified)

---

## 1.1 Existing Benchmark Assessment

### Finding: Most Existing Benchmarks Are Broken

**Attempted benchmarks**:

1. **state_operations_benchmarks.rs** ❌
   - **Status**: BROKEN - API outdated
   - **Error**: `insert()` and `merge()` methods now require `query_length: usize` parameter
   - **Last Modified**: Oct 30, 2024

2. **transition_benchmarks.rs** ❌
   - **Status**: BROKEN - API outdated
   - **Error**: `transition_state()` signature changed
   - **Last Modified**: Oct 29, 2024

3. **benchmarks.rs** (main) ❌
   - **Status**: BROKEN - Missing feature
   - **Error**: Requires `PathMapDictionary` (pathmap-backend feature not enabled)
   - **Last Modified**: Oct 29, 2024

4. **comprehensive_profiling.rs** ❌
   - **Status**: BROKEN - Missing feature
   - **Error**: Requires `pathmap-backend` feature
   - **Last Modified**: Oct 29, 2024

5. **substitution_set_microbench.rs** ✅
   - **Status**: RUNNING
   - **Feature**: Requires `rand` feature
   - **Purpose**: Micro-benchmarks for SubstitutionSet operations
   - **Scope**: NOT full generalized automaton (only substitution lookups)
   - **Last Modified**: Nov 15, 2024

### Key Observations

1. **NO WORKING GENERALIZED AUTOMATON BENCHMARKS**: None of the existing benchmarks test the generalized automaton's core operations (state transitions, successor generation, acceptance).

2. **API Drift**: Many benchmarks haven't been updated since the Phase 3/4 changes (phonetic operations, formal verification).

3. **Feature Dependencies**: Multiple benchmarks require features not enabled by default (pathmap-backend, rand, serialization).

4. **Limited Phonetic Coverage**: Only substitution micro-benchmarks exist; no end-to-end phonetic operation benchmarks.

### Baseline Data Available

**substitution_set_microbench.rs** (partial results):

```
substitution_set/insertion/char/50     969.89 ns  (51.55 Melem/s)
substitution_set/insertion/char/100    1.8056 µs  (55.38 Melem/s)
substitution_set/insertion/char/500    9.7436 µs  (51.32 Melem/s)
substitution_set/presets/byte/phonetic_basic  317.32 ns
substitution_set/presets/byte/keyboard_qwerty 592.33 ns
```

**Interpretation**: Substitution lookups are very fast (~300-600 ns), suggesting they are NOT the primary bottleneck. The real performance issues are likely in:
- State transition logic
- Successor generation
- Subsumption checks
- Overall automaton traversal

---

## 1.2 Code Analysis Findings

### Critical Hot Paths Identified

Based on static code analysis of `/src/transducer/generalized/`:

#### 1. State::successors_i_type() (state.rs:243-563)
- **Size**: 320 lines (HUGE method)
- **Complexity**: High - handles 4 standard ops + 3 multi-char ops
- **Allocation**: Creates new `Vec<GeneralizedPosition>` for each call
- **Repeated operations**:
  - `word_slice.chars().collect()` - allocates Vec<char>
  - String allocations in `can_apply()` checks
  - Bit vector index bounds checks

#### 2. State::add_position() (state.rs:89-114)
- **Complexity**: O(n) subsumption checks × O(log n) binary search insertion
- **Frequency**: Called for EVERY successor position generated
- **Bottleneck**: With 10-20 positions in state, this becomes O(n²)

#### 3. State::transition() (automaton.rs:154-194)
- **Frequency**: Called for every input character
- **Operations**:
  1. Iterate over all positions in current state
  2. Call `successors()` for each position
  3. Add each successor (triggers subsumption)
  4. Return new state

#### 4. Phonetic Operation Completion
- **successors_i_splitting()**: 193 lines (state.rs:999-1191)
- **successors_m_splitting()**: 91 lines (state.rs:1197-1287)
- **Debug overhead**: Multiple `eprintln!` statements in debug builds

### Estimated Complexity

For a single `accepts()` call with word length W, input length I, distance D:

```
Time Complexity:
  O(I × state_size × (ops + subsumption_cost))

Where:
  - I: input length (typical: 5-15 chars)
  - state_size: positions in state (typical: 5-20, worst: 50+)
  - ops: operations checked (standard: 4, phonetic: ~25)
  - subsumption_cost: O(state_size) per successor

Worst case: O(I × state_size²)
```

**Space Complexity**: O(state_size × sizeof(GeneralizedPosition))

### Allocation Hotspots

1. **Vec allocations**:
   - `successors()`: 1 per position per character
   - `word_chars: Vec<char>`: 1 per successor call
   - `String::from()` / `to_string()`: Multiple per operation check

2. **SmallVec usage**:
   - `State` uses `SmallVec<[GeneralizedPosition; 8]>`
   - Typical state size: 5-15 positions (mostly inline)
   - Large states (20+): Heap overflow

---

## 1.3 Hypotheses for Testing

Based on code analysis, we hypothesize:

### H1: Successor Generation Dominates Runtime
**Hypothesis**: `successors_i_type()` and `successors_m_type()` account for 60-80% of CPU time in `accepts()`.

**Rationale**: These are the largest, most complex methods called for every position at every input character.

**Test**: Flamegraph analysis should show these methods as top hotspots.

---

### H2: Repeated char().collect() Causes 10-15% Overhead
**Hypothesis**: Allocating `Vec<char>` repeatedly for `word_slice.chars().collect()` contributes significant overhead.

**Rationale**: Called multiple times per state transition (once per operation type check).

**Test**: Count allocations; cache the Vec and measure improvement.

**Expected improvement**: 10-15% reduction in allocation count, 5-10% runtime improvement.

---

### H3: Subsumption Creates O(n²) Bottleneck for Large States
**Hypothesis**: `add_position()` subsumption checks create quadratic behavior when states have 20+ positions.

**Rationale**: For N positions, adding M successors requires N×M subsumption checks.

**Test**: Benchmark with controlled state sizes (1, 5, 10, 20, 50 positions).

**Expected**: Superlinear time growth with state size.

---

### H4: String Allocations in can_apply() Add 5-10% Overhead
**Hypothesis**: Converting characters to strings (`to_string()`, `String::from()`) in operation checks adds measurable overhead.

**Rationale**: Called for every operation check, requires heap allocation for owned String.

**Test**: Replace with byte slice operations, measure allocation reduction.

**Expected improvement**: 5-10% reduction in allocations, 3-5% runtime improvement.

---

### H5: Phonetic Operations Cause 2-3x Slowdown
**Hypothesis**: Enabling full phonetic operation set (consonant_digraphs + confusions + clusters) causes 2-3x slowdown vs standard operations only.

**Rationale**:
- Standard operations: 4 operations to check
- Full phonetic: ~20-25 operations to check
- Multi-char operations create intermediate states

**Test**: Benchmark same inputs with standard-only vs full phonetic.

**Expected**: 2-3x runtime increase with phonetic operations.

---

### H6: Phonetic Split Completion is 20-30% Slower Than Standard
**Hypothesis**: Split operations (with word_pos calculation and character extraction) add 20-30% overhead compared to standard operations.

**Rationale**: Additional logic for empty subword handling, word position calculation (Phase 4 fixes).

**Test**: Benchmark inputs with splits vs inputs with substitutions.

**Expected**: Split-heavy inputs 20-30% slower.

---

## 1.4 Benchmark Requirements

To test these hypotheses, we need:

### Priority 1: Core Automaton Benchmarks
- State transition with varying state sizes (1, 5, 10, 20, 50 positions)
- Successor generation (I-type, M-type, standard ops, multi-char ops)
- Subsumption overhead measurement
- Input scenarios (best/worst/average case)

### Priority 2: Phonetic Operation Benchmarks
- Standard operations only
- Standard + consonant_digraphs
- Full phonetic operation set
- Individual multi-char operation types (split, transpose, merge)

### Priority 3: End-to-End Acceptance Benchmarks
- Short words (3-5 chars) at distances 0, 1, 2, 3
- Medium words (6-10 chars) at distances 0, 1, 2, 3
- Long words (11-15 chars) at distances 0, 1, 2, 3
- Phonetic-heavy scenarios (multiple splits, transposes)

### Priority 4: Memory Profiling
- Allocation frequency tracking
- SmallVec heap overflow measurement
- Peak memory usage per accepts() call

---

## Next Steps

1. ✅ **Phase 1.1 Complete**: Existing benchmarks assessed, hypotheses formed
2. ⏳ **Phase 1.2**: Create 4 new benchmark files
3. ⏳ **Phase 1.3**: Generate baseline flamegraphs
4. ⏳ **Phase 1.4**: Document complete hypothesis set (this file)

---

## Conclusion

**Key Finding**: Existing benchmark suite is broken and insufficient. We must create comprehensive new benchmarks to properly measure generalized automaton and phonetic operation performance.

**Hypothesis Priority**:
1. **H1** (Successor generation) - Likely biggest impact
2. **H3** (Subsumption O(n²)) - Critical for large states
3. **H2** (char().collect()) - Easy win
4. **H5** (Phonetic slowdown) - Important for understanding phonetic cost
5. **H4** (String allocations) - Small but measurable
6. **H6** (Split overhead) - Specific to Phase 4 implementation

**Ready to proceed with Phase 1.2**: Creating new benchmark files.
