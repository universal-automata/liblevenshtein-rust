# Phase 3: H2 Optimization Implementation Plan

**Optimization**: Cache Character Vectors (H2)
**Target**: 8.47% of cycles (Iterator::collect 4.08% + cfree 4.39%)
**Expected Improvement**: 5-8% overall speedup
**Effort**: Medium (API changes required)
**Date**: November 18, 2025

---

## Hypothesis

**H2**: Repeated `chars().collect()` calls cause 10-15% overhead

**Evidence from Phase 1**:
- 20 instances of `chars().collect()` found in `state.rs`
- Flamegraph shows:
  - `Iterator::collect`: 4.08% (allocation)
  - `cfree`: 4.39% (deallocation of Vec<char>)
  - **Total**: 8.47% of cycles

**Root Cause**: Every call to successor generation methods allocates a new `Vec<char>` by calling `word_slice.chars().collect()`, which is immediately freed after use.

---

## Optimization Strategy

### Current Flow
```rust
pub fn accepts(&self, word: &str, input: &str) -> bool {
    // ...
    for (i, input_char) in input.chars().enumerate() {
        let subword = self.relevant_subword(word, i + 1);
        state.transition(&self.operations, &bit_vector, word, &subword, input_char, i + 1);
        //                                             ^^^^    ^^^^^^^^
        //                                          Each transition call
        //                                          leads to 20+ chars().collect()
    }
}
```

Inside `transition()` → `successors()` → `successors_i_type()`:
```rust
// This is repeated 20+ times per transition!
let word_chars: Vec<char> = word_slice.chars().collect();
```

### Optimized Flow
```rust
pub fn accepts(&self, word: &str, input: &str) -> bool {
    // Pre-compute ONCE
    let word_chars: Vec<char> = word.chars().collect();

    for (i, input_char) in input.chars().enumerate() {
        let subword = self.relevant_subword(word, i + 1);
        state.transition(&self.operations, &bit_vector, word, &word_chars, &subword, input_char, i + 1);
        //                                                     ^^^^^^^^^^^
        //                                                     Pass cached vector
    }
}
```

Inside successor methods:
```rust
// Use slice instead of re-allocating!
// Before: let word_chars: Vec<char> = word_slice.chars().collect();
// After:  Just use word_chars[start..end] directly
```

---

## Implementation Steps

### Step 1: Update `GeneralizedAutomaton::accepts()` ✅

**File**: `src/transducer/generalized/automaton.rs`
**Location**: Line 292

**Changes**:
1. Add `let word_chars: Vec<char> = word.chars().collect();` after line 326
2. Pass `&word_chars` to `state.transition()` call at line 348

**Signature change**: None (internal only)

---

### Step 2: Update `GeneralizedState::transition()`

**File**: `src/transducer/generalized/state.rs`
**Location**: ~line 136 (based on earlier read)

**Changes**:
1. Add parameter: `word_chars: &[char]`
2. Pass `word_chars` to `self.successors()` call

**Signature**:
```rust
// Before
pub fn transition(
    &self,
    operations: &OperationSet,
    bit_vector: &CharacteristicVector,
    full_word: &str,
    word_slice: &str,
    input_char: char,
    query_length: usize,
) -> Option<Self>

// After
pub fn transition(
    &self,
    operations: &OperationSet,
    bit_vector: &CharacteristicVector,
    full_word: &str,
    word_chars: &[char],  // NEW: pre-computed character vector
    word_slice: &str,
    input_char: char,
    query_length: usize,
) -> Option<Self>
```

---

### Step 3: Update `GeneralizedState::successors()`

**File**: `src/transducer/generalized/state.rs`

**Changes**:
1. Add parameter: `word_chars: &[char]`
2. Pass to all successor type methods:
   - `successors_d_type()`
   - `successors_i_type()` ← **Main target (2.75% of cycles)**
   - `successors_s_type()`
   - `successors_t_type()`

**Signature**:
```rust
// Before
pub fn successors(
    &self,
    operations: &OperationSet,
    bit_vector: &CharacteristicVector,
    full_word: &str,
    word_slice: &str,
    input_char: char,
    query_length: usize,
) -> Self

// After
pub fn successors(
    &self,
    operations: &OperationSet,
    bit_vector: &CharacteristicVector,
    full_word: &str,
    word_chars: &[char],  // NEW
    word_slice: &str,
    input_char: char,
    query_length: usize,
) -> Self
```

---

### Step 4: Update `successors_i_type()` ← **CRITICAL**

**File**: `src/transducer/generalized/state.rs`
**Location**: Large method (~320 lines), contains most char().collect() calls

**Changes**:
1. Add parameter: `word_chars: &[char]`
2. Replace ALL instances of:
   ```rust
   let word_chars: Vec<char> = word_slice.chars().collect();
   ```
   With character vector slicing based on position in word

**Challenge**: Need to map `word_slice` positions to indices in `word_chars`

**Approach**:
- Calculate slice offset from `word_slice.as_ptr()` vs `full_word.as_ptr()`
- Or: Pass start/end indices explicitly

---

### Step 5: Update other successor methods

**Files**: `src/transducer/generalized/state.rs`
**Methods**:
- `successors_d_type()` - DELETE operations
- `successors_s_type()` - SUBSTITUTE operations
- `successors_t_type()` - TRANSPOSE operations (phonetic)

**Changes**: Same as Step 4 - add `word_chars` parameter and replace char().collect()

---

### Step 6: Update `CharacteristicVector` usage (if needed)

**File**: `src/transducer/generalized/bit_vector.rs`
**Locations**: Lines 350, 418

**Analysis Needed**: Check if CharacteristicVector also benefits from character vector caching.

---

### Step 7: Run Tests

**Command**:
```bash
RUSTFLAGS="-C target-cpu=native" cargo test
```

**Expected**: All 725+ tests pass

**If failures**: Debug and fix signature mismatches

---

### Step 8: Run Benchmarks

**Command**:
```bash
RUSTFLAGS="-C target-cpu=native" taskset -c 0 cargo bench --bench generalized_automaton_benchmarks
```

**Expected Improvement**:
- 5-8% reduction in total time
- Significant reduction in allocation count (if measurable)

**Output**: `docs/optimization/optimized_h2_generalized_automaton.txt`

---

### Step 9: Generate New Flamegraph

**Command**:
```bash
RUSTFLAGS="-C target-cpu=native" taskset -c 0 cargo flamegraph \
  --bench generalized_automaton_benchmarks \
  --output docs/optimization/flamegraphs/optimized_h2.svg -- --bench
```

**Analysis**:
- Compare to `baseline_standard.svg`
- `Iterator::collect` should drop from 4.08% to near 0%
- `cfree` should drop from 4.39% correspondingly
- New hotspots may emerge

---

### Step 10: Document Results

**File**: `docs/optimization/PHASE3_H2_RESULTS.md`

**Contents**:
1. Hypothesis validation
2. Before/after benchmark comparison
3. Flamegraph analysis
4. Actual vs expected improvement
5. Lessons learned
6. Next optimization target

---

## Potential Challenges

### Challenge 1: Subword Slicing
**Issue**: `word_slice` is a substring of `word`, but we need indices into `word_chars`

**Solutions**:
1. **Option A**: Calculate byte offset and convert to char index
   ```rust
   let byte_offset = word_slice.as_ptr() as usize - word.as_ptr() as usize;
   let char_offset = word[..byte_offset].chars().count();
   ```

2. **Option B**: Pass explicit indices
   ```rust
   // In accepts():
   let (start_idx, end_idx) = self.relevant_subword_indices(word, i + 1);
   let subword_chars = &word_chars[start_idx..end_idx];
   ```

**Recommendation**: Option B (cleaner, more explicit)

### Challenge 2: Phonetic Operations
**Issue**: Some operations use `full_word.chars().collect()` for lookups

**Solution**: Also pass full `word_chars` and use slicing

### Challenge 3: API Compatibility
**Issue**: Changing public API signatures

**Solution**: These are internal methods (not pub), so no external API break

---

## Success Criteria

**Minimum**:
- [ ] All tests pass
- [ ] 3-5% overall speedup in benchmarks
- [ ] Iterator::collect drops to < 1%

**Target**:
- [ ] 5-8% overall speedup
- [ ] cfree + Iterator::collect combined < 2%
- [ ] No performance regressions on any benchmark

**Stretch**:
- [ ] 8-10% speedup
- [ ] Allocation elimination visible in memory profiling

---

## Rollback Plan

If optimization fails or causes issues:
1. Git branch: Create `optimization-h2` branch before changes
2. If tests fail: Debug incrementally, one method at a time
3. If benchmarks regress: Revert and analyze why
4. Document failure in PHASE3_H2_RESULTS.md

---

## Timeline

**Estimated**: 2-3 hours
- Step 1-3: 30 min (simple parameter passing)
- Step 4-5: 60-90 min (bulk replacements + index calculations)
- Step 6-7: 30 min (testing + debugging)
- Step 8-10: 30-60 min (benchmarking + documentation)

---

## Implementation Notes

**Start**: Ready to begin
**Dependencies**: None (Phase 1 complete)
**Blockers**: None identified

**First Action**: Create git branch `optimization-h2` and begin Step 1

---

**Status**: ⏳ Ready to implement
**Next**: Create git branch and start Step 1
