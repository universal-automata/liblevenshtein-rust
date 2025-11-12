# Diagonal Crossing Bug Analysis and Fix Plan

**Date**: 2025-11-12
**Status**: 🐛 **CRITICAL BUG** - Documented, fix planned but not implemented
**Affected Component**: Universal Levenshtein Automata (`src/transducer/universal/state.rs:310-360`)
**Current State**: Diagonal crossing logic **disabled** (commented out) to prevent invalid conversions

---

## Executive Summary

The universal Levenshtein automaton implementation has a critical bug in diagonal crossing detection that causes **premature I-type to M-type position conversions**, violating position invariants and producing incorrect results. The diagonal crossing logic is currently disabled (lines 310-360 in `state.rs`) to prevent these invalid conversions.

**Root Cause**: Missing explicit `length_diff` (m) tracking in state representation
**Impact**: Universal automaton cannot correctly detect when to convert I → M positions
**Workaround**: Diagonal crossing disabled; automaton still functional but may have suboptimal performance
**Fix Complexity**: High - requires architectural changes to state representation and API

---

## Table of Contents

1. [Background: What is Diagonal Crossing?](#1-background-what-is-diagonal-crossing)
2. [The Bug: Symptoms and Behavior](#2-the-bug-symptoms-and-behavior)
3. [Root Cause Analysis](#3-root-cause-analysis)
4. [Current Implementation (Disabled)](#4-current-implementation-disabled)
5. [Proposed Fix: Add length_diff Tracking](#5-proposed-fix-add-length_diff-tracking)
6. [Implementation Plan](#6-implementation-plan)
7. [Testing Strategy](#7-testing-strategy)
8. [Alternative Approaches](#8-alternative-approaches)
9. [References](#9-references)

---

## 1. Background: What is Diagonal Crossing?

### Theoretical Foundation

From TCS 2011 paper (Section 9.2, Pages 2350-2352):

**Diagonal**: In the edit distance dynamic programming matrix, the diagonal represents positions where `|query_word| - |dict_word| = 0` (words have equal length prefix processed).

**Diagonal Crossing**: When processing transitions, if positions "cross" the diagonal (length difference exceeds bounds), they must be **converted** from I-type (non-final) to M-type (final) or vice versa.

**Why It Matters**:
- I-type positions represent "before reaching word end" (non-final)
- M-type positions represent "at or past word end" (final)
- Crossing the diagonal means the automaton has processed enough characters to determine finality

### Key Functions (from thesis)

**f_n**: Diagonal crossing check
```
For I-type: f_n(I + i#e, k) = (k ≤ 2n+1) ∧ (e ≤ i + 2n + 1 - k)
For M-type: f_n(M + i#e, k) = e > i + n
```

**m_n**: Position conversion
```
I → M: m_n(I + i#e, k) = M + (i + n + 1 - k)#e
M → I: m_n(M + i#e, k) = I + (i - n - 1 + k)#e
```

**rm**: Right-most position (maximum e - i)

**Transition Process** (Definition 15, Page 48):
```
δ^∀,χ_n(Q, x) = {
    Δ               if f_n(rm(Δ), |x|) = false
    m_n(Δ, |x|)     if f_n(rm(Δ), |x|) = true
}
where Δ = ⊔_{π∈Q} δ^∀,χ_e(π, x)
```

Translation: After computing successors (Δ), check if rightmost position crossed diagonal. If yes, convert all positions using m_n.

---

## 2. The Bug: Symptoms and Behavior

### Observed Symptoms

1. **Premature Conversions**: I-type positions converted to M-type too early
2. **Invariant Violations**: Converted positions violate M-type invariants (offset > 0, etc.)
3. **Empty States**: After conversion, some states become empty (all positions invalid)
4. **Incorrect Results**: Queries produce wrong distance calculations

### Example Failure Case

```rust
// Initial state: {I + 0#0}
let state = UniversalState::<Standard>::initial(2);

// Transition on bit vector "100" (match at position 0)
let bit_vector = CharacteristicVector::new('a', "abc");
let next = state.transition(&bit_vector, 1);

// BUG: Diagonal crossing check returns true at k=1
// Attempts to convert I + 0#0 → M + (0 + 2 + 1 - 1)#0 = M + 2#0
// M + 2#0 violates invariant: offset > 0 for M-type
// Conversion fails, returns None, state becomes empty
```

**Expected Behavior**: State should remain I-type until actually reaching word boundary.

**Actual Behavior**: Premature conversion attempt, invalid position, empty state.

### Code Location

**File**: `src/transducer/universal/state.rs:310-360`

```rust
// Diagonal crossing check: f_n(rm(Δ), |x|)
//
// NOTE: Currently this is producing invalid position conversions in some cases.
// The diagonal crossing functions (rm, f_n, m_n) are fully implemented and tested,
// but the integration here needs adjustment based on actual word/input lengths.
// Keeping this commented out until Phase 4 provides proper context.

// TODO: Diagonal crossing integration needs fixing
// The diagonal crossing logic is causing premature conversions that violate invariants.
// Disabling for now until the proper semantics are understood.
// See PHASE4_BUG_ANALYSIS.md for details.

/*
if let Some(rm_pos) = crate::transducer::universal::diagonal::right_most(
    next_state.positions()
) {
    if crate::transducer::universal::diagonal::diagonal_crossed(
        &rm_pos,
        input_length,
        self.max_distance,
    ) {
        // Apply m_n conversion to all positions
        let mut converted_state = Self::new(self.max_distance);
        for pos in &next_state.positions {
            if let Some(converted) =
                crate::transducer::universal::diagonal::convert_position(
                    pos,
                    input_length,
                    self.max_distance,
                )
            {
                converted_state.add_position(converted);
            }
        }

        // Only use converted state if it's non-empty
        if !converted_state.is_empty() {
            next_state = converted_state;
        }
    }
}
*/
```

---

## 3. Root Cause Analysis

### Missing Context: Word Length Difference

The **fundamental problem** is that the current implementation lacks explicit tracking of the **length difference** between the two words being compared.

**From Paper** (Section 9.2, Page 2351):

The universal automaton state must track:
- `m`: Length difference between words (|w₁| - |w₂|)
- `m ∈ [-c, +c]` where c is the diagonal bound

**Current Implementation**:
```rust
pub struct UniversalState<V: PositionVariant> {
    positions: SmallVec<[UniversalPosition<V>; 8]>,
    max_distance: u8,  // ← Only has 'n', not 'm'
}
```

**Missing**: `length_diff: i8` field to track m

### Why `input_length` Parameter Isn't Sufficient

The `transition()` method currently receives:
```rust
pub fn transition(&self, bit_vector: &CharacteristicVector, input_length: usize) -> Option<Self>
```

**Problem**: `input_length` (k) alone doesn't provide enough information:
- k = current input position (characters processed from first word)
- But we also need word lengths to compute m = |w₁| - |w₂|

**What's Needed**:
```
m = |w₁| - k  (remaining length in second word)
```

But we don't have |w₁| available in the transition!

### Why Diagonal Crossing Fails

**Formula**: `f_n(I + i#e, k) = (k ≤ 2n+1) ∧ (e ≤ i + 2n + 1 - k)`

**Issue**: This formula assumes k is correctly calibrated with word context, but:
1. k is incremented on each character consumed from query
2. But the formula needs to know relationship to actual word boundary
3. Without m tracking, we can't determine if we've truly crossed diagonal

**Example**:
```
Query: "abc" (length 3)
Dict:  "ab"  (length 2)
m = 3 - 2 = 1 (query is 1 character longer)

At k=2 (processed "ab"):
- Without m: Can't tell if we're at boundary
- With m: Know query has 1 remaining, dict has 0 → crossed diagonal
```

---

## 4. Current Implementation (Disabled)

### Diagonal Module (Correct Implementation)

**File**: `src/transducer/universal/diagonal.rs`

All three functions (rm, f_n, m_n) are **correctly implemented** per paper formulas:

```rust
/// Find right-most position (maximum e - i)
pub fn right_most<'a, V: PositionVariant>(
    positions: impl Iterator<Item = &'a UniversalPosition<V>>
) -> Option<UniversalPosition<V>> {
    positions.max_by_key(|pos| {
        let offset = pos.offset();
        let errors = pos.errors() as i32;
        errors - offset  // e - i
    }).cloned()
}

/// Check if diagonal crossed
pub fn diagonal_crossed<V: PositionVariant>(
    pos: &UniversalPosition<V>,
    k: usize,
    max_distance: u8,
) -> bool {
    match pos {
        UniversalPosition::INonFinal { .. } => {
            // f_n(I + i#e, k) = (k ≤ 2n+1) ∧ (e ≤ i + 2n + 1 - k)
            (k <= 2 * n + 1) && (errors <= offset + 2 * n + 1 - k)
        }
        UniversalPosition::MFinal { .. } => {
            // f_n(M + i#e, k) = e > i + n
            errors > offset + n
        }
    }
}

/// Convert position (I → M or M → I)
pub fn convert_position<V: PositionVariant>(
    pos: &UniversalPosition<V>,
    k: usize,
    max_distance: u8,
) -> Option<UniversalPosition<V>> {
    match pos {
        UniversalPosition::INonFinal { .. } => {
            // I → M: m_n(I + i#e, k) = M + (i + n + 1 - k)#e
            let new_offset = offset + n + 1 - k;
            UniversalPosition::new_m(new_offset, errors, max_distance).ok()
        }
        UniversalPosition::MFinal { .. } => {
            // M → I: m_n(M + i#e, k) = I + (i - n - 1 + k)#e
            let new_offset = offset - n - 1 + k;
            UniversalPosition::new_i(new_offset, errors, max_distance).ok()
        }
    }
}
```

**Status**: ✅ **Formulas correct, tests passing**

### Integration Issue (Buggy)

The problem is in `state.rs` where these functions are called:

```rust
pub fn transition(&self, bit_vector: &CharacteristicVector, _input_length: usize) -> Option<Self> {
    // ... compute successors ...

    // BUG: This integration is incorrect
    // We use input_length as 'k', but it doesn't have proper word context
    // This causes diagonal_crossed() to return true too early

    // [DISABLED CODE]
}
```

**Status**: 🐛 **Integration buggy, disabled**

---

## 5. Proposed Fix: Add length_diff Tracking

### Modified State Structure

**File**: `src/transducer/universal/state.rs`

```rust
/// Universal state with diagonal tracking
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct UniversalState<V: PositionVariant> {
    /// Set of positions (anti-chain)
    positions: SmallVec<[UniversalPosition<V>; 8]>,

    /// Maximum edit distance n
    max_distance: u8,

    /// NEW: Length difference m = |w₁| - |w₂|
    /// Range: [-max_distance, +max_distance]
    /// This tracks position relative to diagonal
    length_diff: i8,
}
```

**Invariant**: `|length_diff| ≤ max_distance` (bounded diagonal property)

### Modified Transition API

**Option 1: Pass Word Lengths**

```rust
pub fn transition(
    &self,
    bit_vector: &CharacteristicVector,
    query_pos: usize,           // Position in query word
    query_length: usize,         // Total query length (NEW)
    dict_length: usize,          // Total dict word length (NEW)
) -> Option<Self> {
    // Compute current length difference
    let query_remaining = query_length - query_pos;
    let dict_remaining = dict_length - query_pos;  // Approximate
    let m = query_remaining as i32 - dict_remaining as i32;

    // ... rest of transition logic ...
}
```

**Option 2: Update length_diff Incrementally**

```rust
pub fn transition(
    &self,
    bit_vector: &CharacteristicVector,
    consumed_query: bool,       // Did we consume query char?
    consumed_dict: bool,        // Did we consume dict char?
) -> Option<Self> {
    // Update length difference based on what was consumed
    let new_length_diff = self.length_diff + {
        match (consumed_query, consumed_dict) {
            (true, true) => 0,   // Both consumed, diff unchanged
            (true, false) => -1, // Query consumed, dict didn't → query shorter
            (false, true) => 1,  // Dict consumed, query didn't → query longer
            (false, false) => 0, // Neither consumed (impossible?)
        }
    };

    // ... rest of transition logic ...
}
```

**Recommendation**: Option 2 is cleaner and doesn't require external word context.

### Modified Diagonal Crossing Check

With explicit m tracking, diagonal crossing becomes simpler:

```rust
/// Check if diagonal crossed using state's length_diff
pub fn diagonal_crossed_with_m(
    state: &UniversalState<V>,
    max_distance: u8,
) -> bool {
    let c = max_distance as i32;

    // Crossed if length difference exceeds bounds
    state.length_diff.abs() > c
}
```

Or integrate into existing check:

```rust
pub fn diagonal_crossed<V: PositionVariant>(
    pos: &UniversalPosition<V>,
    length_diff: i32,  // Use state's length_diff instead of k
    max_distance: u8,
) -> bool {
    let c = max_distance as i32;

    match pos {
        UniversalPosition::INonFinal { .. } => {
            // Simplified: check if we've exceeded diagonal bounds
            length_diff.abs() > c || errors > offset + c
        }
        UniversalPosition::MFinal { .. } => {
            // M-type already past diagonal
            errors > offset + c
        }
    }
}
```

---

## 6. Implementation Plan

### Phase 1: Add length_diff Field (Breaking Change)

**Files to Modify**:
1. `src/transducer/universal/state.rs`
2. `src/transducer/universal/automaton.rs` (if needed)
3. All test files that construct `UniversalState`

**Changes**:

```rust
// state.rs
pub struct UniversalState<V: PositionVariant> {
    positions: SmallVec<[UniversalPosition<V>; 8]>,
    max_distance: u8,
    length_diff: i8,  // NEW
}

impl<V: PositionVariant> UniversalState<V> {
    pub fn new(max_distance: u8) -> Self {
        Self {
            positions: SmallVec::new(),
            max_distance,
            length_diff: 0,  // Start at diagonal
        }
    }

    pub fn initial(max_distance: u8) -> Self {
        let mut state = Self::new(max_distance);
        let initial_pos = UniversalPosition::new_i(0, 0, max_distance)
            .expect("I + 0#0 should always be valid");
        state.positions.push(initial_pos);
        state.length_diff = 0;  // Initially on diagonal
        state
    }

    /// Get current length difference
    pub fn length_diff(&self) -> i8 {
        self.length_diff
    }
}
```

**Testing**: Update all unit tests to handle new field.

### Phase 2: Update Transition Logic

**File**: `src/transducer/universal/state.rs:280-368`

```rust
pub fn transition(
    &self,
    bit_vector: &CharacteristicVector,
    consumed_query: bool,
    consumed_dict: bool,
) -> Option<Self> {
    if self.is_empty() {
        return None;
    }

    // Create new state preserving length_diff
    let mut next_state = Self::new(self.max_distance);

    // Update length difference based on consumption
    next_state.length_diff = self.length_diff + match (consumed_query, consumed_dict) {
        (true, true) => 0,
        (true, false) => -1,
        (false, true) => 1,
        (false, false) => 0,
    };

    // Compute successors Δ
    for pos in &self.positions {
        let successors = pos.successors(bit_vector, self.max_distance);
        for succ in successors {
            next_state.add_position(succ);
        }
    }

    if next_state.is_empty() {
        return None;
    }

    // Diagonal crossing check with length_diff
    if next_state.length_diff.abs() > self.max_distance as i32 {
        // Apply m_n conversion
        let mut converted_state = Self::new(self.max_distance);
        converted_state.length_diff = next_state.length_diff;

        for pos in &next_state.positions {
            // Use simplified conversion (no k parameter needed)
            if let Some(converted) = convert_position_with_m(pos, next_state.length_diff, self.max_distance) {
                converted_state.add_position(converted);
            }
        }

        if !converted_state.is_empty() {
            next_state = converted_state;
        }
    }

    if next_state.is_empty() {
        None
    } else {
        Some(next_state)
    }
}
```

### Phase 3: Update Diagonal Module

**File**: `src/transducer/universal/diagonal.rs`

Add new functions that use length_diff instead of k:

```rust
/// Convert position using length difference
pub fn convert_position_with_m<V: PositionVariant>(
    pos: &UniversalPosition<V>,
    length_diff: i32,
    max_distance: u8,
) -> Option<UniversalPosition<V>> {
    match pos {
        UniversalPosition::INonFinal { .. } => {
            // Simplified: I → M based on length_diff
            let new_offset = offset + (max_distance as i32 - length_diff);
            UniversalPosition::new_m(new_offset, errors, max_distance).ok()
        }
        UniversalPosition::MFinal { .. } => {
            // M → I
            let new_offset = offset - (max_distance as i32 - length_diff);
            UniversalPosition::new_i(new_offset, errors, max_distance).ok()
        }
    }
}
```

**Keep existing functions** for backward compatibility.

### Phase 4: Update Call Sites

**Files to Update**:
- `src/transducer/universal/automaton.rs` - High-level automaton API
- All test files in `src/transducer/universal/`
- Benchmarks if any

**API Change**: Callers must now specify what was consumed:

```rust
// Before:
let next = state.transition(&bit_vector, input_pos);

// After:
let next = state.transition(&bit_vector, consumed_query, consumed_dict);
```

### Phase 5: Comprehensive Testing

**Test Categories**:

1. **Unit Tests**: Verify length_diff updates correctly
   ```rust
   #[test]
   fn test_length_diff_tracking() {
       let state = UniversalState::<Standard>::initial(2);
       assert_eq!(state.length_diff(), 0);

       let next = state.transition(&bv, true, true);
       assert_eq!(next.unwrap().length_diff(), 0);  // Both consumed

       let next2 = next.transition(&bv2, true, false);
       assert_eq!(next2.unwrap().length_diff(), -1);  // Query consumed
   }
   ```

2. **Diagonal Crossing Tests**: Verify conversions happen at right time
   ```rust
   #[test]
   fn test_diagonal_crossing_with_length_diff() {
       // Set up state that should cross diagonal
       // Verify I → M conversion happens correctly
   }
   ```

3. **Regression Tests**: Verify existing functionality still works
4. **Property Tests**: Random word pairs, verify distance calculations match DP

---

## 7. Testing Strategy

### Test Plan Structure

```
tests/
  universal/
    diagonal_crossing/
      unit_tests.rs           # Test individual functions
      integration_tests.rs    # End-to-end transition tests
      property_tests.rs       # Random testing with DP oracle
      regression_tests.rs     # Known failure cases
```

### Critical Test Cases

#### Test 1: Basic Diagonal Crossing

```rust
#[test]
fn test_basic_diagonal_crossing() {
    // Query: "ab" (length 2)
    // Dict:  "abc" (length 3)
    // m = 2 - 3 = -1 (dict is longer)

    let mut state = UniversalState::<Standard>::initial(2);
    assert_eq!(state.length_diff(), 0);

    // Process 'a' (both consume)
    let bv1 = CharacteristicVector::new('a', "abc");
    state = state.transition(&bv1, true, true).unwrap();
    assert_eq!(state.length_diff(), 0);

    // Process 'b' (both consume)
    let bv2 = CharacteristicVector::new('b', "abc");
    state = state.transition(&bv2, true, true).unwrap();
    assert_eq!(state.length_diff(), 0);

    // Process 'c' (dict consumes, query doesn't - at query end)
    let bv3 = CharacteristicVector::new('c', "abc");
    state = state.transition(&bv3, false, true).unwrap();
    assert_eq!(state.length_diff(), 1);  // Dict is now 1 longer

    // Should have M-type positions now
    assert!(state.positions().any(|p| p.is_m_type()));
}
```

#### Test 2: Premature Conversion Prevention

```rust
#[test]
fn test_no_premature_conversion() {
    // Verify that I → M conversion doesn't happen too early
    let state = UniversalState::<Standard>::initial(2);

    // Process first character (shouldn't convert)
    let bv = CharacteristicVector::new('a', "abc");
    let next = state.transition(&bv, true, true).unwrap();

    // Should still have I-type positions
    assert!(next.positions().all(|p| p.is_i_type()));
    assert_eq!(next.length_diff(), 0);
}
```

#### Test 3: Distance Calculation Accuracy

```rust
#[test]
fn test_distance_matches_dp() {
    // Compare universal automaton distance with dynamic programming
    let test_cases = vec![
        ("kitten", "sitting", 3),
        ("abc", "def", 3),
        ("", "abc", 3),
        ("abc", "", 3),
    ];

    for (query, dict, expected_dist) in test_cases {
        let computed = universal_levenshtein_distance(query, dict, 3);
        assert_eq!(computed, expected_dist);
    }
}
```

---

## 8. Alternative Approaches

### Alternative 1: Stateless Diagonal Check

Instead of tracking length_diff in state, compute it on-demand:

**Pros**:
- No state structure changes
- Backward compatible

**Cons**:
- Requires passing word lengths to transition()
- Less efficient (recompute each time)
- Doesn't match paper's state model

**Verdict**: ❌ **Not recommended** - Paper explicitly models m as part of state

### Alternative 2: Delayed Diagonal Crossing

Only check diagonal crossing when reaching final states:

**Pros**:
- Simpler implementation
- Fewer conversions

**Cons**:
- Doesn't match paper's algorithm
- May produce incorrect intermediate states
- Unclear correctness guarantees

**Verdict**: ❌ **Not recommended** - Deviates from proven algorithm

### Alternative 3: Hybrid Approach (Phase-In)

Implement length_diff tracking but keep old API with default behavior:

```rust
impl<V: PositionVariant> UniversalState<V> {
    // New API with explicit consumption
    pub fn transition_with_consumption(
        &self,
        bit_vector: &CharacteristicVector,
        consumed_query: bool,
        consumed_dict: bool,
    ) -> Option<Self> {
        // Full implementation with length_diff
    }

    // Old API (deprecated) - assumes both consumed
    #[deprecated(note = "Use transition_with_consumption instead")]
    pub fn transition(
        &self,
        bit_vector: &CharacteristicVector,
        _input_length: usize,
    ) -> Option<Self> {
        self.transition_with_consumption(bit_vector, true, true)
    }
}
```

**Pros**:
- Gradual migration path
- Backward compatible
- Can test new implementation alongside old

**Cons**:
- API duplication
- Deprecation warnings
- More code to maintain

**Verdict**: ✅ **Recommended for migration** - Smooth transition path

---

## 9. References

### Primary Sources

1. **TCS 2011 Paper**:
   - Mitankin, P., Mihov, S., Schulz, K.U. (2011). "Deciding Word Neighborhood with Universal Neighborhood Automata". *Theoretical Computer Science*, 410(37-39):2339-2358.
   - Section 9.2 (Pages 2350-2352): Diagonal crossing algorithms
   - Definition 15 (Page 48): Universal state transition δ^∀,χ_n

2. **Mitankin Thesis (2005)**:
   - Pages 42-45: Diagonal crossing functions (f_n, m_n, rm)
   - Page 48: State transition with diagonal check

### Related Documentation

1. [TCS_2011_PAPER_ANALYSIS.md](./TCS_2011_PAPER_ANALYSIS.md) - Section 8
2. [TCS_2011_IMPLEMENTATION_MAPPING.md](./TCS_2011_IMPLEMENTATION_MAPPING.md) - Section 8
3. [THEORETICAL_FOUNDATIONS.md](./THEORETICAL_FOUNDATIONS.md) - Diagonal property

### Code References

**Current Implementation**:
- `src/transducer/universal/state.rs:310-360` - Disabled diagonal crossing
- `src/transducer/universal/diagonal.rs` - Correct formulas (rm, f_n, m_n)
- `src/transducer/universal/position.rs` - Position types and invariants

**Tests**:
- `src/transducer/universal/diagonal.rs:201-376` - Unit tests (passing)
- `src/transducer/universal/state.rs:386-910` - State transition tests

---

## Status and Next Steps

### Current Status

- 🐛 **Bug**: Documented and analyzed
- 📋 **Fix Plan**: Detailed implementation plan created
- ⏸️ **Implementation**: Pending (requires architectural changes)
- ✅ **Workaround**: Diagonal crossing disabled, automaton still functional

### Recommended Next Steps

1. **Review this document** with project stakeholders
2. **Get approval** for breaking API changes
3. **Create feature branch**: `fix/diagonal-crossing-bug`
4. **Implement Phase 1**: Add length_diff field
5. **Run full test suite** to identify all breaking changes
6. **Implement Phases 2-4**: Update transition logic, diagonal module, call sites
7. **Add comprehensive tests** (Phase 5)
8. **Benchmark performance**: Verify no regressions
9. **Update documentation**: API changes, migration guide
10. **Merge to main** after review

### Estimated Effort

- **Implementation**: 2-3 days
- **Testing**: 1-2 days
- **Documentation**: 1 day
- **Review/QA**: 1 day
- **Total**: ~5-7 days

### Prerequisites

- Approval for breaking API changes
- Test infrastructure for property testing (DP oracle)
- Benchmark suite for performance validation

---

**Document Version**: 1.0
**Last Updated**: 2025-11-12
**Author**: Claude Code (Anthropic AI Assistant)
**Status**: 📋 **PLANNING COMPLETE** - Ready for implementation approval
