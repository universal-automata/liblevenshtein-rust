# Phase 3b Requirements - Phonetic Split & Transpose Operations

**Date**: 2025-11-13
**Status**: 📋 **PLANNED** - Not Yet Started
**Prerequisites**: Phase 3a Complete ✅

---

## Overview

Phase 3b extends phonetic operation support to include split ⟨1,2⟩ and transpose ⟨2,2⟩ operations. These multi-step operations require architectural changes to the completion functions to support phonetic validation with `can_apply()`.

**Key Challenges**:
1. Completion functions currently only receive `bit_vector`
2. Phonetic validation requires `operations`, `word_slice`, and input characters
3. Split/transpose span multiple input positions

---

## Operations to Implement

### 1. Split ⟨1,2⟩ Phonetic Operations

**Examples**:
```
"k" → "ch"  (work → worch)
"s" → "sh"  (ruse → rushe)
"f" → "ph"  (graf → graph)
"t" → "th"  (bat → bath)
```

**Semantics**:
- Consume 1 word character
- Match 2 input characters
- Two-step operation: enter splitting state, then complete

**Current Implementation** (Phase 2d):
```rust
// Enter split: check first char matches
if bit_vector.is_match(match_index) {
    enter_splitting_state(offset-1, errors+1);
}

// Complete split (next input): check second char matches
if bit_vector.is_match(match_index) {
    complete_split(offset, errors-1);
}
```

**Required for Phonetic**:
```rust
// Enter split: check if operation can apply to (word_char, input_char1)
let word_char = word_slice.chars().nth(match_index);
let input_char1 = current_input_char;

for op in operations where op.consume_x() == 1 && op.consume_y() == 2 {
    if can_start_split(op, word_char, input_char1) {
        // Store operation ID in splitting state
        enter_splitting_state(offset-1, errors+weight, op_id);
    }
}

// Complete split (next input): validate with second char
let input_char2 = current_input_char;
let op = retrieve_operation(op_id);
if op.can_apply([word_char], [input_char1, input_char2]) {
    complete_split(offset, errors-weight);
}
```

**Problem**: Splitting states don't currently store operation IDs or first input character.

### 2. Transpose ⟨2,2⟩ Phonetic Operations

**Examples**:
```
"qu" → "kw"  (queen → kween)
"kw" → "qu"  (kwik → quik)
```

**Semantics**:
- Consume 2 word characters
- Match 2 input characters (potentially swapped)
- Two-step operation: enter transposing state, then complete

**Current Implementation** (Phase 2d):
```rust
// Enter transpose: check first char matches at next position
if bit_vector.is_match(next_match_index) {
    enter_transposing_state(offset-1, errors+1);
}

// Complete transpose: check second char matches at current position
if bit_vector.is_match(match_index) {
    complete_transpose(offset+1, errors-1);
}
```

**Required for Phonetic**:
```rust
// Enter transpose: check first word char and input char
let word_chars = word_slice[match_index..match_index+2];
let input_char1 = current_input_char;

for op in operations where op.consume_x() == 2 && op.consume_y() == 2 {
    if can_start_transpose(op, word_chars[0], input_char1) {
        enter_transposing_state(offset-1, errors+weight, op_id);
    }
}

// Complete transpose: validate with second chars
let input_char2 = current_input_char;
let op = retrieve_operation(op_id);
if op.can_apply(word_chars, [input_char1, input_char2]) {
    complete_transpose(offset+1, errors-weight);
}
```

**Problem**: Same as split - need to pass operations and characters to completion.

---

## Architectural Changes Required

### Change 1: Update Splitting/Transposing Position Types

**Current**:
```rust
pub enum GeneralizedPosition {
    ISplitting { offset: i32, errors: u8 },
    ITransposing { offset: i32, errors: u8 },
    // ...
}
```

**Option A - Store Operation in Position** (Stateful):
```rust
pub enum GeneralizedPosition {
    ISplitting {
        offset: i32,
        errors: u8,
        operation: OperationType,        // NEW: store operation for validation
        first_input_char: char,          // NEW: store first char
    },
    ITransposing {
        offset: i32,
        errors: u8,
        operation: OperationType,        // NEW
        word_chars: (char, char),        // NEW
        first_input_char: char,          // NEW
    },
    // ...
}
```

**Pros**:
- Self-contained validation
- No signature changes to completion functions
- Clear which operation is being completed

**Cons**:
- Increases position size significantly
- Breaks subsumption logic (can't compare positions with different operations)
- Complicates position equality checks

**Option B - Pass Context to Completion Functions** (Stateless):
```rust
// Current signatures
fn successors_i_splitting(
    offset: i32,
    errors: u8,
    bit_vector: &CharacteristicVector,
) -> Vec<GeneralizedPosition>

fn successors_i_transposing(
    offset: i32,
    errors: u8,
    bit_vector: &CharacteristicVector,
) -> Vec<GeneralizedPosition>

// New signatures
fn successors_i_splitting(
    offset: i32,
    errors: u8,
    operations: &OperationSet,          // NEW
    bit_vector: &CharacteristicVector,
    word_slice: &str,                   // NEW
    input_char: char,                   // NEW
    _input_length: usize,
) -> Vec<GeneralizedPosition>

fn successors_i_transposing(
    offset: i32,
    errors: u8,
    operations: &OperationSet,          // NEW
    bit_vector: &CharacteristicVector,
    word_slice: &str,                   // NEW
    input_char: char,                   // NEW
    _input_length: usize,
) -> Vec<GeneralizedPosition>
```

**Pros**:
- No position size increase
- Maintains subsumption logic
- Consistent with other successor functions
- Standard pattern already used for regular successors

**Cons**:
- Need to pass previous input char somehow
- More parameters to pass through

**Recommendation**: **Option B** - Pass context to completion functions

### Change 2: Buffer Previous Input Character

**Problem**: At completion time, need to validate against both input characters, but only current char is available.

**Solution - Store in State**:
```rust
pub struct GeneralizedState {
    positions: Vec<GeneralizedPosition>,
    max_distance: u8,
    previous_input_char: Option<char>,  // NEW: track previous char
}
```

Update transition logic:
```rust
pub fn transition(
    &self,
    operations: &OperationSet,
    bit_vector: &CharacteristicVector,
    word_slice: &str,
    input_char: char,
    input_length: usize,
) -> Option<Self> {
    // ... generate successors ...

    let mut new_state = Self {
        positions: next_positions,
        max_distance: self.max_distance,
        previous_input_char: Some(input_char),  // Store current char for next iteration
    };

    Some(new_state)
}
```

### Change 3: Update Completion Logic for Phonetic Validation

**Splitting Completion**:
```rust
fn successors_i_splitting(
    &self,  // Has access to previous_input_char via self
    offset: i32,
    errors: u8,
    operations: &OperationSet,
    bit_vector: &CharacteristicVector,
    word_slice: &str,
    input_char: char,
    _input_length: usize,
) -> Vec<GeneralizedPosition> {
    let mut successors = Vec::new();
    let n = self.max_distance as i32;
    let match_index = (offset + n) as usize;

    // Extract word character that was split
    let word_chars: Vec<char> = word_slice.chars().collect();
    if match_index >= word_chars.len() {
        return successors;
    }
    let word_char = word_chars[match_index].to_string();

    // Get both input characters
    let prev_char = self.previous_input_char.unwrap_or('\0');
    let curr_char = input_char;
    let input_2chars = format!("{}{}", prev_char, curr_char);

    // Check all split operations
    for op in operations.operations() {
        if op.consume_x() == 1 && op.consume_y() == 2 {
            if op.can_apply(word_char.as_bytes(), input_2chars.as_bytes()) {
                let weight_as_errors = op.weight() as u8;
                // Complete split: errors were incremented on enter, don't decrement
                if let Ok(succ) = GeneralizedPosition::new_i(
                    offset,
                    errors,  // Keep same errors (fractional weight = 0)
                    self.max_distance
                ) {
                    successors.push(succ);
                    break;
                }
            }
        }
    }

    successors
}
```

**Note**: The error handling needs careful thought. Phase 2d increments errors on enter and decrements on complete. For fractional weights, this might not work correctly.

---

## Implementation Plan

### Step 1: Update State to Track Previous Character (1 hour)

**Files**: `src/transducer/generalized/state.rs`

1. Add `previous_input_char: Option<char>` to `GeneralizedState`
2. Update `initial()` to set `previous_input_char: None`
3. Update `transition()` to store current char for next iteration
4. Update all state construction sites

**Testing**: Ensure all 696 tests still pass

### Step 2: Update Completion Function Signatures (2 hours)

**Files**: `src/transducer/generalized/state.rs`

1. Update `successors_i_splitting()` signature
2. Update `successors_m_splitting()` signature
3. Update `successors_i_transposing()` signature
4. Update `successors_m_transposing()` signature
5. Update all call sites in `successors()` function
6. Update Completion functions to accept &self for previous_char access

**Testing**: Ensure compilation succeeds, all tests pass

### Step 3: Implement Phonetic Split (3-4 hours)

**Files**: `src/transducer/generalized/state.rs`

1. Update split enter logic to use `can_apply()`
2. Update `successors_i_splitting()` with phonetic validation
3. Update `successors_m_splitting()` with phonetic validation
4. Handle fractional weight error counting correctly

**Testing**:
- Add test for "k"→"ch"
- Add test for "f"→"ph"
- Add test for "s"→"sh"
- Add test for "t"→"th"
- Test multiple split operations
- Test mixed split + standard operations

### Step 4: Implement Phonetic Transpose (2-3 hours)

**Files**: `src/transducer/generalized/state.rs`

1. Update transpose enter logic to use `can_apply()`
2. Update `successors_i_transposing()` with phonetic validation
3. Update `successors_m_transposing()` with phonetic validation
4. Handle 2-character extraction from word_slice

**Testing**:
- Add test for "qu"→"kw"
- Add test for "kw"→"qu"
- Test multiple transpose operations
- Test mixed transpose + other operations

### Step 5: Cross-Validation Tests (2 hours)

**Files**: `src/transducer/generalized/automaton.rs`

1. Add `test_cross_validate_phonetic_split()`
2. Add `test_cross_validate_phonetic_transpose()`
3. Add edge case tests for split+merge combinations
4. Add tests for distance constraints with split/transpose

### Step 6: Documentation (2 hours)

**Files**: `docs/generalized/phase3b_completion_report.md`

1. Document architectural changes
2. Document API changes (state now tracks previous char)
3. Update examples to include split/transpose
4. Document performance impact
5. Update migration guide

---

## Testing Strategy

### Unit Tests

**Split Operations** (minimum 8 tests):
```rust
#[test]
fn test_phonetic_split_k_to_ch_simple() {
    // "ark" → "arch" via k→ch
}

#[test]
fn test_phonetic_split_f_to_ph_at_end() {
    // "graf" → "graph" via f→ph
}

#[test]
fn test_phonetic_split_multiple() {
    // "kas" → "chas" via k→ch + s→sh (if distance allows)
}

#[test]
fn test_phonetic_split_distance_constraint() {
    // Verify fractional weights work correctly
}
```

**Transpose Operations** (minimum 6 tests):
```rust
#[test]
fn test_phonetic_transpose_qu_to_kw() {
    // "queen" → "kween" via qu→kw
}

#[test]
fn test_phonetic_transpose_kw_to_qu() {
    // "kwik" → "quik" via kw→qu
}

#[test]
fn test_phonetic_transpose_multiple() {
    // Multiple transpositions if distance allows
}
```

### Integration Tests

**Mixed Operations** (minimum 4 tests):
```rust
#[test]
fn test_phonetic_merge_and_split() {
    // Combine ⟨2,1⟩ and ⟨1,2⟩ operations
}

#[test]
fn test_all_phonetic_operations() {
    // Use merge, split, and transpose in same match
}

#[test]
fn test_phonetic_with_standard_complex() {
    // Complex combinations with standard operations
}

#[test]
fn test_phonetic_distance_limits() {
    // Verify distance constraints with all operation types
}
```

### Cross-Validation Tests

```rust
#[test]
fn test_cross_validate_phonetic_split() {
    // Validate split operations work correctly
}

#[test]
fn test_cross_validate_phonetic_transpose() {
    // Validate transpose operations work correctly
}

#[test]
fn test_cross_validate_all_phonetic() {
    // Comprehensive validation of all phonetic operation types
}
```

---

## Performance Considerations

### Memory Impact

**State Size Increase**:
```rust
// Before
struct GeneralizedState {
    positions: Vec<GeneralizedPosition>,  // ~8 bytes
    max_distance: u8,                     // 1 byte
    // padding: 7 bytes
    // Total: ~16 bytes + positions vec
}

// After
struct GeneralizedState {
    positions: Vec<GeneralizedPosition>,  // ~8 bytes
    max_distance: u8,                     // 1 byte
    previous_input_char: Option<char>,    // 5 bytes (1 byte discriminant + 4 bytes char)
    // padding: 2 bytes
    // Total: ~16 bytes + positions vec (no change due to padding)
}
```

**Impact**: Minimal - fits within existing padding

### Computational Impact

**Additional Work Per Transition**:
1. Store previous character (O(1))
2. Character extraction for 2-char sequences (O(1))
3. `can_apply()` validation (O(1) for small strings)

**Estimated Overhead**: < 5% for workloads with phonetic operations

### Optimization Opportunities

1. **Cache Operation Lookups**: Pre-filter operations by consume signature
2. **Early Termination**: Stop checking operations after first match
3. **Character Buffer Reuse**: Avoid string allocations for character pairs

---

## API Impact

### Breaking Changes

**None** - All changes are internal to the generalized automaton module.

### New Capabilities

Users can now use full phonetic operation sets:
```rust
// Phase 3a: Only merge operations worked
let ops = phonetic::consonant_digraphs();  // Has merge, split, transpose
let automaton = GeneralizedAutomaton::with_operations(1, ops);
assert!(automaton.accepts("phone", "fone"));  // ✅ Worked in 3a
assert!(automaton.accepts("graf", "graph"));  // ❌ Failed in 3a, ✅ works in 3b

// Phase 3b: All operations work
assert!(automaton.accepts("phone", "fone"));   // merge: ph→f
assert!(automaton.accepts("graf", "graph"));   // split: f→ph
assert!(automaton.accepts("queen", "kween"));  // transpose: qu→kw
```

---

## Risk Assessment

### High Risk: Error Counting with Fractional Weights

**Issue**: Phase 2d increments errors on enter, decrements on complete. For fractional weights (truncate to 0), this might create:
- Enter: errors = 0 + 0 = 0
- Complete: errors = 0 - 0 = 0 ✓ (works)

But what if starting errors != 0?
- Enter: errors = 1 + 0 = 1
- Complete: errors = 1 - 0 = 1 ✓ (works)

**Mitigation**: Carefully test error counting logic

### Medium Risk: Character Buffering Complexity

**Issue**: Need to track previous character across state transitions

**Mitigation**:
- Store in state structure
- Initialize correctly at start (None)
- Test edge cases (first character, empty input)

### Low Risk: Signature Changes

**Issue**: Many function signatures need updating

**Mitigation**:
- Compiler will catch all call sites
- Update systematically
- Run tests after each change

---

## Success Criteria

Phase 3b will be considered complete when:

### Functional Requirements
- ✅ All phonetic split ⟨1,2⟩ operations work correctly
- ✅ All phonetic transpose ⟨2,2⟩ operations work correctly
- ✅ Fractional weights handled correctly for split/transpose
- ✅ Split/transpose combine correctly with merge operations
- ✅ Split/transpose combine correctly with standard operations
- ✅ Distance constraints respected for all operation combinations

### Testing Requirements
- ✅ Minimum 14 new phonetic split/transpose tests passing
- ✅ All 696 existing tests still passing (no regressions)
- ✅ 3+ new cross-validation tests passing
- ✅ Edge cases covered (distance limits, mixed operations, etc.)

### Documentation Requirements
- ✅ Phase 3b completion report written
- ✅ API changes documented (state structure change)
- ✅ Examples updated to include split/transpose
- ✅ Migration guide complete

### Performance Requirements
- ✅ No significant performance regression (< 5% slowdown)
- ✅ Memory usage increase < 10%
- ✅ Benchmark results documented

---

## Estimated Timeline

| Task | Estimated Time | Dependencies |
|------|----------------|--------------|
| Step 1: Previous char tracking | 1 hour | None |
| Step 2: Signature updates | 2 hours | Step 1 |
| Step 3: Phonetic split impl | 3-4 hours | Step 2 |
| Step 4: Phonetic transpose impl | 2-3 hours | Step 2 |
| Step 5: Cross-validation tests | 2 hours | Steps 3-4 |
| Step 6: Documentation | 2 hours | Steps 3-5 |
| **Total** | **12-14 hours** | |

**Recommended Approach**: Complete in 2-3 focused sessions of 4-5 hours each.

---

## References

### Internal Documentation
- Phase 3a Completion Report: `docs/generalized/phase3a_completion_report.md`
- Phase 2d Completion Report: `docs/generalized/phase2d_completion_report.md`
- Phase 3 Session Handoff: `docs/generalized/phase3_session_handoff.md`

### Code References
- Merge implementation: `src/transducer/generalized/state.rs:360-402` (I-type)
- Split enter logic: `src/transducer/generalized/state.rs:404-424`
- Split completion: `src/transducer/generalized/state.rs:727-750`
- Transpose logic: `src/transducer/generalized/state.rs:339-358`, `656-679`
- Phonetic operations: `src/transducer/phonetic.rs:54-91`

### Theory References
- TCS 2011 Paper: Mitankin's generalized edit distance
- Phase 1 Phonetic Design: Commit `345321f`

---

## Conclusion

Phase 3b completes the phonetic operation integration by adding split and transpose support. The main architectural challenge is passing operation context through the two-step operation completion process. The recommended approach of storing previous input character in the state and updating completion function signatures provides a clean, maintainable solution that extends naturally from the Phase 3a merge implementation.

With Phase 3b complete, the generalized automaton will support the full range of phonetic operations defined in Phase 1, enabling sophisticated phonetic string matching for applications like spell checking, fuzzy search, and linguistic analysis.

---

**Document Created**: 2025-11-13
**Prerequisites**: Phase 3a Complete
**Status**: Ready for Implementation
