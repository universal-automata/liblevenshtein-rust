# Phase 2 Next Steps: Successor Generation Refactoring

**Current Status**: Infrastructure complete, ready for successor generation refactoring

**Estimated Time**: 2-3 hours of focused work

## What's Been Completed ✅

1. **OperationSet Infrastructure** ✅
   - `operations` field added to `GeneralizedAutomaton`
   - Constructors support both default and custom operation sets
   - All 57 tests pass

2. **Parameter Threading** ✅
   - `GeneralizedState::transition()` accepts `&OperationSet` parameter
   - All call sites updated
   - All tests pass

## What's Next: Successor Generation Refactoring

### Current Situation

The `_operations` parameter is threaded through but **not yet used**. The code still uses hardcoded standard operations in:

- `successors_standard()` (state.rs:184-197)
- `successors_i_type_standard()` (state.rs:216-301)
- `successors_m_type_standard()` (state.rs:303-356)

### Goal

Replace the hardcoded standard operation logic with a generic implementation that iterates over `operations.operations()`.

### Step-by-Step Refactoring Plan

#### Step 1: Update Method Signature (5 min)

Change `successors_standard()` to accept operations parameter:

```rust
// BEFORE
fn successors_standard(
    &self,
    pos: &GeneralizedPosition,
    bit_vector: &CharacteristicVector,
) -> Vec<GeneralizedPosition>

// AFTER
fn successors(
    &self,
    pos: &GeneralizedPosition,
    operations: &crate::transducer::OperationSet,
    bit_vector: &CharacteristicVector,
) -> Vec<GeneralizedPosition>
```

Update call site in `transition()`:
```rust
// Line 164: Change from
let successors = self.successors_standard(pos, bit_vector);

// To
let successors = self.successors(pos, operations, bit_vector);
```

**Test**: Run tests to ensure nothing broke.

#### Step 2: Start with I-Type Refactoring (1-1.5 hours)

The `successors_i_type_standard()` method is the most complex. Refactor it incrementally:

**Phase A: Extract Character Matching Logic**

Create helper method:
```rust
/// Check if character at bit_vector[index] matches
fn has_match_at(&self, bit_vector: &CharacteristicVector, index: usize) -> bool {
    index < bit_vector.len() && bit_vector.is_match(index)
}
```

**Phase B: Iterate Over Operations**

Replace hardcoded operation logic with iteration:

```rust
fn successors_i_type(
    &self,
    offset: i32,
    errors: u8,
    operations: &crate::transducer::OperationSet,
    bit_vector: &CharacteristicVector,
) -> Vec<GeneralizedPosition> {
    let mut successors = Vec::new();
    let n = self.max_distance as i32;
    let match_index = (offset + n) as usize;

    // Position within visible window
    if match_index < bit_vector.len() {
        let has_match = bit_vector.is_match(match_index);

        // Iterate over all operations
        for op in operations.operations() {
            // Only handle single-char operations for now
            if op.consume_x() > 1 || op.consume_y() > 1 {
                continue; // Skip multi-char for Phase 2c
            }

            // Classify operation type
            if op.is_match() {
                // Match operation: ⟨1, 1, 0.0⟩
                if has_match && errors <= self.max_distance {
                    if let Ok(succ) = GeneralizedPosition::new_i(offset, errors, self.max_distance) {
                        successors.push(succ);
                        // Early return: match takes precedence
                        return successors;
                    }
                }
            } else if op.is_deletion() {
                // Delete operation: ⟨1, 0, w⟩
                if !has_match && errors < self.max_distance {
                    let new_errors = errors + op.weight() as u8;
                    if new_errors <= self.max_distance {
                        if let Ok(succ) = GeneralizedPosition::new_i(offset - 1, new_errors, self.max_distance) {
                            successors.push(succ);
                        }
                    }
                }
            } else if op.is_insertion() || op.is_substitution() {
                // Insert ⟨0, 1, w⟩ or Substitute ⟨1, 1, w⟩
                if !has_match && errors < self.max_distance {
                    let new_errors = errors + op.weight() as u8;
                    if new_errors <= self.max_distance {
                        if let Ok(succ) = GeneralizedPosition::new_i(offset, new_errors, self.max_distance) {
                            successors.push(succ);
                        }
                    }
                }
            }
        }

        // SKIP-TO-MATCH optimization (Phase 2c: generalize for multi-char)
        if !has_match && errors < self.max_distance {
            for idx in (match_index + 1)..bit_vector.len() {
                if bit_vector.is_match(idx) {
                    let skip_distance = (idx - match_index) as i32;
                    let new_errors = errors + skip_distance as u8;
                    if new_errors <= self.max_distance {
                        if let Ok(succ) = GeneralizedPosition::new_i(offset + skip_distance, new_errors, self.max_distance) {
                            successors.push(succ);
                        }
                    }
                    break;
                }
            }
        }

        return successors;
    }

    // Out-of-window logic (keep as-is for now)
    if errors >= self.max_distance {
        return successors;
    }

    // ... rest of out-of-window logic ...

    successors
}
```

**Test After Each Change**:
```bash
cargo test --lib generalized
```

#### Step 3: M-Type Refactoring (30-45 min)

Similar approach for `successors_m_type_standard()`:

```rust
fn successors_m_type(
    &self,
    offset: i32,
    errors: u8,
    operations: &crate::transducer::OperationSet,
    bit_vector: &CharacteristicVector,
) -> Vec<GeneralizedPosition> {
    let mut successors = Vec::new();

    // Compute match index for M-type
    let bit_index = offset + bit_vector.len() as i32;
    let has_match = bit_index >= 0
        && (bit_index as usize) < bit_vector.len()
        && bit_vector.is_match(bit_index as usize);

    // Iterate over operations
    for op in operations.operations() {
        // Skip multi-char for now
        if op.consume_x() > 1 || op.consume_y() > 1 {
            continue;
        }

        if op.is_match() && has_match {
            if let Ok(succ) = GeneralizedPosition::new_m(offset + 1, errors, self.max_distance) {
                successors.push(succ);
            }
        } else if op.is_deletion() && errors < self.max_distance {
            let new_errors = errors + op.weight() as u8;
            if new_errors <= self.max_distance {
                if let Ok(succ) = GeneralizedPosition::new_m(offset, new_errors, self.max_distance) {
                    successors.push(succ);
                }
            }
        } else if (op.is_insertion() || op.is_substitution()) && errors < self.max_distance {
            let new_errors = errors + op.weight() as u8;
            if new_errors <= self.max_distance {
                if let Ok(succ) = GeneralizedPosition::new_m(offset + 1, new_errors, self.max_distance) {
                    successors.push(succ);
                }
            }
        }
    }

    successors
}
```

#### Step 4: Remove "_" Prefix from operations Parameter (2 min)

Once `operations` is actually used:

```rust
// state.rs:151 - Remove underscore prefix
pub fn transition(
    &self,
    operations: &crate::transducer::OperationSet,  // Was: _operations
    bit_vector: &CharacteristicVector,
    _input_length: usize,
) -> Option<Self>
```

#### Step 5: Run Full Test Suite (5 min)

```bash
# Run all generalized tests
cargo test --lib generalized

# Should see: 57 passed; 0 failed
```

#### Step 6: Cross-Validation with Standard Operations (10 min)

Verify that using `OperationSet::standard()` produces identical results to Phase 1:

```rust
#[test]
fn test_operation_set_standard_equivalence() {
    let automaton_phase2 = GeneralizedAutomaton::new(2);

    let test_cases = vec![
        ("test", "test"),
        ("test", "text"),
        ("test", "tests"),
        ("tests", "test"),
        ("test", "tst"),
    ];

    for (word, input) in test_cases {
        let result = automaton_phase2.accepts(word, input);
        // Should match Phase 1 behavior
        assert_eq!(result, expected_for_distance_2(word, input));
    }
}
```

### Challenges to Watch For

1. **Match Operation Precedence**
   - Match operation should return early (no error operations if match succeeds)
   - Current code does this correctly; preserve this behavior

2. **SKIP-TO-MATCH Optimization**
   - Current implementation assumes single-char deletions
   - For Phase 2c (multi-char), may need to generalize or disable

3. **Out-of-Window Position Handling**
   - Critical for correctness when `input.len() > word.len()`
   - Preserve existing logic initially
   - May need updating for multi-char operations in Phase 2c

4. **Error Budget Tracking**
   - Use `op.weight() as u8` to accumulate errors
   - Check `new_errors <= self.max_distance` before adding successor

5. **I^ε Conversion**
   - Offsets have special meaning in universal positions
   - Delete decreases offset: `offset - 1`
   - Match/substitute keeps offset: `offset`
   - See comments in current code for details

### Testing Strategy

**After each incremental change**:
```bash
cargo test --lib generalized
```

**If tests fail**:
1. Check which test failed
2. Add debug test (like existing `test_debug_*` tests)
3. Compare with Universal automaton behavior
4. Fix and re-test

**Cross-validation script**: Use `/tmp/test_cross_validation.rs` pattern

### Success Criteria

- ✅ All 57 existing tests pass
- ✅ No changes to test expectations
- ✅ Backward compatibility maintained
- ✅ `_operations` parameter is now `operations` (no underscore)
- ✅ Code iterates over `operations.operations()`
- ✅ Standard operation behavior identical to Phase 1

### Files to Modify

1. **state.rs**
   - `successors_standard()` → `successors()`
   - `successors_i_type_standard()` → `successors_i_type()`
   - `successors_m_type_standard()` → `successors_m_type()`
   - Add `operations` parameter to all three
   - Implement operation iteration logic

### Estimated Timeline

- **Step 1 (Signature)**: 5 min
- **Step 2 (I-type)**: 1-1.5 hours
- **Step 3 (M-type)**: 30-45 min
- **Step 4 (Cleanup)**: 2 min
- **Step 5 (Testing)**: 5 min
- **Step 6 (Validation)**: 10 min

**Total**: 2-3 hours

### After This Is Complete

Next phases (Phase 2c-e):
1. Multi-character operations (transposition, phonetic)
2. Restricted operation support (`can_apply()` checks)
3. Custom operation set tests
4. Cross-validation with Universal automaton for transposition
5. Documentation updates

### Reference Files

- **Current implementation**: `src/transducer/generalized/state.rs:184-356`
- **OperationType API**: `src/transducer/operation_type.rs:285-307`
- **OperationSet API**: `src/transducer/operation_set.rs:144-146`
- **Implementation plan**: `docs/generalized/phase2_implementation_plan.md`
- **Progress tracking**: `docs/generalized/phase2_progress.md`

### Notes

- Take incremental approach - test after each change
- Don't try to handle multi-char operations yet (Phase 2c)
- Preserve SKIP-TO-MATCH optimization
- Preserve out-of-window handling
- Focus on correctness first, optimization later
- Use existing debug tests as templates for new tests if needed

Good luck! The infrastructure is solid, this is just methodical refactoring work.
