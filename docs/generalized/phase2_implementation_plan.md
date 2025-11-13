# Phase 2 Implementation Plan: Runtime-Configurable Operations

## Status: IN PROGRESS

### Completed Tasks

1. **Add OperationSet parameter to GeneralizedAutomaton** ✅
   - Added `operations: OperationSet` field to struct (automaton.rs:106)
   - Created `new()` constructor defaulting to `OperationSet::standard()` (automaton.rs:128-133)
   - Created `with_operations()` constructor for custom operation sets (automaton.rs:161-166)
   - All 57 existing tests pass
   - Backward compatibility maintained

### Remaining Tasks

#### 2. Thread OperationSet through state transition methods

**Goal**: Pass OperationSet from automaton down to state transition logic

**Changes Required**:
- `GeneralizedState::transition()` signature needs `operations: &OperationSet` parameter
- `GeneralizedAutomaton::accepts()` must pass `&self.operations` to `state.transition()`
- Update all call sites in tests

**Files to Modify**:
- `src/transducer/generalized/state.rs:148-178`
- `src/transducer/generalized/automaton.rs` (accept method call sites)

#### 3. Refactor successor generation for single-char operations

**Goal**: Replace hardcoded standard operations with OperationSet iteration (Phase 2a)

**Scope**: Only single-character operations first:
- Match: ⟨1, 1, 0.0⟩
- Substitution: ⟨1, 1, 1.0⟩
- Insertion: ⟨0, 1, 1.0⟩
- Deletion: ⟨1, 0, 1.0⟩

**Current Implementation**:
- `successors_i_type_standard()` (state.rs:216-301)
- `successors_m_type_standard()` (state.rs:303-356)

**Refactoring Strategy**:
1. Extract character extraction logic (get char at position from word/subword)
2. For each operation in `operations.operations()`:
   - Check if operation can apply (position within bounds, error budget available)
   - For restricted operations: check `op.can_apply(dict_chars, query_chars)`
   - Compute successor position based on operation's `consume_x`, `consume_y`, `weight`
3. Preserve SKIP-TO-MATCH optimization for deletion operations
4. Preserve out-of-window position handling (state.rs:274-301)

**Implementation Notes**:
- Need to pass subword context to check restricted operations
- For I-type: `offset + n` gives bit vector index
- For M-type: More complex, may need word position tracking
- Weight accumulation: `new_errors = errors + op.weight() as u8`

#### 4. Add support for multi-character operations

**Goal**: Support operations with `consume_x > 1` or `consume_y > 1`

**Examples**:
- Transposition: ⟨2, 2, 1.0⟩
- Phonetic ph→f: ⟨2, 1, 0.15⟩
- Merge operations: ⟨2, 1, w⟩

**Challenges**:
- Need to extract multi-character sequences from word/input
- Bit vector logic needs updating (match multiple positions)
- Subsumption logic may need adjustment
- Out-of-window handling more complex

**Key Implementation Points**:
- Extract `consume_x` characters starting at current word position
- Extract `consume_y` characters from current input position
- Check bounds for both word and input
- For transposition, check if `word[i:i+2]` == reversed `input[j:j+2]`

#### 5. Implement operation matching logic

**Goal**: Correctly handle unrestricted vs restricted operations

**Unrestricted Operations**:
- Always applicable (if position/error budget allows)
- Examples: standard operations

**Restricted Operations**:
- Only applicable if character pair matches restriction set
- Use `op.can_apply(dict_chars, query_chars)` method
- Examples: phonetic corrections, keyboard proximity

**Integration**:
```rust
for op in operations.operations() {
    // Extract characters
    let dict_chars = &word_chars[pos..pos+op.consume_x()];
    let query_chars = &input_chars[pos..pos+op.consume_y()];

    // Check if operation can apply
    if !op.can_apply(dict_chars, query_chars) {
        continue;  // Skip this operation
    }

    // Compute successor...
}
```

#### 6. Add tests for custom operation sets

**Test Cases Required**:

**A. Transposition Tests**:
```rust
#[test]
fn test_transposition_adjacent_swap() {
    let ops = OperationSet::with_transposition();
    let automaton = GeneralizedAutomaton::with_operations(2, ops);

    // "test" vs "tset" (swap 'e' and 's')
    assert!(automaton.accepts("test", "tset"));

    // "test" vs "etst" (swap at start)
    assert!(automaton.accepts("test", "etst"));
}

#[test]
fn test_transposition_with_other_edits() {
    let ops = OperationSet::with_transposition();
    let automaton = GeneralizedAutomaton::with_operations(2, ops);

    // Transposition + substitution
    assert!(automaton.accepts("test", "txst"));  // e→x + swap
}
```

**B. Phonetic Tests**:
```rust
#[test]
fn test_phonetic_ph_to_f() {
    let mut phonetic = SubstitutionSet::new();
    phonetic.allow_str("ph", "f");

    let mut ops = OperationSetBuilder::new()
        .with_match()
        .with_operation(OperationType::with_restriction(
            2, 1, 0.15,
            phonetic,
            "ph_to_f"
        ))
        .with_standard_ops()
        .build();

    let automaton = GeneralizedAutomaton::with_operations(1, ops);

    // "phone" vs "fone" (ph→f digraph)
    assert!(automaton.accepts("phone", "fone"));

    // "graph" vs "graf"
    assert!(automaton.accepts("graph", "graf"));
}
```

**C. Edge Cases**:
- Empty words
- Operations at word boundaries
- Multi-character at end of word (may not fit)
- Error budget exhaustion

#### 7. Cross-validate with UniversalAutomaton

**Goal**: Ensure GeneralizedAutomaton matches UniversalAutomaton for transposition

**Test Setup**:
```rust
#[test]
fn test_cross_validation_transposition() {
    use crate::transducer::universal::{UniversalAutomaton, Transposition};

    let universal: UniversalAutomaton<Transposition> = UniversalAutomaton::new(2);
    let generalized = GeneralizedAutomaton::with_operations(
        2,
        OperationSet::with_transposition()
    );

    let test_cases = vec![
        ("test", "tset"),    // adjacent swap
        ("test", "etst"),    // swap at start
        ("test", "test"),    // identical
        ("test", "tets"),    // swap at end
        ("hello", "hlelo"),  // 'e' and 'l' swap
    ];

    for (word, input) in test_cases {
        let universal_result = universal.accepts(word, input);
        let gen_result = generalized.accepts(word, input);
        assert_eq!(universal_result, gen_result,
                   "Mismatch for word='{}', input='{}'",
                   word, input);
    }
}
```

#### 8. Update documentation

**Files to Update**:

**A. Module documentation** (`src/transducer/generalized/mod.rs`):
- Update Phase 2 status to "Complete"
- Add examples of custom operation sets

**B. Automaton documentation** (`src/transducer/generalized/automaton.rs`):
- Update struct docs with Phase 2 features
- Add more `with_operations()` examples

**C. State documentation** (`src/transducer/generalized/state.rs`):
- Update `transition()` docs to mention OperationSet
- Document multi-character operation handling

**D. README** (`docs/generalized/README.md`):
- Add Phase 2 completion status
- Performance notes for different operation sets

## Implementation Order

**Recommended sequence**:

1. **Thread OperationSet** (30 min)
   - Simple parameter passing
   - Verify tests still pass

2. **Refactor single-char operations** (2-3 hours)
   - Most complex task
   - Break into small testable increments
   - Validate at each step with existing tests

3. **Add transposition tests** (30 min)
   - Before implementing multi-char support
   - Will guide implementation

4. **Multi-character support** (2-3 hours)
   - Build on single-char refactoring
   - Test incrementally

5. **Operation matching logic** (1 hour)
   - Should mostly work from refactoring
   - Add restricted operation tests

6. **Phonetic tests** (30 min)
   - Validate restricted operations

7. **Cross-validation** (30 min)
   - Final validation step

8. **Documentation** (1 hour)
   - Capture learnings

**Total estimated time**: 8-10 hours

## Key Design Decisions

### 1. Preserve Phase 1 Optimizations

**SKIP-TO-MATCH**: Must be preserved for standard operations
- Only applies to deletion operations
- Scans ahead in bit vector for next match
- Critical for performance on deletion-heavy edits

**Out-of-window handling**: Required for correctness
- When input longer than word
- Generates error transitions outside visible window

### 2. Backward Compatibility

- `GeneralizedAutomaton::new()` must default to standard operations
- All existing tests must pass unchanged
- No breaking API changes

### 3. Performance Considerations

- Operation iteration should be fast (typically 4-6 operations)
- Restricted operation matching: O(1) for small sets (bitmap), O(log n) for large (hash)
- Avoid allocations in hot paths
- SmallVec for inline position storage

### 4. Multi-Character Challenges

**Bit vector semantics**:
- Currently encodes single-character matches
- For transposition ⟨2,2⟩: need to check TWO positions match
- May need helper methods for multi-char matching

**Position tracking**:
- Current offset semantics work for single-char
- Multi-char may need different offset calculation
- Test carefully with word boundaries

## Validation Strategy

At each implementation step:

1. **Run existing tests**: `cargo test generalized`
2. **Add new test**: For the feature being implemented
3. **Cross-validate**: Compare with Universal where applicable
4. **Performance check**: Ensure no major regressions

## Known Challenges

1. **M-type position successors**: Less well understood than I-type
   - May need more research into Mitankin's thesis
   - Current implementation is "Phase 1 simplification"

2. **Multi-character at word boundaries**:
   - Transposition at end of word may not fit
   - Need careful bounds checking

3. **SKIP-TO-MATCH with multi-char**:
   - Current optimization assumes single-char deletion
   - May need generalization or disabling for multi-char ops

## Success Criteria

Phase 2 is complete when:

- [x] OperationSet parameter added to GeneralizedAutomaton
- [ ] All operations from OperationSet are used in successor generation
- [ ] Multi-character operations work correctly
- [ ] Restricted operations are enforced
- [ ] Transposition tests pass
- [ ] Phonetic tests pass
- [ ] Cross-validation with Universal succeeds
- [ ] All 57 original tests still pass
- [ ] Documentation updated
- [ ] No significant performance regression for standard operations

## Notes

- This is a major refactoring task
- Take incremental approach
- Validate at each step
- Don't break existing functionality
- If stuck, refer back to Universal implementation for guidance
