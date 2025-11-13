# Universal Automaton: Transposition and Merge/Split Implementation Plan

**Date**: 2025-11-13
**Goal**: Implement transposition and merge/split operations for UniversalAutomaton to unblock GeneralizedAutomaton Phase 2d

## Theoretical Foundation

### From Mitankin's Thesis

**Definition 7 (Page 14-16)**: Elementary transition functions for different distance variants

#### Standard Levenshtein (χ = ε)
Already implemented.

#### Damerau-Levenshtein with Transposition (χ = t)

**Operations**:
- Standard: match, substitute, insert, delete
- **Transposition**: swap two adjacent characters (cost 1)

**Position Types** (Page 31):
- **i#e**: Regular position (usual type)
- **i#e_t**: Transposition state (waiting to complete swap)

**Transition Function δ^D,t_e** (Definition 7, Page 16):

For **regular positions i#e**:
```text
δ^D,t_e(i#e, b) = δ^D,ε_e(i#e, b) ∪ {
    {(i+1)#(e+1)_t}  if b[1] = 0 ∧ e < n  (start transposition)
}
```

For **transposition state i#e_t**:
```text
δ^D,t_e(i#e_t, b) = {
    {(i+2)#e}        if b[1] = 1           (complete transposition - match)
    ∅                otherwise              (transposition failed)
}
```

**Semantics**:
1. From regular position, can enter transposition state if current char doesn't match (b[1] = 0)
2. Transposition state expects next char to match previous char (b[1] = 1)
3. If it matches, we've successfully transposed: consumed 2 from word, 2 from input, cost 1
4. If it doesn't match, transposition fails (dead end)

**Example**: "test" → "etst"
- Position 0, input 'e', word 't': no match, enter transposition state 1#1_t
- Position 1, input 't', word 'e': match previous! Complete transposition → 2#1

#### Merge/Split (χ = ms)

**Operations**:
- Standard: match, substitute, insert, delete
- **Merge**: two word chars → one input char (2→1, cost 1)
- **Split**: one word char → two input chars (1→2, cost 1)

**Position Types** (Page 31):
- **i#e**: Regular position (usual type)
- **i#e_s**: Split state (waiting to emit second character)

**Transition Function δ^D,ms_e** (Definition 7, Page 16):

For **regular positions i#e**:
```text
δ^D,ms_e(i#e, b) = δ^D,ε_e(i#e, b) ∪ {
    {(i+2)#(e+1)}    if b[1] = 1 ∧ e < n   (merge: 2 word chars → 1 input)
    {(i+1)#(e+1)_s}  if b[1] = 1 ∧ e < n   (start split: 1 word char → 2 input)
}
```

For **split state i#e_s**:
```text
δ^D,ms_e(i#e_s, b) = {
    {(i+1)#e}        if b[1] = 1           (complete split - second char matches)
    ∅                otherwise              (split failed)
}
```

**Semantics**:

**Merge**:
- From word position i, if word[i] matches input, can also merge word[i:i+2] → input[j]
- Consumes 2 from word, 1 from input, cost 1

**Split**:
- From word position i, if word[i] matches input[j], enter split state
- In split state, check if word[i] also matches input[j+1]
- If yes, consumed 1 from word, 2 from input, cost 1

## Implementation Strategy

### Phase 1: Add Transposition State Tracking

#### 1.1 Update UniversalPosition Enum

Current implementation has phantom variant data:
```rust
pub enum UniversalPosition<V: PositionVariant> {
    INonFinal { offset: i32, errors: u8, variant: PhantomData<V> },
    MFinal { offset: i32, errors: u8, variant: PhantomData<V> },
}
```

**Need to track actual variant state**:
```rust
pub enum UniversalPosition<V: PositionVariant> {
    INonFinal {
        offset: i32,
        errors: u8,
        state: V  // Actual variant state, not PhantomData
    },
    MFinal {
        offset: i32,
        errors: u8,
        state: V  // Actual variant state, not PhantomData
    },
}
```

**Variant State Types**:
```rust
// Standard variant has no state
impl PositionVariant for Standard {
    // Already implemented, no changes needed
}

// Transposition variant tracks transposition state
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Transposition {
    Usual,              // Regular position i#e
    TranspositionState, // Transposition state i#e_t
}

// Merge/Split variant tracks split state
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum MergeAndSplit {
    Usual,      // Regular position i#e
    SplitState, // Split state i#e_s
}
```

**Problem**: This is a breaking change to the Position API.

**Alternative**: Add state only for non-Standard variants using Default trait:

```rust
// For Standard: zero-sized type, no state
impl Default for Standard {
    fn default() -> Self { Standard }
}

// For Transposition: has state
impl Default for Transposition {
    fn default() -> Self { Transposition::Usual }
}
```

But we still need to store it in the position...

**Best Approach**: Make variant state part of the enum variant:

```rust
pub enum UniversalPosition<V: PositionVariant> {
    INonFinal {
        offset: i32,
        errors: u8,
        variant_state: V::State  // Type associated with variant
    },
    MFinal {
        offset: i32,
        errors: u8,
        variant_state: V::State
    },
}

pub trait PositionVariant: Clone + fmt::Debug + PartialEq + Eq + std::hash::Hash {
    type State: Clone + fmt::Debug + PartialEq + Eq + std::hash::Hash;

    fn variant_name() -> &'static str;
    fn default_state() -> Self::State;
}

impl PositionVariant for Standard {
    type State = ();  // Zero-sized
    fn variant_name() -> &'static str { "Standard" }
    fn default_state() -> Self::State { () }
}

impl PositionVariant for Transposition {
    type State = TranspositionState;
    fn variant_name() -> &'static str { "Transposition" }
    fn default_state() -> Self::State { TranspositionState::Usual }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum TranspositionState {
    Usual,
    Transposing,
}
```

This keeps Standard as zero-overhead while allowing state for Transposition and MergeAndSplit.

#### 1.2 Update Position Constructors

```rust
impl<V: PositionVariant> UniversalPosition<V> {
    pub fn new_i(offset: i32, errors: u8, max_distance: u8) -> Result<Self, PositionError> {
        // ... validation ...
        Ok(Self::INonFinal {
            offset,
            errors,
            variant_state: V::default_state(),
        })
    }

    pub fn new_i_with_state(
        offset: i32,
        errors: u8,
        max_distance: u8,
        variant_state: V::State
    ) -> Result<Self, PositionError> {
        // ... validation ...
        Ok(Self::INonFinal {
            offset,
            errors,
            variant_state,
        })
    }
}
```

### Phase 2: Implement Transposition Successor Logic

#### 2.1 Add Transposition Successor Methods

```rust
impl UniversalPosition<Transposition> {
    fn successors_i_type_transposition(
        offset: i32,
        errors: u8,
        state: TranspositionState,
        bit_vector: &CharacteristicVector,
        max_distance: u8,
    ) -> Vec<Self> {
        let mut successors = Vec::new();

        match state {
            TranspositionState::Usual => {
                // Standard operations
                let standard_succs = Self::successors_i_type_standard(
                    offset, errors, bit_vector, max_distance
                );

                // Convert to Transposition variant
                for succ in standard_succs {
                    if let Ok(trans_succ) = Self::new_i_with_state(
                        succ.offset(),
                        succ.errors(),
                        max_distance,
                        TranspositionState::Usual
                    ) {
                        successors.push(trans_succ);
                    }
                }

                // Add transposition transition
                // If b[1] = 0 (no match at position 1) and e < n
                let match_index = (max_distance as i32 + offset) as usize;
                if match_index < bit_vector.len()
                    && !bit_vector.is_match(match_index)
                    && errors < max_distance
                {
                    // Enter transposition state: (i+1)#(e+1)_t
                    if let Ok(trans_succ) = Self::new_i_with_state(
                        offset + 1,
                        errors + 1,
                        max_distance,
                        TranspositionState::Transposing
                    ) {
                        successors.push(trans_succ);
                    }
                }
            }

            TranspositionState::Transposing => {
                // In transposition state: check if b[1] = 1 (match)
                let match_index = (max_distance as i32 + offset) as usize;

                if match_index < bit_vector.len()
                    && bit_vector.is_match(match_index)
                {
                    // Complete transposition: (i+2)#e (no extra cost, already paid)
                    if let Ok(succ) = Self::new_i_with_state(
                        offset + 1,  // I^ε: (i+2)#e → I+(i+1)#e
                        errors,
                        max_distance,
                        TranspositionState::Usual
                    ) {
                        successors.push(succ);
                    }
                }
                // If no match, transposition fails → no successors
            }
        }

        successors
    }
}
```

#### 2.2 Update Position::successors() to Dispatch by Variant

Need to specialize the `successors()` method based on variant type. This requires trait specialization or manual implementation per variant.

**Approach**: Implement `successors()` separately for each variant:

```rust
impl UniversalPosition<Standard> {
    pub fn successors(...) -> Vec<Self> {
        // Existing standard implementation
    }
}

impl UniversalPosition<Transposition> {
    pub fn successors(
        &self,
        bit_vector: &CharacteristicVector,
        max_distance: u8,
    ) -> Vec<Self> {
        match self {
            Self::INonFinal { offset, errors, variant_state } => {
                Self::successors_i_type_transposition(
                    *offset, *errors, variant_state.clone(), bit_vector, max_distance
                )
            }
            Self::MFinal { offset, errors, variant_state } => {
                Self::successors_m_type_transposition(
                    *offset, *errors, variant_state.clone(), bit_vector, max_distance
                )
            }
        }
    }
}

impl UniversalPosition<MergeAndSplit> {
    pub fn successors(...) -> Vec<Self> {
        // Merge/Split implementation
    }
}
```

### Phase 3: Implement Merge/Split Successor Logic

Similar structure to transposition:

```rust
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum MergeSplitState {
    Usual,
    Splitting,
}

impl UniversalPosition<MergeAndSplit> {
    fn successors_i_type_merge_split(
        offset: i32,
        errors: u8,
        state: MergeSplitState,
        bit_vector: &CharacteristicVector,
        max_distance: u8,
    ) -> Vec<Self> {
        match state {
            MergeSplitState::Usual => {
                // Standard operations + merge + split initiation
                let mut successors = /* standard ops */;

                let match_index = (max_distance as i32 + offset) as usize;
                if match_index < bit_vector.len()
                    && bit_vector.is_match(match_index)
                    && errors < max_distance
                {
                    // MERGE: (i+2)#(e+1) - consume 2 from word, 1 from input
                    if let Ok(merge_succ) = Self::new_i_with_state(
                        offset + 1,  // I^ε: (i+2)#(e+1) → I+(i+1)#(e+1)
                        errors + 1,
                        max_distance,
                        MergeSplitState::Usual
                    ) {
                        successors.push(merge_succ);
                    }

                    // SPLIT initiation: (i+1)#(e+1)_s
                    if let Ok(split_succ) = Self::new_i_with_state(
                        offset,  // I^ε: (i+1)#(e+1) → I+i#(e+1)
                        errors + 1,
                        max_distance,
                        MergeSplitState::Splitting
                    ) {
                        successors.push(split_succ);
                    }
                }

                successors
            }

            MergeSplitState::Splitting => {
                // In split state: check if b[1] = 1 (second char matches)
                let match_index = (max_distance as i32 + offset) as usize;

                if match_index < bit_vector.len()
                    && bit_vector.is_match(match_index)
                {
                    // Complete split: (i+1)#e
                    if let Ok(succ) = Self::new_i_with_state(
                        offset,  // I^ε: (i+1)#e → I+i#e
                        errors,
                        max_distance,
                        MergeSplitState::Usual
                    ) {
                        return vec![succ];
                    }
                }
                // If no match, split fails
                vec![]
            }
        }
    }
}
```

## Testing Strategy

### Transposition Tests

```rust
#[test]
fn test_transposition_adjacent_swap() {
    use crate::transducer::universal::{UniversalAutomaton, Transposition};

    let automaton = UniversalAutomaton::<Transposition>::new(2);

    // "test" vs "etst" - swap first two characters
    assert!(automaton.accepts("test", "etst"));

    // "test" vs "tset" - swap middle two characters
    assert!(automaton.accepts("test", "tset"));
}

#[test]
fn test_transposition_state_transitions() {
    use crate::transducer::universal::{UniversalPosition, Transposition, TranspositionState};
    use crate::transducer::universal::CharacteristicVector;

    // Test entering transposition state
    let pos = UniversalPosition::<Transposition>::new_i_with_state(
        0, 0, 2, TranspositionState::Usual
    ).unwrap();

    // Bit vector for 'e' in "test" at position 0: [0,1,0,0] (no match at [0])
    let bv = CharacteristicVector::new('e', "$$test");
    let succs = pos.successors(&bv, 2);

    // Should include transposition state
    assert!(succs.iter().any(|s| matches!(
        s,
        UniversalPosition::INonFinal {
            variant_state: TranspositionState::Transposing, ..
        }
    )));
}

#[test]
fn test_transposition_completion() {
    // Test completing transposition from transposing state
    let pos = UniversalPosition::<Transposition>::new_i_with_state(
        1, 1, 2, TranspositionState::Transposing
    ).unwrap();

    // Bit vector for 't' in "test" at position 1: [1,0,0,0] (match at [0])
    let bv = CharacteristicVector::new('t', "$$$test");
    let succs = pos.successors(&bv, 2);

    // Should complete transposition back to Usual state
    assert_eq!(succs.len(), 1);
    assert!(matches!(
        succs[0],
        UniversalPosition::INonFinal {
            offset: 2,
            errors: 1,
            variant_state: TranspositionState::Usual
        }
    ));
}
```

### Merge/Split Tests

```rust
#[test]
fn test_merge_operation() {
    let automaton = UniversalAutomaton::<MergeAndSplit>::new(2);

    // "test" vs "tst" - merge 'es' → 's'
    // Not a valid merge in standard definition, need better example

    // "book" vs "bok" - merge 'oo' → 'o'
    assert!(automaton.accepts("book", "bok"));
}

#[test]
fn test_split_operation() {
    let automaton = UniversalAutomaton::<MergeAndSplit>::new(2);

    // "test" vs "teest" - split 'e' → 'ee'
    assert!(automaton.accepts("test", "teest"));
}
```

## Implementation Phases

### Phase 1: Update Position Infrastructure (Breaking Changes)
- [ ] Add `State` associated type to `PositionVariant` trait
- [ ] Update `UniversalPosition` to store `variant_state: V::State`
- [ ] Update all constructors
- [ ] Update Display implementation
- [ ] Fix all compilation errors in existing code
- [ ] Run all existing tests (should still pass)

### Phase 2: Implement Transposition
- [ ] Define `TranspositionState` enum
- [ ] Implement `successors_i_type_transposition()`
- [ ] Implement `successors_m_type_transposition()`
- [ ] Add transposition tests
- [ ] Validate against thesis examples

### Phase 3: Implement Merge/Split
- [ ] Define `MergeSplitState` enum
- [ ] Implement `successors_i_type_merge_split()`
- [ ] Implement `successors_m_type_merge_split()`
- [ ] Add merge/split tests
- [ ] Validate against thesis examples

### Phase 4: Update Generalized Automaton
- [ ] Use UniversalAutomaton<Transposition> as reference
- [ ] Implement transposition in GeneralizedAutomaton
- [ ] Cross-validate results

## Estimated Timeline

- Phase 1: 2-3 hours (breaking changes across codebase)
- Phase 2: 2-3 hours (transposition implementation)
- Phase 3: 2-3 hours (merge/split implementation)
- Phase 4: 1-2 hours (generalized automaton integration)

**Total**: 7-11 hours

## Open Questions

1. **Subsumption with variant states**: Does `i#e_t` subsume `i#e`? Probably not - they're different states.
2. **M-type transposition**: Thesis defines transposition for I-type. What about M-type? Probably same logic.
3. **Display format**: How to show transposition state? `I+0#1_t`?
4. **Backwards compatibility**: Can we maintain API compatibility? Probably not - this is a major change.

## Next Steps

Start with Phase 1: Update position infrastructure to support variant state tracking.
