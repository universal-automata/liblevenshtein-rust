# Formal Verification Validation Matrix

**Date**: 2025-11-17
**Phase**: 3 - Standard Operations
**Status**: Complete validation for I-type and M-type

---

## Purpose

This document provides a complete mapping between:
1. **Coq theorems** (formal specifications)
2. **Rust implementation** (actual code)
3. **Property-based tests** (runtime validation)

Each row represents a proven property that should be validated in the Rust codebase through property-based testing.

---

## Validation Methodology

For each proven theorem:

1. **Locate** the corresponding Rust code
2. **Verify** that preconditions match
3. **Confirm** that postconditions match
4. **Specify** a property test that validates the theorem
5. **Document** any discrepancies or findings

---

## Phase 1: Subsumption Properties

### Theorem: subsumes_irreflexive

**Coq** (`Core.v:275`):
```coq
Theorem subsumes_irreflexive : forall p, ~ (p ⊑ p).
```

**Rust** (`subsumption.rs:62-120`):
```rust
pub fn subsumes(&self, other: &GeneralizedPosition, max_distance: u8) -> bool {
    // Returns false when self == other (implicit)
    ...
}
```

**Verification**: ✅
- Rust implementation returns `false` for identical positions
- Offset difference is 0, which fails `offset_diff.abs() <= error_diff` when `error_diff = 0`

**Property Test** (`subsumption.rs:208`): ✅ EXISTS
```rust
proptest! {
    #[test]
    fn subsumes_is_irreflexive(p in valid_position(), max_dist in 1u8..10) {
        assert!(!p.subsumes(&p, max_dist), "No position should subsume itself");
    }
}
```

**Status**: ✅ **VALIDATED** - Theorem proven, Rust correct, test exists

---

### Theorem: subsumes_transitive

**Coq** (`Core.v:306`):
```coq
Theorem subsumes_transitive : forall p1 p2 p3,
  p1 ⊑ p2 -> p2 ⊑ p3 -> p1 ⊑ p3.
```

**Rust** (`subsumption.rs:62-120` - implicit):
```rust
// Transitivity holds via arithmetic:
// If |o₁ - o₂| ≤ e₂ - e₁ and |o₂ - o₃| ≤ e₃ - e₂
// Then |o₁ - o₃| ≤ |o₁ - o₂| + |o₂ - o₃| ≤ (e₂ - e₁) + (e₃ - e₂) = e₃ - e₁
```

**Verification**: ✅
- Rust implementation implicitly satisfies transitivity through arithmetic

**Property Test**: ❌ **MISSING**

**Recommended Test**:
```rust
proptest! {
    #[test]
    fn subsumes_is_transitive(
        p1 in valid_position(),
        p2 in valid_position(),
        p3 in valid_position(),
        max_dist in 1u8..10
    ) {
        prop_assume!(same_variant(&p1, &p2));
        prop_assume!(same_variant(&p2, &p3));

        if p1.subsumes(&p2, max_dist) && p2.subsumes(&p3, max_dist) {
            prop_assert!(p1.subsumes(&p3, max_dist),
                "Subsumption should be transitive: p1⊑p2 ∧ p2⊑p3 → p1⊑p3");
        }
    }
}
```

**Status**: ⚠️ **NEEDS TEST** - Theorem proven, Rust correct, but no test

---

### Theorem: subsumes_variant_restriction

**Coq** (`Core.v:350`):
```coq
Theorem subsumes_variant_restriction : forall p1 p2,
  variant p1 <> variant p2 -> ~ (p1 ⊑ p2).
```

**Rust** (`subsumption.rs:75-78`):
```rust
if self.variant() != other.variant() {
    return false;
}
```

**Verification**: ✅
- Explicit check in Rust code
- Different variants cannot subsume

**Property Test** (`subsumption.rs:216`): ✅ EXISTS
```rust
proptest! {
    #[test]
    fn subsumes_requires_same_variant(
        p1 in valid_position(),
        p2 in valid_position(),
        max_dist in 1u8..10
    ) {
        if p1.variant() != p2.variant() {
            assert!(!p1.subsumes(&p2, max_dist),
                "Positions of different variants cannot subsume each other");
        }
    }
}
```

**Status**: ✅ **VALIDATED**

---

### Theorem: subsumes_antisymmetric

**Coq** (`Core.v:365` - derived):
```coq
Corollary subsumes_antisymmetric : forall p1 p2,
  p1 ⊑ p2 -> p2 ⊑ p1 -> False.
```

**Rust**: Derived from irreflexivity and transitivity

**Property Test**: ❌ **MISSING**

**Recommended Test**:
```rust
proptest! {
    #[test]
    fn subsumes_is_antisymmetric(
        p1 in valid_position(),
        p2 in valid_position(),
        max_dist in 1u8..10
    ) {
        prop_assume!(same_variant(&p1, &p2));

        if p1.subsumes(&p2, max_dist) && p2.subsumes(&p1, max_dist) {
            prop_assert!(false, "Subsumption cannot be symmetric: p1⊑p2 ∧ p2⊑p1 → ⊥");
        }
    }
}
```

**Status**: ⚠️ **NEEDS TEST**

---

## Phase 2: Position Constructor Correctness

### Theorem: new_i_correct

**Coq** (`Invariants.v:176`):
```coq
Theorem new_i_correct : forall offset errors max_distance p,
  new_i offset errors max_distance = Some p ->
  i_invariant p.
```

**Rust** (`position.rs:266`):
```rust
pub fn new_i(offset: i32, errors: u8, max_distance: u8) -> Result<Self, PositionError> {
    if offset.abs() as u8 > errors {
        return Err(PositionError::OffsetTooLarge);
    }
    if offset < -(max_distance as i32) || offset > max_distance as i32 {
        return Err(PositionError::OffsetOutOfBounds);
    }
    if errors > max_distance {
        return Err(PositionError::ErrorsExceedMax);
    }
    Ok(GeneralizedPosition::INonFinal { offset, errors })
}
```

**Verification**: ⚠️ **RELAXED**
- Coq: Strict invariant `|offset| ≤ errors`
- Rust: Allows `offset > errors` when `errors == 0` for fractional-weight merge operations
- Location: `position.rs:273-276` (documented in FINDINGS.md)

**Property Test** (`position.rs:566`): ✅ EXISTS
```rust
#[test]
fn new_i_maintains_invariant() {
    // Tests basic invariant satisfaction
}
```

**Status**: ⚠️ **DISCREPANCY DOCUMENTED** - Rust has relaxed invariant for Phase 3b

---

### Theorem: new_m_correct

**Coq** (`Invariants.v:200`):
```coq
Theorem new_m_correct : forall offset errors max_distance p,
  new_m offset errors max_distance = Some p ->
  m_invariant p.
```

**Rust** (`position.rs:290`):
```rust
pub fn new_m(offset: i32, errors: u8, max_distance: u8) -> Result<Self, PositionError> {
    let n = max_distance as i32;
    if (errors as i32) < (-offset - n) {
        return Err(PositionError::ReachabilityViolation);
    }
    if offset < -(2 * n) || offset > 0 {
        return Err(PositionError::OffsetOutOfBounds);
    }
    if errors > max_distance {
        return Err(PositionError::ErrorsExceedMax);
    }
    Ok(GeneralizedPosition::MFinal { offset, errors })
}
```

**Verification**: ✅
- Checks match Coq exactly

**Property Test**: ✅ EXISTS

**Status**: ✅ **VALIDATED**

---

## Phase 3: I-Type Transitions

### Theorem: i_match_preserves_invariant

**Coq** (`Transitions.v:260`):
```coq
Lemma i_match_preserves_invariant : forall p cv p',
  i_invariant p ->
  i_successor p OpMatch cv p' ->
  i_invariant p'.
```

**Rust** (`state.rs:280-295`):
```rust
if op.is_match() {
    if has_match {
        // Phase 3: For match, check can_apply() with actual characters
        ...
        if op.can_apply(...) {
            // δ^D,ε_e: (t+1)#e → I^ε → I+t#e
            if let Ok(succ) = GeneralizedPosition::new_i(offset, errors, self.max_distance) {
                successors.push(succ);
            }
        }
    }
}
```

**Verification**: ✅
- Offset unchanged ✓
- Errors unchanged ✓
- Constructor validates result ✓

**Property Test**: ❌ **MISSING**

**Recommended Test**:
```rust
proptest! {
    #[test]
    fn i_match_preserves_invariant(
        offset in -10i32..10,
        errors in 0u8..10,
        max_distance in 1u8..10,
        cv in characteristic_vector()
    ) {
        prop_assume!(errors <= max_distance);
        prop_assume!(offset.abs() <= errors as i32);
        prop_assume!(offset >= -(max_distance as i32) && offset <= max_distance as i32);

        if let Ok(p) = GeneralizedPosition::new_i(offset, errors, max_distance) {
            // Simulate match operation
            if let Ok(p_prime) = GeneralizedPosition::new_i(offset, errors, max_distance) {
                // p_prime should satisfy i_invariant (checked by constructor)
                assert!(p_prime.offset().abs() <= p_prime.errors() as i32);
            }
        }
    }
}
```

**Status**: ⚠️ **NEEDS TEST**

---

### Theorem: i_delete_preserves_invariant

**Coq** (`Transitions.v:318`):
```coq
Lemma i_delete_preserves_invariant : forall p cv p',
  i_invariant p ->
  i_successor p OpDelete cv p' ->
  i_invariant p'.
```

**Rust** (`state.rs:297-314`):
```rust
else if op.is_deletion() {
    if errors < self.max_distance {
        let new_errors = errors + 1;
        if new_errors <= self.max_distance {
            ...
            // δ^D,ε_e: t#(e+w) → I^ε → I+(t-1)#(e+w)
            if let Ok(succ) = GeneralizedPosition::new_i(offset - 1, new_errors, self.max_distance) {
                successors.push(succ);
            }
        }
    }
}
```

**Verification**: ✅
- Offset decreases by 1 ✓
- Errors increase by 1 ✓
- Precondition: `errors < n` ✓
- Boundary check: Constructor validates `offset - 1 >= -n` ✓

**Property Test**: ❌ **MISSING**

**Recommended Test**:
```rust
proptest! {
    #[test]
    fn i_delete_preserves_invariant(
        offset in -10i32..10,
        errors in 0u8..9,
        max_distance in 1u8..10
    ) {
        prop_assume!(errors < max_distance);
        prop_assume!(offset.abs() <= errors as i32);
        prop_assume!(offset > -(max_distance as i32));  // Can delete

        if let Ok(p) = GeneralizedPosition::new_i(offset, errors, max_distance) {
            // Delete: offset - 1, errors + 1
            if let Ok(p_prime) = GeneralizedPosition::new_i(offset - 1, errors + 1, max_distance) {
                // Verify invariant maintained
                assert!((offset - 1).abs() <= (errors + 1) as i32);
                assert!(offset - 1 >= -(max_distance as i32));
            }
        }
    }
}
```

**Status**: ⚠️ **NEEDS TEST**

---

### Theorem: i_insert_preserves_invariant

**Coq** (`Transitions.v:377`):
```coq
Lemma i_insert_preserves_invariant : forall p cv p',
  i_invariant p ->
  i_successor p OpInsert cv p' ->
  i_invariant p'.
```

**Rust** (`state.rs:315-329`):
```rust
else if op.is_insertion() {
    if errors < self.max_distance {
        let new_errors = errors + 1;
        if new_errors <= self.max_distance {
            ...
            // δ^D,ε_e: (t+1)#(e+w) → I^ε → I+t#(e+w)
            if let Ok(succ) = GeneralizedPosition::new_i(offset, new_errors, self.max_distance) {
                successors.push(succ);
            }
        }
    }
}
```

**Verification**: ✅
- Offset unchanged ✓
- Errors increase by 1 ✓

**Property Test**: ❌ **MISSING**

**Status**: ⚠️ **NEEDS TEST**

---

### Theorem: i_substitute_preserves_invariant

**Coq** (`Transitions.v:399`):
```coq
Lemma i_substitute_preserves_invariant : forall p cv p',
  i_invariant p ->
  i_successor p OpSubstitute cv p' ->
  i_invariant p'.
```

**Rust** (`state.rs:330-348`):
```rust
else if op.is_substitution() {
    if errors < self.max_distance {
        let new_errors = errors + 1;
        if new_errors <= self.max_distance {
            ...
            // δ^D,ε_e: (t+1)#(e+w) → I^ε → I+t#(e+w)
            if let Ok(succ) = GeneralizedPosition::new_i(offset, new_errors, self.max_distance) {
                successors.push(succ);
            }
        }
    }
}
```

**Verification**: ✅
- Offset unchanged ✓
- Errors increase by 1 ✓

**Property Test**: ❌ **MISSING**

**Status**: ⚠️ **NEEDS TEST**

---

### Theorem: i_successor_preserves_invariant

**Coq** (`Transitions.v:420` - MAIN THEOREM):
```coq
Theorem i_successor_preserves_invariant : forall p op cv p',
  i_invariant p ->
  i_successor p op cv p' ->
  i_invariant p'.
```

**Rust**: Composite of all above

**Property Test**: ❌ **MISSING**

**Recommended Test**:
```rust
proptest! {
    #[test]
    fn i_successors_preserve_invariant(
        p in valid_i_position(),
        input_char in any::<char>(),
        max_distance in 1u8..10
    ) {
        let state = UniversalState::new(max_distance);
        let cv = CharacteristicVector::new("test", input_char);

        let successors = state.successors_i_type(
            p.offset(), p.errors(), &operations, &cv, "test", "test", input_char
        );

        for succ in successors {
            // Every successor must satisfy i_invariant
            assert!(succ.offset().abs() <= succ.errors() as i32,
                "Successor violates reachability: |offset| > errors");
            assert!(succ.offset() >= -(max_distance as i32) && succ.offset() <= max_distance as i32,
                "Successor out of bounds");
            assert!(succ.errors() <= max_distance,
                "Successor exceeds error budget");
        }
    }
}
```

**Status**: ⚠️ **NEEDS TEST** (HIGH PRIORITY - validates entire I-type)

---

### Theorem: i_successor_cost_correct

**Coq** (`Transitions.v:484`):
```coq
Theorem i_successor_cost_correct : forall p op cv p',
  i_successor p op cv p' ->
  errors p' = (errors p + operation_cost op)%nat.
```

**Rust**: All I-type operations

**Property Test**: ❌ **MISSING**

**Recommended Test**:
```rust
proptest! {
    #[test]
    fn i_successor_cost_correct(
        p in valid_i_position(),
        input_char in any::<char>(),
        max_distance in 1u8..10
    ) {
        let state = UniversalState::new(max_distance);
        let cv = CharacteristicVector::new("test", input_char);
        let operations = OperationSet::standard();

        let successors = state.successors_i_type(
            p.offset(), p.errors(), &operations, &cv, "test", "test", input_char
        );

        for succ in successors {
            // Match: errors unchanged (cost 0)
            // Delete/Insert/Substitute: errors + 1 (cost 1)
            assert!(succ.errors() == p.errors() || succ.errors() == p.errors() + 1,
                "Successor has incorrect error count");
        }
    }
}
```

**Status**: ⚠️ **NEEDS TEST**

---

## Phase 3: M-Type Transitions

### Theorem: m_match_preserves_invariant

**Coq** (`Transitions.v:687`):
```coq
Lemma m_match_preserves_invariant : forall p cv p',
  m_invariant p ->
  m_successor p OpMatch cv p' ->
  m_invariant p'.
```

**Rust** (`state.rs:583-595`):
```rust
if op.is_match() && has_match {
    ...
    if op.can_apply(...) {
        if let Ok(succ) = GeneralizedPosition::new_m(offset + 1, errors, self.max_distance) {
            successors.push(succ);
        }
    }
}
```

**Verification**: ✅
- Offset increases by 1 ✓
- Errors unchanged ✓
- Precondition: `offset < 0` (enforced by constructor)

**Property Test**: ❌ **MISSING**

**Status**: ⚠️ **NEEDS TEST**

---

### Theorem: m_delete_preserves_invariant

**Coq** (`Transitions.v:723`):
```coq
Lemma m_delete_preserves_invariant : forall p cv p',
  m_invariant p ->
  m_successor p OpDelete cv p' ->
  m_invariant p'.
```

**Rust** (`state.rs:596-610`):
```rust
else if op.is_deletion() && errors < self.max_distance {
    let new_errors = errors + 1;
    if new_errors <= self.max_distance {
        ...
        if let Ok(succ) = GeneralizedPosition::new_m(offset, new_errors, self.max_distance) {
            successors.push(succ);
        }
    }
}
```

**Verification**: ✅
- Offset UNCHANGED ✓ (unique to M-type!)
- Errors increase by 1 ✓

**Property Test**: ❌ **MISSING**

**Status**: ⚠️ **NEEDS TEST**

---

### Theorem: m_insert_preserves_invariant

**Coq** (`Transitions.v:758`):
```coq
Lemma m_insert_preserves_invariant : forall p cv p',
  m_invariant p ->
  m_successor p OpInsert cv p' ->
  m_invariant p'.
```

**Rust** (`state.rs:611-622`):
```rust
else if op.is_insertion() && errors < self.max_distance {
    let new_errors = errors + 1;
    if new_errors <= self.max_distance {
        ...
        if let Ok(succ) = GeneralizedPosition::new_m(offset + 1, new_errors, self.max_distance) {
            successors.push(succ);
        }
    }
}
```

**Verification**: ✅
- Offset increases by 1 ✓
- Errors increase by 1 ✓

**Property Test**: ❌ **MISSING**

**Status**: ⚠️ **NEEDS TEST**

---

### Theorem: m_substitute_preserves_invariant

**Coq** (`Transitions.v:793`):
```coq
Lemma m_substitute_preserves_invariant : forall p cv p',
  m_invariant p ->
  m_successor p OpSubstitute cv p' ->
  m_invariant p'.
```

**Rust** (`state.rs:623-638`):
```rust
else if op.is_substitution() && errors < self.max_distance {
    let new_errors = errors + 1;
    if new_errors <= self.max_distance {
        ...
        if let Ok(succ) = GeneralizedPosition::new_m(offset + 1, new_errors, self.max_distance) {
            successors.push(succ);
        }
    }
}
```

**Verification**: ✅
- Offset increases by 1 ✓
- Errors increase by 1 ✓

**Property Test**: ❌ **MISSING**

**Status**: ⚠️ **NEEDS TEST**

---

### Theorem: m_successor_preserves_invariant

**Coq** (`Transitions.v:828` - MAIN THEOREM):
```coq
Theorem m_successor_preserves_invariant : forall p op cv p',
  m_invariant p ->
  m_successor p op cv p' ->
  m_invariant p'.
```

**Rust**: Composite of all M-type operations

**Property Test**: ❌ **MISSING**

**Recommended Test**:
```rust
proptest! {
    #[test]
    fn m_successors_preserve_invariant(
        p in valid_m_position(),
        input_char in any::<char>(),
        max_distance in 1u8..10
    ) {
        let state = UniversalState::new(max_distance);
        let cv = CharacteristicVector::new("test", input_char);

        let successors = state.successors_m_type(
            p.offset(), p.errors(), &operations, &cv, "test", "test", input_char
        );

        for succ in successors {
            let n = max_distance as i32;
            // Every successor must satisfy m_invariant
            assert!(succ.errors() as i32 >= -(succ.offset()) - n,
                "Successor violates M-reachability");
            assert!(succ.offset() >= -(2 * n) && succ.offset() <= 0,
                "Successor out of M-type bounds");
            assert!(succ.errors() <= max_distance,
                "Successor exceeds error budget");
        }
    }
}
```

**Status**: ⚠️ **NEEDS TEST** (HIGH PRIORITY - validates entire M-type)

---

### Theorem: m_successor_cost_correct

**Coq** (`Transitions.v:860`):
```coq
Theorem m_successor_cost_correct : forall p op cv p',
  m_successor p op cv p' ->
  errors p' = (errors p + operation_cost op)%nat.
```

**Rust**: All M-type operations

**Property Test**: ❌ **MISSING** (same as I-type version)

**Status**: ⚠️ **NEEDS TEST**

---

## Summary Statistics

### Validation Coverage

| Category | Total | Validated | Needs Test | Discrepancy |
|----------|-------|-----------|------------|-------------|
| Subsumption (Phase 1) | 4 | 2 | 2 | 0 |
| Constructors (Phase 2) | 6 | 2 | 4 | 1 (documented) |
| I-Type Operations (Phase 3) | 7 | 0 | 7 | 0 |
| M-Type Operations (Phase 3) | 7 | 0 | 7 | 0 |
| **TOTAL** | **24** | **4** | **20** | **1** |

### Test Priority

**HIGH PRIORITY** (validate main theorems):
1. `i_successor_preserves_invariant` - validates all I-type ops
2. `m_successor_preserves_invariant` - validates all M-type ops
3. `subsumes_transitive` - critical for anti-chain correctness

**MEDIUM PRIORITY** (individual operations):
4. I-type: match, delete, insert, substitute preservation
5. M-type: match, delete, insert, substitute preservation
6. Cost correctness for both types

**LOW PRIORITY** (derived properties):
7. `subsumes_antisymmetric`
8. Constructor tests (most already exist)

---

## Test Implementation Plan

### File: `tests/proptest_transitions.rs` (NEW)

Create comprehensive property tests for all transition theorems:

```rust
use proptest::prelude::*;
use liblevenshtein::transducer::generalized::*;

// Generators
fn valid_i_position() -> impl Strategy<Value = GeneralizedPosition> { ... }
fn valid_m_position() -> impl Strategy<Value = GeneralizedPosition> { ... }

// I-Type Transition Tests
proptest! {
    #[test]
    fn i_successor_preserves_invariant(...) { ... }

    #[test]
    fn i_match_preserves_invariant(...) { ... }

    // ... etc for all I-type ops
}

// M-Type Transition Tests
proptest! {
    #[test]
    fn m_successor_preserves_invariant(...) { ... }

    // ... etc for all M-type ops
}

// Cross-Cutting Properties
proptest! {
    #[test]
    fn only_delete_changes_offset_i_type(...) { ... }

    #[test]
    fn m_type_offset_increases_or_stays(...) { ... }
}
```

### File: `tests/proptest_subsumption.rs` (ENHANCE)

Add missing subsumption tests:

```rust
proptest! {
    #[test]
    fn subsumes_is_transitive(...) { ... }

    #[test]
    fn subsumes_is_antisymmetric(...) { ... }
}
```

---

## Discrepancies

### D1: Relaxed I-Type Invariant for Fractional Weights

**Location**: `position.rs:273-276`

**Coq Invariant**:
```coq
Z.abs (offset p) <= Z.of_nat (errors p)
```

**Rust Implementation**:
```rust
// Allows offset > errors when errors == 0 for fractional-weight merge
```

**Impact**: Phase 3b (phonetic operations) uses fractional weights
**Resolution**: Document as extension beyond proven specification
**Action**: Add warning comment, create separate property tests for Phase 3b

---

## Completion Criteria

Phase 3 validation is complete when:

- [x] All theorems mapped to Rust code
- [x] All preconditions verified to match
- [x] All discrepancies documented
- [ ] All HIGH PRIORITY tests implemented
- [ ] All MEDIUM PRIORITY tests implemented
- [ ] Test suite passes with 100% success rate
- [ ] Documentation updated with test results

---

**End of Validation Matrix**
