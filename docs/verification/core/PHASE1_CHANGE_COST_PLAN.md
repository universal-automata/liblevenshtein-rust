# Phase 1: change_cost_compose_bound Proof Plan

**Created**: 2025-11-23
**Status**: Ready for implementation
**Estimated Time**: 4-6.5 hours
**Confidence**: HIGH (85%)

---

## Overview

This document contains the detailed research and proof plan for completing `change_cost_compose_bound` (line 3892-3942 in Distance.v), which bounds the sum of substitution costs in a composed trace.

## Target Lemma

**Location**: Distance.v:3892-3942

```coq
Lemma change_cost_compose_bound :
  forall (A B C : list Char) (T1 : Trace A B) (T2 : Trace B C),
    is_valid_trace A B T1 = true ->
    is_valid_trace B C T2 = true ->
    let comp := compose_trace T1 T2 in
    fold_left (fun sum '(i, k) =>
      sum + subst_cost (nth i A default_char) (nth k C default_char)
    ) comp 0 <=
    fold_left (fun sum '(i, j) =>
      sum + subst_cost (nth i A default_char) (nth j B default_char)
    ) T1 0 +
    fold_left (fun sum '(j, k) =>
      sum + subst_cost (nth j B default_char) (nth k C default_char)
    ) T2 0.
```

**Purpose**: Prove that the sum of substitution costs in the composed trace is bounded by the sum of costs in T1 plus the sum of costs in T2.

**Current Status**: Admitted (line 3942)

---

## Key Discovery: Only ONE Missing Lemma!

After comprehensive analysis of the codebase, the proof infrastructure is **95% complete**. All witness extraction, injectivity, cardinality bounds, and fold_left monotonicity lemmas exist and are proven with Qed.

**The only missing piece**: `fold_left_sum_bound_subset`

This lemma states that the sum over a subset is bounded by the sum over the superset.

---

## Proven Infrastructure

### Witness Extraction (✅ All proven with Qed)

1. **`witness_to_T1`** (line 3377-3402)
   - Extracts `(i,j) ∈ T1` witness for `(i,k) ∈ compose_trace`
   - Status: ✅ Definition complete

2. **`witness_to_T2`** (line 3407-3432)
   - Extracts `(j,k) ∈ T2` witness for `(i,k) ∈ compose_trace`
   - Status: ✅ Definition complete

3. **`witness_to_T1_correct`** (line 3437-3503)
   - Proves `In ik (compose_trace T1 T2) → In (witness_to_T1 ... ik) T1`
   - Status: ✅ Proven with Qed

4. **`witness_to_T2_correct`** (line 3508-3574)
   - Proves `In ik (compose_trace T1 T2) → In (witness_to_T2 ... ik) T2`
   - Status: ✅ Proven with Qed

### Injectivity (✅ All proven with Qed)

5. **`witness_to_T1_injective`** (line 3579-3639)
   - Proves `witness_to_T1` is injective on `compose_trace T1 T2`
   - Uses `witness_j_unique_in_T1` (line 2746)
   - Status: ✅ Proven with Qed

6. **`witness_to_T2_injective`** (line 3644-3704)
   - Proves `witness_to_T2` is injective on `compose_trace T1 T2`
   - Uses `witness_k_unique_in_T2` (line 2773)
   - Status: ✅ Proven with Qed

### Cardinality Bounds (✅ All proven with Qed)

7. **`compose_witness_bounded_T1`** (line 3798-3838)
   - Proves `length (compose_trace T1 T2) ≤ length T1` via injectivity
   - Status: ✅ Proven with Qed (uses `compose_trace_preserves_NoDup`)

8. **`compose_witness_bounded_T2`** (line 3843-3884)
   - Proves `length (compose_trace T1 T2) ≤ length T2` via injectivity
   - Status: ✅ Proven with Qed (uses `compose_trace_preserves_NoDup`)

### fold_left Monotonicity (✅ All proven with Qed)

9. **`fold_left_add_monotone`** (line 2480)
   - If all elements satisfy pointwise bound, fold_left sum bounded
   - Status: ✅ Proven with Qed

10. **`fold_left_add_init_monotone`** (line ~2450)
    - Monotonicity with different initial values
    - Status: ✅ Proven with Qed

### Arithmetic (✅ All proven with Qed)

11. **`subst_cost_triangle`** (line 2059)
    - Triangle inequality: `subst_cost(a,c) ≤ subst_cost(a,b) + subst_cost(b,c)`
    - Status: ✅ Proven with Qed

---

## Missing Infrastructure: fold_left_sum_bound_subset

**What it proves**: Sum over a subset is bounded by sum over the superset.

```coq
Lemma fold_left_sum_bound_subset :
  forall (f : nat * nat -> nat) (sub super : list (nat * nat)),
    (forall x, In x sub -> In x super) ->  (* sub ⊆ super *)
    fold_left (fun sum ik => sum + f ik) sub 0 <=
    fold_left (fun sum ik => sum + f ik) super 0.
```

**Proof strategy**:
1. Induction on `super`
2. Base case: `super = []` implies `sub = []` (from subset property), both sums are 0
3. Inductive case: `super = x :: super'`
   - Case 1: `In x sub`
     - Then `sub = sub' ++ [x]` for some `sub'` (reorder)
     - Use IH on `sub'` and `super'`
     - Both sides add `f x`, preserve inequality
   - Case 2: `¬In x sub`
     - Then `sub ⊆ super'`
     - Use IH on `sub` and `super'`
     - LHS unchanged, RHS increases (by adding `f x`), inequality strengthens

**Estimated effort**: 60-80 lines, 1-1.5 hours

**Alternative**: Could use Coq's standard library lemmas about `fold_left` and subsets if available, potentially reducing to 20-30 lines.

---

## Proof Plan for change_cost_compose_bound

### Step 1: Prove fold_left_sum_bound_subset (1-1.5h)

Create and prove the missing lemma as described above.

**Placement**: Insert before `change_cost_compose_bound` (around line 3890)

### Step 2: Prove witness map inclusion helpers (1-2h)

Create two lemmas showing that the witness maps produce subsets:

```coq
Lemma witness_T1_image_subset :
  forall (A B C : list Char) (T1 : Trace A B) (T2 : Trace B C),
    is_valid_trace A B T1 = true ->
    is_valid_trace B C T2 = true ->
    forall ik, In ik (compose_trace T1 T2) ->
      In (witness_to_T1 A B C T1 T2 ik) T1.
Proof.
  intros. apply witness_to_T1_correct. assumption.
Qed.
```

Similar for `witness_T2_image_subset`.

These may be trivial wrappers around existing correctness lemmas, or may require 40-60 lines each to establish the subset relationship for the full list.

**Estimated effort**: 80-120 lines total, 1-2 hours

### Step 3: Complete main proof using triangle inequality (1-2h)

Now we have all the pieces:

1. **Map composition elements to witnesses**:
   ```coq
   let comp_T1_witnesses := map (witness_to_T1 A B C T1 T2) comp in
   let comp_T2_witnesses := map (witness_to_T2 A B C T1 T2) comp in
   ```

2. **Apply triangle inequality pointwise**:
   Each `(i,k)` in comp has witnesses `(i,j)` in T1 and `(j,k)` in T2:
   ```coq
   subst_cost(A[i], C[k]) ≤ subst_cost(A[i], B[j]) + subst_cost(B[j], C[k])
   ```

3. **Sum both sides**:
   ```coq
   sum_{(i,k) ∈ comp} subst_cost(A[i], C[k]) ≤
   sum_{(i,k) ∈ comp} [subst_cost(A[i], B[j]) + subst_cost(B[j], C[k])]
   ```

4. **Split sum**:
   ```coq
   ≤ sum_{(i,k) ∈ comp} subst_cost(A[i], B[j]) +
     sum_{(i,k) ∈ comp} subst_cost(B[j], C[k])
   ```

5. **Rewrite as sums over witness images**:
   ```coq
   = sum_{(i,j) ∈ comp_T1_witnesses} subst_cost(A[i], B[j]) +
     sum_{(j,k) ∈ comp_T2_witnesses} subst_cost(B[j], C[k])
   ```

6. **Apply fold_left_sum_bound_subset twice**:
   - `comp_T1_witnesses ⊆ T1` (by `witness_T1_image_subset`)
   - `comp_T2_witnesses ⊆ T2` (by `witness_T2_image_subset`)
   - Therefore:
     ```coq
     sum over comp_T1_witnesses ≤ sum over T1
     sum over comp_T2_witnesses ≤ sum over T2
     ```

7. **Combine inequalities**:
   ```coq
   sum over comp ≤ sum over T1 + sum over T2
   ```
   ∎

**Estimated effort**: 60-100 lines, 1-2 hours

---

## Total Effort Estimate

| Task | Lines | Time |
|------|-------|------|
| `fold_left_sum_bound_subset` | 60-80 | 1-1.5h |
| Witness image subset helpers | 80-120 | 1-2h |
| Main proof | 60-100 | 1-2h |
| **Total** | **200-300** | **4-6.5h** |

**Confidence**: HIGH (85%)
- All dependencies proven with Qed
- Clear logical path
- Only one missing lemma
- No circular dependencies

---

## Potential Obstacles

1. **fold_left vs. map interaction**: May need auxiliary lemmas about `fold_left (fun sum x => sum + f x) (map g L) 0` equivalence to `fold_left (fun sum x => sum + f (g x)) L 0`.

   **Mitigation**: These are standard list lemmas; should be straightforward 10-20 line proofs each if needed.

2. **Subset vs. Injection**: The witness maps are injective but may not be surjective. Need to ensure subset lemmas handle this correctly.

   **Mitigation**: We only need `image(witness_map) ⊆ T`, not equality. This is exactly what the correctness lemmas provide.

3. **fold_left commutativity assumptions**: Standard fold_left proofs sometimes require commutativity/associativity of the operation. Addition has both, so this should not be an issue.

   **Mitigation**: Explicitly use `Nat.add_assoc` and `Nat.add_comm` where needed.

---

## Validation Strategy

After completing the proof:

1. **Compilation test**:
   ```bash
   systemd-run --user --scope -p MemoryMax=126G -p CPUQuota=1800% \
     -p IOWeight=30 -p TasksMax=200 \
     coqc -Q docs/verification/core/theories "" \
     docs/verification/core/theories/Distance.v
   ```

2. **Check dependencies**:
   ```coq
   Print Assumptions change_cost_compose_bound.
   ```
   Should show only standard axioms (functional extensionality, etc.), not our custom admits.

3. **Update tracking**:
   - Mark `change_cost_compose_bound` as complete in ADMITTED_LEMMAS_STATUS.md
   - Update PROOF_SESSION_LOGS.md with session details
   - Update progress summary (1/8 lemmas complete)
   - Commit with detailed message

---

## Next Steps After Completion

With `change_cost_compose_bound` proven, the next lemmas in the dependency chain are:

1. **Lemma 4**: `lost_A_positions_bound` (6-10h est.)
2. **Lemma 5**: `lost_C_positions_bound` (2-3h est.)
3. **Lemma 6**: `trace_composition_delete_insert_bound` (1-2h est.)

All three depend on `change_cost_compose_bound` and form the "cost bounds chain" required for the Triangle Inequality.

**Recommended order**: 4 → 5 → 6 (dependency order)

---

## References

- **Distance.v**: Main verification file
- **ADMITTED_LEMMAS_STATUS.md**: Current status of all admitted lemmas
- **PROOF_SESSION_LOGS.md**: Session 2 analysis of change_cost_compose_bound
- **Session 4**: NoDup completion, which unblocked witness bounded lemmas

---

## Scientific Method Tracking

**Hypothesis**: The proof requires only `fold_left_sum_bound_subset`, with all other infrastructure already proven.

**Prediction**: Proof should complete in 4-6.5 hours with high confidence.

**Test**: Implement according to this plan and measure actual time.

**Validation criteria**:
- ✅ All proofs end with `Qed` (not `Admitted`)
- ✅ File compiles with only warnings (no errors)
- ✅ `Print Assumptions` shows no custom admits
- ✅ Time within ±50% of estimate (2-10 hours)

If hypothesis fails, document:
- What additional infrastructure was needed
- Why it wasn't identified during analysis
- Updated time estimates for future lemmas
