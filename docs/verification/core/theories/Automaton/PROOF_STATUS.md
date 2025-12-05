# Automaton Proofs Status

**Date**: December 4, 2025
**Build Status**: ✅ Compiles successfully

## Summary

The Automaton verification module contains proofs for soundness and completeness of Levenshtein automata supporting three algorithms: Standard, Transposition (Damerau), and Merge/Split. The build compiles but has **13 admitted lemmas** across three files.

## Admitted Lemmas by File

### Automaton/Completeness.v (9 admitted)

| Line | Name | Type | Scope | Notes |
|------|------|------|-------|-------|
| 2438 | `reachable_implies_contained_aux` | Lemma | Standard | **CRITICAL** - Core lemma for completeness |
| 2566 | `automaton_run_not_dead_for_reachable` | Lemma | Standard | Depends on contained_aux |
| 2614 | `automaton_final_state_accepts_standard` | Lemma | Standard | Depends on above two |
| 2922 | `automaton_run_step_std_trans` | Lemma | Transposition | Transition step inclusion |
| 2964 | `standard_accepts_implies_transposition_accepts` | Lemma | Transposition | Algorithm inclusion |
| 2996 | `standard_accepts_implies_merge_split_accepts` | Lemma | Merge/Split | **OUT OF SCOPE** |
| 3092 | `automaton_complete_transposition` | Theorem | Transposition | Main transposition completeness |
| 3130 | `automaton_complete_merge_split` | Theorem | Merge/Split | **OUT OF SCOPE** |
| 3187 | `automaton_finds_distance` | Corollary | All | Distance computation corollary |

### Automaton/Soundness.v (3 admitted)

| Line | Name | Type | Scope | Notes |
|------|------|------|-------|-------|
| 3926 | `automaton_run_preserves_reachable_transposition` | Lemma | Transposition | Damerau soundness infrastructure |
| 4417 | `automaton_sound_merge_split` | Theorem | Merge/Split | **OUT OF SCOPE** |
| 4434 | `automaton_sound_merge_split_lev` | Corollary | Merge/Split | **OUT OF SCOPE** |

### Automaton/MainTheorem.v (1 admitted)

| Line | Name | Type | Scope | Notes |
|------|------|------|-------|-------|
| 250 | `automaton_distance_correct` | Theorem | Standard | Distance = lev_distance |

## Dependency Graph

```
reachable_implies_contained_aux (CRITICAL)
    ↓
automaton_run_not_dead_for_reachable
    ↓
automaton_final_state_accepts_standard
    ↓
reachable_final_implies_accepts [PROVEN]
    ↓
automaton_complete_standard [PROVEN]
    ↓
automaton_distance_correct (MainTheorem.v)

automaton_run_step_std_trans
    ↓
standard_accepts_implies_transposition_accepts
    ↓
automaton_complete_transposition

automaton_run_preserves_reachable_transposition (independent, for Damerau soundness)
```

## Critical Issue: `reachable_implies_contained_aux`

### Statement
```coq
Lemma reachable_implies_contained_aux : forall query n dict_prefix p,
  position_reachable query n dict_prefix p ->
  num_errors p <= n ->
  is_special p = false ->
  forall s,
    automaton_run_from_initial Standard query n dict_prefix = Some s ->
    positions_contain (positions s) p.
```

### Problem Analysis

The lemma attempts to prove that if a position `p` is reachable via edit operations, then the automaton's state contains that position. However, there's a **fundamental mismatch** between:

1. **`positions_contain`** (used in the lemma): Requires `position_subsumes p1 p2` which demands:
   - Same `term_index`
   - Same `is_special` flag
   - `num_errors p1 <= num_errors p2`

2. **`subsumes_standard`** (used by automaton's antichain): Allows different `term_index` values when one position dominates another:
   ```coq
   (* A position at term_index i with errors e can subsume
      a position at term_index i+k with errors e+k *)
   ```

### Consequence

When the automaton performs antichain filtering via `fold_left state_insert`, a position at `(i, e)` can remove a position at `(i+1, e+1)` because the first "dominates" the second (you can always reach `(i+1, e+1)` from `(i, e)` via deletion).

This means **the exact reachable position may not survive antichain filtering**, only a dominating position with lower term_index remains.

### Why This Matters

- The current lemma statement is **too strong** for intermediate positions
- Cannot prove that `std_pos (length dict_prefix) e` is in the state if a dominating position `std_pos k e'` (where `k < length dict_prefix` and `k + (length dict_prefix - k) = length dict_prefix`, `e' + (length dict_prefix - k) = e`) is in the antichain

### Possible Solutions

#### Option A: Weaker Predicate
Replace `positions_contain` with a weaker predicate:
```coq
Definition positions_dominate (ps : list Position) (p : Position) : bool :=
  existsb (fun p' =>
    (term_index p' <= term_index p) &&
    (num_errors p' + (term_index p - term_index p') <= num_errors p)
  ) ps.
```

#### Option B: Track Final Positions Only
For completeness, we only need to show that **final positions** survive. The "non-final cannot subsume final" rule (2024-12 bug fix) protects final positions:
```coq
(* In subsumes_standard: *)
if position_is_final p1 qlen then
  if position_is_final p2 qlen then
    (* both final: compare errors *)
    num_errors p1 <=? num_errors p2
  else
    (* p1 final, p2 non-final: p1 cannot subsume p2 *)
    false
else
  (* p1 non-final: standard subsumption *)
  ...
```

This means a final position can only be removed by another final position with fewer errors.

#### Option C: Restructure Completeness Proof
Use existing proven infrastructure:
1. `fold_state_insert_has_final`: If closed_positions contains a final position, the result is accepting
2. `fold_state_insert_preserves_min_error`: Minimum error count is preserved
3. `transition_state_not_dead_standard`: Standard never goes dead if errors < n

New lemma needed:
```coq
Lemma reachable_final_produces_closed_final : forall query n dict_prefix,
  (exists p, position_reachable query n dict_prefix p /\
             position_is_final p (length query) = true /\
             num_errors p <= n) ->
  forall s,
    automaton_run_from_initial Standard query n dict_prefix = Some s ->
    exists p', In p' (positions s) /\
               position_is_final p' (length query) = true.
```

## Progress Made

### Recently Fixed Lemmas

1. **`transition_produces_insert_bounded`** (Completeness.v:1349-1366)
   - Fixed type unification issue by moving `destruct p` before `exists`
   - Used `change` tactic to make definitional equality explicit

2. **`transition_produces_insert_exact`** (Completeness.v:1369-1383)
   - Same fix pattern as above

### Helper Infrastructure Available

The following proven lemmas can help complete the remaining proofs:

- `transition_standard_produces_match` (Transition.v)
- `transition_standard_produces_substitute` (Transition.v)
- `transition_standard_produces_insert` (Transition.v)
- `fold_state_insert_has_final` (Completeness.v)
- `fold_state_insert_preserves_min_error` (Completeness.v)
- `fold_state_insert_accepting` (Completeness.v)
- `transition_state_not_dead_standard` (Completeness.v)

## Out of Scope Lemmas

The following 4 merge/split lemmas are **not in scope** for the current work:

1. `automaton_sound_merge_split` (Soundness.v:4417)
2. `automaton_sound_merge_split_lev` (Soundness.v:4434)
3. `standard_accepts_implies_merge_split_accepts` (Completeness.v:2996)
4. `automaton_complete_merge_split` (Completeness.v:3130)

These require integration with the MergeSplitDistance.v module which defines a different distance metric.

## Recommended Next Steps

1. **Decide on solution approach** for `reachable_implies_contained_aux`:
   - Option A: Weaker predicate (most general, more work)
   - Option B: Final positions only (sufficient for completeness, simpler)
   - Option C: Restructure proof (use existing infrastructure)

2. **If Option B/C chosen**:
   - Create `reachable_final_produces_closed_final` lemma
   - Modify `automaton_final_state_accepts_standard` to use new approach
   - Chain through to `automaton_complete_standard` (already proven given accepts)

3. **For transposition proofs**:
   - `automaton_run_step_std_trans` needs characteristic vector analysis
   - `standard_accepts_implies_transposition_accepts` builds on step lemma
   - `automaton_complete_transposition` may need separate Damerau reachability

4. **For soundness**:
   - `automaton_run_preserves_reachable_transposition` handles special positions
   - Need to account for spurious special positions from epsilon closure

## Build Command

```bash
cd docs/verification/core/theories
systemd-run --user --scope -p MemoryMax=126G -p CPUQuota=1800% -p IOWeight=30 -p TasksMax=200 make -j1
```

## File Locations

- Plan: `/home/dylon/.claude/plans/agile-kindling-pretzel.md`
- Completeness.v: `Automaton/Completeness.v`
- Soundness.v: `Automaton/Soundness.v`
- MainTheorem.v: `Automaton/MainTheorem.v`
- Transition.v: `Automaton/Transition.v` (helper lemmas)
