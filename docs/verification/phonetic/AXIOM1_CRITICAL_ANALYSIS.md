# Axiom 1 Critical Analysis: Fundamental Issue Identified

**Date**: 2025-11-20
**Status**: CRITICAL - Axiom statement may be incorrect
**Priority**: HIGH - Affects correctness of main theorem

---

## Executive Summary

After deep analysis of Axiom 1 and its usage context, I've identified a **fundamental issue**: the axiom as currently stated appears to be **unprovable and possibly incorrect**.

**The Problem**: Axiom 1 claims that when `find_first_match r_head s (length s) = Some pos` for ANY `r_head ∈ rules`, then ALL rules in `rules` don't match before position `pos`. This is demonstrably false.

**Impact**: The main correctness theorem `no_rules_match_before_first_match_preserved` relies on this axiom at line 2817.

**Recommendation**: Reform Axiom 1 to accurately capture the intended execution semantics.

---

## Current Axiom Statement (Lines 1913-1920)

```coq
Axiom find_first_match_in_algorithm_implies_no_earlier_matches :
  forall rules r_head s pos,
    (forall r, In r rules -> wf_rule r) ->
    In r_head rules ->
    find_first_match r_head s (length s) = Some pos ->
    no_rules_match_before rules s pos.
```

**English**: "If `find_first_match` returns position `pos` for rule `r_head` (where `r_head ∈ rules`), then **no rules** in the entire `rules` list match at any position before `pos`."

---

## Counter-Example: The Axiom is False

### Scenario

```coq
rules = [r1; r2]
s = "example string"

(* Suppose: *)
- r2 matches at position 3 in s
- r1 matches at position 5 in s
- find_first_match r1 s (length s) = Some 5
```

### Application of Axiom

```coq
(* Axiom claims: *)
find_first_match r1 s (length s) = Some 5  (* TRUE by assumption *)
In r1 rules  (* TRUE: r1 is in [r1; r2] *)
⟹ no_rules_match_before rules s 5  (* Axiom's conclusion *)
```

### Contradiction

```coq
no_rules_match_before rules s 5 means:
  forall r, In r rules -> forall p, (p < 5)%nat -> can_apply_at r s p = false

But:
  can_apply_at r2 s 3 = true  (* r2 matches at position 3 < 5 *)
  In r2 rules  (* r2 is in [r1; r2] *)

This contradicts no_rules_match_before rules s 5.
```

**Conclusion**: The axiom statement is **INVALID** as written.

---

## Why Was This Axiom Written?

### Intended Meaning

The axiom is trying to capture the execution semantics of `apply_rules_seq`:

```coq
Fixpoint apply_rules_seq (rules : list RewriteRule) (s : PhoneticString) (fuel : nat) :=
  match fuel with
  | O => Some s
  | S fuel' =>
      match rules with
      | [] => Some s
      | r :: rest =>
          match find_first_match r s (length s) with
          | Some pos => (* Apply r at pos and restart *)
              match apply_rule_at r s pos with
              | Some s' => apply_rules_seq rules s' fuel'
              | None => (* ... *)
              end
          | None => apply_rules_seq rest s fuel'  (* Try next rule *)
          end
      end
  end.
```

**Key Observation**: The algorithm **restarts from the beginning** after each application.

### What the Algorithm Actually Guarantees

When `apply_rules_seq` finds a match for rule `r` at position `pos`:

1. **Single-rule guarantee**: `r` doesn't match at any position before `pos`
   - This follows from `find_first_match r s (length s) = Some pos`
   - Proven by existing lemmas

2. **Multi-rule guarantee (INTENDED but not captured)**: In the **execution context** where we find this match, we've been checking all rules sequentially from position 0, and no rules matched before `pos`
   - This is an execution-level property
   - **NOT** derivable from `find_first_match r_head s (length s) = Some pos` alone

---

## How the Axiom is Used

### Usage Context (Line 2803-2821)

```coq
Theorem no_rules_match_before_first_match_preserved :
  forall rules r rest s pos s' p,
    rules = r :: rest ->  (* r is the FIRST rule in rules *)
    (forall r0, In r0 rules -> wf_rule r0) ->
    (forall r0, In r0 rules -> position_dependent_context (context r0) = false) ->
    find_first_match r s (length s) = Some pos ->
    apply_rule_at r s pos = Some s' ->
    (p < pos)%nat ->
    (forall r0, In r0 rules -> can_apply_at r0 s' p = false).
Proof.
  intros rules r rest s pos s' p H_rules H_wf_all H_indep_all H_find H_apply H_p_lt.

  (* Axiom usage: *)
  assert (H_no_match_s: no_rules_match_before rules s pos).
  { eapply find_first_match_in_algorithm_implies_no_earlier_matches.
    - intros r0 H_in. apply H_wf_all. exact H_in.
    - subst rules. left. reflexivity.   (* KEY: r is the HEAD of rules *)
    - exact H_find.
  }
  (* Rest of proof... *)
```

### Key Detail

At line 2819, `subst rules. left. reflexivity` proves that `r` is the **head** (first element) of `rules`.

So the axiom is being applied when:
- `rules = r :: rest`
- `r` is the first rule
- `find_first_match r s (length s) = Some pos`

**Question**: Does this make the axiom valid for this specific case?

**Answer**: NO! Even if `r` is the first rule, other rules in `rest` could still match before position `pos`.

---

## What is Actually Needed?

### Option 1: Weaken the Axiom (Correct but Conservative)

Replace the axiom with a weaker statement that's actually true:

```coq
Lemma find_first_match_implies_single_rule_no_earlier :
  forall r s pos,
    wf_rule r ->
    find_first_match r s (length s) = Some pos ->
    (* Only r doesn't match before pos *)
    forall p, (p < pos)%nat -> can_apply_at r s p = false.
```

**Advantage**: Provable from existing infrastructure
**Disadvantage**: Doesn't give us `no_rules_match_before rules s pos`

### Option 2: Strengthen the Theorem (Add Execution Context)

Add a premise that captures the execution state:

```coq
Axiom find_first_match_with_execution_context :
  forall rules r_head s pos,
    (forall r, In r rules -> wf_rule r) ->
    In r_head rules ->
    find_first_match r_head s (length s) = Some pos ->
    (* NEW: Execution context premise *)
    (forall r, In r rules -> forall p, (p < pos)%nat -> can_apply_at r s p = false) ->
    (* THEN: This holds (trivially) *)
    no_rules_match_before rules s pos.
```

**Problem**: This makes the axiom trivial (conclusion is just restatement of premise).

### Option 3: Model Full Execution (Complete Approach)

Define an inductive predicate capturing `apply_rules_seq` execution:

```coq
Inductive ApplyRulesSeqStep : list RewriteRule -> PhoneticString -> nat -> Prop :=
| apply_seq_found : forall rules r rest s pos s',
    rules = r :: rest ->
    find_first_match r s (length s) = Some pos ->
    apply_rule_at r s pos = Some s' ->
    (* In this execution context, we know: *)
    (* - We checked r from position 0 *)
    (* - r matched first at pos *)
    (* - So r doesn't match before pos *)
    (* - Other rules in 'rest' weren't checked yet in this iteration *)
    ApplyRulesSeqStep rules s pos
| apply_seq_not_found : forall rules r rest s,
    rules = r :: rest ->
    find_first_match r s (length s) = None ->
    (* r doesn't match anywhere, try rest *)
    ApplyRulesSeqStep rest s 0.  (* Reset position for next rule *)
```

Then prove lemmas about this predicate and connect it to `no_rules_match_before`.

**Advantage**: Fully captures execution semantics
**Disadvantage**: Complex, requires significant new infrastructure

### Option 4: Reformulate the Main Theorem

Instead of trying to prove `no_rules_match_before rules s pos`, reformulate the preservation theorem to only claim what's actually provable:

```coq
Theorem single_rule_first_match_preserved :
  forall r s pos s' p,
    wf_rule r ->
    position_dependent_context (context r) = false ->
    find_first_match r s (length s) = Some pos ->
    apply_rule_at r s pos = Some s' ->
    (p < pos)%nat ->
    (* Only claim about the specific rule r *)
    can_apply_at r s' p = false.
```

Then lift this to multi-rule case by proving:

```coq
Lemma all_rules_preserved_independently :
  forall rules r s pos s' p,
    In r rules ->
    (forall r0, In r0 rules -> wf_rule r0) ->
    (forall r0, In r0 rules -> position_dependent_context (context r0) = false) ->
    find_first_match r s (length s) = Some pos ->
    apply_rule_at r s pos = Some s' ->
    (p < pos)%nat ->
    (* If each rule independently doesn't match at p in s *)
    (forall r0, In r0 rules -> can_apply_at r0 s p = false) ->
    (* Then each rule independently doesn't match at p in s' *)
    (forall r0, In r0 rules -> can_apply_at r0 s' p = false).
```

**Advantage**: Avoids the unprovable axiom entirely
**Disadvantage**: Changes the structure of the main theorem

---

## Analysis of Current Usage

### What the Theorem Actually Needs

Looking at `no_rules_match_before_first_match_preserved` (line 2803):

```coq
Theorem no_rules_match_before_first_match_preserved :
  forall rules r rest s pos s' p,
    rules = r :: rest ->
    find_first_match r s (length s) = Some pos ->
    apply_rule_at r s pos = Some s' ->
    (p < pos)%nat ->
    (* GOAL: Show all rules don't match at p in s' *)
    (forall r0, In r0 rules -> can_apply_at r0 s' p = false).
```

**Current approach** (line 2816-2821):
1. Use axiom to establish `no_rules_match_before rules s pos`
2. For each rule `r0`, get `can_apply_at r0 s p = false`
3. Apply preservation to show `can_apply_at r0 s' p = false`

**Problem**: Step 1 uses invalid axiom.

**Alternative approach**:
1. Assume as **premise**: `no_rules_match_before rules s pos`
   - Or weaken to: `forall r0, In r0 rules -> can_apply_at r0 s p = false`
2. For each rule, apply preservation lemma
3. Conclude: `forall r0, In r0 rules -> can_apply_at r0 s' p = false`

This would make the theorem more honest about its assumptions.

---

## Recommended Path Forward

### Phase 1: Document the Issue (DONE ✓)
- This analysis document

### Phase 2: Choose Reformulation Strategy

**Recommendation**: **Option 4** (Reformulate main theorem)

**Rationale**:
1. Avoids unprovable axiom
2. Makes assumptions explicit
3. Aligns theorem with what's actually provable
4. Doesn't require complex execution modeling

### Phase 3: Implementation Plan

**Step 1**: Change `no_rules_match_before_first_match_preserved` to accept premise:

```coq
Theorem no_rules_match_before_first_match_preserved :
  forall rules r rest s pos s' p,
    rules = r :: rest ->
    (forall r0, In r0 rules -> wf_rule r0) ->
    (forall r0, In r0 rules -> position_dependent_context (context r0) = false) ->
    find_first_match r s (length s) = Some pos ->
    apply_rule_at r s pos = Some s' ->
    (p < pos)%nat ->
    (* NEW PREMISE: Explicitly assume no rules match before pos in s *)
    (forall r0, In r0 rules -> can_apply_at r0 s p = false) ->
    (* CONCLUSION: Then no rules match at p in s' *)
    (forall r0, In r0 rules -> can_apply_at r0 s' p = false).
```

**Step 2**: Update proof to use premise instead of axiom

**Step 3**: Check where this theorem is used and update callers

**Step 4**: Remove Axiom 1 entirely (replace with honest premises)

---

## Impact Assessment

### Affected Theorems

Search for usage of `no_rules_match_before_first_match_preserved`:

```bash
grep -n "no_rules_match_before_first_match_preserved" position_skipping_proof.v
```

**Result**: Need to check downstream usage.

### Main Correctness Theorem

The main theorem is `position_skipping_optimization_correct`. Need to verify:
1. Does it depend on `no_rules_match_before_first_match_preserved`?
2. If yes, does the reformulation break the proof?

---

## Conclusion

**Status**: Axiom 1 as currently stated is **invalid** and should be:
1. Either **removed** and replaced with explicit premises, OR
2. **Reformulated** to accurately capture execution semantics

**Next Action**: Implement Option 4 (reformulate main theorem with explicit premises)

**Time Estimate**: 8-12 hours
- Reformulate theorem: 1-2 hours
- Update proof: 2-4 hours
- Check and update downstream usage: 2-3 hours
- Test and verify: 2-3 hours

---

**Document Version**: 1.0
**Created**: 2025-11-20
**Author**: Analysis by Claude Code
**Status**: Awaiting user review and direction
