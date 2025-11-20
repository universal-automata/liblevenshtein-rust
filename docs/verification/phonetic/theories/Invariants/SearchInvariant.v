(** * Search Invariant Lemmas - Position Skipping Optimization

    This module contains lemmas about the SearchInvariant predicate,
    which models the execution state of sequential search.

    The SearchInvariant captures that we've checked all positions before
    'pos' for all rules and found no matches. This is central to proving
    that find_first_match's behavior implies no_rules_match_before.

    Part of: Liblevenshtein.Phonetic.Verification.Invariants
*)

Require Import String List Arith Ascii Bool Nat Lia.
Require Import PhoneticRewrites.rewrite_rules.
From Liblevenshtein.Phonetic.Verification Require Import Auxiliary.Types.
From Liblevenshtein.Phonetic.Verification Require Import Auxiliary.Lib.
From Liblevenshtein.Phonetic.Verification Require Import Core.Rules.
Import ListNotations.

(** * Extraction Lemmas *)

(** Extract the no-match property from search invariant *)
Lemma search_invariant_implies_no_matches :
  forall rules s pos,
    SearchInvariant rules s pos ->
    no_rules_match_before rules s pos.
Proof.
  intros rules s pos H_inv.
  inversion H_inv. assumption.
Qed.

(** Equivalently, using no_rules_match_anywhere *)
Lemma search_invariant_implies_no_matches_anywhere :
  forall rules s pos,
    SearchInvariant rules s pos ->
    no_rules_match_anywhere rules s pos.
Proof.
  intros rules s pos H_inv.
  apply no_rules_match_anywhere_iff_before.
  apply search_invariant_implies_no_matches. assumption.
Qed.

(** * Initialization Lemmas *)

(** The search invariant holds at position 0 (base case).
    This is trivially true because there are no positions p with p < 0.
*)
Lemma search_invariant_init :
  forall rules s,
    SearchInvariant rules s 0.
Proof.
  intros rules s.
  apply search_inv_intro.
  unfold no_rules_match_before.
  intros r H_in p H_p_lt_0.
  (* p < 0 is impossible for natural numbers *)
  lia.
Qed.

(** Initialization lemma for specific rules *)
Lemma search_invariant_init_for_rules :
  forall rules s,
    (forall r, In r rules -> wf_rule r) ->
    SearchInvariant rules s 0.
Proof.
  intros rules s H_wf.
  apply search_invariant_init.
Qed.

(** * Maintenance Lemmas *)

(** If invariant holds at pos and we check position pos for rule r and it doesn't match,
    then the invariant extends to pos+1 for the single-rule list [r].
*)
Lemma search_invariant_step_single_rule :
  forall r s pos,
    wf_rule r ->
    SearchInvariant [r] s pos ->
    can_apply_at r s pos = false ->
    SearchInvariant [r] s (pos + 1).
Proof.
  intros r s pos H_wf H_inv H_no_match.
  apply search_inv_intro.
  unfold no_rules_match_before.
  intros r0 H_in p H_p_lt.
  (* r0 must be r (only rule in singleton list) *)
  destruct H_in as [H_eq | H_in_nil]; [| contradiction].
  subst r0.
  (* Case split on p *)
  destruct (lt_dec p pos) as [H_p_lt_pos | H_p_ge_pos].
  - (* p < pos: use invariant *)
    apply (search_invariant_implies_no_matches [r] s pos H_inv r).
    + left. reflexivity.
    + exact H_p_lt_pos.
  - (* p >= pos: must be p = pos (since p < pos + 1) *)
    assert (H_p_eq_pos: p = pos) by lia.
    subst p.
    (* Use H_no_match *)
    exact H_no_match.
Qed.

(** Main maintenance lemma: SearchInvariant extends from pos to pos+1
    when all rules don't match at pos.
*)
Lemma search_invariant_step_all_rules :
  forall rules s pos,
    (forall r, In r rules -> wf_rule r) ->
    SearchInvariant rules s pos ->
    (forall r, In r rules -> can_apply_at r s pos = false) ->
    SearchInvariant rules s (pos + 1).
Proof.
  intros rules s pos H_wf H_inv H_no_match_pos.
  apply search_inv_intro.
  apply no_rules_match_before_step.
  - apply (search_invariant_implies_no_matches rules s pos H_inv).
  - exact H_no_match_pos.
Qed.

(** Invariant maintenance by induction on positions *)
Lemma search_invariant_extends :
  forall rules s pos1 pos2,
    (forall r, In r rules -> wf_rule r) ->
    SearchInvariant rules s pos1 ->
    (pos1 <= pos2)%nat ->
    (forall p, (pos1 <= p < pos2)%nat -> forall r, In r rules -> can_apply_at r s p = false) ->
    SearchInvariant rules s pos2.
Proof.
  intros rules s pos1 pos2 H_wf H_inv H_le H_no_match_range.
  apply search_inv_intro.
  unfold no_rules_match_before.
  intros r H_in p H_p_lt_pos2.
  destruct (lt_dec p pos1) as [H_p_lt_pos1 | H_p_ge_pos1].
  - (* p < pos1: use original invariant *)
    apply (search_invariant_implies_no_matches rules s pos1 H_inv r H_in p H_p_lt_pos1).
  - (* pos1 <= p < pos2: use range assumption *)
    apply (H_no_match_range p).
    + lia.
    + exact H_in.
Qed.

(** * Connection to find_first_match *)

(** Key observation: if find_first_match returns None, the rule matches nowhere *)
Lemma find_first_match_none_implies_no_match_anywhere :
  forall r s fuel,
    wf_rule r ->
    find_first_match r s fuel = None ->
    (fuel >= length s)%nat ->
    forall p, (p < length s)%nat -> can_apply_at r s p = false.
Proof.
  intros r s fuel H_wf H_none H_fuel_ge p H_p_lt.

  (* Use the helper lemma to convert to find_first_match at length s *)
  assert (H_none_at_len: find_first_match r s (length s) = None).
  { eapply find_first_match_large_fuel_implies_length; eauto. }

  (* Convert to find_first_match_from *)
  assert (H_equiv: find_first_match r s (length s) =
                   find_first_match_from r s 0 (S (length s))).
  {
    assert (H_tmp: find_first_match r s (length s) =
                   find_first_match_from r s 0 (length s - 0 + 1)%nat).
    { apply find_first_match_equiv_from_zero. exact H_wf. }
    rewrite H_tmp.
    f_equal. lia.
  }

  rewrite H_equiv in H_none_at_len.

  (* Apply the find_first_match_from helper *)
  eapply find_first_match_from_none_implies_all_fail; eauto.
  lia.
Qed.

(** If find_first_match returns Some pos for a rule in the list,
    and all other rules in the list match nowhere, then
    SearchInvariant holds for the entire list at pos.

    This captures the sequential execution context where we try all rules
    before the one that matched.
*)
Lemma find_first_match_with_all_rules_fail_before :
  forall rules r_head s pos,
    (forall r, In r rules -> wf_rule r) ->
    In r_head rules ->
    find_first_match r_head s (length s) = Some pos ->
    (* ASSUMPTION: All other rules don't match anywhere before pos *)
    (forall r, In r rules -> r <> r_head -> forall p, (p < pos)%nat -> can_apply_at r s p = false) ->
    SearchInvariant rules s pos.
Proof.
  intros rules r_head s pos H_wf_all H_in_head H_find H_others_no_match.
  apply search_inv_intro.
  unfold no_rules_match_before.
  intros r H_in_r p H_p_lt.
  (* Case split: is r = r_head or r ≠ r_head? *)
  destruct (RewriteRule_eq_dec r r_head) as [H_eq | H_neq].
  - (* r = r_head: use find_first_match_is_first *)
    subst r.
    eapply find_first_match_is_first; eauto.
    lia. (* length s - length s = 0 <= p *)
  - (* r ≠ r_head: use assumption *)
    apply (H_others_no_match r H_in_r H_neq p H_p_lt).
Qed.

(** * Establishment Lemmas *)

(** Lemma: When find_first_match finds a position for a single rule,
    all earlier positions don't match *)
Lemma find_first_match_establishes_invariant_single :
  forall r s pos,
    wf_rule r ->
    find_first_match r s (length s) = Some pos ->
    no_rules_match_before [r] s pos.
Proof.
  intros r s pos H_wf H_find.
  unfold no_rules_match_before.
  intros r0 H_in p H_p_lt.
  (* r0 must be r since [r] is a singleton list *)
  destruct H_in as [H_eq | H_in_empty].
  - (* r0 = r *)
    subst r0.
    (* Use find_first_match_is_first lemma *)
    eapply find_first_match_is_first; eauto.
    (* Need to show: length s - length s <= p *)
    lia.
  - (* r0 ∈ [] - impossible *)
    inversion H_in_empty.
Qed.

(** * Useful Equivalences *)

(** Lemma: If no early matches exist, both find the same match (or both find none) *)
Lemma find_first_match_from_equivalent_when_no_early_matches :
  forall r s start_pos,
    wf_rule r ->
    no_early_matches r s start_pos ->
    (forall pos, find_first_match_from r s start_pos (length s - start_pos + 1) = Some pos ->
                 find_first_match r s (length s) = Some pos).
Proof.
  intros r s start_pos H_wf H_no_early pos H_found.
  unfold no_early_matches in H_no_early.

  (* find_first_match_from found pos, so can_apply_at r s pos = true *)
  assert (H_can_apply: can_apply_at r s pos = true).
  {
    eapply find_first_match_from_implies_can_apply. eauto.
  }

  (* pos >= start_pos *)
  assert (H_bound: (start_pos <= pos)%nat).
  { eapply find_first_match_from_lower_bound. eauto. }

  (* pos < length s: from the search bounds and can_apply_at being true *)
  assert (H_pos_in_bounds: (pos < length s)%nat).
  {
    (* find_first_match_from searched up to position start_pos + n - 1 where n = length s - start_pos + 1 *)
    assert (H_upper: (pos < start_pos + (length s - start_pos + 1))%nat).
    { eapply find_first_match_from_upper_bound. eauto. }
    (* Simplify the bound *)
    destruct (le_lt_dec start_pos (length s)) as [H_start_ok | H_start_large].
    - (* start_pos <= length s, so expression simplifies *)
      assert (H_rewrite: (start_pos + (length s - start_pos + 1) = length s + 1)%nat) by lia.
      rewrite H_rewrite in H_upper.
      (* pos < length s + 1 means pos <= length s *)
      (* To show pos < length s, need to exclude pos = length s *)
      destruct (Nat.eq_dec pos (length s)) as [H_eq | H_ne].
      * (* pos = length s - but can_apply_at at or beyond length s is false for wf rules *)
        subst pos.
        (* This contradicts H_can_apply *)
        assert (H_false: can_apply_at r s (length s) = false).
        { apply can_apply_at_beyond_length. exact H_wf. lia. }
        rewrite H_false in H_can_apply.
        discriminate.
      * (* pos <> length s, and pos <= length s, so pos < length s *)
        lia.
    - (* start_pos > length s, then length s - start_pos = 0 *)
      (* So search range is [start_pos, start_pos + 1) *)
      (* But if can_apply_at is true at pos, and pos >= start_pos > length s *)
      (* This contradicts can_apply_at requiring valid position *)
      (* can_apply_at checks context and pattern at position pos *)
      (* For position >= length s, context matching could succeed, but pattern matching *)
      (* requires pos + pattern_length <= length s, which fails if pos >= length s and pattern non-empty *)
      (* H_upper: pos < start_pos + (length s - start_pos + 1) *)
      (* With length s - start_pos = 0, this becomes pos < start_pos + 1 *)
      (* Which means pos <= start_pos *)
      (* Since start_pos > length s and pos >= start_pos, we have pos >= length s *)
      (* But can_apply_at at position >= length s should be false for non-empty patterns *)
      (* This is getting complex - for now, use a simpler bound *)
      (* Actually, from H_upper, pos < start_pos + 1, so pos <= start_pos *)
      (* Combined with H_bound (start_pos <= pos), we get pos = start_pos *)
      assert (H_pos_eq: pos = start_pos) by lia.
      subst pos.
      (* Now start_pos > length s, but can_apply_at r s start_pos = true *)
      (* This contradicts can_apply_at being false beyond string length for wf rules *)
      assert (H_false: can_apply_at r s start_pos = false).
      { apply can_apply_at_beyond_length. exact H_wf. lia. }
      rewrite H_false in H_can_apply.
      discriminate.
  }

  (* Use find_first_match_finds_first_true to show find_first_match finds pos *)
  apply find_first_match_finds_first_true.
  - exact H_pos_in_bounds.
  - lia.
  - exact H_can_apply.
  - (* For all p in [0, pos), can_apply_at r s p = false *)
    intros p H_range H_lt.
    destruct (Nat.lt_ge_cases p start_pos) as [H_before_start | H_after_start].
    + (* p < start_pos: use H_no_early *)
      apply H_no_early. exact H_before_start.
    + (* start_pos <= p < pos *)
      (* Use find_first_match_from_is_first *)
      eapply find_first_match_from_is_first; eauto.
Qed.
