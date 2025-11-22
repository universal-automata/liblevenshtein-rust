(** * Pattern Helper Lemmas - Basic Infrastructure

    This module contains basic pattern helper lemmas with lightweight proofs.

    Part of: Liblevenshtein.Phonetic.Verification.Patterns
    Split from PatternHelpers.v to reduce memory usage during compilation.
*)

Require Import String List Arith Ascii Bool Nat Lia.
Require Import PhoneticRewrites.rewrite_rules.
From Liblevenshtein.Phonetic.Verification Require Import Auxiliary.Types.
From Liblevenshtein.Phonetic.Verification Require Import Auxiliary.Lib.
From Liblevenshtein.Phonetic.Verification Require Import Core.Rules.
Import ListNotations.

(** * Prefix Preservation Lemma *)

(** Lemma: apply_rule_at preserves phones before the match position *)
Lemma apply_rule_at_preserves_prefix :
  forall r s pos s',
    wf_rule r ->
    apply_rule_at r s pos = Some s' ->
    (forall i, (i < pos)%nat -> nth_error s i = nth_error s' i).
Proof.
  intros r s pos s' H_wf H_apply i H_lt.

  (* First, establish that pos < length s using existing lemma *)
  assert (H_pos_valid: (pos < length s)%nat).
  { eapply apply_rule_at_pos_valid; eauto. }

  unfold apply_rule_at in H_apply.
  destruct (context_matches (context r) s pos) eqn:E_ctx; try discriminate.
  destruct (pattern_matches_at (pattern r) s pos) eqn:E_pat; try discriminate.
  injection H_apply as H_s'.

  (* Goal: nth_error s i = nth_error s' i *)
  (* Strategy: Prove each direction separately then combine *)

  (* First, show what nth_error (firstn pos s) i equals *)
  assert (H_firstn_eq: nth_error (firstn pos s) i = nth_error s i).
  {
    rewrite nth_error_firstn.
    (* This gives: if i <? pos then nth_error s i else None *)
    assert (H_ltb: (i <? pos)%nat = true) by (apply Nat.ltb_lt; exact H_lt).
    rewrite H_ltb.
    reflexivity.
  }

  (* Second, show what nth_error s' i equals *)
  assert (H_s'_eq: nth_error s' i = nth_error (firstn pos s) i).
  {
    rewrite <- H_s'.
    (* Goal: nth_error ((firstn pos s) ++ ...) i = nth_error (firstn pos s) i *)
    rewrite nth_error_app1.
    - reflexivity.
    - (* Show i < length (firstn pos s) *)
      rewrite firstn_length.
      rewrite Nat.min_l by lia.
      exact H_lt.
  }

  (* Combine the two *)
  rewrite H_s'_eq.
  rewrite H_firstn_eq.
  reflexivity.
Qed.

(** * Context Preservation Lemmas (with apply_rule_at) *)

(** Lemma: Initial context is preserved at earlier positions *)
Lemma initial_context_preserved :
  forall r s pos s' p,
    wf_rule r ->
    apply_rule_at r s pos = Some s' ->
    (p < pos)%nat ->
    context_matches Initial s p = context_matches Initial s' p.
Proof.
  intros r s pos s' p H_wf H_apply H_lt.
  (* Initial only matches at position 0 *)
  (* Both check if p = 0; since p is the same in both, they agree *)
  simpl. reflexivity.
Qed.

(** Lemma: BeforeVowel context is preserved at earlier positions *)
Lemma before_vowel_context_preserved :
  forall vowels r s pos s' p,
    wf_rule r ->
    apply_rule_at r s pos = Some s' ->
    (p < pos)%nat ->
    (forall i, (i < pos)%nat -> nth_error s i = nth_error s' i) ->
    context_matches (BeforeVowel vowels) s p = context_matches (BeforeVowel vowels) s' p.
Proof.
  intros vowels r s pos s' p H_wf H_apply H_lt H_prefix.
  simpl.
  (* BeforeVowel checks nth_error s p *)
  rewrite <- (H_prefix p H_lt).
  reflexivity.
Qed.

(** Lemma: BeforeConsonant context is preserved at earlier positions *)
Lemma before_consonant_context_preserved :
  forall consonants r s pos s' p,
    wf_rule r ->
    apply_rule_at r s pos = Some s' ->
    (p < pos)%nat ->
    (forall i, (i < pos)%nat -> nth_error s i = nth_error s' i) ->
    context_matches (BeforeConsonant consonants) s p = context_matches (BeforeConsonant consonants) s' p.
Proof.
  intros consonants r s pos s' p H_wf H_apply H_lt H_prefix.
  simpl.
  (* BeforeConsonant checks nth_error s p *)
  rewrite <- (H_prefix p H_lt).
  reflexivity.
Qed.

(** Lemma: AfterVowel context is preserved at earlier positions *)
Lemma after_vowel_context_preserved :
  forall vowels r s pos s' p,
    wf_rule r ->
    apply_rule_at r s pos = Some s' ->
    (p < pos)%nat ->
    (forall i, (i < pos)%nat -> nth_error s i = nth_error s' i) ->
    context_matches (AfterVowel vowels) s p = context_matches (AfterVowel vowels) s' p.
Proof.
  intros vowels r s pos s' p H_wf H_apply H_lt H_prefix.
  simpl.
  (* AfterVowel checks nth_error s (p - 1) when p > 0 *)
  destruct p as [| p'].
  - (* p = 0: AfterVowel returns false in both cases *)
    reflexivity.
  - (* p = S p': need to show nth_error s p' = nth_error s' p' *)
    assert (H_p'_lt: (p' < pos)%nat) by lia.
    rewrite <- (H_prefix p' H_p'_lt).
    reflexivity.
Qed.

(** Lemma: AfterConsonant context is preserved at earlier positions *)
Lemma after_consonant_context_preserved :
  forall consonants r s pos s' p,
    wf_rule r ->
    apply_rule_at r s pos = Some s' ->
    (p < pos)%nat ->
    (forall i, (i < pos)%nat -> nth_error s i = nth_error s' i) ->
    context_matches (AfterConsonant consonants) s p = context_matches (AfterConsonant consonants) s' p.
Proof.
  intros consonants r s pos s' p H_wf H_apply H_lt H_prefix.
  simpl.
  (* AfterConsonant checks nth_error s (p - 1) when p > 0 *)
  destruct p as [| p'].
  - (* p = 0: AfterConsonant returns false in both cases *)
    reflexivity.
  - (* p = S p': need to show nth_error s p' = nth_error s' p' *)
    assert (H_p'_lt: (p' < pos)%nat) by lia.
    rewrite <- (H_prefix p' H_p'_lt).
    reflexivity.
Qed.

(** * Region Structure Lemma *)

(** Lemma: Characterize nth_error in transformed string by region *)
Lemma apply_rule_at_region_structure :
  forall r s pos s',
    wf_rule r ->
    apply_rule_at r s pos = Some s' ->
    forall i,
      (* Before transformation: preserved *)
      ((i < pos)%nat -> nth_error s i = nth_error s' i) /\
      (* In replacement region: from replacement *)
      ((pos <= i < pos + length (replacement r))%nat ->
        nth_error s' i = nth_error (replacement r) (i - pos)) /\
      (* After replacement: shifted *)
      ((i >= pos + length (replacement r))%nat ->
        nth_error s' i = nth_error s (i + length (pattern r) - length (replacement r))).
Proof.
  intros r s pos s' H_wf H_apply i.

  (* First, establish that pos < length s using existing lemma *)
  assert (H_pos_valid: (pos < length s)%nat) by (eapply apply_rule_at_pos_valid; eauto).

  split; [ | split].

  - (* Before transformation *)
    intro H_i_before.
    apply (apply_rule_at_preserves_prefix r s pos s' H_wf H_apply i H_i_before).

  - (* In replacement region *)
    intro H_i_in_repl.

    (* Unfold apply_rule_at *)
    unfold apply_rule_at in H_apply.
    destruct (context_matches (context r) s pos) eqn:E_ctx; try discriminate.
    destruct (pattern_matches_at (pattern r) s pos) eqn:E_pat; try discriminate.

    (* apply_rule_at returns: Some (prefix ++ replacement ++ suffix) *)
    (* where prefix = firstn pos s, suffix = skipn (pos + length (pattern r)) s *)
    simpl in H_apply.
    injection H_apply as H_eq_s'.
    subst s'.

    (* For i in [pos, pos + length(replacement)), nth_error s' i comes from replacement *)
    rewrite nth_error_app2.
    + (* i >= length (firstn pos s) *)
      rewrite length_firstn.
      rewrite Nat.min_l by lia.
      rewrite nth_error_app1 by lia.
      (* nth_error (replacement r) (i - pos) *)
      replace (i - pos)%nat with (i - pos)%nat by lia.
      reflexivity.
    + (* length (firstn pos s) <= i *)
      rewrite length_firstn.
      rewrite Nat.min_l by lia.
      lia.

  - (* After replacement *)
    intro H_i_after.

    unfold apply_rule_at in H_apply.
    destruct (context_matches (context r) s pos) eqn:E_ctx2; try discriminate.
    destruct (pattern_matches_at (pattern r) s pos) eqn:E_pat2; try discriminate.

    simpl in H_apply.
    injection H_apply as H_eq_s'.
    subst s'.

    (* For i >= pos + length(replacement), nth_error s' i comes from suffix *)
    rewrite nth_error_app2.
    + (* i >= length (firstn pos s) *)
      rewrite length_firstn.
      rewrite Nat.min_l by lia.
      rewrite nth_error_app2 by lia.
      rewrite nth_error_skipn.
      (* Need to show correspondence *)
      f_equal. lia.
    + rewrite length_firstn.
      rewrite Nat.min_l by lia.
      lia.
Qed.
