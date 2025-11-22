(** * Pattern Preservation Lemmas - Position Skipping Optimization

    This module contains lemmas about how pattern matching and context matching
    are preserved across transformations. These are fundamental properties needed
    to prove that the position-skipping optimization is sound.

    **Key Results**:
    - Context preservation at earlier positions
    - Pattern matching preservation before transformation point
    - No new early matches after transformation

    Part of: Liblevenshtein.Phonetic.Verification.Patterns
*)

Require Import String List Arith Ascii Bool Nat Lia.
Require Import PhoneticRewrites.rewrite_rules.
From Liblevenshtein.Phonetic.Verification Require Import Auxiliary.Types.
From Liblevenshtein.Phonetic.Verification Require Import Auxiliary.Lib.
From Liblevenshtein.Phonetic.Verification Require Import Core.Rules.
Import ListNotations.

(** * Context Preservation *)

(** Definition: A context preserves its truth value at earlier positions after a transformation *)
Definition context_preserved_at_earlier_positions (ctx : Context) (s s' : PhoneticString) (transform_pos : nat) : Prop :=
  forall pos, (pos < transform_pos)%nat ->
    context_matches ctx s pos = context_matches ctx s' pos.

(** Lemma: Initial context is always preserved (only depends on pos = 0) *)
Lemma initial_context_preserved :
  forall s s' transform_pos,
    (transform_pos > 0)%nat ->
    context_preserved_at_earlier_positions Initial s s' transform_pos.
Proof.
  intros s s' transform_pos H_pos_gt.
  unfold context_preserved_at_earlier_positions.
  intros pos H_lt.
  unfold context_matches.
  destruct (Nat.eq_dec pos 0) as [H_eq | H_ne].
  - subst pos. reflexivity.
  - reflexivity.
Qed.

(** Lemma: Anywhere context is always preserved (always matches) *)
Lemma anywhere_context_preserved :
  forall s s' transform_pos,
    context_preserved_at_earlier_positions Anywhere s s' transform_pos.
Proof.
  intros s s' transform_pos.
  unfold context_preserved_at_earlier_positions.
  intros pos H_lt.
  unfold context_matches.
  reflexivity.
Qed.

(** Lemma: BeforeVowel context is preserved at earlier positions *)
Lemma before_vowel_context_preserved :
  forall vowels s s' transform_pos,
    (forall i, (i < transform_pos)%nat -> nth_error s i = nth_error s' i) ->
    context_preserved_at_earlier_positions (BeforeVowel vowels) s s' transform_pos.
Proof.
  intros vowels s s' transform_pos H_prefix.
  unfold context_preserved_at_earlier_positions.
  intros pos H_lt.
  unfold context_matches.
  rewrite <- (H_prefix pos H_lt).
  reflexivity.
Qed.

(** Lemma: BeforeConsonant context is preserved at earlier positions *)
Lemma before_consonant_context_preserved :
  forall consonants s s' transform_pos,
    (forall i, (i < transform_pos)%nat -> nth_error s i = nth_error s' i) ->
    context_preserved_at_earlier_positions (BeforeConsonant consonants) s s' transform_pos.
Proof.
  intros consonants s s' transform_pos H_prefix.
  unfold context_preserved_at_earlier_positions.
  intros pos H_lt.
  unfold context_matches.
  rewrite <- (H_prefix pos H_lt).
  reflexivity.
Qed.

(** Lemma: AfterConsonant context is preserved at earlier positions *)
Lemma after_consonant_context_preserved :
  forall consonants s s' transform_pos,
    (forall i, (i < transform_pos)%nat -> nth_error s i = nth_error s' i) ->
    context_preserved_at_earlier_positions (AfterConsonant consonants) s s' transform_pos.
Proof.
  intros consonants s s' transform_pos H_prefix.
  unfold context_preserved_at_earlier_positions.
  intros pos H_lt.
  unfold context_matches.
  destruct pos as [| pos'].
  - reflexivity.
  - assert (H_pos'_lt: (pos' < transform_pos)%nat) by lia.
    rewrite <- (H_prefix pos' H_pos'_lt).
    reflexivity.
Qed.

(** Lemma: AfterVowel context is preserved at earlier positions *)
Lemma after_vowel_context_preserved :
  forall vowels s s' transform_pos,
    (forall i, (i < transform_pos)%nat -> nth_error s i = nth_error s' i) ->
    context_preserved_at_earlier_positions (AfterVowel vowels) s s' transform_pos.
Proof.
  intros vowels s s' transform_pos H_prefix.
  unfold context_preserved_at_earlier_positions.
  intros pos H_lt.
  unfold context_matches.
  destruct pos as [| pos'].
  - reflexivity.
  - assert (H_pos'_lt: (pos' < transform_pos)%nat) by lia.
    rewrite <- (H_prefix pos' H_pos'_lt).
    reflexivity.
Qed.

(** * Pattern Matching Preservation *)

(** Lemma: Pattern matching is preserved at positions before transformation *)
Lemma pattern_matches_preserved_before_transformation :
  forall pat s s' pos transform_pos,
    (forall i, (i < transform_pos)%nat -> nth_error s i = nth_error s' i) ->
    (pos + length pat <= transform_pos)%nat ->
    pattern_matches_at pat s pos = pattern_matches_at pat s' pos.
Proof.
  intros pat.
  induction pat as [| p ps IH]; intros s s' pos transform_pos H_prefix H_bound.
  - (* Base case: empty pattern *)
    simpl. reflexivity.
  - (* Inductive case: p :: ps *)
    simpl.
    simpl in H_bound.
    assert (H_pos_lt: (pos < transform_pos)%nat) by lia.
    rewrite <- (H_prefix pos H_pos_lt).
    destruct (nth_error s pos) as [p'|] eqn:E_nth.
    + destruct (Phone_eqb p p') eqn:E_eq.
      * apply (IH s s' (S pos) transform_pos).
        ** exact H_prefix.
        ** lia.
      * reflexivity.
    + reflexivity.
Qed.

(** * Transformation Preservation *)

(** Lemma: After applying a position-independent rule at pos, no new matches appear before pos
    (for patterns that don't extend into the modified region) *)
Lemma no_new_early_matches_after_transformation :
  forall r s pos s' r' p,
    wf_rule r ->
    wf_rule r' ->
    position_dependent_context (context r') = false ->
    apply_rule_at r s pos = Some s' ->
    (p < pos)%nat ->
    (p + length (pattern r') <= pos)%nat ->
    can_apply_at r' s' p = true ->
    can_apply_at r' s p = true.
Proof.
  intros r s pos s' r' p H_wf H_wf' H_indep H_apply H_p_lt H_pattern_bound H_can_s'.

  (* Step 1: Extract prefix preservation *)
  assert (H_prefix: forall i, (i < pos)%nat -> nth_error s i = nth_error s' i).
  { intros i H_i_lt.
    assert (H_pos_valid: (pos < length s)%nat) by (apply (apply_rule_at_pos_valid r s pos s' H_wf H_apply)).
    unfold apply_rule_at in H_apply.
    destruct (context_matches (context r) s pos) eqn:E_ctx; try discriminate.
    destruct (pattern_matches_at (pattern r) s pos) eqn:E_pat; try discriminate.
    injection H_apply as H_s'.
    assert (H_firstn_eq: nth_error (firstn pos s) i = nth_error s i).
    {
      rewrite nth_error_firstn.
      assert (H_ltb: (i <? pos)%nat = true) by (apply Nat.ltb_lt; exact H_i_lt).
      rewrite H_ltb.
      reflexivity.
    }
    assert (H_s'_eq: nth_error s' i = nth_error (firstn pos s) i).
    {
      rewrite <- H_s'.
      rewrite nth_error_app1.
      - reflexivity.
      - rewrite firstn_length.
        rewrite Nat.min_l by lia.
        exact H_i_lt.
    }
    rewrite H_s'_eq.
    rewrite H_firstn_eq.
    reflexivity.
  }

  (* Step 2: Unfold can_apply_at and analyze H_can_s' *)
  unfold can_apply_at in H_can_s'.
  destruct (context_matches (context r') s' p) eqn:E_ctx_s'; try discriminate.
  destruct (pattern_matches_at (pattern r') s' p) eqn:E_pat_s'; try discriminate.
  clear H_can_s'.

  (* Step 3: Case analysis on context type *)
  unfold can_apply_at.
  destruct (context r') eqn:E_ctx.

  - (* Initial *)
    assert (H_ctx_eq: context_matches Initial s p = context_matches Initial s' p).
    { pose proof (initial_context_preserved s s' pos) as H_pres.
      assert (H_pos_gt: (pos > 0)%nat) by lia.
      specialize (H_pres H_pos_gt).
      unfold context_preserved_at_earlier_positions in H_pres.
      apply (H_pres p H_p_lt).
    }
    rewrite H_ctx_eq, E_ctx_s'.
    rewrite (pattern_matches_preserved_before_transformation (pattern r') s s' p pos); auto.

  - (* Final - contradiction *)
    simpl in H_indep.
    discriminate H_indep.

  - (* BeforeVowel *)
    assert (H_ctx_eq: context_matches (BeforeVowel l) s p = context_matches (BeforeVowel l) s' p).
    { pose proof (before_vowel_context_preserved l s s' pos H_prefix) as H_pres.
      unfold context_preserved_at_earlier_positions in H_pres.
      apply (H_pres p H_p_lt).
    }
    rewrite H_ctx_eq, E_ctx_s'.
    rewrite (pattern_matches_preserved_before_transformation (pattern r') s s' p pos); auto.

  - (* AfterConsonant *)
    assert (H_ctx_eq: context_matches (AfterConsonant l) s p = context_matches (AfterConsonant l) s' p).
    { pose proof (after_consonant_context_preserved l s s' pos H_prefix) as H_pres.
      unfold context_preserved_at_earlier_positions in H_pres.
      apply (H_pres p H_p_lt).
    }
    rewrite H_ctx_eq, E_ctx_s'.
    rewrite (pattern_matches_preserved_before_transformation (pattern r') s s' p pos); auto.

  - (* BeforeConsonant *)
    assert (H_ctx_eq: context_matches (BeforeConsonant l) s p = context_matches (BeforeConsonant l) s' p).
    { pose proof (before_consonant_context_preserved l s s' pos H_prefix) as H_pres.
      unfold context_preserved_at_earlier_positions in H_pres.
      apply (H_pres p H_p_lt).
    }
    rewrite H_ctx_eq, E_ctx_s'.
    rewrite (pattern_matches_preserved_before_transformation (pattern r') s s' p pos); auto.

  - (* AfterVowel *)
    assert (H_ctx_eq: context_matches (AfterVowel l) s p = context_matches (AfterVowel l) s' p).
    { pose proof (after_vowel_context_preserved l s s' pos H_prefix) as H_pres.
      unfold context_preserved_at_earlier_positions in H_pres.
      apply (H_pres p H_p_lt).
    }
    rewrite H_ctx_eq, E_ctx_s'.
    rewrite (pattern_matches_preserved_before_transformation (pattern r') s s' p pos); auto.

  - (* Anywhere *)
    assert (H_ctx_eq: context_matches Anywhere s p = context_matches Anywhere s' p).
    { pose proof (anywhere_context_preserved s s' pos) as H_pres.
      unfold context_preserved_at_earlier_positions in H_pres.
      apply (H_pres p H_p_lt).
    }
    rewrite H_ctx_eq, E_ctx_s'.
    rewrite (pattern_matches_preserved_before_transformation (pattern r') s s' p pos); auto.
Qed.
