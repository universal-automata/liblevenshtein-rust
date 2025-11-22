(** * Pattern Matching Properties - Simple Helpers

    This module contains simple helper lemmas for pattern matching properties
    with lightweight proofs. Designed for reusability across pattern matching
    verification tasks.

    Part of: Liblevenshtein.Phonetic.Verification.Patterns
    Renamed from PatternHelpers_Mismatch_Simple.v for better reusability.
*)

Require Import String List Arith Ascii Bool Nat Lia.
Require Import PhoneticRewrites.rewrite_rules.
From Liblevenshtein.Phonetic.Verification Require Import Auxiliary.Types.
From Liblevenshtein.Phonetic.Verification Require Import Auxiliary.Lib.
From Liblevenshtein.Phonetic.Verification Require Import Core.Rules.
Import ListNotations.

(** * Pattern Mismatch Helpers *)

(** Lemma: If nth_error returns None in pattern range, pattern doesn't match *)
Lemma nth_error_none_implies_no_pattern_match :
  forall pat s p i,
    (p <= i < p + length pat)%nat ->
    nth_error s i = None ->
    pattern_matches_at pat s p = false.
Proof.
  intros pat s p i H_i_range H_none.
  generalize dependent p.
  generalize dependent i.
  induction pat as [| ph pat' IH].
  - (* Empty pattern *)
    intros. simpl in H_i_range. lia.
  - (* Pattern ph :: pat' *)
    intros i H_none p H_i_range.
    simpl.
    destruct (lt_dec i p) as [H_i_lt_p | H_i_ge_p].
    + (* i < p: impossible given H_i_range *)
      lia.
    + (* i >= p *)
      destruct (Nat.eq_dec i p) as [H_i_eq_p | H_i_ne_p].
      * (* i = p *)
        subst i.
        rewrite H_none.
        reflexivity.
      * (* i > p *)
        assert (H_i_gt_p: (i > p)%nat) by lia.
        (* i is in the tail pattern *)
        destruct (nth_error s p) eqn:E_p.
        -- (* s has phone at p *)
           destruct (Phone_eqb ph p0) eqn:E_eq.
           ++ (* Phones match at p, recurse *)
              apply (IH i H_none (S p)).
              simpl in H_i_range. lia.
           ++ (* Phones don't match at p *)
              reflexivity.
        -- (* s is None at p *)
           reflexivity.
Qed.

(** Lemma: If phones mismatch at a position, pattern doesn't match *)
Lemma phone_mismatch_implies_no_pattern_match :
  forall pat s p i ph pat_ph,
    (p <= i < p + length pat)%nat ->
    nth_error s i = Some ph ->
    nth_error pat (i - p) = Some pat_ph ->
    Phone_eqb ph pat_ph = false ->
    pattern_matches_at pat s p = false.
Proof.
  intros pat s p i ph pat_ph H_i_range H_s_i H_pat_i H_neq.
  revert p i ph pat_ph H_i_range H_s_i H_pat_i H_neq.
  induction pat as [| ph_pat pat' IH].
  - (* Empty pattern *)
    intros. simpl in H_i_range. lia.
  - (* Pattern ph_pat :: pat' *)
    intros p i ph pat_ph H_i_range H_s_i H_pat_i H_neq_phones.
    simpl.
    destruct (Nat.eq_dec i p) as [H_i_eq_p | H_i_ne_p].
    + (* i = p: mismatch at first position *)
      subst i.
      replace (p - p)%nat with 0%nat in H_pat_i by lia.
      simpl in H_pat_i.
      inversion H_pat_i; subst pat_ph.
      rewrite H_s_i.
      (* Goal: (if Phone_eqb ph_pat ph then pattern_matches_at pat' s (S p) else false) = false *)
      (* We have H_neq_phones: Phone_eqb ph ph_pat = false *)
      (* Use case analysis *)
      destruct (Phone_eqb ph_pat ph) eqn:E_eqb.
      * (* Phone_eqb ph_pat ph = true contradicts H_neq_phones *)
        (* Phone_eqb is symmetric *)
        exfalso.
        (* Use Phone_eqb_sym from rewrite_rules.v *)
        rewrite Phone_eqb_sym in E_eqb.
        rewrite E_eqb in H_neq_phones.
        discriminate H_neq_phones.
      * (* Phone_eqb ph_pat ph = false, so if-then-else is false *)
        reflexivity.
    + (* i ≠ p: mismatch is in tail *)
      assert (H_i_gt_p: (i > p)%nat) by lia.
      destruct (nth_error s p) eqn:E_p.
      * (* s has phone at p *)
        destruct (Phone_eqb ph_pat p0) eqn:E_eq.
        -- (* Match at p, recurse to tail *)
           apply (IH (S p) i ph pat_ph).
           ++ (* S p <= i < S p + length pat' *)
              simpl in H_i_range. lia.
           ++ (* nth_error s i = Some ph *)
              exact H_s_i.
           ++ (* nth_error pat' (i - S p) = Some pat_ph *)
              replace (i - p)%nat with (S (i - S p))%nat in H_pat_i by lia.
              simpl in H_pat_i.
              exact H_pat_i.
           ++ (* Phone_eqb ph pat_ph = false *)
              exact H_neq_phones.
        -- (* Mismatch at p *)
           reflexivity.
      * (* s is None at p *)
        reflexivity.
Qed.
