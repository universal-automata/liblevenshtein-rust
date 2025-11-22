(** * Pattern Helper Lemmas - Mismatch Characterization

    This module contains lemmas for characterizing pattern matching failures
    and identifying where mismatches occur.

    Part of: Liblevenshtein.Phonetic.Verification.Patterns
    Split from PatternHelpers.v to reduce memory usage during compilation.
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

(** * Missing Pattern Mismatch Lemmas *)

(** These lemmas characterize pattern matching failures and are needed
    by PatternOverlap.v for the overlap preservation proof. *)

(** Lemma: If pattern_matches_at returns false, there exists a position where matching fails *)
Lemma pattern_matches_at_has_mismatch :
  forall pat s p,
    pattern_matches_at pat s p = false ->
    (length pat > 0)%nat ->
    exists i,
      (p <= i < p + length pat)%nat /\
      (nth_error s i = None \/
       exists ph pat_ph,
         nth_error s i = Some ph /\
         nth_error pat (i - p) = Some pat_ph /\
         Phone_eqb ph pat_ph = false).
Proof.
  intros pat s p H_no_match H_len_pos.

  (* Induction on pattern structure *)
  generalize dependent p.
  induction pat as [| ph_pat pat' IH].

  - (* Empty pattern: contradicts H_len_pos *)
    simpl in H_len_pos. lia.

  - (* Pattern ph_pat :: pat' *)
    intros p H_no_match.
    simpl in H_no_match.

    (* Check what nth_error s p returns *)
    destruct (nth_error s p) as [ph_s | ] eqn:E_nth.

    + (* nth_error s p = Some ph_s *)
      destruct (Phone_eqb ph_pat ph_s) eqn:E_eq.

      * (* Phones match: failure must be in tail *)
        (* Apply IH to pat' *)
        destruct pat' as [| ph2 pat''] eqn:E_pat'.

        -- (* pat' is empty: pattern_matches_at returns true, contradiction *)
           simpl in H_no_match. discriminate H_no_match.

        -- (* pat' is non-empty *)
           assert (H_len_pos': (length (ph2 :: pat'') > 0)%nat) by (simpl; lia).
           assert (H_no_match': pattern_matches_at (ph2 :: pat'') s (S p) = false) by exact H_no_match.

           specialize (IH H_len_pos' (S p) H_no_match').
           destruct IH as [i [H_i_range H_i_mismatch]].

           exists i.
           split.
           ++ (* S p <= i < S p + length (ph2 :: pat'') *)
              (* Need to show: p <= i < p + length (ph_pat :: ph2 :: pat'') *)
              simpl. simpl in H_i_range. lia.
           ++ (* Mismatch property *)
              destruct H_i_mismatch as [H_none | H_mismatch].
              ** left. exact H_none.
              ** right. destruct H_mismatch as [ph [pat_ph [H_s_i [H_pat_i H_neq]]]].
                 exists ph, pat_ph.
                 split; [exact H_s_i | ].
                 split; [ | exact H_neq].
                 (* Show nth_error (ph_pat :: ph2 :: pat'') (i - p) = Some pat_ph *)
                 (* Since i >= S p, we have i - p >= 1 *)
                 (* So nth_error (ph_pat :: pat') (i - p) = nth_error pat' (i - p - 1) *)
                 (*                                         = nth_error pat' (i - S p) *)
                 assert (H_i_ge: (i >= S p)%nat) by lia.
                 replace (i - p)%nat with (S (i - S p))%nat by lia.
                 simpl. subst pat'. exact H_pat_i.

      * (* Phones don't match at position p *)
        exists p.
        split.
        -- (* p <= p < p + length (ph_pat :: pat') *)
           simpl. lia.
        -- (* Mismatch at p *)
           right.
           exists ph_s, ph_pat.
           split; [exact E_nth | ].
           split.
           ++ (* nth_error (ph_pat :: pat') (p - p) = Some ph_pat *)
              replace (p - p)%nat with 0%nat by lia.
              simpl. reflexivity.
           ++ (* Phone_eqb ph_s ph_pat = false *)
              (* E_eq says Phone_eqb ph_pat ph_s = false *)
              (* Need Phone_eqb ph_s ph_pat = false *)
              (* Phone_eqb is symmetric, so we can show this *)
              unfold Phone_eqb in *.
              destruct ph_pat, ph_s; simpl in *;
                try exact E_eq;
                (* For char cases, use eqb_sym from Ascii *)
                try (rewrite Ascii.eqb_sym; exact E_eq);
                (* For digraph cases with multiple chars *)
                try (rewrite !Ascii.eqb_sym; exact E_eq).

    + (* nth_error s p = None: string too short *)
      exists p.
      split.
      * simpl. lia.
      * left. exact E_nth.
Qed.
