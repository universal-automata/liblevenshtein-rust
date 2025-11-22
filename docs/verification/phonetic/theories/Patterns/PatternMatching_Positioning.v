(** * Pattern Matching Positioning - Positional Analysis

    This module contains positional analysis lemmas for pattern matching,
    including leftmost position determination with deep nested induction.
    Designed for reusability in pattern position verification tasks.

    Part of: Liblevenshtein.Phonetic.Verification.Patterns
    Renamed from PatternHelpers_Leftmost.v for better reusability.
*)

Require Import String List Arith Ascii Bool Nat Lia.
Require Import PhoneticRewrites.rewrite_rules.
From Liblevenshtein.Phonetic.Verification Require Import Auxiliary.Types.
From Liblevenshtein.Phonetic.Verification Require Import Auxiliary.Lib.
From Liblevenshtein.Phonetic.Verification Require Import Core.Rules.
Import ListNotations.

(** * Leftmost Mismatch Analysis *)

(** Lemma: Pattern mismatch has a leftmost (first) position where it fails

    If a pattern doesn't match, there exists a leftmost position where the mismatch occurs.
    All positions before this leftmost position must match successfully.
*)
Lemma pattern_has_leftmost_mismatch :
  forall pat s p,
    pattern_matches_at pat s p = false ->
    (length pat > 0)%nat ->
    exists i,
      (p <= i < p + length pat)%nat /\
      (nth_error s i = None \/
       exists ph pat_ph,
         nth_error s i = Some ph /\
         nth_error pat (i - p) = Some pat_ph /\
         Phone_eqb ph pat_ph = false) /\
      (* i is the LEFTMOST mismatch: all positions before i match *)
      (forall j, (p <= j < i)%nat ->
         exists s_ph pat_ph,
           nth_error s j = Some s_ph /\
           nth_error pat (j - p) = Some pat_ph /\
           Phone_eqb s_ph pat_ph = true).
Proof.
  intros pat s p H_no_match H_len_pos.

  (* Use strong induction on the pattern structure *)
  generalize dependent p.
  induction pat as [| ph_pat pat' IH].

  - (* Empty pattern *)
    intros. simpl in H_len_pos. lia.

  - (* Pattern ph_pat :: pat' *)
    intros p H_no_match.
    simpl in H_no_match.

    (* Check what happens at position p *)
    destruct (nth_error s p) as [ph_s |] eqn:E_nth_p.

    + (* s has phone at p *)
      destruct (Phone_eqb ph_pat ph_s) eqn:E_eq_p.

      * (* Phones match at p - mismatch must be later *)
        (* Pattern matching failed on the tail *)
        destruct pat' as [| ph2 pat''] eqn:E_pat'.

        -- (* pat' is empty *)
           simpl in H_no_match. discriminate H_no_match.

        -- (* pat' is non-empty *)
           (* Recursively find leftmost mismatch in tail *)
           assert (H_len_pos': (length (ph2 :: pat'') > 0)%nat) by (simpl; lia).
           assert (H_no_match': pattern_matches_at (ph2 :: pat'') s (S p) = false)
             by exact H_no_match.

           specialize (IH H_len_pos' (S p) H_no_match').
           destruct IH as [i [H_i_range [H_i_mismatch H_i_leftmost]]].

           (* i is the leftmost mismatch for the tail *)
           (* It's also the leftmost for the whole pattern *)
           exists i.
           split; [| split].

           ++ (* Range: S p <= i < S p + length(ph2 :: pat'') *)
              (* Need: p <= i < p + length(ph_pat :: ph2 :: pat'') *)
              simpl. simpl in H_i_range. lia.

           ++ (* Mismatch at i *)
              destruct H_i_mismatch as [H_none | [ph [pat_ph [H_s_i [H_pat_tail_i H_neq]]]]].
              ** left. exact H_none.
              ** right.
                 exists ph, pat_ph.
                 split; [exact H_s_i |].
                 split; [| exact H_neq].
                 (* nth_error (ph_pat :: ph2 :: pat'') (i - p) = Some pat_ph *)
                 (* We have: nth_error (ph2 :: pat'') (i - S p) = Some pat_ph *)
                 (* Since i >= S p, we have i - p >= 1 *)
                 assert (H_i_ge: (i >= S p)%nat) by lia.
                 replace (i - p)%nat with (S (i - S p))%nat by lia.
                 simpl. subst pat'. exact H_pat_tail_i.

           ++ (* Leftmost property: all j < i match *)
              intros j H_j_range.
              destruct (Nat.eq_dec j p) as [H_j_eq_p | H_j_ne_p].

              ** (* j = p: we know it matches *)
                 subst j.
                 exists ph_s, ph_pat.
                 split; [exact E_nth_p |].
                 split.
                 --- replace (p - p)%nat with 0%nat by lia.
                     simpl. reflexivity.
                 --- rewrite Phone_eqb_sym. exact E_eq_p.

              ** (* p < j < i: use IH leftmost property *)
                 assert (H_j_gt_p: (j > p)%nat) by lia.
                 assert (H_j_range': (S p <= j < i)%nat) by lia.

                 specialize (H_i_leftmost j H_j_range').
                 destruct H_i_leftmost as [s_ph [pat_ph_tail [H_s_j [H_pat_tail_j H_eq_j]]]].

                 exists s_ph, pat_ph_tail.
                 split; [exact H_s_j |].
                 split; [| exact H_eq_j].
                 (* nth_error (ph_pat :: ph2 :: pat'') (j - p) = Some pat_ph_tail *)
                 (* We have: nth_error (ph2 :: pat'') (j - S p) = Some pat_ph_tail *)
                 replace (j - p)%nat with (S (j - S p))%nat by lia.
                 simpl. subst pat'. exact H_pat_tail_j.

      * (* Phones don't match at p - this is the leftmost mismatch *)
        exists p.
        split; [| split].

        -- (* Range *)
           simpl. lia.

        -- (* Mismatch at p *)
           right.
           exists ph_s, ph_pat.
           split; [exact E_nth_p |].
           split.
           ++ replace (p - p)%nat with 0%nat by lia.
              simpl. reflexivity.
           ++ rewrite Phone_eqb_sym. exact E_eq_p.

        -- (* Leftmost: no positions before p (vacuously true) *)
           intros j H_j_range. lia.

    + (* nth_error s p = None: mismatch at p *)
      exists p.
      split; [| split].

      * (* Range *)
        simpl. lia.

      * (* Mismatch: None *)
        left. exact E_nth_p.

      * (* Leftmost: no positions before p *)
        intros j H_j_range. lia.
Qed.
