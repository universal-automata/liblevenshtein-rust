(** * Pattern Helper Lemmas - Position Skipping Optimization

    This module contains helper lemmas for reasoning about pattern matching,
    including characterization of mismatches and leftmost mismatch analysis.

    These lemmas are essential infrastructure for proving pattern overlap
    preservation (Axiom 2).

    Part of: Liblevenshtein.Phonetic.Verification.Patterns
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
                 --- exact E_eq_p.

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
           ++ exact E_eq_p.

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
