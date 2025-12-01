(** * Metric Properties of Levenshtein Distance

    This module proves the key metric properties of Levenshtein distance:
    identity, symmetry, upper bound, and lower bound based on length difference.

    Part of: Liblevenshtein.Core

    Decomposed from: Distance.v (lines 302-676)
*)

From Coq Require Import String List Arith Ascii Bool Nat Lia Wf_nat.
Import ListNotations.

From Liblevenshtein.Core Require Import Core.Definitions.
From Liblevenshtein.Core Require Import Core.LevDistance.
From Liblevenshtein.Core Require Import Core.MinLemmas.

(** * Identity Property *)

(** Theorem: Distance from a string to itself is 0 *)
Theorem lev_distance_identity :
  forall (s : list Char),
    lev_distance s s = 0.
Proof.
  intros s.
  induction s as [| c rest IH].
  - rewrite lev_distance_empty_left.
    simpl. reflexivity.
  - rewrite lev_distance_cons.
    rewrite IH.
    rewrite subst_cost_eq.
    unfold min3.
    simpl.
    rewrite Nat.min_0_r.
    apply Nat.min_0_r.
Qed.

(** * Symmetry Property *)

(** Theorem: distance(s1, s2) = distance(s2, s1) *)
Theorem lev_distance_symmetry :
  forall (s1 s2 : list Char),
    lev_distance s1 s2 = lev_distance s2 s1.
Proof.
  intro s1.
  induction s1 as [| c1 s1' IHs1].

  - intro s2.
    induction s2 as [| c2 s2' IHs2].
    + reflexivity.
    + rewrite lev_distance_empty_left.
      rewrite lev_distance_empty_right.
      reflexivity.

  - intro s2.
    induction s2 as [| c2 s2' IHs2].
    + rewrite lev_distance_empty_left.
      rewrite lev_distance_empty_right.
      reflexivity.
    + rewrite lev_distance_cons.
      rewrite (lev_distance_cons c2 c1 s2' s1').
      rewrite IHs1.
      rewrite IHs2.
      rewrite IHs1.

      assert (H_subst_symm: subst_cost c1 c2 = subst_cost c2 c1).
      {
        unfold subst_cost.
        destruct (char_eq c1 c2) eqn:E1;
        destruct (char_eq c2 c1) eqn:E2.
        - reflexivity.
        - apply char_eq_correct in E1.
          apply eq_sym in E1.
          apply char_eq_correct in E1.
          rewrite E1 in E2.
          discriminate E2.
        - apply char_eq_correct in E2.
          apply eq_sym in E2.
          apply char_eq_correct in E2.
          rewrite E2 in E1.
          discriminate E1.
        - reflexivity.
      }

      rewrite H_subst_symm.
      apply min3_comm_12.
Qed.

(** * Upper Bound Property *)

(** Theorem: Distance is at most max(|s1|, |s2|) *)
Theorem lev_distance_upper_bound :
  forall (s1 s2 : list Char),
    lev_distance s1 s2 <= Nat.max (length s1) (length s2).
Proof.
  intro s1.
  induction s1 as [| c1 s1' IHs1].

  - intro s2.
    rewrite lev_distance_empty_left.
    induction s2 as [| c2 s2' IHs2].
    + simpl. lia.
    + simpl. lia.

  - intro s2.
    destruct s2 as [| c2 s2'].
    + rewrite lev_distance_empty_right.
      simpl. lia.
    + rewrite lev_distance_cons.
      assert (H_bounds := min3_lower_bound
                           (lev_distance s1' (c2 :: s2') + 1)
                           (lev_distance (c1 :: s1') s2' + 1)
                           (lev_distance s1' s2' + subst_cost c1 c2)).
      destruct H_bounds as [H1 [H2 H3]].

      simpl.

      assert (IH1: lev_distance s1' (c2 :: s2') <= Nat.max (length s1') (S (length s2'))).
      { apply IHs1. }

      assert (IH2: lev_distance (c1 :: s1') s2' <= Nat.max (S (length s1')) (length s2')).
      {
        clear H1 H2 H3 IH1.
        generalize dependent c2.
        induction s2' as [| c2' s2'' IHs2].
        - intro c2.
          rewrite lev_distance_empty_right.
          simpl. lia.
        - intro c2.
          rewrite lev_distance_cons.
          simpl.
          assert (H_IH_s1_s2'': lev_distance s1' (c2' :: s2'') <= Nat.max (length s1') (S (length s2''))).
          { apply IHs1. }
          assert (H_IH_s1_s2: lev_distance s1' s2'' <= Nat.max (length s1') (length s2'')).
          { apply IHs1. }
          specialize (IHs2 c2').
          assert (H_subst_bound': subst_cost c1 c2' <= 1).
          { unfold subst_cost. destruct (char_eq c1 c2'); lia. }
          unfold min3.
          lia.
      }

      assert (IH3: lev_distance s1' s2' <= Nat.max (length s1') (length s2')).
      { apply IHs1. }

      assert (H_subst_bound: subst_cost c1 c2 <= 1).
      { unfold subst_cost. destruct (char_eq c1 c2); lia. }

      lia.
Qed.

(** * Lower Bound Property *)

(** Helper lemma: Adding 1 to abs_diff with incremented second argument *)
Lemma abs_diff_succ_bound : forall a b,
  abs_diff a b <= abs_diff a (S b) + 1.
Proof.
  intros a b.
  unfold abs_diff.
  destruct (le_lt_dec a b) as [H_le | H_gt].
  - assert (E1: (a <=? b) = true) by (apply Nat.leb_le; exact H_le).
    assert (E2: (a <=? S b) = true) by (apply Nat.leb_le; lia).
    rewrite E1, E2.
    lia.
  - destruct (le_lt_dec a (S b)) as [H_le2 | H_gt2].
    + assert (E1: (a <=? b) = false) by (apply Nat.leb_gt; exact H_gt).
      assert (E2: (a <=? S b) = true) by (apply Nat.leb_le; exact H_le2).
      rewrite E1, E2.
      lia.
    + assert (E1: (a <=? b) = false) by (apply Nat.leb_gt; exact H_gt).
      assert (E2: (a <=? S b) = false) by (apply Nat.leb_gt; exact H_gt2).
      rewrite E1, E2.
      lia.
Qed.

(** Helper lemma: Symmetric version for first argument *)
Lemma abs_diff_succ_bound_fst : forall a b,
  abs_diff a b <= abs_diff (S a) b + 1.
Proof.
  intros a b.
  unfold abs_diff.
  destruct (le_lt_dec a b) as [H_le | H_gt].
  - destruct (le_lt_dec (S a) b) as [H_le2 | H_gt2].
    + assert (E1: (a <=? b) = true) by (apply Nat.leb_le; exact H_le).
      assert (E2: (S a <=? b) = true) by (apply Nat.leb_le; exact H_le2).
      rewrite E1, E2.
      lia.
    + assert (E1: (a <=? b) = true) by (apply Nat.leb_le; exact H_le).
      assert (E2: (S a <=? b) = false) by (apply Nat.leb_gt; exact H_gt2).
      rewrite E1, E2.
      lia.
  - assert (E1: (a <=? b) = false) by (apply Nat.leb_gt; exact H_gt).
    assert (E2: (S a <=? b) = false) by (apply Nat.leb_gt; lia).
    rewrite E1, E2.
    lia.
Qed.

(** Lemma: Distance is at least the difference in lengths *)
Lemma lev_distance_length_diff_lower :
  forall (s1 s2 : list Char),
    lev_distance s1 s2 >= abs_diff (length s1) (length s2).
Proof.
  intros s1 s2.

  assert (H_wf: forall n s1' s2',
    length s1' + length s2' = n ->
    lev_distance s1' s2' >= abs_diff (length s1') (length s2')).
  {
    intro n.
    induction n as [n IH] using lt_wf_ind.
    intros s1' s2' H_sum.

    destruct s1' as [| c1 s1''].
    - rewrite lev_distance_empty_left.
      unfold abs_diff.
      simpl length.
      destruct (0 <=? length s2') eqn:E.
      + simpl. lia.
      + apply Nat.leb_gt in E. lia.

    - destruct s2' as [| c2 s2''].
      + rewrite lev_distance_empty_right.
        unfold abs_diff.
        simpl length.
        destruct (S (length s1'') <=? 0) eqn:E.
        * apply Nat.leb_le in E. lia.
        * simpl. lia.

      + rewrite lev_distance_cons.
        simpl length.

        assert (H_abs_eq: abs_diff (S (length s1'')) (S (length s2'')) =
                          abs_diff (length s1'') (length s2'')).
        {
          unfold abs_diff.
          assert (H_leb_succ: forall a b, (S a <=? S b) = (a <=? b)).
          { intros. destruct (a <=? b) eqn:E1; destruct (S a <=? S b) eqn:E2; try reflexivity.
            - apply Nat.leb_le in E1. apply Nat.leb_gt in E2. lia.
            - apply Nat.leb_gt in E1. apply Nat.leb_le in E2. lia. }
          rewrite H_leb_succ.
          destruct (length s1'' <=? length s2''); simpl; reflexivity.
        }
        rewrite H_abs_eq.

        assert (H_br1: lev_distance s1'' (c2 :: s2'') + 1 >= abs_diff (length s1'') (length s2'')).
        {
          assert (IH1: lev_distance s1'' (c2 :: s2'') >= abs_diff (length s1'') (S (length s2''))).
          { apply (IH (length s1'' + S (length s2''))).
            - simpl in H_sum. lia.
            - simpl. lia. }
          pose proof (abs_diff_succ_bound (length s1'') (length s2'')) as H_le.
          lia. }

        assert (H_br2: lev_distance (c1 :: s1'') s2'' + 1 >= abs_diff (length s1'') (length s2'')).
        {
          assert (IH2: lev_distance (c1 :: s1'') s2'' >= abs_diff (S (length s1'')) (length s2'')).
          { apply (IH (S (length s1'') + length s2'')).
            - simpl in H_sum. lia.
            - simpl. lia. }
          pose proof (abs_diff_succ_bound_fst (length s1'') (length s2'')) as H_le.
          lia. }

        assert (H_br3: lev_distance s1'' s2'' + subst_cost c1 c2 >= abs_diff (length s1'') (length s2'')).
        {
          assert (IH3: lev_distance s1'' s2'' >= abs_diff (length s1'') (length s2'')).
          { apply (IH (length s1'' + length s2'')).
            - simpl in H_sum. lia.
            - lia. }
          assert (H_subst: subst_cost c1 c2 <= 1).
          { unfold subst_cost. destruct (char_eq c1 c2); lia. }
          lia. }

        unfold min3.
        assert (H_min: forall x y z k, x >= k -> y >= k -> z >= k ->
                       Nat.min x (Nat.min y z) >= k).
        { intros x y z k Hx Hy Hz.
          apply Nat.min_case; [assumption | apply Nat.min_case; assumption]. }
        apply H_min; [exact H_br1 | exact H_br2 | exact H_br3].
  }

  apply (H_wf (length s1 + length s2) s1 s2).
  reflexivity.
Qed.
