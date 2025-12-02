(** * Optimal Trace Cost Equality

    This module proves that trace_cost of the optimal trace equals lev_distance.

    Part of: Liblevenshtein.Core

    Decomposed from: Distance.v (lines 7065-7854)
*)

From Coq Require Import String List Arith Ascii Bool Nat Lia Wf_nat.
Import ListNotations.

From Liblevenshtein.Core Require Import Core.Definitions.
From Liblevenshtein.Core Require Import Core.LevDistance.
From Liblevenshtein.Core Require Import Trace.TraceBasics.
From Liblevenshtein.Core Require Import Trace.TouchedPositions.
From Liblevenshtein.Core Require Import Trace.TraceCost.
From Liblevenshtein.Core Require Import Cardinality.NoDupPreservation.
From Liblevenshtein.Core Require Import OptimalTrace.Construction.
From Liblevenshtein.Core Require Import OptimalTrace.Validity.

(** * Additional Fold_left Shift Lemmas *)

(** Fold_left shift lemma for S_id (first index shift only) *)
Lemma fold_left_change_cost_shift_S_id_aux :
  forall A B T c1 acc,
    Forall (fun '(i, _) => i >= 1) T ->
    fold_left (fun a '(i, j) =>
      a + subst_cost (nth (i-1) (c1::A) default_char) (nth (j-1) B default_char))
      (map (fun '(i, j) => (S i, j)) T) acc =
    fold_left (fun a '(i, j) =>
      a + subst_cost (nth (i-1) A default_char) (nth (j-1) B default_char)) T acc.
Proof.
  intros A' B' T c1.
  induction T as [| [i j] rest IH]; intros acc Hvalid.
  - simpl. reflexivity.
  - rewrite Forall_cons_iff in Hvalid.
    destruct Hvalid as [Hi Hrest].
    simpl map. simpl fold_left.
    rewrite (match_nth_eq A' c1 i Hi).
    apply IH. exact Hrest.
Qed.

Lemma fold_left_change_cost_shift_S_id :
  forall A B T c1,
    Forall (fun '(i, _) => i >= 1) T ->
    fold_left (fun acc '(i, j) =>
      acc + subst_cost (nth (i-1) (c1::A) default_char) (nth (j-1) B default_char))
      (map (fun '(i, j) => (S i, j)) T) 0 =
    fold_left (fun acc '(i, j) =>
      acc + subst_cost (nth (i-1) A default_char) (nth (j-1) B default_char)) T 0.
Proof.
  intros. apply fold_left_change_cost_shift_S_id_aux. exact H.
Qed.

(** Fold_left shift lemma for id_S (second index shift only) *)
Lemma fold_left_change_cost_shift_id_S_aux :
  forall A B T c2 acc,
    Forall (fun '(_, j) => j >= 1) T ->
    fold_left (fun a '(i, j) =>
      a + subst_cost (nth (i-1) A default_char) (nth (j-1) (c2::B) default_char))
      (map (fun '(i, j) => (i, S j)) T) acc =
    fold_left (fun a '(i, j) =>
      a + subst_cost (nth (i-1) A default_char) (nth (j-1) B default_char)) T acc.
Proof.
  intros A' B' T c2.
  induction T as [| [i j] rest IH]; intros acc Hvalid.
  - simpl. reflexivity.
  - rewrite Forall_cons_iff in Hvalid.
    destruct Hvalid as [Hj Hrest].
    simpl map. simpl fold_left.
    rewrite (match_nth_eq B' c2 j Hj).
    apply IH. exact Hrest.
Qed.

Lemma fold_left_change_cost_shift_id_S :
  forall A B T c2,
    Forall (fun '(_, j) => j >= 1) T ->
    fold_left (fun acc '(i, j) =>
      acc + subst_cost (nth (i-1) A default_char) (nth (j-1) (c2::B) default_char))
      (map (fun '(i, j) => (i, S j)) T) 0 =
    fold_left (fun acc '(i, j) =>
      acc + subst_cost (nth (i-1) A default_char) (nth (j-1) B default_char)) T 0.
Proof.
  intros. apply fold_left_change_cost_shift_id_S_aux. exact H.
Qed.

(** * Main Cost Equality Theorem *)

(**
   Optimal trace cost equals Levenshtein distance

   The key theorem: trace_cost of the optimal trace equals lev_distance.

   Proof by strong induction on |A| + |B|:
   - Base cases (empty A or B): trace is empty, cost = |A| + |B| = lev_distance
   - Inductive case: case split on which DP branch was taken
     - Substitution: trace_cost = subst_cost(c1,c2) + trace_cost(s1',s2')
                                = subst_cost(c1,c2) + lev_distance(s1',s2')
     - Deletion: trace_cost = 1 + trace_cost(s1', c2::s2')
                            = 1 + lev_distance(s1', c2::s2')
     - Insertion: trace_cost = 1 + trace_cost(c1::s1', s2')
                             = 1 + lev_distance(c1::s1', s2')
   Each case equals min3 by the branching condition.
*)
Lemma optimal_trace_cost :
  forall (A B : list Char),
    trace_cost A B (optimal_trace A B) = lev_distance A B.
Proof.
  intros A' B'.
  unfold optimal_trace.
  remember (length A' + length B') as n eqn:Hn.
  revert A' B' Hn.
  induction n as [n IH] using lt_wf_ind.
  intros A' B' Hn.

  rewrite optimal_trace_pair_unfold.

  destruct A' as [| c1 s1'], B' as [| c2 s2'].

  - (* A = [], B = [] *)
    unfold trace_cost. simpl.
    rewrite lev_distance_empty_left. reflexivity.

  - (* A = [], B = c2::s2' *)
    unfold trace_cost. simpl.
    rewrite lev_distance_empty_left. reflexivity.

  - (* A = c1::s1', B = [] *)
    unfold trace_cost. simpl.
    rewrite lev_distance_empty_right. simpl length. lia.

  - (* A = c1::s1', B = c2::s2' *)
    cbv zeta.

    set (cost_del := lev_distance s1' (c2 :: s2') + 1).
    set (cost_ins := lev_distance (c1 :: s1') s2' + 1).
    set (cost_sub := lev_distance s1' s2' + subst_cost c1 c2).

    assert (H_dist: lev_distance (c1 :: s1') (c2 :: s2') = min3 cost_del cost_ins cost_sub).
    { rewrite lev_distance_cons. unfold cost_del, cost_ins, cost_sub. reflexivity. }

    destruct ((cost_sub <=? cost_del) && (cost_sub <=? cost_ins)) eqn:E_sub.

    + (* Substitution branch *)
      apply andb_prop in E_sub. destruct E_sub as [E1 E2].
      apply Nat.leb_le in E1. apply Nat.leb_le in E2.

      assert (H_min: min3 cost_del cost_ins cost_sub = cost_sub).
      { unfold min3. rewrite Nat.min_r by lia. apply Nat.min_r. lia. }

      rewrite H_dist, H_min. unfold cost_sub.

      set (T' := optimal_trace_pair (s1', s2')).

      assert (IH_sub: trace_cost s1' s2' T' = lev_distance s1' s2').
      { apply (IH (length s1' + length s2')). subst n. simpl. lia. reflexivity. }

      assert (Hvalid: valid_indices T').
      { unfold T'. apply optimal_trace_pair_valid_indices. }

      unfold trace_cost.
      simpl touched_in_A. simpl touched_in_B.
      rewrite touched_in_A_map_SS, touched_in_B_map_SS.
      simpl length.
      rewrite !length_map.
      rewrite !touched_length_eq_A, !touched_length_eq_B.

      simpl fold_left at 1.

      rewrite (fold_left_change_cost_shift_SS_aux s1' s2' T' c1 c2 _ Hvalid).
      rewrite fold_left_acc_extract.

      unfold trace_cost in IH_sub.
      pose proof (optimal_trace_pair_length_bound s1' s2') as Hbound.
      fold T' in Hbound.
      rewrite !touched_length_eq_A, !touched_length_eq_B in IH_sub.

      lia.

    + destruct (cost_del <=? cost_ins) eqn:E_del.

      * (* Deletion branch *)
        apply Nat.leb_le in E_del.
        apply Bool.andb_false_iff in E_sub.
        destruct E_sub as [E_sub | E_sub]; apply Nat.leb_gt in E_sub.
        -- (* cost_sub > cost_del *)
           assert (H_min: min3 cost_del cost_ins cost_sub = cost_del).
           { unfold min3. lia. }
           rewrite H_dist, H_min. unfold cost_del.

           set (T' := optimal_trace_pair (s1', (c2 :: s2'))).

           assert (IH_del: trace_cost s1' (c2 :: s2') T' = lev_distance s1' (c2 :: s2')).
           { apply (IH (length s1' + length (c2 :: s2'))). subst n. simpl. lia. reflexivity. }

           assert (Hvalid_i: Forall (fun '(i, _) => i >= 1) T').
           { unfold T'. apply optimal_trace_pair_i_valid. }

           unfold trace_cost.
           rewrite touched_in_A_map_S_id, touched_in_B_map_S_id.
           simpl length.
           rewrite !length_map.
           rewrite !touched_length_eq_A, !touched_length_eq_B.

           rewrite (fold_left_change_cost_shift_S_id s1' (c2 :: s2') T' c1 Hvalid_i).

           unfold trace_cost in IH_del.
           simpl length in IH_del.
           rewrite !touched_length_eq_A, !touched_length_eq_B in IH_del.

           pose proof (optimal_trace_pair_length_bound s1' (c2 :: s2')) as Hbound.
           fold T' in Hbound. simpl in Hbound.

           lia.

        -- (* cost_sub > cost_ins but cost_del <= cost_ins, so cost_del is min *)
           assert (H_min: min3 cost_del cost_ins cost_sub = cost_del).
           { unfold min3. lia. }
           rewrite H_dist, H_min. unfold cost_del.

           set (T' := optimal_trace_pair (s1', (c2 :: s2'))).

           assert (IH_del: trace_cost s1' (c2 :: s2') T' = lev_distance s1' (c2 :: s2')).
           { apply (IH (length s1' + length (c2 :: s2'))). subst n. simpl. lia. reflexivity. }

           assert (Hvalid_i: Forall (fun '(i, _) => i >= 1) T').
           { unfold T'. apply optimal_trace_pair_i_valid. }

           unfold trace_cost.
           rewrite touched_in_A_map_S_id, touched_in_B_map_S_id.
           simpl length.
           rewrite !length_map.
           rewrite !touched_length_eq_A, !touched_length_eq_B.

           rewrite (fold_left_change_cost_shift_S_id s1' (c2 :: s2') T' c1 Hvalid_i).

           unfold trace_cost in IH_del.
           simpl length in IH_del.
           rewrite !touched_length_eq_A, !touched_length_eq_B in IH_del.

           pose proof (optimal_trace_pair_length_bound s1' (c2 :: s2')) as Hbound.
           fold T' in Hbound. simpl in Hbound.

           lia.

      * (* Insertion branch *)
        apply Nat.leb_gt in E_del.
        apply Bool.andb_false_iff in E_sub.

        assert (H_min: min3 cost_del cost_ins cost_sub = cost_ins).
        { unfold min3. destruct E_sub as [E | E]; apply Nat.leb_gt in E; lia. }

        rewrite H_dist, H_min. unfold cost_ins.

        set (T' := optimal_trace_pair ((c1 :: s1'), s2')).

        assert (IH_ins: trace_cost (c1 :: s1') s2' T' = lev_distance (c1 :: s1') s2').
        { apply (IH (length (c1 :: s1') + length s2')). subst n. simpl. lia. reflexivity. }

        assert (Hvalid_j: Forall (fun '(_, j) => j >= 1) T').
        { unfold T'. apply optimal_trace_pair_j_valid. }

        unfold trace_cost.
        rewrite touched_in_A_map_id_S, touched_in_B_map_id_S.
        simpl length.
        rewrite !length_map.
        rewrite !touched_length_eq_A, !touched_length_eq_B.

        rewrite (fold_left_change_cost_shift_id_S (c1 :: s1') s2' T' c2 Hvalid_j).

        unfold trace_cost in IH_ins.
        simpl length in IH_ins.
        rewrite !touched_length_eq_A, !touched_length_eq_B in IH_ins.

        pose proof (optimal_trace_pair_length_bound (c1 :: s1') s2') as Hbound.
        fold T' in Hbound.

        assert (HT'_bound: length T' <= length s2').
        { eapply Nat.le_trans. exact Hbound. apply Nat.le_min_r. }

        lia.
Qed.
