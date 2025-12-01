(** * Trace Cost Fold Lemmas

    This module provides the trace cost fold function and related lemmas
    for the cost decomposition under shift operations.

    Part of: Liblevenshtein.Core

    Decomposed from: TraceLowerBound.v (lines 1871-1995)
*)

From Stdlib Require Import String List Arith Ascii Bool Nat Lia.
Import ListNotations.

From Liblevenshtein.Core Require Import Core.Definitions.
From Liblevenshtein.Core Require Import LowerBound.Definitions.
From Liblevenshtein.Core Require Import LowerBound.HasPredicates.
From Liblevenshtein.Core Require Import LowerBound.ShiftTrace11.
From Liblevenshtein.Core Require Import LowerBound.MonotonicityLemmas.

(** * Trace Cost Fold Definition *)

(** Cost function for a trace (wrapper for fold_left) *)
Definition trace_cost_fold (A B : list Char) (T : Trace) : nat :=
  fold_left (fun acc '(i, j) => acc + subst_cost (nth (i-1) A default_char) (nth (j-1) B default_char)) T 0.

(** * Accumulator Properties *)

(** Accumulator property for fold_left *)
Lemma trace_cost_fold_cons : forall A B i j rest,
  trace_cost_fold A B ((i, j) :: rest) =
  subst_cost (nth (i-1) A default_char) (nth (j-1) B default_char) + trace_cost_fold A B rest.
Proof.
  intros A B i j rest.
  unfold trace_cost_fold. simpl fold_left.
  set (cost := subst_cost (nth (i-1) A default_char) (nth (j-1) B default_char)).
  clearbody cost.
  revert cost.
  induction rest as [| [a b] rest' IH]; intros cost.
  - simpl. lia.
  - simpl fold_left.
    rewrite IH.
    set (cost2 := subst_cost (nth (a-1) A default_char) (nth (b-1) B default_char)).
    rewrite IH with (cost := cost2).
    unfold cost2. lia.
Qed.

(** * All Indices >= 2 Lemmas *)

(** Helper: when all indices >= 2, trace_cost on (c1::A, c2::B) equals trace_cost on (A, B) after shift *)
Lemma trace_cost_fold_shift_all_ge2 : forall T (A B : list Char) c1 c2,
  Forall (fun '(i, j) => i >= 2 /\ j >= 2) T ->
  trace_cost_fold (c1::A) (c2::B) T = trace_cost_fold A B (shift_trace_11 T).
Proof.
  induction T as [| [i j] rest IH]; intros A B c1 c2 Hge2.
  - reflexivity.
  - rewrite Forall_cons_iff in Hge2. destruct Hge2 as [[Hi Hj] Hrest].
    assert (Enot11: (i =? 1) && (j =? 1) = false).
    { destruct (i =? 1) eqn:Ei; [apply Nat.eqb_eq in Ei; lia | reflexivity]. }
    simpl shift_trace_11. rewrite Enot11.

    rewrite trace_cost_fold_cons.
    rewrite trace_cost_fold_cons.

    (* The key: nth (i-1) (c1::A) = nth (i-2) A when i >= 2 *)
    destruct i as [| [| i']]; [lia | lia |].
    destruct j as [| [| j']]; [lia | lia |].
    (* Now i = S (S i'), j = S (S j') *)
    simpl Nat.sub. simpl nth.
    replace (i' - 0) with i' by lia.
    replace (j' - 0) with j' by lia.

    f_equal.
    apply IH. exact Hrest.
Qed.

(** * Change Cost Decomposition *)

(** Change cost decomposition for shift_trace_11 - requires NoDup *)
Lemma change_cost_shift_11 : forall T A B c1 c2,
  has_pair_11 T = true ->
  NoDup (touched_in_A T) ->
  NoDup (touched_in_B T) ->
  Forall (fun '(i, j) => i >= 1 /\ j >= 1) T ->
  trace_cost_fold (c1::A) (c2::B) T =
  subst_cost c1 c2 + trace_cost_fold A B (shift_trace_11 T).
Proof.
  induction T as [| [i j] rest IH]; intros A B c1 c2 H11 HnodupA HnodupB Hvalid.
  - simpl in H11. discriminate.

  - rewrite Forall_cons_iff in Hvalid. destruct Hvalid as [[Hi Hj] Hrest].
    simpl touched_in_A in HnodupA. simpl touched_in_B in HnodupB.
    inversion HnodupA as [| x xs Hnot_in_A Hnodup_restA Heq1]. subst.
    inversion HnodupB as [| y ys Hnot_in_B Hnodup_restB Heq2]. subst.

    destruct ((i =? 1) && (j =? 1)) eqn:E11.
    + (* (i, j) = (1, 1) *)
      apply andb_prop in E11. destruct E11 as [Ei Ej].
      apply Nat.eqb_eq in Ei. apply Nat.eqb_eq in Ej. subst i j.
      simpl shift_trace_11.

      (* All pairs in rest have i >= 2 and j >= 2 because NoDup excludes 1 *)
      assert (H_rest_ge2: Forall (fun '(i', j') => i' >= 2 /\ j' >= 2) rest).
      { rewrite Forall_forall. intros [i' j'] Hin.
        assert (Hne1_A: i' <> 1).
        { intro Heq. subst i'. apply Hnot_in_A.
          apply in_pair_in_A with j'. exact Hin. }
        assert (Hne1_B: j' <> 1).
        { intro Heq. subst j'. apply Hnot_in_B.
          apply in_pair_in_B with i'. exact Hin. }
        rewrite Forall_forall in Hrest. specialize (Hrest (i', j') Hin).
        destruct Hrest as [Hi_ge1 Hj_ge1].
        lia. }

      rewrite trace_cost_fold_cons.
      simpl Nat.sub. simpl nth.

      (* Use the helper lemma for the rest *)
      rewrite trace_cost_fold_shift_all_ge2 by exact H_rest_ge2.
      lia.

    + (* (i, j) ≠ (1, 1), so (1,1) must be in rest *)
      assert (H11_rest: has_pair_11 rest = true).
      { unfold has_pair_11 in H11. simpl existsb in H11.
        unfold has_pair_11. rewrite E11 in H11. simpl in H11. exact H11. }

      assert (Hi_neq1: i <> 1).
      { intro Heq. subst i.
        apply Hnot_in_A. apply has_pair_11_in_A. exact H11_rest. }

      assert (Hj_neq1: j <> 1).
      { intro Heq. subst j.
        apply Hnot_in_B. apply has_pair_11_in_B. exact H11_rest. }

      assert (Hige2: i >= 2) by lia.
      assert (Hjge2: j >= 2) by lia.

      simpl shift_trace_11. rewrite E11.

      rewrite trace_cost_fold_cons.
      rewrite trace_cost_fold_cons.

      (* The key: nth (i-1) (c1::A) = nth (i-2) A when i >= 2 *)
      destruct i as [| [| i']]; [lia | lia |].
      destruct j as [| [| j']]; [lia | lia |].
      simpl Nat.sub. simpl nth.
      replace (i' - 0) with i' by lia.
      replace (j' - 0) with j' by lia.

      specialize (IH A B c1 c2 H11_rest Hnodup_restA Hnodup_restB Hrest).
      rewrite IH.
      lia.
Qed.

