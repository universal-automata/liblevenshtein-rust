(** * Shift Trace (1,1) Operations

    This module provides operations for shifting traces by removing (1,1) pairs
    and related counting lemmas.

    Part of: Liblevenshtein.Core

    Decomposed from: TraceLowerBound.v (lines 285-387)
*)

From Stdlib Require Import String List Arith Ascii Bool Nat Lia.
Import ListNotations.

From Liblevenshtein.Core Require Import LowerBound.Definitions.
From Liblevenshtein.Core Require Import LowerBound.HasPredicates.

(** * Shift and Count Definitions *)

(** Filter out (1, 1) from trace and shift indices *)
Fixpoint shift_trace_11 (T : Trace) : Trace :=
  match T with
  | [] => []
  | (i, j) :: rest =>
      if (i =? 1) && (j =? 1)
      then shift_trace_11 rest  (* skip (1,1) *)
      else (i - 1, j - 1) :: shift_trace_11 rest  (* shift down *)
  end.

(** Count occurrences of (1,1) *)
Fixpoint count_11 (T : Trace) : nat :=
  match T with
  | [] => 0
  | (i, j) :: rest =>
      if (i =? 1) && (j =? 1) then 1 + count_11 rest else count_11 rest
  end.

(** * Count Lemmas *)

(** count_11 is bounded by length *)
Lemma count_11_le_length : forall T, count_11 T <= length T.
Proof.
  induction T as [| [i j] rest IH].
  - simpl. lia.
  - simpl. destruct ((i =? 1) && (j =? 1)); lia.
Qed.

(** Fundamental length property *)
Lemma shift_trace_11_length_general : forall T,
  length (shift_trace_11 T) = length T - count_11 T.
Proof.
  induction T as [| [i j] rest IH].
  - simpl. reflexivity.
  - simpl shift_trace_11. simpl count_11.
    destruct ((i =? 1) && (j =? 1)) eqn:E.
    + (* (i,j) = (1,1), skipped *)
      simpl length.
      pose proof (count_11_le_length rest) as Hbound.
      lia.
    + (* (i,j) ≠ (1,1), included *)
      simpl length.
      rewrite IH.
      pose proof (count_11_le_length rest) as Hbound.
      lia.
Qed.

(** (1,1) can appear at most once if both projections are NoDup *)
Lemma count_11_le_1_aux : forall T,
  NoDup (touched_in_A T) -> NoDup (touched_in_B T) -> count_11 T <= 1.
Proof.
  induction T as [| [i j] rest IH]; intros HnodupA HnodupB.
  - simpl. lia.
  - simpl touched_in_A in HnodupA. simpl touched_in_B in HnodupB.
    inversion HnodupA as [| x xs Hnot_in_A Hnodup_restA Heq1]. subst.
    inversion HnodupB as [| y ys Hnot_in_B Hnodup_restB Heq2]. subst.
    simpl count_11.
    destruct ((i =? 1) && (j =? 1)) eqn:E.
    + (* (i,j) = (1,1) *)
      apply andb_prop in E. destruct E as [Ei Ej].
      apply Nat.eqb_eq in Ei. apply Nat.eqb_eq in Ej. subst i j.
      (* Now 1 is not in touched_in_A rest and 1 is not in touched_in_B rest *)
      (* So (1,1) cannot be in rest *)
      assert (Hcount_rest: count_11 rest = 0).
      { (* Generalized statement: any list where 1 not in A projection has count_11 = 0 *)
        assert (Hgen: forall L, ~ In 1 (touched_in_A L) -> count_11 L = 0).
        { clear IH Hnodup_restA Hnodup_restB Hnot_in_A Hnot_in_B rest HnodupA HnodupB.
          induction L as [| [i' j'] L' IHL'].
          - reflexivity.
          - intros Hnot_in.
            simpl count_11.
            destruct ((i' =? 1) && (j' =? 1)) eqn:E'.
            + (* (i', j') = (1,1), contradiction *)
              apply andb_prop in E'. destruct E' as [Ei' _].
              apply Nat.eqb_eq in Ei'. subst.
              exfalso. apply Hnot_in. simpl. left. reflexivity.
            + apply IHL'. intro H. apply Hnot_in. simpl. right. exact H. }
        apply Hgen. exact Hnot_in_A. }
      lia.
    + (* (i,j) ≠ (1,1), apply IH *)
      assert (Hle: count_11 rest <= 1) by (apply IH; assumption).
      lia.
Qed.

(** has_pair_11 implies count_11 >= 1 *)
Lemma has_pair_11_count : forall T,
  has_pair_11 T = true -> count_11 T >= 1.
Proof.
  induction T as [| [i j] rest IH].
  - simpl. intros H. discriminate.
  - intro H.
    simpl count_11.
    destruct ((i =? 1) && (j =? 1)) eqn:E.
    + lia.
    + assert (Hrest: count_11 rest >= 1).
      { apply IH.
        unfold has_pair_11 in H. simpl existsb in H.
        unfold has_pair_11.
        destruct (i =? 1) eqn:Ei, (j =? 1) eqn:Ej; simpl in E; try discriminate.
        - simpl in H. exact H.
        - simpl in H. exact H.
        - simpl in H. exact H. }
      lia.
Qed.

