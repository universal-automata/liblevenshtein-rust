(** * Shift Trace A Operations

    This module provides operations for filtering and shifting traces
    that involve the first string position (A1).

    Part of: Liblevenshtein.Core

    Decomposed from: TraceLowerBound.v (lines 388-627)
*)

From Stdlib Require Import String List Arith Ascii Bool Nat Lia.
Import ListNotations.

From Liblevenshtein.Core Require Import Core.Definitions.
From Liblevenshtein.Core Require Import LowerBound.Definitions.
From Liblevenshtein.Core Require Import LowerBound.HasPredicates.

(** * Filter and Shift Definitions *)

(** Filter to keep only pairs with i = 1 *)
Fixpoint filter_A1 (T : Trace) : Trace :=
  match T with
  | [] => []
  | (i, j) :: rest => if i =? 1 then (i, j) :: filter_A1 rest else filter_A1 rest
  end.

(** Filter to keep pairs with i > 1 and shift *)
Fixpoint shift_trace_A (T : Trace) : Trace :=
  match T with
  | [] => []
  | (i, j) :: rest =>
      if i =? 1 then shift_trace_A rest
      else (i - 1, j) :: shift_trace_A rest
  end.

(** * Helper Lemmas *)

(** has_A1 decomposes over cons *)
Lemma has_A1_cons : forall i j rest,
  has_A1 ((i, j) :: rest) = (i =? 1) || has_A1 rest.
Proof.
  intros. unfold has_A1. simpl. reflexivity.
Qed.

(** When has_A1 T = false, shift_trace_A preserves length *)
Lemma shift_trace_A_length_no_A1 : forall T,
  has_A1 T = false -> length (shift_trace_A T) = length T.
Proof.
  induction T as [| [i j] rest IH]; intros H.
  - reflexivity.
  - rewrite has_A1_cons in H.
    apply orb_false_elim in H. destruct H as [Hi Hrest].
    simpl. rewrite Hi. simpl.
    f_equal. apply IH. exact Hrest.
Qed.

(** When has_A1 T = true and NoDup, length decreases by 1 *)
Lemma shift_trace_A_length_with_A1 : forall T,
  has_A1 T = true ->
  NoDup (touched_in_A T) ->
  length (shift_trace_A T) = length T - 1.
Proof.
  induction T as [| [i j] rest IH]; intros H_A1 Hnodup.
  - simpl in H_A1. discriminate.
  - unfold has_A1 in H_A1. simpl in H_A1.
    destruct (i =? 1) eqn:Ei.
    + simpl shift_trace_A. rewrite Ei.
      apply Nat.eqb_eq in Ei. subst i.
      simpl touched_in_A in Hnodup.
      inversion Hnodup as [| x xs Hnot_in Hnodup_rest Heq]. subst.
      assert (Hno_A1_rest: has_A1 rest = false).
      { unfold has_A1.
        destruct (existsb (fun i => i =? 1) (touched_in_A rest)) eqn:E.
        - apply existsb_exists in E. destruct E as [k [Hk Hk_eq]].
          apply Nat.eqb_eq in Hk_eq. subst k.
          exfalso. apply Hnot_in. exact Hk.
        - reflexivity. }
      rewrite shift_trace_A_length_no_A1 by exact Hno_A1_rest.
      simpl. lia.
    + simpl shift_trace_A. rewrite Ei. simpl.
      simpl touched_in_A in Hnodup.
      inversion Hnodup as [| x xs Hnot_in Hnodup_rest Heq]. subst.
      assert (H_A1_rest: has_A1 rest = true).
      { unfold has_A1. exact H_A1. }
      rewrite IH by assumption.
      destruct rest as [| p rest'].
      * simpl in H_A1. discriminate.
      * simpl. lia.
Qed.

(** * Index Shifting Lemmas *)

(** For accessing nth element: nth (i-1) (c::A) = nth (i-1-1) A when i >= 2 *)
Lemma nth_cons_shift : forall (A : list Char) c i d,
  i >= 2 -> nth (i - 1) (c :: A) d = nth (i - 1 - 1) A d.
Proof.
  intros A c i d Hi.
  destruct i as [| [| i']].
  - lia.
  - lia.
  - simpl. f_equal. lia.
Qed.

(** After simpl, nth (i-1) (c::A) becomes a match. This handles that form. *)
Lemma nth_cons_match_eq : forall (A : list Char) c i d,
  i >= 2 ->
  (match i - 1 with | 0 => c | S m => nth m A d end) = nth (i - 1 - 1) A d.
Proof.
  intros A c i d Hi.
  destruct i as [| [| i']].
  - lia.
  - lia.
  - simpl. f_equal. lia.
Qed.

(** * Fold Lemmas *)

(** Helper: fold_left with shifted trace - generalized for any accumulator *)
Lemma fold_left_shift_A_aux : forall T A B c1 acc,
  has_A1 T = false ->
  Forall (fun '(i, j) => i >= 2 /\ j >= 1) T ->
  fold_left (fun acc0 '(i, j) =>
    acc0 + subst_cost (nth (i-1) (c1::A) default_char) (nth (j-1) B default_char)) T acc =
  fold_left (fun acc0 '(i, j) =>
    acc0 + subst_cost (nth (i-1) A default_char) (nth (j-1) B default_char)) (shift_trace_A T) acc.
Proof.
  induction T as [| [i j] rest IH]; intros A B c1 acc Hno_A1 Hbounds.
  - reflexivity.
  - rewrite has_A1_cons in Hno_A1.
    apply orb_false_elim in Hno_A1. destruct Hno_A1 as [Hi_neq1 Hno_A1_rest].
    rewrite Forall_cons_iff in Hbounds. destruct Hbounds as [[Hi Hj] Hrest].
    simpl shift_trace_A. rewrite Hi_neq1.
    simpl fold_left.
    assert (Hshift: (match i - 1 with | 0 => c1 | S m => nth m A default_char end) =
                    nth (i - 1 - 1) A default_char).
    { apply nth_cons_match_eq. lia. }
    rewrite Hshift.
    apply IH; assumption.
Qed.

(** Change cost equality for shift_trace_A *)
Lemma change_cost_shift_A : forall T A B c1,
  has_A1 T = false ->
  Forall (fun '(i, j) => i >= 2 /\ j >= 1) T ->
  fold_left (fun acc '(i, j) =>
    acc + subst_cost (nth (i-1) (c1::A) default_char) (nth (j-1) B default_char)) T 0 =
  fold_left (fun acc '(i, j) =>
    acc + subst_cost (nth (i-1) A default_char) (nth (j-1) B default_char)) (shift_trace_A T) 0.
Proof.
  intros. apply fold_left_shift_A_aux; assumption.
Qed.

(** * Validity Lemmas *)

(** Validity of shift_trace_A *)
Lemma shift_trace_A_valid : forall lenA lenB T,
  has_A1 T = false ->
  simple_valid_trace (S lenA) lenB T = true ->
  simple_valid_trace lenA lenB (shift_trace_A T) = true.
Proof.
  intros lenA lenB T Hno_A1 Hvalid.
  unfold simple_valid_trace in *.
  rewrite forallb_forall in *.
  intros [i' j'] Hin.
  induction T as [| [i0 j0] rest IH].
  - simpl in Hin. destruct Hin.
  - rewrite has_A1_cons in Hno_A1.
    apply orb_false_elim in Hno_A1. destruct Hno_A1 as [Hi0_neq1 Hno_A1_rest].
    simpl in Hin. rewrite Hi0_neq1 in Hin. simpl in Hin.
    destruct Hin as [Heq | Hin'].
    + injection Heq as Hi' Hj'.
      assert (Hin_orig: In (i0, j0) ((i0, j0) :: rest)) by (left; reflexivity).
      specialize (Hvalid (i0, j0) Hin_orig).
      apply andb_prop in Hvalid. destruct Hvalid as [Hvalid1 Hj0_upper].
      apply andb_prop in Hvalid1. destruct Hvalid1 as [Hvalid2 Hj0_lower].
      apply andb_prop in Hvalid2. destruct Hvalid2 as [Hi0_lower Hi0_upper].
      apply Nat.leb_le in Hi0_lower.
      apply Nat.leb_le in Hi0_upper.
      apply Nat.leb_le in Hj0_lower.
      apply Nat.leb_le in Hj0_upper.
      apply Nat.eqb_neq in Hi0_neq1.
      subst i' j'.
      repeat (apply andb_true_intro; split); apply Nat.leb_le; lia.
    + apply IH.
      { exact Hno_A1_rest. }
      { intros x Hx. apply Hvalid. right. exact Hx. }
      { exact Hin'. }
Qed.

(** General validity of shift_trace_A - doesn't require has_A1 = false *)
Lemma shift_trace_A_valid_general : forall lenA lenB T,
  simple_valid_trace (S lenA) (S lenB) T = true ->
  simple_valid_trace lenA (S lenB) (shift_trace_A T) = true.
Proof.
  intros lenA lenB T Hvalid.
  unfold simple_valid_trace in *.
  rewrite forallb_forall in *.
  intros [i' j'] Hin.
  induction T as [| [i j] rest IH].
  - simpl in Hin. destruct Hin.
  - simpl shift_trace_A in Hin.
    destruct (i =? 1) eqn:Ei.
    + apply IH.
      { intros x Hx. apply Hvalid. right. exact Hx. }
      { exact Hin. }
    + simpl in Hin. destruct Hin as [Heq | Hin'].
      * injection Heq as Hi' Hj'.
        assert (Hin_orig: In (i, j) ((i, j) :: rest)) by (left; reflexivity).
        specialize (Hvalid (i, j) Hin_orig).
        apply andb_prop in Hvalid. destruct Hvalid as [Hvalid1 Hj_upper].
        apply andb_prop in Hvalid1. destruct Hvalid1 as [Hvalid2 Hj_lower].
        apply andb_prop in Hvalid2. destruct Hvalid2 as [Hi_lower Hi_upper].
        apply Nat.leb_le in Hi_lower.
        apply Nat.leb_le in Hi_upper.
        apply Nat.leb_le in Hj_lower.
        apply Nat.leb_le in Hj_upper.
        apply Nat.eqb_neq in Ei.
        subst i' j'.
        repeat (apply andb_true_intro; split); apply Nat.leb_le; lia.
      * apply IH.
        { intros x Hx. apply Hvalid. right. exact Hx. }
        { exact Hin'. }
Qed.

(** * Empty Trace Lemmas *)

(** For base cases: if lenA = 0 or lenB = 0, valid trace must be empty *)
Lemma valid_trace_empty_A : forall lenB T,
  simple_valid_trace 0 lenB T = true -> T = [].
Proof.
  intros lenB T Hvalid.
  destruct T as [| [i j] rest].
  - reflexivity.
  - unfold simple_valid_trace in Hvalid. simpl in Hvalid.
    destruct i as [| i']; destruct j as [| j']; destruct lenB as [| lenB'];
      simpl in Hvalid; discriminate.
Qed.

