(** * Shift Trace B Operations

    This module provides operations for filtering and shifting traces
    that involve the second string position (B1).

    Part of: Liblevenshtein.Core

    Decomposed from: TraceLowerBound.v (lines 404-747)
*)

From Stdlib Require Import String List Arith Ascii Bool Nat Lia.
Import ListNotations.

From Liblevenshtein.Core Require Import Core.Definitions.
From Liblevenshtein.Core Require Import LowerBound.Definitions.
From Liblevenshtein.Core Require Import LowerBound.HasPredicates.

(** * Filter and Shift Definitions *)

(** Filter to keep pairs with j > 1 and shift *)
Fixpoint shift_trace_B (T : Trace) : Trace :=
  match T with
  | [] => []
  | (i, j) :: rest =>
      if j =? 1 then shift_trace_B rest
      else (i, j - 1) :: shift_trace_B rest
  end.

(** * Helper Lemmas *)

(** has_B1 decomposes over cons *)
Lemma has_B1_cons : forall i j rest,
  has_B1 ((i, j) :: rest) = (j =? 1) || has_B1 rest.
Proof.
  intros. unfold has_B1. simpl. reflexivity.
Qed.

(** When has_B1 T = false, shift_trace_B preserves length *)
Lemma shift_trace_B_length_no_B1 : forall T,
  has_B1 T = false -> length (shift_trace_B T) = length T.
Proof.
  induction T as [| [i j] rest IH]; intros H.
  - reflexivity.
  - rewrite has_B1_cons in H.
    apply orb_false_elim in H. destruct H as [Hj Hrest].
    simpl. rewrite Hj. simpl.
    f_equal. apply IH. exact Hrest.
Qed.

(** * Index Shifting Lemmas *)

(** After simpl, nth (j-1) (c::B) becomes a match. This handles that form. *)
Lemma nth_cons_match_eq_B : forall (B : list Char) c j d,
  j >= 2 ->
  (match j - 1 with | 0 => c | S m => nth m B d end) = nth (j - 1 - 1) B d.
Proof.
  intros B' c j d Hj.
  destruct j as [| [| j']].
  - lia.
  - lia.
  - simpl. f_equal. lia.
Qed.

(** * Fold Lemmas *)

(** Helper: fold_left with shifted trace for B - generalized for any accumulator *)
Lemma fold_left_shift_B_aux : forall T A B c2 acc,
  has_B1 T = false ->
  Forall (fun '(i, j) => i >= 1 /\ j >= 2) T ->
  fold_left (fun acc0 '(i, j) =>
    acc0 + subst_cost (nth (i-1) A default_char) (nth (j-1) (c2::B) default_char)) T acc =
  fold_left (fun acc0 '(i, j) =>
    acc0 + subst_cost (nth (i-1) A default_char) (nth (j-1) B default_char)) (shift_trace_B T) acc.
Proof.
  induction T as [| [i j] rest IH]; intros A B c2 acc Hno_B1 Hbounds.
  - reflexivity.
  - rewrite has_B1_cons in Hno_B1.
    apply orb_false_elim in Hno_B1. destruct Hno_B1 as [Hj_neq1 Hno_B1_rest].
    rewrite Forall_cons_iff in Hbounds. destruct Hbounds as [[Hi Hj] Hrest].
    simpl shift_trace_B. rewrite Hj_neq1.
    simpl fold_left.
    assert (Hshift: (match j - 1 with | 0 => c2 | S m => nth m B default_char end) =
                    nth (j - 1 - 1) B default_char).
    { apply nth_cons_match_eq_B. lia. }
    rewrite Hshift.
    apply IH; assumption.
Qed.

(** Change cost equality for shift_trace_B *)
Lemma change_cost_shift_B : forall T A B c2,
  has_B1 T = false ->
  Forall (fun '(i, j) => i >= 1 /\ j >= 2) T ->
  fold_left (fun acc '(i, j) =>
    acc + subst_cost (nth (i-1) A default_char) (nth (j-1) (c2::B) default_char)) T 0 =
  fold_left (fun acc '(i, j) =>
    acc + subst_cost (nth (i-1) A default_char) (nth (j-1) B default_char)) (shift_trace_B T) 0.
Proof.
  intros. apply fold_left_shift_B_aux; assumption.
Qed.

(** * Validity Lemmas *)

(** Validity of shift_trace_B *)
Lemma shift_trace_B_valid : forall lenA lenB T,
  has_B1 T = false ->
  simple_valid_trace lenA (S lenB) T = true ->
  simple_valid_trace lenA lenB (shift_trace_B T) = true.
Proof.
  intros lenA lenB T Hno_B1 Hvalid.
  unfold simple_valid_trace in *.
  rewrite forallb_forall in *.
  intros [i' j'] Hin.
  induction T as [| [i0 j0] rest IH].
  - simpl in Hin. destruct Hin.
  - rewrite has_B1_cons in Hno_B1.
    apply orb_false_elim in Hno_B1. destruct Hno_B1 as [Hj0_neq1 Hno_B1_rest].
    simpl in Hin. rewrite Hj0_neq1 in Hin. simpl in Hin.
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
      apply Nat.eqb_neq in Hj0_neq1.
      subst i' j'.
      repeat (apply andb_true_intro; split); apply Nat.leb_le; lia.
    + apply IH.
      { exact Hno_B1_rest. }
      { intros x Hx. apply Hvalid. right. exact Hx. }
      { exact Hin'. }
Qed.

(** General validity of shift_trace_B - doesn't require has_B1 = false *)
Lemma shift_trace_B_valid_general : forall lenA lenB T,
  simple_valid_trace (S lenA) (S lenB) T = true ->
  simple_valid_trace (S lenA) lenB (shift_trace_B T) = true.
Proof.
  intros lenA lenB T Hvalid.
  unfold simple_valid_trace in *.
  rewrite forallb_forall in *.
  intros [i' j'] Hin.
  induction T as [| [i j] rest IH].
  - simpl in Hin. destruct Hin.
  - simpl shift_trace_B in Hin.
    destruct (j =? 1) eqn:Ej.
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
        apply Nat.eqb_neq in Ej.
        subst i' j'.
        repeat (apply andb_true_intro; split); apply Nat.leb_le; lia.
      * apply IH.
        { intros x Hx. apply Hvalid. right. exact Hx. }
        { exact Hin'. }
Qed.

(** * Empty Trace Lemmas *)

(** For base cases: if lenB = 0, valid trace must be empty *)
Lemma valid_trace_empty_B : forall lenA T,
  simple_valid_trace lenA 0 T = true -> T = [].
Proof.
  intros lenA T Hvalid.
  destruct T as [| [i j] rest].
  - reflexivity.
  - exfalso.
    unfold simple_valid_trace in Hvalid. simpl in Hvalid.
    destruct j as [| j'].
    + apply andb_prop in Hvalid. destruct Hvalid as [Hfirst _].
      apply andb_prop in Hfirst. destruct Hfirst as [Hfirst _].
      apply andb_prop in Hfirst. destruct Hfirst as [_ Hj_lower].
      simpl in Hj_lower. discriminate.
    + apply andb_prop in Hvalid. destruct Hvalid as [Hfirst _].
      apply andb_prop in Hfirst. destruct Hfirst as [Hfirst Hj_le0].
      simpl in Hj_le0. discriminate.
Qed.

