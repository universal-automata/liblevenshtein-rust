(** * Optimal Trace Construction

    This module defines the optimal trace construction via DP backtracking.
    The optimal trace achieves exactly the Levenshtein distance cost.

    Part of: Liblevenshtein.Core

    Decomposed from: Distance.v (lines 6905-7100)
*)

From Coq Require Import String List Arith Ascii Bool Nat Lia Wf_nat.
From Coq Require Import Program.Wf.
From Coq Require Import Recdef.
Import ListNotations.

From Liblevenshtein.Core Require Import Core.Definitions.
From Liblevenshtein.Core Require Import Core.LevDistance.
From Liblevenshtein.Core Require Import Trace.TraceBasics.
From Liblevenshtein.Core Require Import Trace.TouchedPositions.

(** * Optimal Trace Definition *)

(** Measure for well-founded recursion *)
Definition optimal_trace_measure (p : list Char * list Char) : nat :=
  length (fst p) + length (snd p).

(** Optimal trace construction via DP backtracking *)
Function optimal_trace_pair (p : list Char * list Char)
  {measure optimal_trace_measure p} : list (nat * nat) :=
  match p with
  | ([], _) => []
  | (_, []) => []
  | (c1 :: s1', c2 :: s2') =>
      let cost_del := lev_distance s1' (c2 :: s2') + 1 in
      let cost_ins := lev_distance (c1 :: s1') s2' + 1 in
      let cost_sub := lev_distance s1' s2' + subst_cost c1 c2 in
      if (cost_sub <=? cost_del) && (cost_sub <=? cost_ins)
      then (1, 1) :: map (fun '(i, j) => (S i, S j)) (optimal_trace_pair (s1', s2'))
      else if cost_del <=? cost_ins
      then map (fun '(i, j) => (S i, j)) (optimal_trace_pair (s1', c2 :: s2'))
      else map (fun '(i, j) => (i, S j)) (optimal_trace_pair (c1 :: s1', s2'))
  end.
Proof.
  - intros. unfold optimal_trace_measure. simpl. lia.
  - intros. unfold optimal_trace_measure. simpl. lia.
  - intros. unfold optimal_trace_measure. simpl. lia.
Defined.

(** Wrapper: optimal_trace for given strings A, B *)
Definition optimal_trace (A B : list Char) : Trace A B :=
  optimal_trace_pair (A, B).

(** * Map Lemmas for touched_in Functions *)

Lemma touched_in_A_map_SS : forall (A B : list Char) (T : Trace A B),
  touched_in_A A B (map (fun '(i, j) => (S i, S j)) T) = map S (touched_in_A A B T).
Proof.
  intros A' B' T.
  induction T as [| [i j] rest IH]; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

Lemma touched_in_B_map_SS : forall (A B : list Char) (T : Trace A B),
  touched_in_B A B (map (fun '(i, j) => (S i, S j)) T) = map S (touched_in_B A B T).
Proof.
  intros A' B' T.
  induction T as [| [i j] rest IH]; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

Lemma touched_in_A_map_S_id : forall (A B : list Char) (T : Trace A B),
  touched_in_A A B (map (fun '(i, j) => (S i, j)) T) = map S (touched_in_A A B T).
Proof.
  intros A' B' T.
  induction T as [| [i j] rest IH]; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

Lemma touched_in_B_map_S_id : forall (A B : list Char) (T : Trace A B),
  touched_in_B A B (map (fun '(i, j) => (S i, j)) T) = touched_in_B A B T.
Proof.
  intros A' B' T.
  induction T as [| [i j] rest IH]; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

Lemma touched_in_A_map_id_S : forall (A B : list Char) (T : Trace A B),
  touched_in_A A B (map (fun '(i, j) => (i, S j)) T) = touched_in_A A B T.
Proof.
  intros A' B' T.
  induction T as [| [i j] rest IH]; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

Lemma touched_in_B_map_id_S : forall (A B : list Char) (T : Trace A B),
  touched_in_B A B (map (fun '(i, j) => (i, S j)) T) = map S (touched_in_B A B T).
Proof.
  intros A' B' T.
  induction T as [| [i j] rest IH]; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

(** * Valid Indices Predicate *)

(** All indices in trace are >= 1 *)
Definition valid_indices (T : list (nat * nat)) : Prop :=
  Forall (fun '(i, j) => i >= 1 /\ j >= 1) T.

(** Helper: match_nth equality after simpl *)
Lemma match_nth_eq : forall (A : list Char) c i,
  i >= 1 ->
  match i - 0 with | 0 => c | S m => nth m A default_char end = nth (i - 1) A default_char.
Proof.
  intros A' c i Hi.
  destruct i as [| i'].
  - lia.
  - simpl. rewrite Nat.sub_0_r. reflexivity.
Qed.

(** * Fold Accumulator Lemmas *)

(** Fold_left accumulator extraction for additive functions *)
Lemma fold_left_acc_extract :
  forall (A B : list Char) (T : list (nat * nat)) (acc : nat),
    fold_left (fun a '(i, j) =>
      a + subst_cost (nth (i-1) A default_char) (nth (j-1) B default_char)) T acc =
    fold_left (fun a '(i, j) =>
      a + subst_cost (nth (i-1) A default_char) (nth (j-1) B default_char)) T 0 + acc.
Proof.
  intros A' B' T.
  induction T as [| [i j] rest IH]; intros acc; simpl.
  - lia.
  - rewrite IH.
    set (cost := subst_cost (nth (i - 1) A' default_char) (nth (j - 1) B' default_char)).
    specialize (IH cost).
    lia.
Qed.

(** Fold_left shift for SS mapping *)
Lemma fold_left_change_cost_shift_SS_aux :
  forall A B T c1 c2 acc,
    valid_indices T ->
    fold_left (fun a '(i, j) =>
      a + subst_cost (nth (i-1) (c1::A) default_char) (nth (j-1) (c2::B) default_char))
      (map (fun '(i, j) => (S i, S j)) T) acc =
    fold_left (fun a '(i, j) =>
      a + subst_cost (nth (i-1) A default_char) (nth (j-1) B default_char)) T acc.
Proof.
  intros A' B' T c1 c2.
  induction T as [| [i j] rest IH]; intros acc Hvalid.
  - simpl. reflexivity.
  - unfold valid_indices in Hvalid.
    rewrite Forall_cons_iff in Hvalid.
    destruct Hvalid as [[Hi Hj] Hrest].
    simpl map. simpl fold_left.
    rewrite (match_nth_eq A' c1 i Hi).
    rewrite (match_nth_eq B' c2 j Hj).
    apply IH. unfold valid_indices. exact Hrest.
Qed.
