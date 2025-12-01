(** * Has Predicates for Trace Analysis

    This module provides predicates to check whether specific positions
    are touched by a trace, plus key lemmas about monotonicity and cross-matching.

    Part of: Liblevenshtein.Core

    Decomposed from: TraceLowerBound.v (lines 161-283)
*)

From Stdlib Require Import String List Arith Ascii Bool Nat Lia.
Import ListNotations.

From Liblevenshtein.Core Require Import LowerBound.Definitions.

(** * Has Predicates *)

(** Check if (1, 1) is in the trace *)
Definition has_pair_11 (T : Trace) : bool :=
  existsb (fun '(i, j) => (i =? 1) && (j =? 1)) T.

(** Check if 1 is in touched_in_A *)
Definition has_A1 (T : Trace) : bool :=
  existsb (fun i => i =? 1) (touched_in_A T).

(** Check if 1 is in touched_in_B *)
Definition has_B1 (T : Trace) : bool :=
  existsb (fun j => j =? 1) (touched_in_B T).

(** * Monotonicity and Cross-Matching *)

(** Key lemma: Monotonicity eliminates cross-matching *)
Lemma monotonicity_eliminates_cross_matching :
  forall T i j,
    trace_monotonic T ->
    In (1, j) T -> j >= 2 ->
    In (i, 1) T -> i >= 2 ->
    False.
Proof.
  intros T i j Hmono H1j Hj_ge2 Hi1 Hi_ge2.
  unfold trace_monotonic in Hmono.
  assert (H: j < 1).
  { specialize (Hmono 1 j i 1 H1j Hi1).
    assert (H_lt: 1 < i) by lia.
    specialize (Hmono H_lt).
    exact Hmono. }
  lia.
Qed.

(** * Helper Lemmas for Extracting Pairs *)

(** Extract (1, j) from touched_in_A containing 1 *)
Lemma touched_in_A_1_implies_pair : forall T,
  In 1 (touched_in_A T) -> exists j, In (1, j) T.
Proof.
  induction T as [| [a b] rest IH]; intros Hin.
  - simpl in Hin. destruct Hin.
  - simpl touched_in_A in Hin. simpl in Hin.
    destruct Hin as [Heq | Hin_rest].
    + subst. exists b. left. reflexivity.
    + destruct (IH Hin_rest) as [j' Hj'].
      exists j'. right. exact Hj'.
Qed.

(** Extract (i, 1) from touched_in_B containing 1 *)
Lemma touched_in_B_1_implies_pair : forall T,
  In 1 (touched_in_B T) -> exists i, In (i, 1) T.
Proof.
  induction T as [| [a b] rest IH]; intros Hin.
  - simpl in Hin. destruct Hin.
  - simpl touched_in_B in Hin. simpl in Hin.
    destruct Hin as [Heq | Hin_rest].
    + subst. exists a. left. reflexivity.
    + destruct (IH Hin_rest) as [i' Hi'].
      exists i'. right. exact Hi'.
Qed.

(** Pairs in valid trace have indices >= 1 *)
Lemma valid_trace_indices_ge1 : forall lenA lenB T i j,
  simple_valid_trace lenA lenB T = true ->
  In (i, j) T ->
  i >= 1 /\ j >= 1.
Proof.
  intros lenA lenB T i j Hvalid Hin.
  unfold simple_valid_trace in Hvalid.
  rewrite forallb_forall in Hvalid.
  specialize (Hvalid (i, j) Hin).
  apply andb_prop in Hvalid. destruct Hvalid as [Hvalid1 Hj_upper].
  apply andb_prop in Hvalid1. destruct Hvalid1 as [Hvalid2 Hj_lower].
  apply andb_prop in Hvalid2. destruct Hvalid2 as [Hi_lower Hi_upper].
  apply Nat.leb_le in Hi_lower. apply Nat.leb_le in Hj_lower.
  split; lia.
Qed.

(** * Cross-Matching Impossibility *)

(** With monotonicity and validity, cross-matching is impossible *)
Lemma monotonic_cross_matching_impossible :
  forall lenA lenB T,
    simple_valid_trace lenA lenB T = true ->
    trace_monotonic T ->
    has_A1 T = true ->
    has_B1 T = true ->
    has_pair_11 T = false ->
    False.
Proof.
  intros lenA lenB T Hvalid Hmono HA1 HB1 H11.
  unfold has_A1 in HA1. unfold has_B1 in HB1. unfold has_pair_11 in H11.
  apply existsb_exists in HA1. destruct HA1 as [i1 [Hin_A1 Hi1_eq]].
  apply existsb_exists in HB1. destruct HB1 as [j1 [Hin_B1 Hj1_eq]].
  apply Nat.eqb_eq in Hi1_eq. apply Nat.eqb_eq in Hj1_eq.
  subst i1 j1.
  destruct (touched_in_A_1_implies_pair T Hin_A1) as [j H1j].
  destruct (touched_in_B_1_implies_pair T Hin_B1) as [i Hi1].
  pose proof (valid_trace_indices_ge1 lenA lenB T 1 j Hvalid H1j) as [_ Hj_ge1].
  pose proof (valid_trace_indices_ge1 lenA lenB T i 1 Hvalid Hi1) as [Hi_ge1 _].
  destruct (Nat.eq_dec i 1) as [Ei | Ei].
  - subst i.
    assert (Hhas11: existsb (fun '(i, j) => (i =? 1) && (j =? 1)) T = true).
    { apply existsb_exists. exists (1, 1). split; [exact Hi1 | reflexivity]. }
    rewrite Hhas11 in H11. discriminate.
  - destruct (Nat.eq_dec j 1) as [Ej | Ej].
    + subst j.
      assert (Hhas11: existsb (fun '(i, j) => (i =? 1) && (j =? 1)) T = true).
      { apply existsb_exists. exists (1, 1). split; [exact H1j | reflexivity]. }
      rewrite Hhas11 in H11. discriminate.
    + assert (Hi_ge2: i >= 2) by lia.
      assert (Hj_ge2: j >= 2) by lia.
      apply (monotonicity_eliminates_cross_matching T i j Hmono H1j Hj_ge2 Hi1 Hi_ge2).
Qed.
