(** * Pigeonhole Principle for NoDup Bounds

    This module provides the pigeonhole-based cardinality bounds for traces
    with unique touched positions.

    Part of: Liblevenshtein.Core

    Decomposed from: TraceLowerBound.v (lines 839-1021)
*)

From Stdlib Require Import String List Arith Ascii Bool Nat Lia.
Import ListNotations.

From Liblevenshtein.Core Require Import LowerBound.Definitions.
From Liblevenshtein.Core Require Import LowerBound.HasPredicates.
From Liblevenshtein.Core Require Import LowerBound.ShiftTraceA.
From Liblevenshtein.Core Require Import LowerBound.ShiftTraceB.

(** * Validity Helper Lemmas *)

(** Helper lemma: Convert leb to le for bounds - use forallb_forall *)
Lemma valid_trace_first_bounds : forall lenA lenB i j rest,
  simple_valid_trace lenA lenB ((i, j) :: rest) = true ->
  1 <= i /\ i <= lenA /\ 1 <= j /\ j <= lenB.
Proof.
  intros lenA lenB i j rest Hvalid.
  unfold simple_valid_trace in Hvalid.
  rewrite forallb_forall in Hvalid.
  specialize (Hvalid (i, j) (in_eq (i, j) rest)).
  apply andb_prop in Hvalid. destruct Hvalid as [Hvalid' H4].
  apply andb_prop in Hvalid'. destruct Hvalid' as [Hvalid'' H3].
  apply andb_prop in Hvalid''. destruct Hvalid'' as [H1 H2].
  apply Nat.leb_le in H1.
  apply Nat.leb_le in H2.
  apply Nat.leb_le in H3.
  apply Nat.leb_le in H4.
  repeat split; assumption.
Qed.

(** Get validity for rest *)
Lemma valid_trace_rest : forall lenA lenB x rest,
  simple_valid_trace lenA lenB (x :: rest) = true ->
  simple_valid_trace lenA lenB rest = true.
Proof.
  intros lenA lenB x rest Hvalid.
  unfold simple_valid_trace in *.
  rewrite forallb_forall in *.
  intros y Hy.
  apply Hvalid. right. exact Hy.
Qed.

(** Simple corollary for what we actually need *)
Lemma valid_trace_i_bounds : forall lenA lenB i j rest,
  simple_valid_trace lenA lenB ((i, j) :: rest) = true ->
  1 <= i <= lenA.
Proof.
  intros.
  pose proof (valid_trace_first_bounds lenA lenB i j rest H) as [H1 [H2 _]].
  split; assumption.
Qed.

Lemma valid_trace_j_bounds : forall lenA lenB i j rest,
  simple_valid_trace lenA lenB ((i, j) :: rest) = true ->
  1 <= j <= lenB.
Proof.
  intros.
  pose proof (valid_trace_first_bounds lenA lenB i j rest H) as [_ [_ [H1 H2]]].
  split; assumption.
Qed.

(** * Touched Position Range Lemmas *)

(** Helper: All elements in touched_in_A are in range [2, S lenA] when has_A1=false *)
Lemma touched_in_A_in_range : forall lenA lenB T,
  simple_valid_trace (S lenA) lenB T = true ->
  has_A1 T = false ->
  forall x, In x (touched_in_A T) -> 2 <= x <= S lenA.
Proof.
  intros lenA lenB T Hvalid Hno_A1.
  induction T as [| [i j] rest IH].
  - intros x Hin. simpl in Hin. destruct Hin.
  - intros x Hin.
    rewrite has_A1_cons in Hno_A1.
    apply orb_false_elim in Hno_A1. destruct Hno_A1 as [Hi_neq1 Hno_A1_rest].
    apply Nat.eqb_neq in Hi_neq1.
    pose proof (valid_trace_i_bounds (S lenA) lenB i j rest Hvalid) as [Hi_lo Hi_hi].
    pose proof (valid_trace_rest (S lenA) lenB (i, j) rest Hvalid) as Hrest.
    simpl in Hin. destruct Hin as [Heq | Hin'].
    + subst x. split; lia.
    + apply IH; assumption.
Qed.

(** Symmetric for B *)
Lemma touched_in_B_in_range : forall lenA lenB T,
  simple_valid_trace lenA (S lenB) T = true ->
  has_B1 T = false ->
  forall x, In x (touched_in_B T) -> 2 <= x <= S lenB.
Proof.
  intros lenA lenB T Hvalid Hno_B1.
  induction T as [| [i j] rest IH].
  - intros x Hin. simpl in Hin. destruct Hin.
  - intros x Hin.
    rewrite has_B1_cons in Hno_B1.
    apply orb_false_elim in Hno_B1. destruct Hno_B1 as [Hj_neq1 Hno_B1_rest].
    apply Nat.eqb_neq in Hj_neq1.
    pose proof (valid_trace_j_bounds lenA (S lenB) i j rest Hvalid) as [Hj_lo Hj_hi].
    pose proof (valid_trace_rest lenA (S lenB) (i, j) rest Hvalid) as Hrest.
    simpl in Hin. destruct Hin as [Heq | Hin'].
    + subst x. split; lia.
    + apply IH; assumption.
Qed.

(** * Pigeonhole Lemma *)

(** Pigeonhole: NoDup list with elements in [a, b] has length <= b - a + 1 *)
Lemma NoDup_length_le_range : forall (l : list nat) a b,
  NoDup l ->
  (forall x, In x l -> a <= x <= b) ->
  a <= b + 1 ->
  length l <= b - a + 1.
Proof.
  intros l a b Hnodup Hrange Hab.
  assert (Hincl: incl l (seq a (b - a + 1))).
  { unfold incl. intros x Hin.
    specialize (Hrange x Hin).
    apply in_seq. lia. }
  pose proof (NoDup_incl_length Hnodup Hincl) as Hlen.
  rewrite length_seq in Hlen.
  exact Hlen.
Qed.

(** * NoDup Trace Length Bounds *)

(** Key lemma: NoDup + validity + has_A1 = false implies |T| <= |s1'| *)
Lemma NoDup_A_bound : forall lenA lenB T,
  simple_valid_trace (S lenA) lenB T = true ->
  has_A1 T = false ->
  NoDup (touched_in_A T) ->
  length T <= lenA.
Proof.
  intros lenA lenB T Hvalid Hno_A1 Hnodup.
  pose proof (touched_in_A_in_range lenA lenB T Hvalid Hno_A1) as Hrange.
  rewrite <- touched_in_A_length.
  destruct lenA as [| lenA'].
  - (* lenA = 0: range is [2, 1] which is empty *)
    destruct T as [| [i j] rest] eqn:ET.
    + simpl. lia.
    + simpl touched_in_A.
      exfalso.
      assert (Hin: In i (i :: touched_in_A rest)) by (left; reflexivity).
      specialize (Hrange i Hin).
      lia.
  - (* lenA = S lenA' *)
    assert (Hlen: length (touched_in_A T) <= S (S lenA') - 2 + 1).
    { apply NoDup_length_le_range; try assumption; lia. }
    lia.
Qed.

(** Symmetric: NoDup + validity + has_B1 = false implies |T| <= |s2'| *)
Lemma NoDup_B_bound : forall lenA lenB T,
  simple_valid_trace lenA (S lenB) T = true ->
  has_B1 T = false ->
  NoDup (touched_in_B T) ->
  length T <= lenB.
Proof.
  intros lenA lenB T Hvalid Hno_B1 Hnodup.
  pose proof (touched_in_B_in_range lenA lenB T Hvalid Hno_B1) as Hrange.
  rewrite <- touched_in_B_length.
  destruct lenB as [| lenB'].
  - destruct T as [| [i j] rest] eqn:ET.
    + simpl. lia.
    + simpl touched_in_B.
      exfalso.
      assert (Hin: In j (j :: touched_in_B rest)) by (left; reflexivity).
      specialize (Hrange j Hin).
      lia.
  - assert (Hlen: length (touched_in_B T) <= S (S lenB') - 2 + 1).
    { apply NoDup_length_le_range; try assumption; lia. }
    lia.
Qed.

(** * Touched Position Shift Lemmas *)

(** When has_A1 = false, shift_trace_A doesn't filter anything *)
Lemma touched_in_B_shift_trace_A : forall T,
  has_A1 T = false ->
  touched_in_B (shift_trace_A T) = touched_in_B T.
Proof.
  induction T as [| [i j] rest IH]; intros Hno_A1.
  - reflexivity.
  - rewrite has_A1_cons in Hno_A1.
    apply orb_false_elim in Hno_A1. destruct Hno_A1 as [Hi_neq1 Hno_A1_rest].
    simpl shift_trace_A. rewrite Hi_neq1.
    simpl touched_in_B.
    f_equal. apply IH. exact Hno_A1_rest.
Qed.

Lemma touched_in_A_shift_trace_B : forall T,
  has_B1 T = false ->
  touched_in_A (shift_trace_B T) = touched_in_A T.
Proof.
  induction T as [| [i j] rest IH]; intros Hno_B1.
  - reflexivity.
  - rewrite has_B1_cons in Hno_B1.
    apply orb_false_elim in Hno_B1. destruct Hno_B1 as [Hj_neq1 Hno_B1_rest].
    simpl shift_trace_B. rewrite Hj_neq1.
    simpl touched_in_A.
    f_equal. apply IH. exact Hno_B1_rest.
Qed.

