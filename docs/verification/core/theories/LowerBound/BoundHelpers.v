(** * Bound Helper Lemmas

    This module provides helper lemmas for establishing bounds on trace indices
    when has_A1 or has_B1 predicates are false.

    Part of: Liblevenshtein.Core

    Decomposed from: TraceLowerBound.v (lines 744-837)
*)

From Stdlib Require Import String List Arith Ascii Bool Nat Lia.
Import ListNotations.

From Liblevenshtein.Core Require Import LowerBound.Definitions.
From Liblevenshtein.Core Require Import LowerBound.HasPredicates.
From Liblevenshtein.Core Require Import LowerBound.ShiftTraceA.
From Liblevenshtein.Core Require Import LowerBound.ShiftTraceB.

(** * Validity Bounds *)

(** When has_A1 = false, all indices in A are >= 2 *)
Lemma valid_no_A1_bounds : forall lenA lenB T,
  simple_valid_trace (S lenA) lenB T = true ->
  has_A1 T = false ->
  Forall (fun '(i, j) => i >= 2 /\ j >= 1) T.
Proof.
  induction T as [| [i j] rest IH]; intros Hvalid Hno_A1.
  - constructor.
  - constructor.
    + (* Show i >= 2 /\ j >= 1 for the head *)
      rewrite has_A1_cons in Hno_A1.
      apply orb_false_elim in Hno_A1. destruct Hno_A1 as [Hi_neq1 Hno_A1_rest].
      apply Nat.eqb_neq in Hi_neq1.
      (* From validity: 1 <= i <= S lenA and 1 <= j <= lenB *)
      unfold simple_valid_trace in Hvalid.
      simpl forallb in Hvalid.
      (* Destruct i to handle the match expression from (1 <=? i) *)
      destruct i as [| i'].
      { (* i = 0: (1 <=? 0) = false, so Hvalid is false = true *)
        exfalso. simpl in Hvalid. discriminate Hvalid. }
      { (* i = S i': now 1 <=? S i' = true, and we need S i' >= 2, i.e., i' >= 1 *)
        (* Need to also destruct j to handle (1 <=? j) match expression *)
        destruct j as [| j'].
        { (* j = 0: (1 <=? 0) = false *)
          exfalso.
          unfold simple_valid_trace in Hvalid.
          simpl forallb in Hvalid. simpl in Hvalid.
          (* After simpl: (i' <=? lenA) && false && forallb ... = true *)
          (* Need to show contradiction *)
          rewrite andb_false_r in Hvalid. discriminate Hvalid. }
        { simpl in Hvalid.
          (* After simpl with i = S i', j = S j':
             structure is: ((i' <=? lenA) && (j' <=? lenB)) && rest *)
          apply andb_prop in Hvalid. destruct Hvalid as [Hfirst Hrest].
          (* Hfirst: (i' <=? lenA) && (j' <=? lenB) = true *)
          apply andb_prop in Hfirst. destruct Hfirst as [Hi_upper Hj_upper].
          (* From Hi_neq1: S i' <> 1, so i' <> 0, meaning i' >= 1, so S i' >= 2 *)
          split; lia. } }
    + (* Apply IH for the rest *)
      rewrite has_A1_cons in Hno_A1.
      apply orb_false_elim in Hno_A1. destruct Hno_A1 as [_ Hno_A1_rest].
      unfold simple_valid_trace in Hvalid.
      simpl forallb in Hvalid.
      destruct i as [| i'].
      { simpl in Hvalid. discriminate Hvalid. }
      { destruct j as [| j'].
        { exfalso. simpl in Hvalid. rewrite andb_false_r in Hvalid. discriminate Hvalid. }
        { simpl in Hvalid.
          apply andb_prop in Hvalid. destruct Hvalid as [_ Hrest].
          apply IH.
          { unfold simple_valid_trace. exact Hrest. }
          { exact Hno_A1_rest. } } }
Qed.

(** When has_B1 = false, all indices in B are >= 2 *)
Lemma valid_no_B1_bounds : forall lenA lenB T,
  simple_valid_trace lenA (S lenB) T = true ->
  has_B1 T = false ->
  Forall (fun '(i, j) => i >= 1 /\ j >= 2) T.
Proof.
  induction T as [| [i j] rest IH]; intros Hvalid Hno_B1.
  - constructor.
  - constructor.
    + (* Show i >= 1 /\ j >= 2 for the head *)
      rewrite has_B1_cons in Hno_B1.
      apply orb_false_elim in Hno_B1. destruct Hno_B1 as [Hj_neq1 Hno_B1_rest].
      apply Nat.eqb_neq in Hj_neq1.
      unfold simple_valid_trace in Hvalid.
      simpl forallb in Hvalid.
      (* Destruct i and j to handle the match expressions *)
      destruct i as [| i'].
      { simpl in Hvalid. discriminate Hvalid. }
      { destruct j as [| j'].
        { exfalso. simpl in Hvalid. rewrite andb_false_r in Hvalid. discriminate Hvalid. }
        { simpl in Hvalid.
          apply andb_prop in Hvalid. destruct Hvalid as [Hfirst Hrest].
          apply andb_prop in Hfirst. destruct Hfirst as [Hi_upper Hj_upper].
          (* From Hj_neq1: S j' <> 1, so j' <> 0, meaning j' >= 1, so S j' >= 2 *)
          split; lia. } }
    + (* Apply IH for the rest *)
      rewrite has_B1_cons in Hno_B1.
      apply orb_false_elim in Hno_B1. destruct Hno_B1 as [_ Hno_B1_rest].
      unfold simple_valid_trace in Hvalid.
      simpl forallb in Hvalid.
      destruct i as [| i'].
      { simpl in Hvalid. discriminate Hvalid. }
      { destruct j as [| j'].
        { exfalso. simpl in Hvalid. rewrite andb_false_r in Hvalid. discriminate Hvalid. }
        { simpl in Hvalid.
          apply andb_prop in Hvalid. destruct Hvalid as [_ Hrest].
          apply IH.
          { unfold simple_valid_trace. exact Hrest. }
          { exact Hno_B1_rest. } } }
Qed.

