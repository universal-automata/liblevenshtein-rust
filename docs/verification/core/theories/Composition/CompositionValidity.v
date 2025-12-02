(** * Composition Validity Preservation

    This module proves that trace composition preserves validity.

    Part of: Liblevenshtein.Core

    Decomposed from: Distance.v (lines 3516-3700)
*)

From Coq Require Import String List Arith Ascii Bool Nat Lia.
Import ListNotations.

From Liblevenshtein.Core Require Import Core.Definitions.
From Liblevenshtein.Core Require Import Trace.TraceBasics.
From Liblevenshtein.Core Require Import Trace.TraceComposition.
From Liblevenshtein.Core Require Import Composition.WitnessLemmas.
From Liblevenshtein.Core Require Import Composition.CompositionNoDup.
From Liblevenshtein.Core Require Import Triangle.SubstCostTriangle.

(** * Trace Composition Preserves Validity *)

(**
   Trace Composition Preserves Validity

   If T1 is a valid trace from A to B and T2 is a valid trace from B to C,
   then their composition T1∘T2 is a valid trace from A to C.

   A valid trace must satisfy:
   1. All pairs have valid positions (1 ≤ i ≤ |A|, 1 ≤ k ≤ |C|)
   2. Pairs are compatible (no crossing lines, at most one match per position)
   3. No duplicate pairs (NoDup)
*)
Lemma compose_trace_preserves_validity :
  forall (A B C : list Char) (T1 : Trace A B) (T2 : Trace B C),
    is_valid_trace A B T1 = true ->
    is_valid_trace B C T2 = true ->
    is_valid_trace A C (compose_trace T1 T2) = true.
Proof.
  intros A B C T1 T2 H_valid1 H_valid2.
  unfold is_valid_trace in *.
  apply andb_true_iff in H_valid1 as [H_rest1 H_nodup1].
  apply andb_true_iff in H_rest1 as [H_bounds1 H_aux1].
  apply andb_true_iff in H_valid2 as [H_rest2 H_nodup2].
  apply andb_true_iff in H_rest2 as [H_bounds2 H_aux2].

  apply andb_true_iff. split.
  apply andb_true_iff. split.

  - (* Part 1: All pairs in composed trace have valid bounds *)
    apply forallb_forall.
    intros [i k] H_in.
    rewrite In_compose_trace in H_in.
    destruct H_in as [j [H_in1 H_in2]].
    rewrite forallb_forall in H_bounds1.
    rewrite forallb_forall in H_bounds2.
    apply valid_pair_compose with (lenB := length B) (j := j).
    + apply H_bounds1. exact H_in1.
    + apply H_bounds2. exact H_in2.

  - (* Part 2: All pairs in composed trace are pairwise compatible *)
    apply is_valid_trace_aux_from_pairwise.
    intros p1 p2 H_in1 H_in2.
    eapply compose_trace_pairwise_compatible.
    + exact H_aux1.
    + exact H_aux2.
    + exact H_in1.
    + exact H_in2.

  - (* Part 3: NoDup for composed trace *)
    assert (Hnodup1_prop: NoDup T1).
    { apply (proj1 (NoDup_dec_correct pair_eq_dec T1)). exact H_nodup1. }
    assert (Hnodup2_prop: NoDup T2).
    { apply (proj1 (NoDup_dec_correct pair_eq_dec T2)). exact H_nodup2. }
    apply (proj2 (NoDup_dec_correct pair_eq_dec (compose_trace T1 T2))).
    apply compose_trace_NoDup_axiom; assumption.
Qed.

(** * fold_left Summation Infrastructure *)

(**
   Helper: fold_left with addition preserves initial value ordering.

   If init1 ≤ init2, then fold_left preserves this ordering.
*)
Lemma fold_left_add_init_monotone :
  forall {A : Type} (l : list A) (f : A -> nat) (init1 init2 : nat),
    init1 <= init2 ->
    fold_left (fun acc x => acc + f x) l init1 <=
    fold_left (fun acc x => acc + f x) l init2.
Proof.
  intros A l f init1 init2 H_init.
  generalize dependent init2.
  generalize dependent init1.
  induction l as [| a l' IH].
  - intros init1 init2 H_init.
    simpl. exact H_init.
  - intros init1 init2 H_init.
    simpl.
    apply IH.
    lia.
Qed.

(**
   Basic monotonicity for fold_left with addition.

   If f x ≤ g x for all x in the list, then the fold_left sums preserve the inequality.
*)
Lemma fold_left_add_monotone :
  forall {A : Type} (l : list A) (f g : A -> nat) (init : nat),
    (forall x, In x l -> f x <= g x) ->
    fold_left (fun acc x => acc + f x) l init <=
    fold_left (fun acc x => acc + g x) l init.
Proof.
  intros A l f g init H_pointwise.
  generalize dependent init.
  induction l as [| a l' IH].
  - intros init.
    simpl. lia.
  - intros init.
    simpl.
    assert (H_a: f a <= g a).
    { apply H_pointwise. left. reflexivity. }
    transitivity (fold_left (fun acc x => acc + f x) l' (init + g a)).
    + apply fold_left_add_init_monotone. lia.
    + apply IH. intros x H_in. apply H_pointwise. right. exact H_in.
Qed.

(**
   Helper: fold_left with addition starting from any accumulator is at least
   the accumulator value.
*)
Lemma fold_left_add_lower_bound :
  forall {A : Type} (l : list A) (f : A -> nat) (acc : nat),
    acc <= fold_left (fun a x => a + f x) l acc.
Proof.
  intros A l f acc.
  generalize dependent acc.
  induction l as [| x l' IH].
  - intro acc. simpl. lia.
  - intro acc. simpl.
    transitivity (acc + f x).
    + lia.
    + apply IH.
Qed.

(**
   Helper: If an element is in a list, its value contributes to the fold_left sum.
*)
Lemma in_list_contributes_to_sum :
  forall {A : Type} (x : A) (l : list A) (f : A -> nat),
    In x l ->
    f x <= fold_left (fun acc y => acc + f y) l 0.
Proof.
  intros A x l f H_in.
  induction l as [| a l' IH].
  - contradiction.
  - simpl.
    destruct H_in as [H_eq | H_in'].
    + subst a.
      apply fold_left_add_lower_bound.
    + assert (H_IH': f x <= fold_left (fun acc y => acc + f y) l' 0).
      { apply IH. exact H_in'. }
      transitivity (fold_left (fun acc y => acc + f y) l' 0).
      * exact H_IH'.
      * apply fold_left_add_init_monotone. lia.
Qed.

(** * Compose Trace Element Bound *)

(**
   Helper: Each element of the composition contributes at most the sum of corresponding
   elements from T1 and T2.
*)
Lemma compose_trace_elem_bound :
  forall (A B C : list Char) (T1 : Trace A B) (T2 : Trace B C) (i k : nat),
    In (i, k) (compose_trace T1 T2) ->
    exists j,
      In (i, j) T1 /\
      In (j, k) T2 /\
      subst_cost (nth (i-1) A default_char) (nth (k-1) C default_char) <=
      subst_cost (nth (i-1) A default_char) (nth (j-1) B default_char) +
      subst_cost (nth (j-1) B default_char) (nth (k-1) C default_char).
Proof.
  intros A B C T1 T2 i k H_in.
  apply In_compose_trace in H_in as [j [H_T1 H_T2]].
  exists j.
  split; [exact H_T1 | split; [exact H_T2 |]].
  (* Apply subst_cost_triangle from Triangle.SubstCostTriangle *)
  apply subst_cost_triangle.
Qed.
