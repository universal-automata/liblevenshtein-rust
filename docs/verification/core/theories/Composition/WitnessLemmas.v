(** * Witness Lemmas for Trace Composition

    This module provides lemmas about witness uniqueness and extraction
    for trace composition operations.

    Part of: Liblevenshtein.Core

    Decomposed from: Distance.v (lines 3098-4070)
*)

From Coq Require Import String List Arith Ascii Bool Nat Lia.
Import ListNotations.

From Liblevenshtein.Core Require Import Core.Definitions.
From Liblevenshtein.Core Require Import Trace.TraceBasics.
From Liblevenshtein.Core Require Import Trace.TraceComposition.

(** * Witness Uniqueness *)

(**
   Lemma: If T1 has valid compatible pairs, then for any i, there is at most one j
   such that (i,j) ∈ T1.

   Proof: By compatible_pairs constraint, distinct pairs cannot share first components.
*)
Lemma witness_j_unique_in_T1 :
  forall (A B : list Char) (T1 : Trace A B) (i j1 j2 : nat),
    is_valid_trace_aux T1 = true ->
    In (i, j1) T1 ->
    In (i, j2) T1 ->
    j1 = j2.
Proof.
  intros A B T1 i j1 j2 H_valid H_in1 H_in2.
  destruct (Nat.eq_dec j1 j2) as [H_eq | H_neq].
  - exact H_eq.
  - assert (H_compat: compatible_pairs (i, j1) (i, j2) = true).
    { eapply is_valid_trace_aux_In_compatible; eauto. }
    unfold compatible_pairs in H_compat.
    assert (H_i_eq: (i =? i) = true). { apply Nat.eqb_refl. }
    assert (H_j_neq: (j1 =? j2) = false). { apply Nat.eqb_neq. exact H_neq. }
    rewrite H_i_eq, H_j_neq in H_compat.
    discriminate H_compat.
Qed.

(**
   Symmetric lemma for T2: unique first component.
*)
Lemma witness_k_unique_in_T2 :
  forall (B C : list Char) (T2 : Trace B C) (j k1 k2 : nat),
    is_valid_trace_aux T2 = true ->
    In (j, k1) T2 ->
    In (j, k2) T2 ->
    k1 = k2.
Proof.
  intros B C T2 j k1 k2 H_valid H_in1 H_in2.
  destruct (Nat.eq_dec k1 k2) as [H_eq | H_neq].
  - exact H_eq.
  - assert (H_compat: compatible_pairs (j, k1) (j, k2) = true).
    { eapply is_valid_trace_aux_In_compatible; eauto. }
    unfold compatible_pairs in H_compat.
    assert (H_j_eq: (j =? j) = true). { apply Nat.eqb_refl. }
    assert (H_k_neq: (k1 =? k2) = false). { apply Nat.eqb_neq. exact H_neq. }
    rewrite H_j_eq, H_k_neq in H_compat.
    discriminate H_compat.
Qed.

(** * Compose Trace First Component Properties *)

(**
   Helper: First components of compose_trace come from first components of T1.

   More precisely: i is a first component of compose_trace iff
   (i, j) ∈ T1 and (j, k) ∈ T2 for some j, k.
*)
Lemma compose_trace_fst_subset_T1_fst :
  forall (A B C : list Char) (T1 : Trace A B) (T2 : Trace B C) (i : nat),
    In i (map fst (compose_trace T1 T2)) ->
    In i (map fst T1).
Proof.
  intros A B C T1 T2 i Hin.
  apply in_map_iff in Hin as [[i' k] [Heq Hin_comp]].
  simpl in Heq. subst i'.
  apply In_compose_trace in Hin_comp as [j [Hin1 _]].
  apply in_map_iff.
  exists (i, j). split; [reflexivity | exact Hin1].
Qed.

(**
   Helper: Each first component appears at most once in compose_trace.

   This follows from witness uniqueness: for a given i, there's a unique j
   with (i,j) ∈ T1, and for that j, a unique k with (j,k) ∈ T2.
*)
Lemma compose_trace_fst_unique :
  forall (A B C : list Char) (T1 : Trace A B) (T2 : Trace B C) (i k1 k2 : nat),
    is_valid_trace_aux T1 = true ->
    is_valid_trace_aux T2 = true ->
    In (i, k1) (compose_trace T1 T2) ->
    In (i, k2) (compose_trace T1 T2) ->
    k1 = k2.
Proof.
  intros A B C T1 T2 i k1 k2 Haux1 Haux2 Hin1 Hin2.
  apply In_compose_trace in Hin1 as [j1 [HinT1_1 HinT2_1]].
  apply In_compose_trace in Hin2 as [j2 [HinT1_2 HinT2_2]].
  assert (Hj_eq: j1 = j2).
  { eapply (witness_j_unique_in_T1 A B T1 i j1 j2); assumption. }
  subst j2.
  eapply (witness_k_unique_in_T2 B C T2 j1 k1 k2); assumption.
Qed.

(** * Witness Uniqueness and Existence *)

(**
   Definition: Functional property for witness extraction.

   For each (i,k) in compose_trace T1 T2, there exists a UNIQUE j such that
   (i,j) ∈ T1 and (j,k) ∈ T2.
*)
Definition has_unique_witness (A B C : list Char) (T1 : Trace A B) (T2 : Trace B C) (ik : nat * nat) : Prop :=
  let '(i, k) := ik in
  In ik (compose_trace T1 T2) ->
  exists! j, In (i, j) T1 /\ In (j, k) T2.

(**
   Lemma: Witness extraction is well-defined for valid traces.

   Every element in compose_trace has a unique witness when both traces are valid.
*)
Lemma compose_witness_unique :
  forall (A B C : list Char) (T1 : Trace A B) (T2 : Trace B C) (i k : nat),
    is_valid_trace_aux T1 = true ->
    is_valid_trace_aux T2 = true ->
    In (i, k) (compose_trace T1 T2) ->
    exists! j, In (i, j) T1 /\ In (j, k) T2.
Proof.
  intros A B C T1 T2 i k Hval1 Hval2 Hin_comp.
  apply In_compose_trace in Hin_comp as [j [Hin1 Hin2]].
  exists j. split.
  - split; assumption.
  - intros j' [Hin1' Hin2'].
    symmetry.
    eapply witness_j_unique_in_T1.
    + exact Hval1.
    + exact Hin1'.
    + exact Hin1.
Qed.

(** * Witness Extraction Functions *)

(**
   Helper: Extract the unique witness j for a composition pair (i,k).

   This function is well-defined when T1 has compatible pairs (proven below).
*)
Definition witness_j_for_comp (A B C : list Char) (T1 : Trace A B) (T2 : Trace B C) (ik : nat * nat) : option nat :=
  let '(i, k) := ik in
  match find (fun p1 => let '(i1, j1) := p1 in (i =? i1)) T1 with
  | Some (_, j) =>
      if existsb (fun p2 => let '(j2, k2) := p2 in (j =? j2) && (k =? k2)) T2
      then Some j
      else None
  | None => None
  end.

(**
   Helper: Extract the witness j for a given (i,k) in composition.

   This is a constructive version using find. Returns Some j if witness exists.
*)
Definition extract_witness_j (A B C : list Char) (T1 : Trace A B) (T2 : Trace B C) (i k : nat) : option nat :=
  match find (fun p1 => let '(i1, j1) := p1 in i =? i1) T1 with
  | Some (_, j) =>
      if existsb (fun p2 => let '(j2, k2) := p2 in (j =? j2) && (k =? k2)) T2
      then Some j
      else None
  | None => None
  end.

(** * find Helper Lemmas *)

(**
   Helper: find returns Some for elements in the list when predicate holds.
*)
Lemma find_some_in_iff :
  forall {A : Type} (f : A -> bool) (l : list A) (x : A),
    find f l = Some x -> In x l /\ f x = true.
Proof.
  intros A f l x.
  induction l as [| a l' IH].
  - intro H. discriminate H.
  - simpl. destruct (f a) eqn:Hfa.
    + intro H. inversion H; subst.
      split.
      * left. reflexivity.
      * exact Hfa.
    + intro H. apply IH in H as [Hin Hfx].
      split.
      * right. exact Hin.
      * exact Hfx.
Qed.

(**
   Helper: If element satisfies predicate and is in list, find eventually returns it or earlier match.
*)
Lemma in_find_some :
  forall {A : Type} (f : A -> bool) (l : list A) (x : A),
    In x l -> f x = true -> exists y, find f l = Some y /\ f y = true.
Proof.
  intros A f l x Hin Hfx.
  induction l as [| a l' IH].
  - contradiction.
  - simpl. destruct (f a) eqn:Hfa.
    + exists a. split.
      * reflexivity.
      * exact Hfa.
    + destruct Hin as [Heq | Hin'].
      * subst a. rewrite Hfx in Hfa. discriminate Hfa.
      * apply IH in Hin' as [y [Hfind Hfy]].
        exists y. split.
        -- exact Hfind.
        -- exact Hfy.
Qed.

(**
   Lemma: extract_witness_j is correct - it finds the unique witness.
*)
Lemma extract_witness_j_correct :
  forall (A B C : list Char) (T1 : Trace A B) (T2 : Trace B C) (i k j : nat),
    is_valid_trace_aux T1 = true ->
    is_valid_trace_aux T2 = true ->
    In (i, k) (compose_trace T1 T2) ->
    In (i, j) T1 ->
    In (j, k) T2 ->
    extract_witness_j A B C T1 T2 i k = Some j.
Proof.
  intros A B C T1 T2 i k j Hval1 Hval2 Hin_comp Hin1 Hin2.
  unfold extract_witness_j.
  assert (Hfind_ex: exists p, find (fun p1 => let '(i1, j1) := p1 in i =? i1) T1 = Some p).
  {
    destruct (in_find_some (fun p1 => let '(i1, j1) := p1 in i =? i1) T1 (i, j) Hin1) as [p [Hfind Hpred]].
    - simpl. apply Nat.eqb_refl.
    - exists p. exact Hfind.
  }
  destruct Hfind_ex as [[i' j'] Hfind].
  rewrite Hfind.
  apply find_some_in_iff in Hfind as [Hin_ij' Hpred'].
  simpl in Hpred'.
  apply Nat.eqb_eq in Hpred' as Hi'_eq.
  subst i'.
  assert (Hj'_eq: j' = j).
  {
    eapply witness_j_unique_in_T1.
    - exact Hval1.
    - exact Hin_ij'.
    - exact Hin1.
  }
  subst j'.
  assert (Hexists: existsb (fun p2 => let '(j2, k2) := p2 in (j =? j2) && (k =? k2)) T2 = true).
  {
    apply existsb_exists.
    exists (j, k).
    split.
    - exact Hin2.
    - simpl. rewrite Nat.eqb_refl. rewrite Nat.eqb_refl. reflexivity.
  }
  rewrite Hexists.
  reflexivity.
Qed.
