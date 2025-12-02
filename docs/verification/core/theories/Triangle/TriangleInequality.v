(** * Triangle Inequality for Levenshtein Distance

    This module proves the triangle inequality for Levenshtein distance:
    d(A, C) <= d(A, B) + d(B, C)

    Part of: Liblevenshtein.Core

    Decomposed from: Distance.v (lines 7856-7972)
*)

From Stdlib Require Import String List Arith Ascii Bool Nat Lia Wf_nat.
Import ListNotations.

From Liblevenshtein.Core Require Import Core.Definitions.
From Liblevenshtein.Core Require Import Core.LevDistance.
From Liblevenshtein.Core Require Import Trace.TraceBasics.
From Liblevenshtein.Core Require Import Trace.TouchedPositions.
From Liblevenshtein.Core Require Import Trace.TraceCost.
From Liblevenshtein.Core Require Import Trace.TraceComposition.
From Liblevenshtein.Core Require Import Cardinality.NoDupPreservation.
From Liblevenshtein.Core Require Import Composition.CompositionValidity.
From Liblevenshtein.Core Require Import Composition.CostBounds.
From Liblevenshtein.Core Require Import OptimalTrace.Construction.
From Liblevenshtein.Core Require Import OptimalTrace.Validity.
From Liblevenshtein.Core Require Import OptimalTrace.CostEquality.

(** Import LowerBound modules - use explicit qualification to avoid shadowing *)
From Liblevenshtein.Core Require LowerBound.Definitions.
From Liblevenshtein.Core Require LowerBound.MainTheorem.
(** Note: LowerBound.Definitions.Trace shadows TraceBasics.Trace, so we use
    'list (nat * nat)' or qualified 'TraceBasics.Trace A B' when needed. *)

(** Notation: LowerBound module uses simplified signatures:
    - LowerBound.Definitions.Trace = list (nat * nat)
    - LowerBound.Definitions.touched_in_A : Trace -> list nat
    - LowerBound.Definitions.touched_in_B : Trace -> list nat
    - LowerBound.Definitions.trace_cost : nat -> nat -> list Char -> list Char -> Trace -> nat
    - LowerBound.Definitions.simple_valid_trace : nat -> nat -> Trace -> bool
    - LowerBound.Definitions.trace_monotonic : Trace -> Prop

    Core modules use:
    - Trace A B = list (nat * nat) (same underlying type)
    - touched_in_A A B T (extra unused params for typing)
    - trace_cost A B T (uses length A, length B internally)
    - is_valid_trace A B T
    - trace_monotonic T (same)
*)

(** * Bridge Lemmas: Equivalence between Core and LowerBound definitions *)

(** touched_in_A equivalence: Core's definition equals LowerBound's definition *)
Lemma touched_in_A_equiv_LB : forall (A B : list Char) (T : list (nat * nat)),
  touched_in_A A B T = LowerBound.Definitions.touched_in_A T.
Proof.
  intros A B T.
  induction T as [| [i j] rest IH]; simpl; [reflexivity | rewrite IH; reflexivity].
Qed.

(** touched_in_B equivalence: Core's definition equals LowerBound's definition *)
Lemma touched_in_B_equiv_LB : forall (A B : list Char) (T : list (nat * nat)),
  touched_in_B A B T = LowerBound.Definitions.touched_in_B T.
Proof.
  intros A B T.
  induction T as [| [i j] rest IH]; simpl; [reflexivity | rewrite IH; reflexivity].
Qed.

(** trace_cost equivalence: Core's definition equals LowerBound's definition *)
Lemma trace_cost_equiv_LB : forall (A B : list Char) (T : list (nat * nat)),
  trace_cost A B T = LowerBound.Definitions.trace_cost (length A) (length B) A B T.
Proof.
  intros A B T.
  unfold trace_cost, LowerBound.Definitions.trace_cost.
  rewrite touched_in_A_equiv_LB, touched_in_B_equiv_LB.
  reflexivity.
Qed.

(** trace_monotonic equivalence *)
Lemma trace_monotonic_equiv_LB : forall (T : list (nat * nat)),
  trace_monotonic T <-> LowerBound.Definitions.trace_monotonic T.
Proof.
  intros. unfold trace_monotonic, LowerBound.Definitions.trace_monotonic. split; auto.
Qed.

(** NoDup equivalence for touched_in_A *)
Lemma NoDup_touched_in_A_equiv_LB : forall (A B : list Char) (T : list (nat * nat)),
  NoDup (touched_in_A A B T) <-> NoDup (LowerBound.Definitions.touched_in_A T).
Proof.
  intros. rewrite touched_in_A_equiv_LB. split; auto.
Qed.

(** NoDup equivalence for touched_in_B *)
Lemma NoDup_touched_in_B_equiv_LB : forall (A B : list Char) (T : list (nat * nat)),
  NoDup (touched_in_B A B T) <-> NoDup (LowerBound.Definitions.touched_in_B T).
Proof.
  intros. rewrite touched_in_B_equiv_LB. split; auto.
Qed.

(** valid_pair equivalence with LowerBound.Definitions.simple_valid_trace bounds *)
Lemma valid_pair_equiv_LB : forall lenA lenB i j,
  valid_pair lenA lenB (i, j) = ((1 <=? i) && (i <=? lenA) && (1 <=? j) && (j <=? lenB)).
Proof.
  intros. unfold valid_pair. reflexivity.
Qed.

(** is_valid_trace implies LowerBound.Definitions.simple_valid_trace *)
Lemma is_valid_trace_implies_LB_valid : forall (A B : list Char) (T : list (nat * nat)),
  is_valid_trace A B T = true -> LowerBound.Definitions.simple_valid_trace (length A) (length B) T = true.
Proof.
  intros A B T Hvalid.
  unfold is_valid_trace in Hvalid.
  apply andb_true_iff in Hvalid as [H_rest H_nodup].
  apply andb_true_iff in H_rest as [H_bounds H_aux].
  unfold LowerBound.Definitions.simple_valid_trace.
  rewrite forallb_forall in H_bounds.
  rewrite forallb_forall.
  intros [i j] Hin.
  specialize (H_bounds (i, j) Hin).
  rewrite valid_pair_equiv_LB in H_bounds.
  exact H_bounds.
Qed.

(** is_valid_trace implies monotonicity *)
Lemma is_valid_trace_implies_monotonic : forall (A B : list Char) (T : list (nat * nat)),
  is_valid_trace A B T = true -> trace_monotonic T.
Proof.
  intros A B T Hvalid.
  unfold is_valid_trace in Hvalid.
  apply andb_true_iff in Hvalid as [H_rest H_nodup].
  apply andb_true_iff in H_rest as [H_bounds H_aux].
  (* Get NoDup from NoDup_dec *)
  apply NoDup_dec_correct in H_nodup.
  (* Use the existing lemma from TraceBasics *)
  apply is_valid_trace_aux_implies_monotonic; assumption.
Qed.

(** * Lower Bound Adapter

    This adapter connects the is_valid_trace predicate from the core module
    to the lower bound theorem from LowerBound/MainTheorem.v.

    The LowerBound module proves:
      trace_cost T >= lev_distance A B
    for traces satisfying simple_valid_trace, NoDup conditions, and monotonicity.

    Since is_valid_trace implies all these conditions, we can use the lower bound.
*)

(**
   Lower bound: Any valid trace has cost >= Levenshtein distance.

   This is the key theorem from the LowerBound module, adapted to use is_valid_trace.
   The proof uses the fact that is_valid_trace implies:
   1. All pairs have valid bounds (simple_valid_trace)
   2. NoDup on touched_in_A and touched_in_B
   3. Monotonicity (from is_valid_trace_aux / compatible_pairs)
*)
Lemma trace_cost_lower_bound_internal :
  forall (A B : list Char) (T : list (nat * nat)),
    is_valid_trace A B T = true ->
    trace_cost A B T >= lev_distance A B.
Proof.
  intros A B T Hvalid.
  rewrite trace_cost_equiv_LB.
  assert (H_simple_valid: LowerBound.Definitions.simple_valid_trace (length A) (length B) T = true)
    by (apply is_valid_trace_implies_LB_valid; exact Hvalid).
  assert (H_nodup_A: NoDup (LowerBound.Definitions.touched_in_A T)).
  { apply (proj1 (NoDup_touched_in_A_equiv_LB A B T)). apply touched_in_A_NoDup. exact Hvalid. }
  assert (H_nodup_B: NoDup (LowerBound.Definitions.touched_in_B T)).
  { apply (proj1 (NoDup_touched_in_B_equiv_LB A B T)). apply touched_in_B_NoDup. exact Hvalid. }
  assert (H_mono: LowerBound.Definitions.trace_monotonic T).
  { apply (proj1 (trace_monotonic_equiv_LB T)). apply (is_valid_trace_implies_monotonic A B T). exact Hvalid. }
  pose proof (LowerBound.MainTheorem.trace_cost_lower_bound A B T H_simple_valid H_nodup_A H_nodup_B H_mono) as H.
  exact H.
Qed.

(** * Main Theorems *)

(**
   Theorem: Existence and optimality of traces

   For any two strings A and B, there exists an optimal trace T_opt that:
   1. Is a valid trace from A to B
   2. Has cost equal to the Levenshtein distance
   3. Has minimum cost among all valid traces
*)
Theorem distance_equals_min_trace_cost :
  forall (A B : list Char),
    exists (T_opt : Trace A B),
      is_valid_trace A B T_opt = true /\
      trace_cost A B T_opt = lev_distance A B /\
      (forall T : Trace A B, is_valid_trace A B T = true ->
        trace_cost A B T_opt <= trace_cost A B T).
Proof.
  intros A B.
  (* Construct the optimal trace *)
  exists (optimal_trace A B).
  split; [| split].

  - (* Property 1: is_valid_trace = true *)
    apply optimal_trace_valid.

  - (* Property 2: trace_cost = lev_distance *)
    apply optimal_trace_cost.

  - (* Property 3: minimality *)
    intros T Hvalid.
    (* trace_cost T >= lev_distance (by lower bound) *)
    (* trace_cost T_opt = lev_distance (by cost equality) *)
    (* Therefore trace_cost T_opt <= trace_cost T *)
    rewrite optimal_trace_cost.
    apply trace_cost_lower_bound_internal.
    exact Hvalid.
Qed.

(**
   Theorem: Triangle inequality - distance satisfies metric property

   Proof Strategy (Wagner-Fischer 1974):

   Instead of complex induction on intermediate strings with nested min3 expressions,
   we use the trace abstraction and prove via trace composition.

   Key insights:
   1. Theorem 1: d(A, B) = min{cost(T) | T: A→B is valid}
   2. Lemma 1: cost(T₁ ∘ T₂) ≤ cost(T₁) + cost(T₂)

   From this, the triangle inequality follows immediately:
     d(A, C) = min{cost(T) | T: A→C}                    [by Theorem 1]
            ≤ cost(T₁ ∘ T₂)                              [for optimal T₁: A→B, T₂: B→C]
            ≤ cost(T₁) + cost(T₂)                        [by Lemma 1]
            = d(A, B) + d(B, C)                          [by Theorem 1]
*)
Theorem lev_distance_triangle_inequality :
  forall (s1 s2 s3 : list Char),
    lev_distance s1 s3 <= lev_distance s1 s2 + lev_distance s2 s3.
Proof.
  intros s1 s2 s3.

  (* By Theorem 1, there exist optimal traces T1: s1→s2 and T2: s2→s3 *)
  destruct (distance_equals_min_trace_cost s1 s2) as [T1 [H_valid1 [H_cost1 H_opt1]]].
  destruct (distance_equals_min_trace_cost s2 s3) as [T2 [H_valid2 [H_cost2 H_opt2]]].

  (* Compose the traces: T_comp = T1 ∘ T2 : s1→s3 *)
  set (T_comp := compose_trace T1 T2).

  (* By Theorem 1, there exists an optimal trace for s1→s3 *)
  destruct (distance_equals_min_trace_cost s1 s3) as [T_opt [H_valid_opt [H_cost_opt H_opt]]].

  (* Now we show: d(s1,s3) ≤ d(s1,s2) + d(s2,s3) *)
  rewrite <- H_cost_opt.           (* d(s1,s3) = cost(T_opt) *)
  rewrite <- H_cost1.              (* d(s1,s2) = cost(T1) *)
  rewrite <- H_cost2.              (* d(s2,s3) = cost(T2) *)

  (* Need to prove: cost(T_opt) ≤ cost(T1) + cost(T2) *)

  (* Prove that T_comp is valid using compose_trace_preserves_validity *)
  assert (H_comp_valid: is_valid_trace s1 s3 T_comp = true).
  {
    unfold T_comp.
    apply compose_trace_preserves_validity.
    - exact H_valid1.
    - exact H_valid2.
  }

  (* By optimality of T_opt, we have cost(T_opt) ≤ cost(T_comp) *)
  assert (H_bound: trace_cost s1 s3 T_opt <= trace_cost s1 s3 T_comp).
  {
    apply H_opt.
    exact H_comp_valid.
  }

  (* By Lemma 1, we have cost(T_comp) ≤ cost(T1) + cost(T2) *)
  assert (H_lemma1: trace_cost s1 s3 T_comp <= trace_cost s1 s2 T1 + trace_cost s2 s3 T2).
  {
    unfold T_comp.
    apply trace_composition_cost_bound.
    - exact H_valid1.
    - exact H_valid2.
  }

  (* Combining the bounds: cost(T_opt) ≤ cost(T_comp) ≤ cost(T1) + cost(T2) *)
  lia.
Qed.
