(** * Trace Cost Calculation

    This module defines the cost of a trace according to the Wagner-Fischer
    definition: sum of change costs plus deletion costs plus insertion costs.

    Part of: Liblevenshtein.Core

    Decomposed from: Distance.v (lines 1173-1187)
*)

From Coq Require Import String List Arith Ascii Bool Nat Lia.
Import ListNotations.

From Liblevenshtein.Core Require Import Core.Definitions.
From Liblevenshtein.Core Require Import Core.LevDistance.
From Liblevenshtein.Core Require Import Trace.TraceBasics.
From Liblevenshtein.Core Require Import Trace.TouchedPositions.

(** * Trace Cost Definition *)

(** Cost of a trace according to Wagner-Fischer definition *)
Definition trace_cost (A B : list Char) (T : Trace A B) : nat :=
  (* Cost of change operations for matched pairs *)
  let change_cost := fold_left (fun acc p =>
    let '(i, j) := p in
    acc + subst_cost (nth (i-1) A default_char) (nth (j-1) B default_char)
  ) T 0 in

  (* Cost of deletions (positions in A not touched) *)
  let delete_cost := length A - length (touched_in_A A B T) in

  (* Cost of insertions (positions in B not touched) *)
  let insert_cost := length B - length (touched_in_B A B T) in

  change_cost + delete_cost + insert_cost.

(** * Basic Lemmas *)

(** Trace cost for empty trace *)
Lemma trace_cost_empty :
  forall (A B : list Char),
    trace_cost A B [] = length A + length B.
Proof.
  intros A B.
  unfold trace_cost.
  simpl. lia.
Qed.

(** Substitution cost is bounded by 1 *)
Lemma subst_cost_bound :
  forall (c1 c2 : Char),
    subst_cost c1 c2 <= 1.
Proof.
  intros c1 c2.
  unfold subst_cost.
  destruct (char_eq c1 c2); lia.
Qed.

(** Change cost accumulator is non-decreasing *)
Lemma fold_left_change_cost_ge :
  forall (A B : list Char) (T : Trace A B) acc,
    fold_left (fun acc' p =>
      let '(i, j) := p in
      acc' + subst_cost (nth (i-1) A default_char) (nth (j-1) B default_char)
    ) T acc >= acc.
Proof.
  intros A B T.
  induction T as [| [i j] rest IH].
  - simpl. lia.
  - simpl. intro acc.
    specialize (IH (acc + subst_cost (nth (i - 1) A default_char) (nth (j - 1) B default_char))).
    lia.
Qed.
