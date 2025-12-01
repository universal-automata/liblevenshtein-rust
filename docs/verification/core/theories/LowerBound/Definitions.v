(** * Lower Bound Definitions

    This module provides the foundational definitions for the trace lower bound proof.
    It imports shared definitions from Core modules and adds unique lemmas.

    Part of: Liblevenshtein.Core

    Decomposed from: TraceLowerBound.v (lines 45-103)
    NOTE: Duplicates at lines 10-29 are replaced by imports from Core modules.
*)

From Stdlib Require Import String List Arith Ascii Bool Nat Lia.
Import ListNotations.

(** Import shared definitions instead of duplicating *)
From Liblevenshtein.Core Require Import Core.Definitions.
From Liblevenshtein.Core Require Import Core.LevDistance.
From Liblevenshtein.Core Require Import Core.MinLemmas.

(** * Unique Lemmas (not in Distance.v) *)

Lemma lev_distance_nil_nil : lev_distance [] [] = 0.
Proof. unfold lev_distance. rewrite lev_distance_pair_equation. reflexivity. Qed.

Lemma lev_distance_nil_l : forall s, lev_distance [] s = length s.
Proof. intro s. unfold lev_distance. rewrite lev_distance_pair_equation. reflexivity. Qed.

Lemma lev_distance_nil_r : forall s, lev_distance s [] = length s.
Proof. intro s. unfold lev_distance. rewrite lev_distance_pair_equation. destruct s; reflexivity. Qed.

Lemma lev_distance_cons_cons : forall c1 c2 s1 s2,
  lev_distance (c1 :: s1) (c2 :: s2) =
  min3 (lev_distance s1 (c2 :: s2) + 1) (lev_distance (c1 :: s1) s2 + 1) (lev_distance s1 s2 + subst_cost c1 c2).
Proof. intros. unfold lev_distance. rewrite lev_distance_pair_equation. reflexivity. Qed.

(** * Trace Definitions (Simplified) *)

(** Simplified trace type for lower bound proof *)
Definition Trace := list (nat * nat).

(** Extract positions touched in A *)
Fixpoint touched_in_A (T : Trace) : list nat :=
  match T with [] => [] | (i, _) :: rest => i :: touched_in_A rest end.

(** Extract positions touched in B *)
Fixpoint touched_in_B (T : Trace) : list nat :=
  match T with [] => [] | (_, j) :: rest => j :: touched_in_B rest end.

(** * Trace Cost Definition *)

Definition trace_cost (lenA lenB : nat) (A B : list Char) (T : Trace) : nat :=
  let change_cost := fold_left (fun acc p =>
    let '(i, j) := p in acc + subst_cost (nth (i-1) A default_char) (nth (j-1) B default_char)) T 0 in
  change_cost + (lenA - length (touched_in_A T)) + (lenB - length (touched_in_B T)).

(** * Basic Lemmas *)

Lemma touched_in_A_length : forall T, length (touched_in_A T) = length T.
Proof. induction T as [| [i j] rest IH]; simpl; [reflexivity | rewrite IH; reflexivity]. Qed.

Lemma touched_in_B_length : forall T, length (touched_in_B T) = length T.
Proof. induction T as [| [i j] rest IH]; simpl; [reflexivity | rewrite IH; reflexivity]. Qed.

(** * Validity and Monotonicity *)

Definition simple_valid_trace (lenA lenB : nat) (T : Trace) : bool :=
  forallb (fun '(i, j) => (1 <=? i) && (i <=? lenA) && (1 <=? j) && (j <=? lenB)) T.

Definition trace_monotonic (T : Trace) : Prop :=
  forall i1 j1 i2 j2,
    In (i1, j1) T -> In (i2, j2) T -> i1 < i2 -> j1 < j2.

(** * Trace Cost Formulas *)

Lemma trace_cost_formula : forall lenA lenB A B T,
  length T <= lenA ->
  length T <= lenB ->
  trace_cost lenA lenB A B T =
  fold_left (fun acc '(i, j) =>
    acc + subst_cost (nth (i-1) A default_char) (nth (j-1) B default_char)) T 0 +
  (lenA - length T) + (lenB - length T).
Proof.
  intros.
  unfold trace_cost.
  rewrite touched_in_A_length, touched_in_B_length.
  reflexivity.
Qed.

Lemma trace_cost_nil : forall lenA lenB A B,
  trace_cost lenA lenB A B [] = lenA + lenB.
Proof.
  intros. unfold trace_cost. simpl. lia.
Qed.

(** * Upper Bound *)

Lemma lev_distance_upper_bound : forall A B,
  lev_distance A B <= length A + length B.
Proof.
  intros A.
  induction A as [| c1 s1' IHA].
  - intro B. rewrite lev_distance_nil_l. simpl. lia.
  - intro B. induction B as [| c2 s2' IHB].
    + rewrite lev_distance_nil_r. simpl. lia.
    + rewrite lev_distance_cons_cons.
      unfold min3.
      assert (H3: lev_distance s1' s2' <= length s1' + length s2') by (apply IHA).
      assert (Hsub: subst_cost c1 c2 <= 1).
      { unfold subst_cost, char_eq. destruct ascii_dec; lia. }
      eapply Nat.le_trans. apply Nat.le_min_r.
      simpl length.
      assert (S (length s1') + S (length s2') = S (S (length s1' + length s2'))) by lia.
      rewrite H. clear H.
      assert (lev_distance s1' s2' + subst_cost c1 c2 <= length s1' + length s2' + 1) by lia.
      lia.
Qed.
