(** * Helper Lemmas for min3 and Character Operations

    This module contains key lemmas about min3, character equality,
    and substitution cost used throughout the Levenshtein proofs.

    Part of: Liblevenshtein.Core

    Decomposed from: Distance.v (lines 212-301)
*)

From Coq Require Import String List Arith Ascii Bool Nat Lia.
Import ListNotations.

From Liblevenshtein.Core Require Import Core.Definitions.

(** * min3 Lemmas *)

(** Lemma: min3 returns a value less than or equal to all inputs *)
Lemma min3_lower_bound :
  forall a b c : nat,
    min3 a b c <= a /\ min3 a b c <= b /\ min3 a b c <= c.
Proof.
  intros a b c.
  unfold min3.
  split.
  - apply Nat.le_min_l.
  - split.
    + transitivity (min b c).
      * apply Nat.le_min_r.
      * apply Nat.le_min_l.
    + transitivity (min b c).
      * apply Nat.le_min_r.
      * apply Nat.le_min_r.
Qed.

(** Lemma: min3 is commutative in its first two arguments *)
Lemma min3_comm_12 :
  forall a b c : nat,
    min3 a b c = min3 b a c.
Proof.
  intros a b c.
  unfold min3.
  rewrite Nat.min_assoc.
  rewrite (Nat.min_comm a b).
  rewrite <- Nat.min_assoc.
  reflexivity.
Qed.

(** * Character Equality Lemmas *)

(** Lemma: Character equality is decidable *)
Lemma char_eq_decidable :
  forall (c1 c2 : Char), {c1 = c2} + {c1 <> c2}.
Proof.
  intros c1 c2.
  apply ascii_dec.
Qed.

(** Lemma: char_eq correctly tests equality *)
Lemma char_eq_correct :
  forall (c1 c2 : Char),
    char_eq c1 c2 = true <-> c1 = c2.
Proof.
  intros c1 c2.
  unfold char_eq.
  destruct (ascii_dec c1 c2) as [H_eq | H_neq].
  - split; intros.
    + exact H_eq.
    + reflexivity.
  - split; intros H_contra.
    + discriminate H_contra.
    + contradiction.
Qed.

(** * Substitution Cost Lemmas *)

(** Lemma: subst_cost is 0 for identical characters *)
Lemma subst_cost_eq :
  forall (c : Char),
    subst_cost c c = 0.
Proof.
  intros c.
  unfold subst_cost.
  destruct (char_eq c c) eqn:E.
  - reflexivity.
  - assert (H: c = c) by reflexivity.
    apply char_eq_correct in H.
    rewrite H in E.
    discriminate E.
Qed.

(** Lemma: subst_cost is 1 for different characters *)
Lemma subst_cost_neq :
  forall (c1 c2 : Char),
    c1 <> c2 ->
    subst_cost c1 c2 = 1.
Proof.
  intros c1 c2 H_neq.
  unfold subst_cost.
  destruct (char_eq c1 c2) eqn:E.
  - apply char_eq_correct in E.
    contradiction.
  - reflexivity.
Qed.

(** Lemma: subst_cost is bounded by 1 *)
Lemma subst_cost_bound :
  forall (c1 c2 : Char),
    subst_cost c1 c2 <= 1.
Proof.
  intros c1 c2.
  unfold subst_cost.
  destruct (char_eq c1 c2); lia.
Qed.
