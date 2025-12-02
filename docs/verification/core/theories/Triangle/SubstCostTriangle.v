(** * Substitution Cost Triangle Inequality

    This module contains the subst_cost_triangle lemma which proves that
    the substitution cost satisfies the weak triangle inequality.

    Part of: Liblevenshtein.Core

    Decomposed from: Distance.v (lines 2530-2555)
*)

From Coq Require Import String List Arith Ascii Bool Nat Lia.
Import ListNotations.

From Liblevenshtein.Core Require Import Core.Definitions.
From Liblevenshtein.Core Require Import Core.MinLemmas.

(**
   Substitution cost satisfies weak triangle inequality.

   The cost of substituting a for c is at most the cost of substituting
   a for b plus the cost of substituting b for c.
*)
Lemma subst_cost_triangle :
  forall (a b c : Char),
    subst_cost a c <= subst_cost a b + subst_cost b c.
Proof.
  intros a b c.
  unfold subst_cost.
  destruct (char_eq a b) eqn:Eab;
  destruct (char_eq b c) eqn:Ebc;
  destruct (char_eq a c) eqn:Eac; simpl; try lia;
  (* Three impossible cases remain - all involve transitivity contradictions *)
  repeat match goal with
  | H1: char_eq ?x ?y = true, H2: char_eq ?y ?z = true |- _ =>
      apply char_eq_correct in H1; apply char_eq_correct in H2; subst
  end;
  match goal with
  | H: char_eq ?x ?x = false |- _ =>
      assert (Hrefl: char_eq x x = true) by (apply char_eq_correct; reflexivity);
      rewrite Hrefl in H; discriminate
  end.
Qed.
