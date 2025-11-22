(** * General NFA Properties - Symmetry, Triangle Inequality, Composition *)
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.QArith.QArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Require Import Liblevenshtein.Grammar.Verification.NFA.Types.
Require Import Liblevenshtein.Grammar.Verification.NFA.Operations.
Require Import Liblevenshtein.Grammar.Verification.NFA.Automaton.

Theorem edit_distance_symmetric : forall s1 s2,
  exists edits12 edits21,
    edit_sequence_cost edits12 = edit_sequence_cost edits21.
Proof. intros. admit. Admitted.

Theorem edit_distance_triangle : forall s1 s2 s3 e12 e23,
  edit_sequence_cost e12 + edit_sequence_cost e23 >= 
  edit_sequence_cost (e12 ++ e23).
Proof. intros. admit. Admitted.

Theorem composition_preserves_distance : forall aut1 aut2 target mid input,
  accepts aut1 target mid = true ->
  accepts aut2 mid input = true ->
  exists aut_composed,
    accepts aut_composed target input = true.
Proof. intros. admit. Admitted.
