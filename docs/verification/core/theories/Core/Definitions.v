(** * Core Definitions for Levenshtein Distance

    This module contains the foundational type definitions and helper functions
    used throughout the Levenshtein distance verification.

    Part of: Liblevenshtein.Core

    Decomposed from: Distance.v (lines 1-61)
*)

From Coq Require Import String List Arith Ascii Bool Nat Lia.
Import ListNotations.

(** * Type Definitions *)

(** Characters are represented as Coq's ascii type, corresponding to
    Rust's char (Unicode scalar values). *)
Definition Char := ascii.

(** Default character for out-of-bounds access (ASCII NUL) *)
Definition default_char : Char := Ascii.zero.

(** Dynamic programming matrix: nested list representing 2D array *)
Definition Matrix (A : Type) := list (list A).

(** * Helper Functions *)

(** Minimum of three natural numbers *)
Definition min3 (a b c : nat) : nat :=
  min a (min b c).

(** Absolute difference between two natural numbers *)
Definition abs_diff (a b : nat) : nat :=
  if a <=? b then b - a else a - b.

(** Character equality (decidable) *)
Definition char_eq (c1 c2 : Char) : bool :=
  if ascii_dec c1 c2 then true else false.

(** Substitution cost: 0 if characters match, 1 otherwise *)
Definition subst_cost (c1 c2 : Char) : nat :=
  if char_eq c1 c2 then 0 else 1.

(** Safe matrix access with default value *)
Fixpoint nth_row (m : Matrix nat) (i : nat) (default_row : list nat) : list nat :=
  nth i m default_row.

Definition get_cell (m : Matrix nat) (i j : nat) : nat :=
  nth j (nth_row m i []) 0.
