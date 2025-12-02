(** * Matrix Operations for Wagner-Fischer Algorithm

    This module provides matrix initialization and update operations
    for the dynamic programming implementation of Levenshtein distance.

    Part of: Liblevenshtein.Core

    Decomposed from: Distance.v (lines 153-211)
*)

From Coq Require Import String List Arith Ascii Bool Nat Lia.
Import ListNotations.

From Liblevenshtein.Core Require Import Core.Definitions.

(** * Matrix Initialization *)

(** Initialize a row with given length, filled with default value *)
Fixpoint init_matrix_row (n : nat) (default : nat) : list nat :=
  match n with
  | 0 => []
  | S n' => default :: init_matrix_row n' default
  end.

(** Initialize matrix with given dimensions, filled with default value *)
Fixpoint init_matrix (rows cols : nat) (default : nat) : Matrix nat :=
  match rows with
  | 0 => []
  | S rows' => init_matrix_row cols default :: init_matrix rows' cols default
  end.

(** Initialize first row: matrix[0][j] = j (insertions from empty string) *)
Fixpoint init_first_row (n : nat) : list nat :=
  match n with
  | 0 => [0]
  | S n' => init_first_row n' ++ [S n']
  end.

(** Initialize first column: matrix[i][0] = i (deletions to empty string) *)
Fixpoint init_first_col_helper (matrix : Matrix nat) (i : nat) {struct matrix} : Matrix nat :=
  match matrix with
  | [] => []
  | row :: rest =>
      match row with
      | [] => row :: init_first_col_helper rest (S i)  (* Preserve empty rows *)
      | _ :: row_tail => (i :: row_tail) :: init_first_col_helper rest (S i)
      end
  end.

Definition init_first_col (matrix : Matrix nat) : Matrix nat :=
  init_first_col_helper matrix 0.

(** * Matrix Update Operations *)

(** Update a single row at position j *)
Fixpoint update_row (row : list nat) (j : nat) (value : nat) : list nat :=
  match row, j with
  | [], _ => []
  | x :: xs, 0 => value :: xs
  | x :: xs, S j' => x :: update_row xs j' value
  end.

(** Update matrix cell at position (i, j) *)
Fixpoint update_matrix (matrix : Matrix nat) (i j : nat) (value : nat) : Matrix nat :=
  match matrix, i with
  | [], _ => []
  | row :: rest, 0 => update_row row j value :: rest
  | row :: rest, S i' => row :: update_matrix rest i' j value
  end.

(** * Matrix Properties *)

(** Length of initialized row *)
Lemma init_matrix_row_length :
  forall n default,
    length (init_matrix_row n default) = n.
Proof.
  induction n as [| n' IH]; intros default.
  - reflexivity.
  - simpl. f_equal. apply IH.
Qed.

(** Number of rows in initialized matrix *)
Lemma init_matrix_rows :
  forall rows cols default,
    length (init_matrix rows cols default) = rows.
Proof.
  induction rows as [| rows' IH]; intros cols default.
  - reflexivity.
  - simpl. f_equal. apply IH.
Qed.

(** Length of first row after initialization *)
Lemma init_first_row_length :
  forall n,
    length (init_first_row n) = S n.
Proof.
  induction n as [| n' IH].
  - reflexivity.
  - simpl. rewrite length_app. simpl. rewrite IH. lia.
Qed.

(** Access to initialized first row *)
Lemma init_first_row_nth :
  forall n k,
    k <= n ->
    nth k (init_first_row n) 0 = k.
Proof.
  induction n as [| n' IH]; intros k Hk.
  - (* n = 0 *)
    assert (k = 0) by lia. subst. reflexivity.
  - (* n = S n' *)
    destruct (Nat.eq_dec k (S n')) as [Heq | Hneq].
    + (* k = S n' *)
      subst k. simpl.
      rewrite app_nth2.
      * rewrite init_first_row_length. replace (S n' - S n') with 0 by lia.
        reflexivity.
      * rewrite init_first_row_length. lia.
    + (* k < S n' *)
      assert (Hk': k <= n') by lia.
      simpl. rewrite app_nth1.
      * apply IH. exact Hk'.
      * rewrite init_first_row_length. lia.
Qed.

(** update_row preserves length *)
Lemma update_row_length :
  forall row j value,
    length (update_row row j value) = length row.
Proof.
  induction row as [| x xs IH]; intros j value.
  - reflexivity.
  - destruct j as [| j'].
    + reflexivity.
    + simpl. f_equal. apply IH.
Qed.

(** update_matrix preserves dimensions *)
Lemma update_matrix_length :
  forall matrix i j value,
    length (update_matrix matrix i j value) = length matrix.
Proof.
  induction matrix as [| row rest IH]; intros i j value.
  - reflexivity.
  - destruct i as [| i'].
    + reflexivity.
    + simpl. f_equal. apply IH.
Qed.

(** Additional properties can be proven as needed.
    The core operations above are sufficient for the DP correctness theorem. *)

(** Accessing updated cell returns new value - commented out pending Rocq compatibility fixes

Lemma get_cell_update_same :
  forall matrix i j value,
    i < length matrix ->
    j < length (nth i matrix []) ->
    get_cell (update_matrix matrix i j value) i j = value.

Lemma get_cell_update_other :
  forall matrix i j i' j' value,
    (i <> i' \/ j <> j') ->
    get_cell (update_matrix matrix i j value) i' j' = get_cell matrix i' j'.
*)
