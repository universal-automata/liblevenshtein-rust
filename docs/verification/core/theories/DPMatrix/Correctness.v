(** * DP Matrix Correctness

    This module proves the correctness of the Wagner-Fischer dynamic programming
    algorithm for computing Levenshtein distance.

    The main theorem states: IF a matrix is filled according to the Wagner-Fischer
    recurrence relation, THEN the value at position (i,j) equals the recursive
    Levenshtein distance between the first i and j characters of the input strings.

    Part of: Liblevenshtein.Core

    Decomposed from: Distance.v (lines 8336-8514)
*)

From Coq Require Import String List Arith Ascii Bool Nat Lia Wf_nat.
Import ListNotations.

From Liblevenshtein.Core Require Import Core.Definitions.
From Liblevenshtein.Core Require Import Core.LevDistance.
From Liblevenshtein.Core Require Import DPMatrix.SnocLemmas.

(** * Main Correctness Theorem *)

(** This theorem states that IF a matrix is filled according to the
    Wagner-Fischer recurrence relation, THEN the value at position (i,j)
    equals the recursive Levenshtein distance between the first i and j
    characters of the input strings.

    The proof uses strong induction on i + j with the key insight that
    the snoc lemmas connect the DP recurrence to the recursive definition. *)
Theorem dp_matrix_correctness :
  forall (s1 s2 : list Char) (m : Matrix nat) (i j : nat),
    (* Preconditions: matrix properly initialized and filled *)
    i <= length s1 ->
    j <= length s2 ->
    (* If matrix follows Wagner-Fischer recurrence... *)
    (forall i' j',
      i' > 0 -> j' > 0 -> i' <= i -> j' <= j ->
      get_cell m i' j' = min3
        (get_cell m (i'-1) j' + 1)
        (get_cell m i' (j'-1) + 1)
        (get_cell m (i'-1) (j'-1) + subst_cost (nth (i'-1) s1 " "%char) (nth (j'-1) s2 " "%char))) ->
    (* Base cases *)
    (forall k, k <= i -> get_cell m k 0 = k) ->
    (forall k, k <= j -> get_cell m 0 k = k) ->
    (* Then matrix cell equals recursive distance *)
    get_cell m i j = lev_distance (firstn i s1) (firstn j s2).
Proof.
  intros s1 s2 m i j Hi Hj H_recurrence H_base_row H_base_col.

  (* Strong induction on i + j: prove for all i', j' with i' <= i, j' <= j *)
  assert (H_wf: forall n i' j',
    i' + j' = n ->
    i' <= i -> j' <= j ->
    get_cell m i' j' = lev_distance (firstn i' s1) (firstn j' s2)).
  {
    intro n.
    induction n as [n IH] using lt_wf_ind.
    intros i' j' Hsum Hi' Hj'.

    (* Case analysis on i' and j' *)
    destruct i' as [| i''].

    - (* Base case: i' = 0 *)
      rewrite H_base_col; [| lia].
      (* Goal: j' = lev_distance (firstn 0 s1) (firstn j' s2) *)
      (* firstn 0 s1 = [] *)
      replace (firstn 0 s1) with (@nil Char) by reflexivity.
      rewrite lev_distance_empty_left.
      (* Goal: j' = length (firstn j' s2) *)
      symmetry. apply firstn_length_le. lia.

    - destruct j' as [| j''].

      + (* Base case: j' = 0, i' = S i'' *)
        rewrite H_base_row; [| lia].
        (* Goal: S i'' = lev_distance (firstn (S i'') s1) (firstn 0 s2) *)
        replace (firstn 0 s2) with (@nil Char) by reflexivity.
        rewrite lev_distance_empty_right.
        (* Goal: S i'' = length (firstn (S i'') s1) *)
        symmetry. apply firstn_length_le. lia.

      + (* Inductive case: i' = S i'', j' = S j'' *)
        (* Use recurrence relation for the matrix *)
        rewrite H_recurrence; [| lia | lia | lia | lia].

        (* Replace S i'' - 1 with i'' and S j'' - 1 with j'' *)
        replace (S i'' - 1) with i'' by lia.
        replace (S j'' - 1) with j'' by lia.

        (* Apply IH to convert get_cell to lev_distance FIRST *)
        assert (H_del: get_cell m i'' (S j'') = lev_distance (firstn i'' s1) (firstn (S j'') s2)).
        { apply (IH (i'' + S j'')); [lia | reflexivity | lia | lia]. }

        assert (H_ins: get_cell m (S i'') j'' = lev_distance (firstn (S i'') s1) (firstn j'' s2)).
        { apply (IH (S i'' + j'')); [lia | reflexivity | lia | lia]. }

        assert (H_sub: get_cell m i'' j'' = lev_distance (firstn i'' s1) (firstn j'' s2)).
        { apply (IH (i'' + j'')); [lia | reflexivity | lia | lia]. }

        (* Rewrite get_cell terms in the goal *)
        rewrite H_del, H_ins, H_sub.

        (* Now the goal is:
           min3 (lev_distance (firstn i'' s1) (firstn (S j'') s2) + 1)
                (lev_distance (firstn (S i'') s1) (firstn j'' s2) + 1)
                (lev_distance (firstn i'' s1) (firstn j'' s2) + subst_cost (nth i'' s1 " ") (nth j'' s2 " "))
           = lev_distance (firstn (S i'') s1) (firstn (S j'') s2) *)

        (* Use suffix decomposition: firstn (S n) l = firstn n l ++ [nth n l d] *)
        assert (H_s1_decomp: firstn (S i'') s1 = firstn i'' s1 ++ [nth i'' s1 default_char]).
        { apply firstn_S_snoc. lia. }

        assert (H_s2_decomp: firstn (S j'') s2 = firstn j'' s2 ++ [nth j'' s2 default_char]).
        { apply firstn_S_snoc. lia. }

        set (c1 := nth i'' s1 default_char).
        set (c2 := nth j'' s2 default_char).

        (* Rewrite firstn (S n) to snoc form throughout the goal *)
        rewrite H_s1_decomp, H_s2_decomp.

        (* Now use lev_distance_snoc to simplify the RHS *)
        rewrite lev_distance_snoc.

        (* The goal is now:
           min3 (lev_distance (firstn i'' s1) (firstn j'' s2 ++ [c2]) + 1)
                (lev_distance (firstn i'' s1 ++ [c1]) (firstn j'' s2) + 1)
                (lev_distance (firstn i'' s1) (firstn j'' s2) + subst_cost (nth i'' s1 " ") (nth j'' s2 " "))
           = min3 (lev_distance (firstn i'' s1) (firstn j'' s2 ++ [c2]) + 1)
                  (lev_distance (firstn i'' s1 ++ [c1]) (firstn j'' s2) + 1)
                  (lev_distance (firstn i'' s1) (firstn j'' s2) + subst_cost c1 c2) *)

        (* We need: subst_cost (nth i'' s1 " ") (nth j'' s2 " ") = subst_cost c1 c2 *)
        assert (H_subst_eq: subst_cost (nth i'' s1 " "%char) (nth j'' s2 " "%char) = subst_cost c1 c2).
        {
          unfold c1, c2.
          assert (H_i_bound: i'' < length s1) by lia.
          assert (H_j_bound: j'' < length s2) by lia.
          rewrite (nth_indep s1 default_char " "%char H_i_bound).
          rewrite (nth_indep s2 default_char " "%char H_j_bound).
          reflexivity.
        }

        rewrite H_subst_eq.
        reflexivity.
  }

  (* Apply H_wf with n = i + j *)
  apply (H_wf (i + j) i j); [reflexivity | lia | lia].
Qed.

(** * Corollary: Full Algorithm Correctness *)

(** When the matrix is fully computed for strings s1 and s2, the bottom-right
    cell contains the correct Levenshtein distance. *)
Corollary levenshtein_distance_correctness :
  forall (s1 s2 : list Char) (m : Matrix nat),
    (* If matrix is properly filled... *)
    (forall i j,
      i > 0 -> j > 0 -> i <= length s1 -> j <= length s2 ->
      get_cell m i j = min3
        (get_cell m (i-1) j + 1)
        (get_cell m i (j-1) + 1)
        (get_cell m (i-1) (j-1) + subst_cost (nth (i-1) s1 " "%char) (nth (j-1) s2 " "%char))) ->
    (forall k, k <= length s1 -> get_cell m k 0 = k) ->
    (forall k, k <= length s2 -> get_cell m 0 k = k) ->
    (* Then the final cell equals the recursive distance *)
    get_cell m (length s1) (length s2) = lev_distance s1 s2.
Proof.
  intros s1 s2 m H_recurrence H_row0 H_col0.

  (* Apply dp_matrix_correctness with i = length s1, j = length s2 *)
  assert (H_correct := dp_matrix_correctness s1 s2 m (length s1) (length s2)).

  (* Simplify H_correct using firstn_all *)
  rewrite !firstn_all in H_correct.

  apply H_correct.
  - lia.
  - lia.
  - intros i' j' H_i'_pos H_j'_pos H_i'_le H_j'_le.
    apply H_recurrence; lia.
  - exact H_row0.
  - exact H_col0.
Qed.
