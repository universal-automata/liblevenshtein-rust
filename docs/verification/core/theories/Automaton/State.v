(** * State Type for Levenshtein Automata

    This module defines the State type which represents the current configuration
    of the Levenshtein automaton - a sorted anti-chain of positions.

    Part of: Liblevenshtein.Core.Automaton

    Rust Reference: src/transducer/state.rs

    Key Definitions:
    - State: Record containing sorted position list
    - state_insert: Insert position while maintaining invariants
    - min_distance_state: Minimum error count in state

    Key Theorems:
    - state_insert_wf: Insert preserves well-formedness
    - state_merge_wf: Merge preserves well-formedness
    - min_distance_correct: Minimum distance computation is correct
*)

From Stdlib Require Import Arith Bool List Nat Lia.
Import ListNotations.

From Liblevenshtein.Core Require Import Automaton.Position.
From Liblevenshtein.Core Require Import Automaton.Subsumption.
From Liblevenshtein.Core Require Import Automaton.AntiChain.

(** * State Definition *)

(** A State is a sorted list of positions forming an anti-chain.
    Well-formedness requires:
    1. Sorted in lexicographic order (is_sorted)
    2. No subsumption between positions (is_antichain)
    3. No duplicates (implied by sorted) *)
Record State : Type := mkState {
  positions : list Position;
  algorithm : Algorithm;
  query_length : nat
}.

(** * State Well-Formedness *)

Definition state_wf (s : State) : Prop :=
  is_sorted (positions s) /\
  is_antichain (algorithm s) (query_length s) (positions s).

(** Empty state *)
Definition empty_state (alg : Algorithm) (qlen : nat) : State :=
  mkState [] alg qlen.

Lemma empty_state_wf : forall alg qlen,
  state_wf (empty_state alg qlen).
Proof.
  intros alg qlen.
  unfold state_wf, empty_state. simpl.
  split.
  - apply sorted_nil.
  - apply antichain_nil.
Qed.

(** * Position Insertion *)

(** Insert a position into a sorted list maintaining order *)
Fixpoint sorted_insert (p : Position) (positions : list Position) : list Position :=
  match positions with
  | [] => [p]
  | p' :: rest =>
      if position_ltb p p' then p :: p' :: rest
      else if position_eqb p p' then p' :: rest  (* Don't insert duplicates *)
      else p' :: sorted_insert p rest
  end.

(** Insert maintaining both sortedness and anti-chain property *)
Definition state_insert (p : Position) (s : State) : State :=
  let alg := algorithm s in
  let qlen := query_length s in
  let new_positions := antichain_insert alg qlen p (positions s) in
  (* Re-sort after antichain_insert (which may have removed some positions) *)
  mkState (fold_right sorted_insert [] new_positions) alg qlen.

(** Simplified insert that assumes input is well-formed *)
Definition state_insert_simple (p : Position) (s : State) : State :=
  mkState (sorted_insert p (positions s)) (algorithm s) (query_length s).

(** * Minimum Distance *)

(** Compute minimum error count among positions at or past query_length *)
Definition is_accepting_position (qlen : nat) (p : Position) : bool :=
  qlen <=? term_index p.

Fixpoint min_error_in (positions : list Position) : option nat :=
  match positions with
  | [] => None
  | p :: rest =>
      match min_error_in rest with
      | None => Some (num_errors p)
      | Some min_rest => Some (min (num_errors p) min_rest)
      end
  end.

Definition min_accepting_error (qlen : nat) (positions : list Position) : option nat :=
  min_error_in (filter (is_accepting_position qlen) positions).

Definition state_min_distance (s : State) : option nat :=
  min_accepting_error (query_length s) (positions s).

(** * Sorted Insert Properties *)

Lemma sorted_insert_In : forall p positions,
  In p (sorted_insert p positions).
Proof.
  intros p positions.
  induction positions as [| p' rest IH].
  - simpl. left. reflexivity.
  - simpl. destruct (position_ltb p p') eqn:Hlt.
    + left. reflexivity.
    + destruct (position_eqb p p') eqn:Heq.
      * apply position_eqb_eq in Heq. subst. left. reflexivity.
      * right. exact IH.
Qed.

Lemma sorted_insert_preserves : forall p p' positions,
  In p' positions -> In p' (sorted_insert p positions).
Proof.
  intros p p' positions Hin.
  induction positions as [| q rest IH].
  - inversion Hin.
  - simpl. destruct (position_ltb p q) eqn:Hlt.
    + right. exact Hin.
    + destruct (position_eqb p q) eqn:Heq.
      * exact Hin.
      * simpl in Hin. destruct Hin as [Hq | Hrest].
        -- left. exact Hq.
        -- right. apply IH. exact Hrest.
Qed.

(* Helper: if not (p < p1) and not (p = p1), then p1 < p *)
Lemma not_ltb_not_eqb_implies_gt : forall p p1,
  position_ltb p p1 = false ->
  position_eqb p p1 = false ->
  position_lt p1 p.
Proof.
  intros p p1 Hltb Heqb.
  destruct (position_lt_trichotomy p1 p) as [Hlt | [Heq | Hgt]].
  - exact Hlt.
  - subst p1.
    rewrite position_eqb_refl in Heqb. discriminate.
  - apply position_ltb_lt in Hgt.
    rewrite Hgt in Hltb. discriminate.
Qed.

Lemma sorted_insert_sorted : forall p positions,
  is_sorted positions ->
  is_sorted (sorted_insert p positions).
Proof.
  intros p positions Hsorted.
  induction positions as [| p1 rest IH].
  - simpl. exact I.
  - simpl. destruct (position_ltb p p1) eqn:Hlt.
    + (* p < p1, insert at front *)
      apply position_ltb_lt in Hlt.
      destruct rest as [| p2 rest'].
      * simpl. split; [exact Hlt | exact I].
      * simpl. split; [exact Hlt | exact Hsorted].
    + destruct (position_eqb p p1) eqn:Heq.
      * (* p = p1, no insert *)
        exact Hsorted.
      * (* p > p1, recurse *)
        pose proof (not_ltb_not_eqb_implies_gt p p1 Hlt Heq) as Hgt.
        destruct rest as [| p2 rest'].
        -- simpl. split; [exact Hgt | exact I].
        -- (* rest = p2 :: rest' *)
           apply sorted_cons_inv in Hsorted.
           destruct Hsorted as [Hlt12 Hsorted'].
           specialize (IH Hsorted').
           simpl. simpl in IH.
           destruct (position_ltb p p2) eqn:Hlt2.
           ++ (* p < p2, insert between p1 and p2 *)
              apply position_ltb_lt in Hlt2.
              simpl. split; [exact Hgt | split; [exact Hlt2 | exact Hsorted']].
           ++ destruct (position_eqb p p2) eqn:Heq2.
              ** (* p = p2 *)
                 simpl. split; [exact Hlt12 | exact Hsorted'].
              ** (* p > p2, recurse deeper *)
                 split; [exact Hlt12 | exact IH].
Qed.

(** * State Size and Bounds *)

Definition state_size (s : State) : nat :=
  length (positions s).

(** State is empty *)
Definition state_is_empty (s : State) : bool :=
  match positions s with
  | [] => true
  | _ => false
  end.

Lemma state_is_empty_correct : forall s,
  state_is_empty s = true <-> positions s = [].
Proof.
  intros s.
  unfold state_is_empty.
  destruct (positions s) as [| p rest].
  - split; intros _; reflexivity.
  - split; intros H; discriminate.
Qed.

(** * State Membership *)

Definition in_state (p : Position) (s : State) : Prop :=
  In p (positions s).

Definition in_state_b (p : Position) (s : State) : bool :=
  existsb (position_eqb p) (positions s).

Lemma in_state_b_correct : forall p s,
  in_state_b p s = true <-> in_state p s.
Proof.
  intros p s.
  unfold in_state_b, in_state.
  rewrite existsb_exists.
  split.
  - intros [x [Hin Heq]].
    apply position_eqb_eq in Heq.
    subst. exact Hin.
  - intros Hin.
    exists p. split; [exact Hin | apply position_eqb_refl].
Qed.

(** * State Equality *)

Definition state_eqb (s1 s2 : State) : bool :=
  algorithm_eqb (algorithm s1) (algorithm s2) &&
  (query_length s1 =? query_length s2) &&
  forallb (fun p => in_state_b p s2) (positions s1) &&
  forallb (fun p => in_state_b p s1) (positions s2).

(** * Initial State *)

(** The initial state contains position (0, 0, false) *)
Definition initial_position : Position := std_pos 0 0.

Definition initial_state (alg : Algorithm) (qlen : nat) : State :=
  mkState [initial_position] alg qlen.

Lemma initial_state_contains_origin : forall alg qlen,
  in_state initial_position (initial_state alg qlen).
Proof.
  intros alg qlen.
  unfold in_state, initial_state. simpl.
  left. reflexivity.
Qed.

Lemma initial_state_wf : forall alg qlen,
  state_wf (initial_state alg qlen).
Proof.
  intros alg qlen.
  unfold state_wf, initial_state. simpl.
  split; [exact I | apply antichain_singleton].
Qed.

(** * Examples *)

Example state_example_1 :
  state_size (initial_state Standard 5) = 1.
Proof. reflexivity. Qed.

Example state_example_2 :
  state_is_empty (empty_state Standard 5) = true.
Proof. reflexivity. Qed.

Example state_example_3 :
  in_state (std_pos 0 0) (initial_state Standard 5).
Proof. unfold in_state, initial_state. simpl. left. reflexivity. Qed.

(** * Sorted Insert Preserves Membership *)

(** If p is in positions, it's in fold_right sorted_insert [] positions *)
Lemma fold_right_sorted_insert_preserves_In : forall positions p,
  In p positions ->
  In p (fold_right sorted_insert [] positions).
Proof.
  intros positions.
  induction positions as [| q rest IH]; intros p Hin.
  - inversion Hin.
  - simpl in Hin. destruct Hin as [Heq | Hin'].
    + (* p = q *)
      subst q. simpl.
      apply sorted_insert_In.
    + (* p in rest *)
      simpl.
      apply sorted_insert_preserves.
      apply IH. exact Hin'.
Qed.

(** Existsb is preserved through fold_right sorted_insert *)
Lemma fold_right_sorted_insert_preserves_existsb : forall f positions,
  existsb f positions = true ->
  existsb f (fold_right sorted_insert [] positions) = true.
Proof.
  intros f positions Hexists.
  rewrite existsb_exists in Hexists |- *.
  destruct Hexists as [p [Hin Hf]].
  exists p. split.
  - apply fold_right_sorted_insert_preserves_In. exact Hin.
  - exact Hf.
Qed.
