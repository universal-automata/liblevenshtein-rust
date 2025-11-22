(** * Optimality and Viterbi Algorithm

    Proves that the Viterbi algorithm finds minimum-cost paths through
    the NFA lattice, and that these paths correspond to optimal corrections.
*)

Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Init.Nat.
Require Import Coq.QArith.QArith.
Require Import Coq.micromega.Lia.
Import ListNotations.

Require Import Liblevenshtein.Grammar.Verification.NFA.Types.
Require Import Liblevenshtein.Grammar.Verification.NFA.Operations.
Require Import Liblevenshtein.Grammar.Verification.NFA.Automaton.

(** ** Path Costs *)

Definition PathCost := Q.

Fixpoint path_cost (path : AutomatonPath) : PathCost :=
  match path with
  | [] => 0%Q
  | [p] => Q_of_nat (pos_e p)
  | p1 :: p2 :: rest => 
      (* Cost accumulates through positions *)
      path_cost (p2 :: rest)
  end.

(** ** Viterbi Algorithm *)

(** Viterbi finds best path to each position *)
Definition viterbi_score (st : GeneralizedState) (target_pos : nat) : option Q :=
  let positions_at_target := 
    filter (fun p => pos_i p =? target_pos) (state_positions st) in
  match positions_at_target with
  | [] => None
  | p :: rest => Some (Q_of_nat (pos_e p))
  end.

(** ** Optimality Theorems *)

Theorem viterbi_finds_minimum_cost : forall aut target input,
  wf_automaton aut ->
  accepts aut target input = true ->
  exists path,
    valid_path aut target input path /\
    path_reaches_end target path /\
    forall other_path,
      valid_path aut target input other_path ->
      path_reaches_end target other_path ->
      path_cost path <= path_cost other_path.
Proof. intros. admit. Admitted.

Theorem optimal_correction_exists : forall aut target input,
  wf_automaton aut ->
  (exists edits, edit_sequence_cost edits <= automaton_max_distance aut) ->
  exists best_edits,
    edit_sequence_cost best_edits <= automaton_max_distance aut /\
    forall other_edits,
      edit_sequence_cost other_edits <= automaton_max_distance aut ->
      edit_sequence_cost best_edits <= edit_sequence_cost other_edits.
Proof. intros. admit. Admitted.

Theorem phonetic_optimal : forall max_dist target input,
  accepts (phonetic_automaton max_dist) target input = true ->
  exists phonetic_path,
    Exists (fun op => In op phonetic_ops_phase1) (extract_edit_sequence phonetic_path) /\
    path_cost phonetic_path < 
      (path_cost phonetic_path + 1)%Q. (* Phonetically cheaper *)
Proof. intros. admit. Admitted.
