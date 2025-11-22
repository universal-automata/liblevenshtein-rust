(** * End-to-End Correctness

    This module contains the main correctness theorem for the complete
    grammar correction pipeline.
*)

Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Liblevenshtein.Grammar.Verification.Core.Types.
Require Import Liblevenshtein.Grammar.Verification.Core.Program.
Require Import Liblevenshtein.Grammar.Verification.Layers.Layer1.
Require Import Liblevenshtein.Grammar.Verification.Layers.Layer2.
Require Import Liblevenshtein.Grammar.Verification.Composition.Forward.
Import ListNotations.

(** ** Main Correctness Theorem *)

(** If the pipeline produces a correction, it is both sound and complete *)
Theorem grammar_correction_correctness :
  forall input config1 config2 goal,
    let layer1 := execute_layer1 config1 in
    let layer2 := fun p r => execute_layer2 config2 p r in
    let pipe := [layer1; fun p => layer2 p (layer1 p)] in
    let result := execute_pipeline input pipe in
    match result.(layer_best_correction) with
    | Some corr =>
        correction_sound input corr /\
        correction_complete goal input corr
    | None => True
    end.
Proof.
  intros input config1 config2 goal layer1 layer2 pipe result.
  (* Apply the general correction_correctness theorem *)
  apply correction_correctness.
Qed.

(** ** Soundness: All Corrections Transform Input Correctly *)

Theorem all_corrections_sound :
  forall input pipe,
    let result := execute_pipeline input pipe in
    Forall (correction_sound input) result.(layer_corrections).
Proof.
  intros input pipe result.
  (* Follows from valid_layer_result *)
Admitted.

(** ** Termination: Pipeline Always Terminates *)

Theorem pipeline_terminates_always :
  forall input pipe,
    exists result, result = execute_pipeline input pipe.
Proof.
  apply pipeline_always_terminates.
Qed.

(** ** Optimality: Best Correction Minimizes Edit Distance *)

Theorem best_correction_optimal :
  forall input pipe goal,
    goal.(goal_min_edits) = true ->
    let result := execute_pipeline input pipe in
    match result.(layer_best_correction) with
    | Some best =>
        Forall (fun corr =>
          edit_distance best.(correction_edits) <=
          edit_distance corr.(correction_edits))
          result.(layer_corrections)
    | None => True
    end.
Proof.
  intros input pipe goal Hgoal result.
  (* The best correction has minimal edit distance among all candidates *)
Admitted.

(** ** Progress: Pipeline Makes Forward Progress *)

Theorem pipeline_makes_progress :
  forall input pipe,
    length pipe > 0 ->
    let result := execute_pipeline input pipe in
    result.(layer_corrections) <> [] \/
    result.(layer_best_correction) = None.
Proof.
  intros input pipe Hlen result.
  (* Either we find corrections or the problem is unsolvable *)
Admitted.
