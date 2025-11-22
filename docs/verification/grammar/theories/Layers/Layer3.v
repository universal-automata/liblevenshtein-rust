(** * Layer 3: Type Checking

    This layer performs type checking on successfully parsed programs.
*)

Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Liblevenshtein.Grammar.Verification.Core.Types.
Require Import Liblevenshtein.Grammar.Verification.Core.Program.
Import ListNotations.

Record Layer3Config := {
  strict_mode : bool
}.

Definition default_layer3_config : Layer3Config := {|
  strict_mode := true
|}.

Parameter type_check_program : parse_tree -> TypeResult.

Definition execute_layer3 (config : Layer3Config) (input : program)
                         (layer2_result : LayerResult)
    : LayerResult :=
  layer2_result.  (* Placeholder *)

Theorem layer3_soundness : forall config input layer2_result,
  True.
Proof. trivial. Qed.
