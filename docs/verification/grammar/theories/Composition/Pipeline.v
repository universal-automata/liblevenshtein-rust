(** * Pipeline Execution *)

Require Import Coq.Lists.List.
Require Import Liblevenshtein.Grammar.Verification.Core.Program.
Import ListNotations.

(** Pipeline already defined in Program.v *)

Theorem pipeline_always_produces_result : forall input pipe,
  exists result, result = execute_pipeline input pipe.
Proof.
  apply pipeline_always_terminates.
Qed.
