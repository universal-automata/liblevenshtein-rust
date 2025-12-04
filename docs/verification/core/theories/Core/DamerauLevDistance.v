(** * Damerau-Levenshtein Distance - Full Metric Properties

    This module re-exports the Damerau-Levenshtein distance function and all
    basic lemmas from DamerauLevDistanceDef, and adds the triangle inequality
    proof from DamerauComposition.

    Part of: Liblevenshtein.Core

    This module provides the complete interface for Damerau-Levenshtein distance
    including:
    - The distance function (from DamerauLevDistanceDef)
    - Basic lemmas: empty cases, single char, symmetry, etc. (from DamerauLevDistanceDef)
    - Triangle inequality: d(s1, s3) <= d(s1, s2) + d(s2, s3) (from DamerauComposition)

    Module dependency structure (no cycles):
    - DamerauLevDistanceDef: defines distance function + basic lemmas
    - DamerauTrace: imports DamerauLevDistanceDef, defines trace infrastructure
    - DamerauComposition: imports DamerauTrace + DamerauLevDistanceDef, proves triangle
    - DamerauLevDistance (this module): imports DamerauLevDistanceDef + DamerauComposition
*)

From Stdlib Require Import String List Arith Ascii Bool Nat Lia Wf_nat.
Import ListNotations.

(** Re-export all definitions and lemmas from DamerauLevDistanceDef *)
From Liblevenshtein.Core Require Export Core.DamerauLevDistanceDef.

(** Import the triangle inequality proof from DamerauComposition *)
From Liblevenshtein.Core Require Import Composition.DamerauComposition.

(** * Triangle Inequality for Damerau-Levenshtein Distance

    d(s1, s3) <= d(s1, s2) + d(s2, s3)

    This is the key metric property that makes Damerau-Levenshtein distance
    a proper metric (along with identity, symmetry, and non-negativity).

    The proof is via trace composition in DamerauComposition:
    1. For any strings A, B, construct an optimal DL trace with cost = d(A,B)
    2. Composing traces T1 (A→B) and T2 (B→C) yields trace T with cost <= cost(T1) + cost(T2)
    3. Since d(A,C) <= cost(T), we have d(A,C) <= d(A,B) + d(B,C)
*)
Lemma damerau_lev_triangle : forall s1 s2 s3,
  damerau_lev_distance s1 s3 <= damerau_lev_distance s1 s2 + damerau_lev_distance s2 s3.
Proof.
  exact damerau_lev_triangle_via_composition.
Qed.

