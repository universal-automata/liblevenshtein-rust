(******************************************************************************)
(* Core.v - Foundational Definitions for Levenshtein Automata                *)
(*                                                                            *)
(* This file contains the core type definitions and basic properties for     *)
(* Levenshtein automata. The formalization is based on:                      *)
(*   - docs/research/weighted-levenshtein-automata/README.md                 *)
(*   - Mitankin's thesis on Levenshtein automata                             *)
(*   - Implementation in src/transducer/generalized/                         *)
(*                                                                            *)
(* Key concepts:                                                              *)
(*   - Positions: (index, errors) pairs with variant flags                   *)
(*   - Subsumption: Partial order on positions for minimization              *)
(*   - Invariants: Geometric reachability constraints                        *)
(*                                                                            *)
(* Authors: Formal verification team                                          *)
(* Date: 2025-11-17                                                          *)
(******************************************************************************)

From Stdlib Require Import ZArith.
From Stdlib Require Import Arith.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From Stdlib Require Import Ascii.
From Stdlib Require Import String.

Open Scope Z_scope.

(******************************************************************************)
(* SECTION 1: Position Variants                                              *)
(*                                                                            *)
(* Position variants distinguish different types of automaton states:        *)
(*   - I-type: Within dictionary term (index < term_length)                  *)
(*   - M-type: Matched to end of dictionary term (final positions)           *)
(*   - Transposing: Mid-transposition operation (2-step)                     *)
(*   - Splitting: Mid-split operation for phonetic (2-step)                  *)
(*                                                                            *)
(* THEORY: These correspond to Mitankin's Definition 15 (position types)     *)
(* IMPLEMENTATION: src/transducer/generalized/position.rs:35-48              *)
(******************************************************************************)

Inductive PositionVariant : Type :=
  | VarINonFinal       (* I-type: within term, non-final *)
  | VarMFinal          (* M-type: at term end, final state *)
  | VarITransposing    (* I-type + transposing flag *)
  | VarMTransposing    (* M-type + transposing flag *)
  | VarISplitting      (* I-type + splitting flag *)
  | VarMSplitting.     (* M-type + splitting flag *)

(* Decidable equality for variants *)
Definition variant_eq_dec : forall (v1 v2 : PositionVariant), {v1 = v2} + {v1 <> v2}.
Proof.
  decide equality.
Defined.

(* Variants can be compared for equality as booleans *)
Definition variant_eqb (v1 v2 : PositionVariant) : bool :=
  if variant_eq_dec v1 v2 then true else false.

(******************************************************************************)
(* SECTION 2: Position Structure                                             *)
(*                                                                            *)
(* A position tracks location in the edit graph and remaining error budget:  *)
(*   - variant: Type of position (I/M/Transposing/Splitting)                *)
(*   - offset: Relative index in term (can be negative for M-type)          *)
(*   - errors: Remaining error budget (0 ≤ errors ≤ max_distance)           *)
(*   - max_distance: Maximum allowed distance (n)                            *)
(*   - entry_char: Stored character for multi-step operations (optional)    *)
(*                                                                            *)
(* GEOMETRIC INTERPRETATION:                                                  *)
(*   Position (offset, errors) has reachable region R = Manhattan ball       *)
(*   of radius (max_distance - errors) centered at offset in edit graph.    *)
(*                                                                            *)
(* THEORY: Lemma 2.0.2 (Suffix Independence) justifies this representation  *)
(* IMPLEMENTATION: src/transducer/generalized/position.rs:50-80              *)
(******************************************************************************)

Record Position : Type := mkPosition {
  variant : PositionVariant;
  offset : Z;              (* Position in term: I-type ≥ 0, M-type < 0 *)
  errors : nat;            (* Remaining error budget: 0 ≤ errors ≤ n *)
  max_distance : nat;      (* Maximum Levenshtein distance (n) *)
  entry_char : option ascii (* For multi-step ops: stores first char *)
}.

(* Notation for cleaner position construction *)
Notation "'⟨' v ',' o ',' e ',' n '⟩'" :=
  (mkPosition v o e n None) (at level 0).

Notation "'⟨' v ',' o ',' e ',' n ',' c '⟩'" :=
  (mkPosition v o e n (Some c)) (at level 0).

(******************************************************************************)
(* SECTION 3: Position Invariants                                            *)
(*                                                                            *)
(* Each position type has geometric constraints derived from edit graph      *)
(* reachability. These ensure positions remain within valid bounds.          *)
(*                                                                            *)
(* DERIVATION: From edit graph path analysis (Part I of theory doc)          *)
(*   - |offset| ≤ errors: Can reach diagonal from current position           *)
(*   - -n ≤ offset ≤ n: Cannot move more than n steps from diagonal          *)
(*                                                                            *)
(* KEY INSIGHT: Invariants ensure O(n²) position space bound                 *)
(******************************************************************************)

(* I-type invariant: Within term, non-negative offset *)
(* FORMULA: |offset| ≤ errors ∧ -n ≤ offset ≤ n ∧ 0 ≤ errors ≤ n *)
(* GEOMETRIC: Position can reach diagonal within remaining error budget *)
Definition i_invariant (p : Position) : Prop :=
  variant p = VarINonFinal /\
  Z.abs (offset p) <= Z.of_nat (errors p) /\
  -Z.of_nat (max_distance p) <= offset p <= Z.of_nat (max_distance p) /\
  (errors p <= max_distance p)%nat.

(* M-type invariant: At term end, negative offset tracks overshoot *)
(* FORMULA: errors ≥ -offset - n ∧ -2n ≤ offset ≤ 0 ∧ 0 ≤ errors ≤ n *)
(* GEOMETRIC: From term end, can still reach query end within budget *)
Definition m_invariant (p : Position) : Prop :=
  variant p = VarMFinal /\
  Z.of_nat (errors p) >= (-(offset p) - Z.of_nat (max_distance p)) /\
  (-Z.of_nat (2 * max_distance p)) <= offset p <= 0 /\
  (errors p <= max_distance p)%nat.

(* Transposing variants inherit base invariants *)
Definition i_transposing_invariant (p : Position) : Prop :=
  variant p = VarITransposing /\
  Z.abs (offset p) <= Z.of_nat (errors p) /\
  -Z.of_nat (max_distance p) <= offset p <= Z.of_nat (max_distance p) /\
  (errors p <= max_distance p)%nat /\
  entry_char p <> None.  (* Must store transposition entry character *)

Definition m_transposing_invariant (p : Position) : Prop :=
  variant p = VarMTransposing /\
  Z.of_nat (errors p) >= (-(offset p) - Z.of_nat (max_distance p)) /\
  (-Z.of_nat (2 * max_distance p)) <= offset p <= 0 /\
  (errors p <= max_distance p)%nat /\
  entry_char p <> None.

(* Splitting variants for phonetic operations (Phase 3b) *)
(* NOTE: May have relaxed offset bounds for fractional-weight operations *)
Definition i_splitting_invariant (p : Position) : Prop :=
  variant p = VarISplitting /\
  Z.abs (offset p) <= Z.of_nat (errors p) /\
  -Z.of_nat (max_distance p) <= offset p <= Z.of_nat (max_distance p) /\
  (errors p <= max_distance p)%nat /\
  entry_char p <> None.  (* Must store split entry character *)

Definition m_splitting_invariant (p : Position) : Prop :=
  variant p = VarMSplitting /\
  Z.of_nat (errors p) >= (-(offset p) - Z.of_nat (max_distance p)) /\
  (-Z.of_nat (2 * max_distance p)) <= offset p <= 0 /\
  (errors p <= max_distance p)%nat /\
  entry_char p <> None.

(* Universal validity predicate: position satisfies its variant's invariant *)
Definition valid_position (p : Position) : Prop :=
  match variant p with
  | VarINonFinal => i_invariant p
  | VarMFinal => m_invariant p
  | VarITransposing => i_transposing_invariant p
  | VarMTransposing => m_transposing_invariant p
  | VarISplitting => i_splitting_invariant p
  | VarMSplitting => m_splitting_invariant p
  end.

(******************************************************************************)
(* SECTION 4: Subsumption Relation                                           *)
(*                                                                            *)
(* Subsumption (⊑) is a partial order on positions used for minimization:    *)
(*   p₁ ⊑ p₂ means p₁'s reachable region contains p₂'s region                *)
(*                                                                            *)
(* DEFINITION: p₁ ⊑ p₂ iff:                                                  *)
(*   1. variant(p₁) = variant(p₂)  (same position type)                      *)
(*   2. errors(p₂) > errors(p₁)     (p₂ has less budget)                     *)
(*   3. |offset(p₂) - offset(p₁)| ≤ errors(p₂) - errors(p₁)                 *)
(*                                                                            *)
(* GEOMETRIC INTUITION:                                                       *)
(*   Position (i,e) has reachable region R(i,e) = Manhattan ball             *)
(*   R(j,f) ⊆ R(i,e) when f > e and |j-i| ≤ f-e                             *)
(*                                                                            *)
(* PROPERTIES TO PROVE:                                                       *)
(*   - Irreflexive: ¬(p ⊑ p)           [errors(p) > errors(p) impossible]    *)
(*   - Transitive: p₁⊑p₂ ∧ p₂⊑p₃ → p₁⊑p₃  [geometric containment chains]    *)
(*   - Anti-symmetric: p₁⊑p₂ ∧ p₂⊑p₁ → False  [from irreflexive]            *)
(*                                                                            *)
(* THEORY: Lemma 3.1 (Subsumption Correctness) from theory doc               *)
(* IMPLEMENTATION: src/transducer/generalized/subsumption.rs:80-150          *)
(******************************************************************************)

(* Core subsumption check for positions with same variant *)
Definition subsumes_core (offset1 : Z) (errors1 : nat)
                         (offset2 : Z) (errors2 : nat) : Prop :=
  (errors2 > errors1)%nat /\
  Z.abs (offset2 - offset1) <= Z.of_nat (errors2 - errors1).

(* Full subsumption relation: checks variant equality + core relation *)
Definition subsumes (p1 p2 : Position) : Prop :=
  variant p1 = variant p2 /\
  subsumes_core (offset p1) (errors p1) (offset p2) (errors p2).

(* Notation for subsumption *)
Notation "p1 '⊑' p2" := (subsumes p1 p2) (at level 70).

(* Decidable subsumption for computational proofs *)
Definition subsumes_dec (p1 p2 : Position) : {p1 ⊑ p2} + {~ (p1 ⊑ p2)}.
Proof.
  unfold subsumes, subsumes_core.
  destruct (variant_eq_dec (variant p1) (variant p2)).
  - (* Variants equal, check numeric constraints *)
    destruct (Nat.ltb (errors p1) (errors p2)) eqn:Herr.
    + apply Nat.ltb_lt in Herr.
      destruct (Z.leb (Z.abs (offset p2 - offset p1))
                      (Z.of_nat (errors p2 - errors p1))) eqn:Hoff.
      * apply Z.leb_le in Hoff.
        left. auto.
      * apply Z.leb_gt in Hoff.
        right. intros [_ [_ Hcontr]]. lia.
    + apply Nat.ltb_ge in Herr.
      right. intros [_ [Hcontr _]]. lia.
  - (* Variants differ *)
    right. intros [Hcontr _]. contradiction.
Defined.

(******************************************************************************)
(* SECTION 5: Basic Properties                                               *)
(*                                                                            *)
(* Simple helper lemmas used throughout the development                       *)
(******************************************************************************)

(* Helper: errors must be non-zero for non-trivial subsumption *)
Lemma subsumes_requires_error_gap : forall p1 p2,
  p1 ⊑ p2 -> (errors p2 > errors p1)%nat.
Proof.
  intros p1 p2 [_ [Hgap _]].
  exact Hgap.
Qed.

(* Helper: subsumption preserves variant *)
Lemma subsumes_same_variant : forall p1 p2,
  p1 ⊑ p2 -> variant p1 = variant p2.
Proof.
  intros p1 p2 [Hvar _].
  exact Hvar.
Qed.

(* Helper: offset distance bounded by error gap *)
Lemma subsumes_offset_bound : forall p1 p2,
  p1 ⊑ p2 -> Z.abs (offset p2 - offset p1) <= Z.of_nat (errors p2 - errors p1).
Proof.
  intros p1 p2 [_ [_ Hbound]].
  exact Hbound.
Qed.

(******************************************************************************)
(* SECTION 6: Fundamental Subsumption Properties                             *)
(*                                                                            *)
(* These three theorems establish subsumption as a strict partial order.     *)
(* They are the foundation for anti-chain state minimization.                *)
(******************************************************************************)

(**
  THEOREM: Subsumption is Irreflexive

  STATEMENT: ∀p, ¬(p ⊑ p)

  INTUITION: A position cannot subsume itself because subsumption requires
             errors(p₂) > errors(p₁), but errors(p) = errors(p) always holds.

  PROOF STRATEGY: Direct from definition - subsumes_core requires e₂ > e₁,
                   but for p ⊑ p we have e₂ = e₁, contradiction.

  IMPLEMENTATION: This ensures no position is redundant with itself in states.

  REFERENCE: Part II, Section 3.1 of theory doc (anti-chain property)
*)
Theorem subsumes_irreflexive : forall p, ~ (p ⊑ p).
Proof.
  intros p [_ [Hcontr _]].
  (* subsumes_core requires errors p > errors p *)
  lia.  (* Contradiction: n > n is impossible *)
Qed.

(**
  THEOREM: Subsumption is Transitive

  STATEMENT: ∀p₁ p₂ p₃, p₁ ⊑ p₂ → p₂ ⊑ p₃ → p₁ ⊑ p₃

  INTUITION: If R(p₂) ⊆ R(p₁) and R(p₃) ⊆ R(p₂), then R(p₃) ⊆ R(p₁)
             by geometric containment transitivity.

  PROOF STRUCTURE:
    1. Assume p₁ ⊑ p₂ and p₂ ⊑ p₃
    2. Show variant(p₁) = variant(p₃) by transitivity through p₂
    3. Show e₃ > e₁ by transitivity: e₃ > e₂ > e₁
    4. Show |o₃ - o₁| ≤ e₃ - e₁ by triangle inequality:
       |o₃ - o₁| ≤ |o₃ - o₂| + |o₂ - o₁|    [triangle inequality]
                 ≤ (e₃ - e₂) + (e₂ - e₁)    [from assumptions]
                 = e₃ - e₁                   [algebra]

  KEY INSIGHT: The Manhattan distance satisfies triangle inequality,
               and error gaps add, so containment chains compose.

  IMPLEMENTATION: Allows transitive redundancy elimination in states.

  REFERENCE: Lemma 3.2 (Subsumption Transitivity) from theory doc
*)
Theorem subsumes_transitive : forall p1 p2 p3,
  p1 ⊑ p2 -> p2 ⊑ p3 -> p1 ⊑ p3.
Proof.
  intros p1 p2 p3
         [Hv12 [He12 Ho12]]
         [Hv23 [He23 Ho23]].
  unfold subsumes, subsumes_core.

  (* Step 1: Variants must all be equal *)
  split.
  { rewrite Hv12. exact Hv23. }

  (* Step 2: Error transitivity *)
  split.
  { lia. }  (* e₃ > e₂ > e₁ implies e₃ > e₁ *)

  (* Step 3: Offset bound by triangle inequality *)
  (* Goal: |o₃ - o₁| ≤ e₃ - e₁ *)
  assert (Htri : Z.abs (offset p3 - offset p1) <=
                 Z.abs (offset p3 - offset p2) + Z.abs (offset p2 - offset p1)).
  { replace (offset p3 - offset p1) with ((offset p3 - offset p2) + (offset p2 - offset p1)) by lia.
    apply Z.abs_triangle. }

  (* Combine with assumptions *)
  assert (Hsum : Z.abs (offset p3 - offset p2) + Z.abs (offset p2 - offset p1) <=
                 Z.of_nat (errors p3 - errors p2) + Z.of_nat (errors p2 - errors p1)).
  { (* Both terms bounded by assumptions Ho23 and Ho12 *)
    assert (Z.abs (offset p3 - offset p2) <= Z.of_nat (errors p3 - errors p2)) by exact Ho23.
    assert (Z.abs (offset p2 - offset p1) <= Z.of_nat (errors p2 - errors p1)) by exact Ho12.
    lia. }

  (* Simplify sum of gaps *)
  assert (Hsimpl : Z.of_nat (errors p3 - errors p2) + Z.of_nat (errors p2 - errors p1) =
                   Z.of_nat (errors p3 - errors p1)).
  { (* e₃ > e₂ > e₁ so we can combine the gaps *)
    assert (Hgap: (errors p3 - errors p2 + (errors p2 - errors p1) = errors p3 - errors p1)%nat). {
      lia.
    }
    rewrite <- Hgap.
    rewrite Nat2Z.inj_add.
    reflexivity. }

  (* Chain inequalities *)
  rewrite Hsimpl in Hsum.
  lia.  (* |o₃-o₁| ≤ |o₃-o₂| + |o₂-o₁| ≤ (e₃-e₂) + (e₂-e₁) = e₃-e₁ *)
Qed.

(**
  THEOREM: Subsumption Respects Variant Boundaries

  STATEMENT: ∀p₁ p₂, variant(p₁) ≠ variant(p₂) → ¬(p₁ ⊑ p₂)

  INTUITION: Different position types (I vs M, or base vs transposing)
             represent fundamentally different automaton states that
             cannot subsume each other.

  PROOF STRATEGY: Direct from definition - subsumption requires
                   variant equality as first conjunct.

  IMPLEMENTATION IMPACT:
    - Anti-chain maintenance only compares same-variant positions
    - Subsumption checks can early-exit on variant mismatch
    - State minimization preserves all variant types

  RUST CODE: src/transducer/generalized/subsumption.rs:143-148
             Uses match statement to enforce variant equality

  REFERENCE: Definition 16 (Subsumption) from Mitankin thesis
*)
Theorem subsumes_variant_restriction : forall p1 p2,
  variant p1 <> variant p2 -> ~ (p1 ⊑ p2).
Proof.
  intros p1 p2 Hneq [Heq _].
  (* subsumes requires variant equality *)
  contradiction.  (* Heq says they're equal, Hneq says they're not *)
Qed.

(******************************************************************************)
(* SECTION 7: Anti-Symmetry (Derived Property)                               *)
(*                                                                            *)
(* While not directly used, anti-symmetry confirms subsumption has no cycles *)
(******************************************************************************)

(**
  THEOREM: Subsumption is Anti-Symmetric

  STATEMENT: ∀p₁ p₂, p₁ ⊑ p₂ → p₂ ⊑ p₁ → False

  PROOF: Follows immediately from irreflexivity and transitivity.
         If p₁ ⊑ p₂ and p₂ ⊑ p₁, then p₁ ⊑ p₁ by transitivity,
         contradicting irreflexivity.

  INTUITION: Subsumption is a strict ordering - no position can
             subsume another that subsumes it back.
*)
Theorem subsumes_antisymmetric : forall p1 p2,
  p1 ⊑ p2 -> p2 ⊑ p1 -> False.
Proof.
  intros p1 p2 H12 H21.
  (* By transitivity: p1 ⊑ p2 ⊑ p1 implies p1 ⊑ p1 *)
  assert (Hcontr : p1 ⊑ p1).
  { apply (subsumes_transitive p1 p2 p1); assumption. }
  (* But subsumption is irreflexive *)
  apply (subsumes_irreflexive p1).
  exact Hcontr.
Qed.

(******************************************************************************)
(* SECTION 8: Computational Reflection                                       *)
(*                                                                            *)
(* Bridge between logical Prop and computational bool for testing             *)
(******************************************************************************)

(* Boolean version of subsumption for computational proofs *)
Definition subsumes_b (p1 p2 : Position) : bool :=
  variant_eqb (variant p1) (variant p2) &&
  Nat.ltb (errors p1) (errors p2) &&
  Z.leb (Z.abs (offset p2 - offset p1))
        (Z.of_nat (errors p2 - errors p1)).

(* Correctness: boolean version reflects Prop version *)
Lemma subsumes_b_correct : forall p1 p2,
  subsumes_b p1 p2 = true <-> p1 ⊑ p2.
Proof.
  intros p1 p2.
  unfold subsumes_b, subsumes, subsumes_core.
  split; intro H.
  - (* true -> Prop *)
    apply andb_true_iff in H as [H1 H2].
    apply andb_true_iff in H1 as [Hvar Herr].
    unfold variant_eqb in Hvar.
    destruct (variant_eq_dec (variant p1) (variant p2)); [|discriminate].
    apply Nat.ltb_lt in Herr.
    apply Z.leb_le in H2.
    split; [exact e | split; lia].
  - (* Prop -> true *)
    destruct H as [Hvar [Herr Hoff]].
    apply andb_true_iff; split.
    + apply andb_true_iff; split.
      * unfold variant_eqb.
        destruct (variant_eq_dec (variant p1) (variant p2)); [reflexivity | contradiction].
      * apply Nat.ltb_lt. exact Herr.
    + apply Z.leb_le. exact Hoff.
Qed.

(******************************************************************************)
(* END OF CORE.V                                                              *)
(*                                                                            *)
(* This file establishes the foundational definitions and proves the three    *)
(* key properties of subsumption: irreflexivity, transitivity, and variant   *)
(* restriction. These properties are essential for anti-chain maintenance    *)
(* and state minimization in the automaton.                                  *)
(*                                                                            *)
(* NEXT STEPS:                                                                *)
(*   - Invariants.v: Prove position constructor correctness                  *)
(*   - Operations.v: Formalize standard edit operations                      *)
(*   - Transitions.v: Prove successor correctness                            *)
(*   - State.v: Prove anti-chain preservation                                *)
(******************************************************************************)
