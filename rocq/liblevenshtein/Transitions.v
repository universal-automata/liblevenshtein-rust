(*******************************************************************************)
(* Transitions.v - Automaton Transition Relations and Invariant Preservation  *)
(*                                                                             *)
(* This file formalizes the successor relation for Levenshtein automata and   *)
(* proves that transitions preserve position invariants. This is the CORE     *)
(* correctness property: automaton operations maintain well-formedness.       *)
(*                                                                             *)
(* Key Results:                                                                *)
(*   - i_successor relation defines valid I-type transitions                  *)
(*   - m_successor relation defines valid M-type transitions                  *)
(*   - Invariant preservation: valid positions → valid successors             *)
(*   - Cost correctness: error accounting matches operation costs             *)
(*                                                                             *)
(* BUG DISCOVERY GOAL:                                                         *)
(*   As we prove these theorems, proof failures will reveal missing           *)
(*   preconditions, incorrect boundary checks, or invalid transitions.        *)
(*                                                                             *)
(* References:                                                                 *)
(*   - Implementation: src/transducer/generalized/state.rs:238-890            *)
(*   - Theory: docs/research/weighted-levenshtein-automata/README.md          *)
(*                                                                             *)
(* Authors: Formal Verification Team                                           *)
(* Date: 2025-11-17                                                           *)
(*******************************************************************************)

From Stdlib Require Import ZArith.
From Stdlib Require Import Arith.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.

Require Import Core.
Require Import Invariants.
Require Import Operations.

(* Open Z scope for integer comparisons *)
Open Scope Z_scope.

(*******************************************************************************)
(* SECTION 1: I-Type Successor Relation                                       *)
(*                                                                             *)
(* Defines the four standard transitions for I-type positions:                *)
(*   - Match: Characters equal, no cost, offset unchanged                     *)
(*   - Delete: Remove word character, cost 1, offset decreases by 1           *)
(*   - Insert: Add query character, cost 1, offset unchanged                  *)
(*   - Substitute: Replace character, cost 1, offset unchanged                *)
(*                                                                             *)
(* RUST CORRESPONDENCE: state.rs:252-549 (successors_i_type)                  *)
(*                                                                             *)
(* CRITICAL DESIGN DECISION:                                                   *)
(*   We model the successor relation as an INDUCTIVE RELATION rather than     *)
(*   a function. This allows us to:                                           *)
(*   1. Express preconditions clearly in each constructor                     *)
(*   2. Prove properties about all valid transitions uniformly                *)
(*   3. Handle non-determinism (multiple possible operations)                 *)
(*******************************************************************************)

(**
  I-type successor relation

  i_successor p op cv p' means:
    "From position p, applying operation op with characteristic vector cv
     produces valid successor position p'"

  PRECONDITIONS (encoded in each constructor):
    - Source position p must satisfy i_invariant
    - Operation must be applicable (match needs character match, others need budget)
    - Result position p' must satisfy i_invariant (will prove this!)

  RUST: This models the logic in state.rs:272-349 (standard operations loop)
*)
Inductive i_successor : Position -> StandardOperation ->
                        CharacteristicVector -> Position -> Prop :=

  (** MATCH TRANSITION

      PRECONDITIONS:
        - Source must be I-type non-final
        - Characteristic vector shows match at index (offset + n)
        - Error budget is not required (match is free)

      POSTCONDITION:
        - Offset unchanged (diagonal move in edit graph)
        - Errors unchanged (no cost)
        - Variant unchanged (stay in I-type)

      RUST: state.rs:280-295
        if op.is_match() && has_match {
          if let Ok(succ) = GeneralizedPosition::new_i(offset, errors, max_distance) {
            successors.push(succ);
          }
        }

      GEOMETRIC: In Wagner-Fischer DP grid:
        (i, j) → (i+1, j+1) if word[i] = query[j]
        Offset t = i - j stays constant: (i+1) - (j+1) = i - j
  *)
  | ISucc_Match : forall offset errors n cv,
      has_match cv (Z.to_nat (offset + Z.of_nat n)) ->
      (errors <= n)%nat ->
      i_successor
        (mkPosition VarINonFinal offset errors n None)
        OpMatch
        cv
        (mkPosition VarINonFinal offset errors n None)

  (** DELETE TRANSITION

      PRECONDITIONS:
        - Source must be I-type non-final
        - Error budget available: errors < n
        - NOT at left boundary: offset > -n (CRITICAL CHECK!)

      POSTCONDITION:
        - Offset decreases by 1 (move left in edit graph)
        - Errors increase by 1 (deletion costs 1 edit)
        - Variant unchanged (stay in I-type)

      RUST: state.rs:297-314
        else if op.is_deletion() {
          if errors < self.max_distance {
            let new_errors = errors + 1;
            if new_errors <= self.max_distance {
              if let Ok(succ) = GeneralizedPosition::new_i(offset - 1, new_errors, ...) {
                successors.push(succ);
              }
            }
          }
        }

      BUG CHECK: Does Rust verify offset > -n BEFORE attempting delete?
        Answer: No explicit check. The check is inside new_i() constructor.
        Constructor requires: -n ≤ offset - 1 ≤ n
        This means: offset ≥ -n + 1, i.e., offset > -n ✓

        However, this means invalid deletes are silently rejected (Ok vs Err).
        POTENTIAL OPTIMIZATION: Add explicit precondition check to avoid
        unnecessary constructor calls.

      GEOMETRIC: In Wagner-Fischer DP grid:
        (i, j) → (i+1, j) - consume word character, don't advance query
        Offset change: (i+1) - j = (i - j) + 1 - 1 = offset - 1
  *)
  | ISucc_Delete : forall offset errors n cv,
      (errors < n)%nat ->
      offset > -Z.of_nat n ->
      i_successor
        (mkPosition VarINonFinal offset errors n None)
        OpDelete
        cv
        (mkPosition VarINonFinal (offset - 1) (S errors) n None)

  (** INSERT TRANSITION

      PRECONDITIONS:
        - Source must be I-type non-final
        - Error budget available: errors < n
        - No offset boundary check needed (offset unchanged)

      POSTCONDITION:
        - Offset unchanged (horizontal move in edit graph)
        - Errors increase by 1 (insertion costs 1 edit)
        - Variant unchanged (stay in I-type)

      RUST: state.rs:315-329
        else if op.is_insertion() {
          if errors < self.max_distance {
            let new_errors = errors + 1;
            if new_errors <= self.max_distance {
              if let Ok(succ) = GeneralizedPosition::new_i(offset, new_errors, ...) {
                successors.push(succ);
              }
            }
          }
        }

      OBSERVATION: Rust checks both errors < n AND errors + 1 ≤ n.
        These are EQUIVALENT for natural numbers!
        errors < n  ⟺  errors + 1 ≤ n  (for nat)

        SIMPLIFICATION OPPORTUNITY: Second check is redundant for standard
        operations (weight = 1). Only needed for fractional weights.

      GEOMETRIC: In Wagner-Fischer DP grid:
        (i, j) → (i, j+1) - don't consume word, advance query
        Offset change: i - (j+1) = (i - j) - 1 + 1 = offset (unchanged)
  *)
  | ISucc_Insert : forall offset errors n cv,
      (errors < n)%nat ->
      -Z.of_nat n <= offset <= Z.of_nat n ->
      i_successor
        (mkPosition VarINonFinal offset errors n None)
        OpInsert
        cv
        (mkPosition VarINonFinal offset (S errors) n None)

  (** SUBSTITUTE TRANSITION

      PRECONDITIONS:
        - Source must be I-type non-final
        - Error budget available: errors < n
        - No character match required (unlike Match)
        - No offset boundary check needed (offset unchanged)

      POSTCONDITION:
        - Offset unchanged (diagonal move, but different characters)
        - Errors increase by 1 (substitution costs 1 edit)
        - Variant unchanged (stay in I-type)

      RUST: state.rs:330-348
        else if op.is_substitution() {
          if errors < self.max_distance {
            let new_errors = errors + 1;
            if new_errors <= self.max_distance {
              if let Ok(succ) = GeneralizedPosition::new_i(offset, new_errors, ...) {
                successors.push(succ);
              }
            }
          }
        }

      GEOMETRIC: In Wagner-Fischer DP grid:
        (i, j) → (i+1, j+1) but word[i] ≠ query[j]
        Offset change: (i+1) - (j+1) = i - j = offset (unchanged)
  *)
  | ISucc_Substitute : forall offset errors n cv,
      (errors < n)%nat ->
      -Z.of_nat n <= offset <= Z.of_nat n ->
      i_successor
        (mkPosition VarINonFinal offset errors n None)
        OpSubstitute
        cv
        (mkPosition VarINonFinal offset (S errors) n None).

(*******************************************************************************)
(* SECTION 2: Invariant Preservation for I-Type                               *)
(*                                                                             *)
(* MAIN THEOREM: i_successor preserves i_invariant                             *)
(*                                                                             *)
(* Strategy:                                                                   *)
(*   1. Prove lemma for each operation separately                             *)
(*   2. Combine lemmas via case analysis on operation type                    *)
(*                                                                             *)
(* EXPECTED BUGS:                                                              *)
(*   - Missing preconditions will cause proof failures                        *)
(*   - Incorrect offset calculations will break invariant bounds              *)
(*   - Wrong error accounting will violate budget constraints                 *)
(*******************************************************************************)

(**
  LEMMA: Match preserves I-type invariant

  PROOF STRUCTURE:
    Assume: p satisfies i_invariant
    Assume: i_successor p OpMatch cv p'
    Prove: p' satisfies i_invariant

    By inversion on i_successor, the only applicable case is ISucc_Match.
    This case sets p' = mkPosition VarINonFinal offset errors n None
    with same offset and errors as p.

    Since p satisfied i_invariant, and all components unchanged, p' does too.
*)
Lemma i_match_preserves_invariant : forall p cv p',
  i_invariant p ->
  i_successor p OpMatch cv p' ->
  i_invariant p'.
Proof.
  intros p cv p' Hinv Hsucc.

  (* Invert the successor relation to get the Match case *)
  inversion Hsucc; subst.

  (* After inversion, p and p' are both mkPosition VarINonFinal offset errors n None *)
  (* Since Match doesn't change anything, p' = p, invariant is preserved trivially *)
  (* Extract components from source invariant *)
  unfold i_invariant in *.
  simpl in Hinv.
  destruct Hinv as [Hvar [Hreach [Hbounds Herr]]].

  (* Prove i_invariant for p' = p (same position) *)
  unfold i_invariant. simpl.
  split.
  - (* Variant *) reflexivity.
  - split.
    + (* Reachability *) exact Hreach.
    + split.
      * (* Bounds *) exact Hbounds.
      * (* Error budget *) exact Herr.
Qed.

(**
  LEMMA: Delete preserves I-type invariant

  PROOF STRATEGY:
    Key challenge: Prove that offset - 1 still satisfies bounds.

    From source invariant:
      - |offset| ≤ errors
      - -n ≤ offset ≤ n
      - errors ≤ n

    From successor preconditions (ISucc_Delete):
      - errors < n  (budget available)
      - offset > -n  (not at left boundary)

    Must prove for successor:
      - |offset - 1| ≤ errors + 1
      - -n ≤ offset - 1 ≤ n
      - errors + 1 ≤ n

    Third conjunct: errors < n ⟹ errors + 1 ≤ n ✓
    Second conjunct: offset > -n ⟹ offset - 1 ≥ -n ✓
                     offset ≤ n ⟹ offset - 1 < n ≤ n ✓

    First conjunct (HARD): Need to show |offset - 1| ≤ errors + 1
      Case 1: offset ≥ 0
        Then |offset - 1| ≤ |offset| + 1 (by triangle inequality variant)
                         ≤ errors + 1 (by source |offset| ≤ errors)

      Case 2: offset < 0
        Then offset - 1 < offset < 0
        So |offset - 1| = -(offset - 1) = -offset + 1
        From source: |offset| ≤ errors, so -offset ≤ errors
        Thus -offset + 1 ≤ errors + 1 ✓
*)
Lemma i_delete_preserves_invariant : forall p cv p',
  i_invariant p ->
  i_successor p OpDelete cv p' ->
  i_invariant p'.
Proof.
  intros p cv p' Hinv Hsucc.

  (* Invert successor to get Delete case *)
  inversion Hsucc; subst.

  (* Extract source invariant components *)
  unfold i_invariant in *.
  destruct Hinv as [Hvar [Hreach [Hbounds Herr]]].
  simpl in *.

  (* Prove i_invariant for successor *)
  unfold i_invariant.
  simpl.

  (* Split into four conjuncts *)
  split.
  - (* 1. Variant is I-type *)
    reflexivity.

  - split.
    + (* 2. Reachability: |offset - 1| ≤ errors + 1 *)
      (* Convert S errors to Z properly *)
      replace (Z.of_nat (S errors)) with (Z.of_nat errors + 1) by lia.
      (* Now goal is: Z.abs (offset - 1) <= Z.of_nat errors + 1 *)

      (* Case analysis on sign of offset *)
      destruct (Z.leb_spec 0 offset) as [Hpos | Hneg].

      * (* Case: offset ≥ 0 *)
        destruct (Z.leb_spec 0 (offset - 1)) as [Hpos' | Hneg'].

        -- (* Subcase: offset - 1 ≥ 0 *)
           rewrite Z.abs_eq in Hreach by assumption.
           rewrite Z.abs_eq by assumption.
           lia.

        -- (* Subcase: offset - 1 < 0 but offset ≥ 0, so offset ∈ {0, 1} *)
           rewrite Z.abs_eq in Hreach by assumption.
           assert (offset = 0 \/ offset = 1) as [Heq | Heq] by lia.
           ++ rewrite Heq in *. simpl in *. lia.
           ++ rewrite Heq in *. simpl in *. lia.

      * (* Case: offset < 0, so offset - 1 < 0 *)
        rewrite Z.abs_neq in Hreach by lia.
        rewrite Z.abs_neq by lia.
        lia.

    + split.
      * (* 3. Bounds: -n ≤ offset - 1 ≤ n *)
        lia.

      * (* 4. Error budget: errors + 1 ≤ n *)
        lia.
Qed.

(**
  LEMMA: Insert preserves I-type invariant

  PROOF STRATEGY:
    Simpler than Delete because offset doesn't change!

    From source invariant:
      - |offset| ≤ errors
      - -n ≤ offset ≤ n
      - errors ≤ n

    From successor preconditions:
      - errors < n
      - -n ≤ offset ≤ n (explicit in our i_successor definition)

    Must prove for successor:
      - |offset| ≤ errors + 1  ✓ (follows from |offset| ≤ errors)
      - -n ≤ offset ≤ n      ✓ (unchanged)
      - errors + 1 ≤ n       ✓ (from errors < n)
*)
Lemma i_insert_preserves_invariant : forall p cv p',
  i_invariant p ->
  i_successor p OpInsert cv p' ->
  i_invariant p'.
Proof.
  intros p cv p' Hinv Hsucc.

  (* Invert successor *)
  inversion Hsucc; subst.

  (* Extract source invariant *)
  unfold i_invariant in *.
  destruct Hinv as [Hvar [Hreach [Hbounds Herr]]].
  simpl in *.

  (* All easy: offset unchanged, errors increase by 1 *)
  repeat split; simpl; try reflexivity; lia.
Qed.

(**
  LEMMA: Substitute preserves I-type invariant

  PROOF STRATEGY:
    Identical to Insert (offset unchanged, errors increase)
*)
Lemma i_substitute_preserves_invariant : forall p cv p',
  i_invariant p ->
  i_successor p OpSubstitute cv p' ->
  i_invariant p'.
Proof.
  intros p cv p' Hinv Hsucc.

  (* Invert successor *)
  inversion Hsucc; subst.

  (* Extract source invariant *)
  unfold i_invariant in *.
  destruct Hinv as [Hvar [Hreach [Hbounds Herr]]].
  simpl in *.

  (* Identical proof to Insert *)
  repeat split; simpl; try reflexivity; lia.
Qed.

(**
  MAIN THEOREM: I-type successor preserves invariant

  For ANY valid I-type position and ANY applicable operation,
  the resulting successor position is also valid.

  This is the CORE CORRECTNESS property for I-type transitions.
*)
Theorem i_successor_preserves_invariant : forall p op cv p',
  i_invariant p ->
  i_successor p op cv p' ->
  i_invariant p'.
Proof.
  intros p op cv p' Hinv Hsucc.

  (* Case analysis on which operation was applied *)
  destruct op.

  - (* Match *)
    apply (i_match_preserves_invariant p cv p' Hinv Hsucc).

  - (* Delete *)
    apply (i_delete_preserves_invariant p cv p' Hinv Hsucc).

  - (* Insert *)
    apply (i_insert_preserves_invariant p cv p' Hinv Hsucc).

  - (* Substitute *)
    apply (i_substitute_preserves_invariant p cv p' Hinv Hsucc).
Qed.

(*******************************************************************************)
(* SECTION 3: Cost Correctness for I-Type                                     *)
(*                                                                             *)
(* Prove that error accounting matches operation costs.                       *)
(*******************************************************************************)

(**
  THEOREM: Successor error count equals source errors + operation cost

  This validates that the automaton correctly tracks edit distance.
*)
Theorem i_successor_cost_correct : forall p op cv p',
  i_successor p op cv p' ->
  errors p' = (errors p + operation_cost op)%nat.
Proof.
  intros p op cv p' Hsucc.

  (* Case analysis on which operation was applied *)
  inversion Hsucc; subst; simpl.

  (* All cases: Match (errors+0=errors), Delete/Insert/Substitute (S errors = errors+1) *)
  - lia. (* Match *)
  - lia. (* Delete *)
  - lia. (* Insert *)
  - lia. (* Substitute *)
Qed.

(*******************************************************************************)
(* END OF TRANSITIONS.V (I-Type portion complete)                              *)
(*                                                                             *)
(* NEXT STEPS:                                                                 *)
(*   - Add M-type successor relation                                          *)
(*   - Prove M-type invariant preservation                                    *)
(*   - Add transposing/splitting transitions (Phase 4)                        *)
(*******************************************************************************)
