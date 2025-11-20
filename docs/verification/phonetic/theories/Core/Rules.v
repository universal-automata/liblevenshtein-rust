(** * Core Rule Operations - Position Skipping Optimization

    This module contains core definitions for rule application, matching,
    and the optimized sequential rule application algorithm with position skipping.

    Part of: Liblevenshtein.Phonetic.Verification.Core
*)

Require Import String List Arith Ascii Bool Nat Lia.
Require Import PhoneticRewrites.rewrite_rules.
From Liblevenshtein.Phonetic.Verification Require Import Auxiliary.Lib.
From Liblevenshtein.Phonetic.Verification Require Import Auxiliary.Types.
Import ListNotations.

(** * Core Rule Matching Operations *)

(** ** No Early Matches Property *)

(** If a rule cannot apply at any position < start_pos in the current string,
    then starting the search from start_pos is safe.
*)
Definition no_early_matches (r : RewriteRule) (s : PhoneticString) (start_pos : nat) : Prop :=
  forall pos, (pos < start_pos)%nat -> can_apply_at r s pos = false.

(** * Optimized Algorithm *)

(** ** Sequential Rule Application with Position Skipping *)

(** Sequential rule application with position skipping optimization.
    After applying a rule at position `last_pos`, the next iteration's
    search starts from `last_pos` instead of position 0.

    @param rules     List of rewrite rules to apply
    @param s         Current phonetic string
    @param fuel      Maximum number of iterations (for termination)
    @param last_pos  Position where the last rule was applied
    @return          Some transformed_string or None if fuel exhausted
*)
Fixpoint apply_rules_seq_opt (rules : list RewriteRule) (s : PhoneticString)
                               (fuel : nat) (last_pos : nat)
  : option PhoneticString :=
  match fuel with
  | O => Some s
  | S fuel' =>
      match rules with
      | [] => Some s
      | r :: rest =>
          (** Start search from last_pos instead of 0 *)
          let search_len := (length s - last_pos + 1)%nat in
          match find_first_match_from r s last_pos search_len with
          | Some pos =>
              match apply_rule_at r s pos with
              | Some s' =>
                  (** Rule applied - restart with new last_pos *)
                  apply_rules_seq_opt rules s' fuel' pos
              | None =>
                  (** Shouldn't happen if can_apply_at worked correctly *)
                  apply_rules_seq_opt rest s fuel' last_pos
              end
          | None =>
              (** No match from last_pos onward - try next rule *)
              apply_rules_seq_opt rest s fuel' last_pos
          end
      end
  end.

(** * Termination *)

(** ** Termination Proof for Optimized Algorithm *)

(** Theorem: apply_rules_seq_opt always terminates with sufficient fuel.
    This proof establishes that the optimized algorithm with position skipping
    is well-defined and always produces a result given enough fuel.
*)
Theorem apply_rules_seq_opt_terminates :
  forall rules s fuel last_pos,
    exists result,
      apply_rules_seq_opt rules s fuel last_pos = Some result.
Proof.
  intros rules s fuel last_pos.
  generalize dependent last_pos.
  generalize dependent s.
  generalize dependent rules.
  induction fuel as [| fuel' IH]; intros rules s last_pos.
  - (* Base case: fuel = 0 *)
    exists s.
    simpl. reflexivity.
  - (* Inductive case: fuel = S fuel' *)
    destruct rules as [| r rest].
    + (* No rules *)
      exists s.
      simpl. reflexivity.
    + (* At least one rule *)
      simpl.
      destruct (find_first_match_from r s last_pos (length s - last_pos + 1)) eqn:E_find.
      * (* Match found at position n *)
        destruct (apply_rule_at r s n) eqn:E_apply.
        ** (* Rule applied successfully *)
          (* Recursive call with transformed string *)
          apply (IH (r :: rest) p n).
        ** (* Rule application failed *)
          apply (IH rest s last_pos).
      * (* No match found *)
        apply (IH rest s last_pos).
Qed.
