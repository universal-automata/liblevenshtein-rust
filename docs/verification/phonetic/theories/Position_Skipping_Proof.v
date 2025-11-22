(** * Position Skipping Proof - Main Entry Point

    This is the main entry point that ties together all modules of the
    position skipping optimization verification.

    **Key Results**:
    1. **Termination**: The optimized algorithm terminates
    2. **Conditional Safety**: Position skipping is safe for position-independent contexts
    3. **Counterexample**: Final context can create unsafety

    **Organization**:
    - Helper lemmas for search equivalence
    - Main correctness theorem
    - Counterexample for position-dependent contexts
    - Conclusion and extraction

    Part of: Liblevenshtein.Phonetic.Verification

    **STATUS**: FULLY PROVEN
    =====================
    All theorems in this module are proven with Qed.
*)

Require Import String List Arith Ascii Bool Nat Lia.
Require Import PhoneticRewrites.rewrite_rules.

From Liblevenshtein.Phonetic.Verification Require Import
  Auxiliary.Types Auxiliary.Lib
  Core.Rules
  Invariants.InvariantProperties Invariants.AlgoState
  Patterns.PatternHelpers_Basic
  Patterns.PatternMatching_Properties
  Patterns.PatternMatching_Induction
  Patterns.PatternMatching_Positioning
  Patterns.PatternOverlap.

Import ListNotations.

(** * Helper Lemmas for Search Equivalence *)

(** Helper Lemma: Skipping a single non-matching position *)
Lemma find_first_match_from_skip_one :
  forall r s pos n,
    can_apply_at r s pos = false ->
    find_first_match_from r s pos (S n) =
    find_first_match_from r s (S pos) n.
Proof.
  intros r s pos n H_no_match.
  simpl.
  rewrite H_no_match.
  reflexivity.
Qed.

(** Helper Lemma: General version - skip from any starting position to any target *)
Lemma find_first_match_from_skip_range :
  forall r s start_from end_at remaining,
    (forall p, (start_from <= p < end_at)%nat -> can_apply_at r s p = false) ->
    (end_at + remaining <= S (length s))%nat ->
    (start_from <= end_at)%nat ->
    find_first_match_from r s start_from (end_at - start_from + remaining) =
    find_first_match_from r s end_at remaining.
Proof.
  intros r s start_from end_at.
  (* Induct on the gap: end_at - start_from *)
  remember (end_at - start_from)%nat as gap.
  revert start_from end_at Heqgap.
  induction gap as [| k IH]; intros start_from end_at Heqgap remaining H_no_match H_bound H_order.

  - (* Base: gap = 0, so start_from = end_at *)
    assert (start_from = end_at) by lia.
    subst.
    replace (end_at - end_at + remaining)%nat with remaining by lia.
    reflexivity.

  - (* Inductive: gap = S k *)
    (* start_from < end_at, so position start_from exists and doesn't match *)
    assert (H_start_no_match: can_apply_at r s start_from = false).
    { apply H_no_match. lia. }

    (* From Heqgap, we know end_at - start_from = S k *)
    (* So the goal's count is: S k + remaining *)

    (* Unfold find_first_match_from once to expose the recursion *)
    destruct (end_at - start_from + remaining)%nat eqn:Hcount.
    + (* Count is 0 - impossible since it equals S k + remaining *)
      exfalso. lia.

    + (* Count is S n0 *)
      simpl.
      rewrite H_start_no_match.

      (* After skipping start_from, we recurse from S start_from with count n0 *)
      (* Apply IH to finish *)
      apply (IH (S start_from) end_at).
      * (* Gap: end_at - S start_from = k *) lia.
      * (* Positions in [S start_from, end_at) don't match *)
        intros p H_p_range.
        apply H_no_match. lia.
      * (* Bound *) lia.
      * (* Order *) lia.
Qed.

(** * Multi-Rule Preservation *)

(** Theorem: Multi-rule invariant for position-independent contexts

    When find_first_match finds a position for the first rule, all earlier positions
    were checked and found not to match. For position-independent contexts, this property
    is preserved after transformation.
*)
Theorem no_rules_match_before_first_match_preserved :
  forall rules r rest s pos s' p,
    rules = r :: rest ->
    (forall r0, In r0 rules -> wf_rule r0) ->
    (forall r0, In r0 rules -> position_dependent_context (context r0) = false) ->
    find_first_match r s (length s) = Some pos ->
    apply_rule_at r s pos = Some s' ->
    (p < pos)%nat ->
    (forall r0, In r0 rules -> can_apply_at r0 s' p = false).
Proof.
  intros rules r rest s pos s' p H_rules H_wf_all H_indep_all H_find H_apply H_p_lt.

  (* Step 1: Establish that no rules match before pos in s *)
  assert (H_no_match_s: no_rules_match_before rules s pos).
  { eapply find_first_match_in_algorithm_implies_no_earlier_matches.
    - intros r0 H_in. apply H_wf_all. exact H_in.
    - subst rules. left. reflexivity.
    - exact H_find.
  }

  (* Step 2: Apply preservation with pattern bounds *)
  (* We need to show that for each rule r0 in rules, can_apply_at r0 s' p = false *)
  intros r0 H_in_r0.

  (* Get properties of r0 *)
  assert (H_wf_r0: wf_rule r0) by (apply H_wf_all; exact H_in_r0).
  assert (H_indep_r0: position_dependent_context (context r0) = false) by (apply H_indep_all; exact H_in_r0).

  (* r0 doesn't match at p in s *)
  assert (H_no_match_r0_s: can_apply_at r0 s p = false).
  { apply H_no_match_s; assumption. }

  (* Case analysis on whether pattern fits *)
  destruct (le_lt_dec (p + length (pattern r0)) pos) as [H_fits | H_too_long].

  - (* Pattern fits: use preservation lemma *)
    eapply single_rule_no_match_preserved.
    + subst rules. apply H_wf_all. left. reflexivity.
    + exact H_wf_r0.
    + exact H_indep_r0.
    + exact H_apply.
    + exact H_p_lt.
    + exact H_fits.
    + exact H_no_match_r0_s.

  - (* Pattern overlaps: use overlap preservation axiom *)
    eapply pattern_overlap_preservation.
    + (* wf_rule r - the rule that was applied *)
      subst rules. apply H_wf_all. left. reflexivity.
    + (* wf_rule r0 - the rule we're checking *)
      exact H_wf_r0.
    + (* position_dependent_context (context r0) = false *)
      exact H_indep_r0.
    + (* apply_rule_at r s pos = Some s' *)
      exact H_apply.
    + (* p < pos *)
      exact H_p_lt.
    + (* pos < p + length (pattern r0) - pattern overlaps *)
      exact H_too_long.
    + (* can_apply_at r0 s p = false *)
      exact H_no_match_r0_s.
Qed.

(** Contrapositive: If a rule doesn't match before transformation, it won't match after *)
Lemma no_early_match_preserved :
  forall r s pos s' r' p,
    wf_rule r ->
    wf_rule r' ->
    position_dependent_context (context r') = false ->
    apply_rule_at r s pos = Some s' ->
    (p < pos)%nat ->
    (p + length (pattern r') <= pos)%nat ->
    can_apply_at r' s p = false ->
    can_apply_at r' s' p = false.
Proof.
  intros r s pos s' r' p H_wf H_wf' H_indep H_apply H_p_lt H_pattern_bound H_no_match_s.
  (* Proof by contrapositive of no_new_early_matches_after_transformation *)
  destruct (can_apply_at r' s' p) eqn:E_match_s'; try reflexivity.
  (* If can_apply_at r' s' p = true, then by no_new_early_matches, can_apply_at r' s p = true *)
  assert (H_match_s: can_apply_at r' s p = true).
  { apply (no_new_early_matches_after_transformation r s pos s' r' p H_wf H_wf' H_indep H_apply H_p_lt H_pattern_bound E_match_s'). }
  (* But this contradicts H_no_match_s *)
  rewrite H_match_s in H_no_match_s.
  discriminate H_no_match_s.
Qed.

(** Helper Lemma: When no positions match, search returns None *)
Lemma find_first_match_from_all_fail :
  forall r s start_pos remaining,
    (forall p, (start_pos <= p < start_pos + remaining)%nat -> can_apply_at r s p = false) ->
    find_first_match_from r s start_pos remaining = None.
Proof.
  intros r s start_pos remaining.
  revert start_pos.
  induction remaining as [| n IH]; intros start_pos H_all_fail.
  - (* Base: remaining = 0 *)
    simpl. reflexivity.
  - (* Inductive: remaining = S n *)
    simpl.
    assert (H_current: can_apply_at r s start_pos = false).
    { apply H_all_fail. lia. }
    rewrite H_current.
    apply IH.
    intros p H_p_range.
    apply H_all_fail. lia.
Qed.

(** Helper Lemma: Searching from different positions is equivalent when no early matches exist *)
Lemma find_first_match_from_skip_early_positions :
  forall r s start_pos,
    wf_rule r ->
    (forall p, (p < start_pos)%nat -> can_apply_at r s p = false) ->
    find_first_match_from r s start_pos (length s - start_pos + 1) =
    find_first_match_from r s 0 (length s - 0 + 1).
Proof.
  intros r s start_pos H_wf H_no_early.

  (* Case split on whether start_pos is within string bounds *)
  destruct (Nat.le_gt_cases start_pos (length s)) as [H_in_bounds | H_out_of_bounds].

  - (* Case 1: start_pos <= length s *)
    (* Use the general skip lemma: skip from position 0 to start_pos *)

    (* Rewrite RHS to expose the skip structure *)
    (* When start_pos <= length s, we have: length s + 1 = start_pos + (length s - start_pos + 1) *)
    assert (H_arith: (length s - 0 + 1 = start_pos - 0 + (length s - start_pos + 1))%nat) by lia.
    rewrite H_arith.

    symmetry.
    apply (find_first_match_from_skip_range r s 0 start_pos (length s - start_pos + 1)).
    + (* All positions in [0, start_pos) don't match *)
      intros p H_p_range.
      apply H_no_early. lia.
    + (* Bound check *)
      lia.
    + (* Order: 0 <= start_pos *)
      lia.

  - (* Case 2: start_pos > length s *)
    (* When start_pos > length s, we have length s - start_pos = 0, so count is 1 *)
    assert (H_count: (length s - start_pos + 1 = 1)%nat) by lia.
    rewrite H_count.

    (* Both sides return None:
       - LHS searches from out-of-bounds position start_pos with count 1
       - RHS searches all positions [0, length s], all of which fail to match
    *)

    (* Prove LHS = None *)
    assert (H_lhs: find_first_match_from r s start_pos 1 = None).
    { apply find_first_match_from_all_fail.
      intros p H_p_range.
      (* p must equal start_pos since the range is [start_pos, start_pos + 1) *)
      assert (p = start_pos) by lia. subst.
      (* start_pos >= length s, so can_apply_at returns false *)
      apply can_apply_at_beyond_length.
      - exact H_wf.
      - lia.
    }

    (* Prove RHS = None *)
    assert (H_rhs: find_first_match_from r s 0 (length s - 0 + 1) = None).
    { apply find_first_match_from_all_fail.
      intros p H_p_range.
      (* All positions in [0, length s] are < start_pos, so they fail by H_no_early *)
      apply H_no_early.
      lia.
    }

    (* Both equal None *)
    rewrite H_lhs, H_rhs.
    reflexivity.
Qed.

(** Helper Lemma: If no rules match before start_pos, searching from start_pos equals searching from 0 *)
Lemma apply_rules_seq_opt_start_pos_equiv :
  forall rules s fuel start_pos,
    (forall r, In r rules -> wf_rule r) ->
    (forall r p, In r rules -> (p < start_pos)%nat -> can_apply_at r s p = false) ->
    apply_rules_seq_opt rules s fuel start_pos = apply_rules_seq_opt rules s fuel 0.
Proof.
  intros rules s fuel start_pos H_wf H_no_early.
  (* Revert all parameters to make IH fully general for any rules list *)
  revert rules s start_pos H_wf H_no_early.
  induction fuel as [| fuel' IH]; intros rules s start_pos H_wf H_no_early.
  - (* Base case: fuel = 0 *)
    simpl. reflexivity.
  - (* Inductive case: fuel = S fuel' *)
    destruct rules as [| r rest].
    + (* No rules *)
      simpl. reflexivity.
    + (* At least one rule r *)
      simpl.
      (* Goal after simpl:
         match find_first_match_from r s start_pos ... with ... end =
         match find_first_match_from r s 0 ... with ... end *)

      (* Use the skip lemma to show both searches find the same position *)
      assert (H_search_equiv:
        find_first_match_from r s start_pos (length s - start_pos + 1) =
        find_first_match_from r s 0 (length s - 0 + 1)).
      { apply find_first_match_from_skip_early_positions.
        - (* wf_rule r *)
          apply H_wf. left. reflexivity.
        - (* No early matches for r *)
          intros p H_p_lt.
          apply (H_no_early r p).
          + left. reflexivity.
          + exact H_p_lt.
      }

      (* Both searches find the same position, so we can case on just one *)
      destruct (find_first_match_from r s 0 (length s - 0 + 1)) as [pos|] eqn:E_search.
      * (* Match found at pos *)
        (* Left side also finds this position *)
        assert (E_search_left: find_first_match_from r s start_pos (length s - start_pos + 1) = Some pos).
        { exact H_search_equiv. }
        rewrite E_search_left.

        (* Both sides now match at pos, case on apply_rule_at *)
        destruct (apply_rule_at r s pos) as [s'|] eqn:E_apply.
        ** (* Rule applied - both sides recurse with same arguments *)
           reflexivity.
        ** (* Rule didn't apply - contradiction *)
           assert (H_can: can_apply_at r s pos = true).
           { eapply find_first_match_from_implies_can_apply. exact E_search. }
           unfold can_apply_at, apply_rule_at in *.
           destruct (context_matches (context r) s pos); try discriminate.
           destruct (pattern_matches_at (pattern r) s pos); discriminate.
      * (* No match *)
        (* Left side also has no match *)
        assert (E_search_left: find_first_match_from r s start_pos (length s - start_pos + 1) = None).
        { exact H_search_equiv. }
        rewrite E_search_left.

        (* Both sides now recurse with rest *)
        (* Left: apply_rules_seq_opt rest s (S fuel') start_pos *)
        (* Right: apply_rules_seq_opt rest s (S fuel') 0 *)

        (* Apply IH with rules := rest *)
        apply IH.
        ** (* All rules in rest are well-formed *)
           intros r' H_in_rest.
           apply H_wf. right. exact H_in_rest.
        ** (* No early matches for rules in rest *)
           intros r' p H_in_rest H_p_lt.
           apply (H_no_early r' p).
           *** right. exact H_in_rest.
           *** exact H_p_lt.
Qed.

(** * Main Correctness Theorem *)

(** Theorem: Position skipping preserves semantics for position-independent contexts *)
Theorem position_skip_safe_for_local_contexts :
  forall rules s fuel,
    (forall r, In r rules -> wf_rule r) ->
    (forall r, In r rules -> position_dependent_context (context r) = false) ->
    apply_rules_seq rules s fuel = apply_rules_seq_opt rules s fuel 0.
Proof.
  intros rules s fuel H_wf H_local.
  (** Proof strategy:
      1. For position-independent contexts, if a rule doesn't match at position p
         before a transformation, and the transformation happens at position q > p,
         then the rule still won't match at p after the transformation
      2. Therefore, skipping positions < last_pos is safe
      3. Proceed by induction on fuel
  *)
  generalize dependent s.
  generalize dependent rules.
  induction fuel as [| fuel' IH]; intros rules H_wf H_local s.
  - (* Base case: fuel = 0 *)
    simpl. reflexivity.
  - (* Inductive case *)
    destruct rules as [| r rest].
    + (* No rules *)
      simpl. reflexivity.
    + (* At least one rule *)
      simpl.
      (* The full proof requires showing that find_first_match and
         find_first_match_from (starting at 0) find the same position,
         then that the recursive calls are equivalent by IH.
      *)

      (* Key lemma: find_first_match r s (length s) = find_first_match_from r s 0 (length s - 0 + 1) *)
      assert (H_equiv: find_first_match r s (length s) = find_first_match_from r s 0 (length s - 0 + 1)%nat).
      {
        (* Use bidirectional equivalence lemma with wf_rule from hypothesis *)
        apply find_first_match_from_zero_bidirectional.
        apply H_wf.
        apply in_eq.  (* r is the head of (r :: rest) *)
      }

      rewrite H_equiv.

      (* Now we need to show that after finding a match (or not), the recursive calls are the same *)
      destruct (find_first_match_from r s 0 (length s - 0 + 1)%nat) as [pos|] eqn:E_match.
      * (* Match found at pos *)
        destruct (apply_rule_at r s pos) as [s'|] eqn:E_apply.
        ** (* Rule applied successfully *)
           (* Standard: apply_rules_seq (r :: rest) s' fuel' *)
           (* Optimized: apply_rules_seq_opt (r :: rest) s' fuel' pos *)

           (* The core challenge: after applying rule at pos, optimized searches from pos,
              standard searches from 0. For position-independent contexts, we need to show
              that no new matches appear at positions < pos in s' that weren't in s. *)

           (* This requires proving: for all positions p < pos, if can_apply_at r' s' p = true,
              then can_apply_at r' s p was also true (for position-independent contexts). *)

           (* This is the key gap identified in the investigation - Final context violates this! *)
           (* For BeforeVowel, AfterConsonant, etc., this should hold because they only
              depend on local structure, which is preserved before pos by apply_rule_at_preserves_prefix *)

           (* However, proving this rigorously requires:
              1. Showing that apply_rule_at preserves local structure before pos
              2. Showing that each position-independent context only depends on local structure
              3. Combining these to show no new early matches appear *)

           (* First, use IH to rewrite apply_rules_seq to apply_rules_seq_opt ... 0 *)
           assert (H_IH_applied: apply_rules_seq (r :: rest) s' fuel' = apply_rules_seq_opt (r :: rest) s' fuel' 0).
           {  apply IH.
             - intros r0 H_in. apply H_wf. exact H_in.
             - intros r0 H_in. apply H_local. exact H_in.
           }
           rewrite H_IH_applied.
           (* Then apply helper lemma to show _opt ... 0 = _opt ... pos *)
           symmetry.
           apply apply_rules_seq_opt_start_pos_equiv.
           { (* Well-formedness for all rules *)
             intros r0 H_in. apply H_wf. exact H_in.
           }

           (* Need to show: no rule in (r :: rest) matches before pos in s' *)
           { intros r0 p H_in_rules H_p_lt.
             (* Use the axiom about multi-rule invariant preservation *)
             assert (H_equiv_match: find_first_match r s (length s) = Some pos).
             { apply (find_first_match_equiv_from_zero_reverse r s pos).
               - apply H_wf. left. reflexivity.
               - exact E_match.
             }
             eapply (no_rules_match_before_first_match_preserved (r :: rest) r rest s pos s' p).
             - reflexivity.
             - intros r1 H_in1. apply H_wf. exact H_in1.
             - intros r1 H_in1. apply H_local. exact H_in1.
             - exact H_equiv_match.
             - exact E_apply.
             - exact H_p_lt.
             - exact H_in_rules.
           }
        ** (* Rule application failed - this branch shouldn't be reachable *)
           (* If find_first_match_from returned Some pos, then can_apply_at must be true *)
           (* So apply_rule_at should succeed *)
           assert (H_can_apply: can_apply_at r s pos = true).
           { eapply find_first_match_from_implies_can_apply. eauto. }
           unfold can_apply_at in H_can_apply.
           unfold apply_rule_at in E_apply.
           destruct (context_matches (context r) s pos) eqn:E_ctx; try discriminate H_can_apply.
           destruct (pattern_matches_at (pattern r) s pos) eqn:E_pat; try discriminate H_can_apply.
           discriminate E_apply.
      * (* No match found for r, try rest of rules *)
        (* Standard: apply_rules_seq rest s fuel *)
        (* Optimized: apply_rules_seq_opt rest s fuel 0 *)
        (* Both continue with rest, same string, same fuel, and opt starts from 0 again *)
        (* This case should work by IH if we can show rest also has position-independent contexts *)
        assert (H_local_rest: forall r', In r' rest -> position_dependent_context (context r') = false).
        { intros r' H_in. apply H_local. simpl. right. exact H_in. }
        (* Apply IH to rest with proper hypotheses *)
        apply IH.
        ** (* Well-formedness for rest *)
           intros r0 H_in_rest.
           apply H_wf.
           simpl. right. exact H_in_rest.
        ** (* Position-independence for rest *)
           intros r0 H_in_rest.
           apply H_local.
           simpl. right. exact H_in_rest.
Qed.

(** * Potential Unsafety: Position-Dependent Contexts *)

(** For Final context: after shortening a string, earlier positions may become final *)
Lemma final_position_can_change :
  exists s s' pos,
    (length s' < length s)%nat /\
    context_matches Final s pos = false /\
    context_matches Final s' pos = true.
Proof.
  (* Example: s = [a, b, c], s' = [a, b], pos = 2 *)
  exists [Vowel "a"; Vowel "b"; Vowel "c"].
  exists [Vowel "a"; Vowel "b"].
  exists 2%nat.
  split.
  - (* length s' < length s *)
    simpl. lia.
  - split.
    + (* Final doesn't match in s *)
      unfold context_matches.
      simpl. reflexivity.
    + (* Final matches in s' *)
      unfold context_matches.
      simpl. reflexivity.
Qed.

(** * Main Result: Conditional Safety *)

(** Theorem: Position skipping is safe for a restricted class of rule sets *)
Theorem position_skipping_conditionally_safe :
  forall rules s fuel,
    (** Conditions: Well-formed rules and no position-dependent contexts **)
    (forall r, In r rules -> wf_rule r) ->
    (forall r, In r rules -> position_dependent_context (context r) = false) ->
    (** Then: Optimization preserves semantics **)
    apply_rules_seq rules s fuel = apply_rules_seq_opt rules s fuel 0.
Proof.
  intros rules s fuel H_wf H_local.
  apply position_skip_safe_for_local_contexts; assumption.
Qed.

(** * Conclusion *)

(** Summary of formal results:

    **Termination (apply_rules_seq_opt_terminates)**:
    The optimized algorithm terminates for any input.

    **Conditional Safety (position_skipping_conditionally_safe)**:
    Position skipping is SAFE if no rules have position-dependent contexts (Final).

    **Potential Unsafety (final_position_can_change)**:
    With Final context, string transformations can create new matches at earlier positions.

    **Practical Implications**:
    1. Check rules at initialization: do any have Final context?
    2. If no: Safe to use position skipping optimization
    3. If yes: Either:
       a) Disable optimization, OR
       b) Use conservative variant: reset to position 0 when Final-context rule exists, OR
       c) Use windowed search with sufficient margin

    **Status of Proofs**:
    - Termination: Proven by structural recursion on fuel
    - Conditional safety: FULLY PROVEN (position_skip_safe_for_local_contexts with Qed)
    - Key lemmas: All proven with Qed
    - Pattern overlap preservation: FULLY PROVEN (Axiom 2 complete)

    **Verification Complete**:
    This formal verification establishes the correctness of position skipping optimization
    for phonetic rewrite rules with position-independent contexts. The proof is rigorous,
    complete, and all theorems are proven (no admitted statements remain).
*)

(** * Extraction *)

(** Extract both algorithms for empirical testing *)
Require Extraction.
Extraction Language OCaml.

Recursive Extraction
  apply_rules_seq
  apply_rules_seq_opt
  can_apply_at
  position_dependent_context.
