(** * Auxiliary Library - Position Skipping Optimization

    This module contains auxiliary lemmas for arithmetic, bounds checking,
    list operations, well-formedness, and search helper functions.
    These lemmas support the position skipping optimization proof.

    Part of: Liblevenshtein.Phonetic.Verification
*)

Require Import String List Arith Ascii Bool Nat Lia.
Require Import PhoneticRewrites.rewrite_rules.
From Liblevenshtein.Phonetic.Verification Require Import Auxiliary.Types.
Import ListNotations.

(** * Core Search Functions *)

(** ** Find First Match *)

(** Find first match starting from a given position.
    This is the core search function that supports position skipping.

    @param r          The rule to search for
    @param s          The input string
    @param start_pos  Position to start searching from
    @param remaining  Number of positions to check
    @return           Some pos if a match is found, None otherwise
*)
Fixpoint find_first_match_from (r : RewriteRule) (s : PhoneticString)
                                (start_pos : nat) (remaining : nat) : option nat :=
  match remaining with
  | O => None
  | S remaining' =>
      if can_apply_at r s start_pos then
        Some start_pos
      else
        find_first_match_from r s (S start_pos) remaining'
  end.

(** ** Immediate Properties of find_first_match_from *)

(** Lemma: find_first_match_from only searches from start_pos onward.
    If a match is found at position pos, then pos >= start_pos.
*)
Lemma find_first_match_from_lower_bound :
  forall r s start_pos n pos,
    find_first_match_from r s start_pos n = Some pos ->
    (start_pos <= pos)%nat.
Proof.
  intros r s start_pos n.
  generalize dependent start_pos.
  induction n as [| n' IH]; intros start_pos pos H.
  - (* Base case: n = 0 *)
    simpl in H. discriminate H.
  - (* Inductive case *)
    simpl in H.
    destruct (can_apply_at r s start_pos) eqn:E.
    + (* Match found at start_pos *)
      injection H as H_eq.
      subst. lia.
    + (* No match, continue searching *)
      apply IH in H.
      lia.
Qed.

(** Lemma: find_first_match_from with insufficient range returns None.
    If start_pos > length s, then searching with 0 remaining positions returns None.
*)
Lemma find_first_match_from_empty :
  forall r s start_pos,
    (start_pos > length s)%nat ->
    find_first_match_from r s start_pos 0 = None.
Proof.
  intros. simpl. reflexivity.
Qed.

(** * Auxiliary Lemmas for Arithmetic and Bounds *)

(** Helper lemmas for reasoning about truncating natural number subtraction *)

Lemma sub_add_inverse : forall a b,
  (b <= a)%nat -> (a - b + b = a)%nat.
Proof.
  intros a b H.
  lia.
Qed.

Lemma sub_S_decompose : forall a b,
  (S b <= a)%nat -> (a - S b = a - b - 1)%nat.
Proof.
  intros a b H.
  lia.
Qed.

Lemma sub_lt_mono : forall a b c,
  (a - S b <= c)%nat -> (S b <= a)%nat -> (a - b <= S c)%nat.
Proof.
  intros a b c H H_bound.
  lia.
Qed.

Lemma pos_in_search_range : forall start_pos n pos,
  (pos < start_pos + n)%nat -> (start_pos <= pos)%nat -> (pos - start_pos < n)%nat.
Proof.
  intros start_pos n pos H H_ge.
  lia.
Qed.

Lemma search_range_bound : forall (s : PhoneticString) start_pos pos,
  (pos < start_pos + (length s - start_pos + 1))%nat ->
  (start_pos <= length s)%nat ->
  (pos <= length s)%nat.
Proof.
  intros s start_pos pos H H_bound.
  lia.
Qed.

Lemma search_range_strict_bound : forall (s : PhoneticString) start_pos pos,
  (pos < start_pos + (length s - start_pos + 1))%nat ->
  (start_pos <= length s)%nat ->
  (pos < length s + 1)%nat.
Proof.
  intros s start_pos pos H H_bound.
  assert (H_rewrite: (start_pos + (length s - start_pos + 1) = length s + 1)%nat).
  { lia. }
  rewrite H_rewrite in H.
  exact H.
Qed.

(** * Pattern Non-Emptiness Lemmas *)

(** Well-formed rules have non-empty patterns *)
Lemma pattern_non_empty : forall r,
  wf_rule r -> (length (pattern r) > 0)%nat.
Proof.
  intros r H.
  unfold wf_rule in H.
  destruct H as [H_len H_weight].
  exact H_len.
Qed.

(** Pattern matching requires sufficient space *)
Lemma pattern_matches_at_requires_space : forall pat s pos,
  (length pat > 0)%nat ->
  (pos >= length s)%nat ->
  pattern_matches_at pat s pos = false.
Proof.
  intros pat s pos H_len H_pos.
  destruct pat as [| p ps] eqn:E_pat.
  - (* pat = [], contradicts H_len *)
    simpl in H_len. lia.
  - (* pat = p :: ps, so pattern is non-empty *)
    simpl.
    (* nth_error s pos when pos >= length s returns None *)
    assert (H_nth: nth_error s pos = None).
    { apply nth_error_None. lia. }
    rewrite H_nth.
    reflexivity.
Qed.

(** can_apply_at returns false at or beyond string length for non-empty patterns *)
Lemma can_apply_at_beyond_length : forall r s pos,
  wf_rule r ->
  (pos >= length s)%nat ->
  can_apply_at r s pos = false.
Proof.
  intros r s pos H_wf H_pos.
  unfold can_apply_at.
  destruct (context_matches (context r) s pos) eqn:E_ctx.
  - (* Context matches - check pattern *)
    assert (H_pat_len: (length (pattern r) > 0)%nat).
    { apply pattern_non_empty. exact H_wf. }
    rewrite (pattern_matches_at_requires_space (pattern r) s pos H_pat_len H_pos).
    reflexivity.
  - (* Context doesn't match *)
    reflexivity.
Qed.

(** * Helper Lemmas for Phase 3 *)

(** ** Arithmetic Helpers *)

(** Fuel bound shift: If lower bound holds for fuel, it holds for S fuel *)
Lemma fuel_bound_shift : forall (s : PhoneticString) fuel pos,
  (length s - fuel <= pos)%nat ->
  (length s - S fuel <= pos)%nat.
Proof.
  intros s fuel pos H.
  lia.
Qed.

(** Range arithmetic simplification *)
Lemma range_arithmetic : forall n,
  (n - 0 + 1 = S n)%nat.
Proof.
  intros n.
  lia.
Qed.

(** Natural number subtraction with successor *)
Lemma nat_sub_succ : forall n m,
  (n >= S m)%nat ->
  (n - S m = n - m - 1)%nat.
Proof.
  intros n m H.
  lia.
Qed.

(** ** List Helpers *)

(** Element at head of list *)
Lemma In_head : forall {A : Type} (x : A) (xs : list A),
  In x (x :: xs).
Proof.
  intros A x xs.
  simpl.
  left.
  reflexivity.
Qed.

(** If element in tail, it's in the whole list *)
Lemma In_tail : forall {A : Type} (x y : A) (xs : list A),
  In x xs ->
  In x (y :: xs).
Proof.
  intros A x y xs H.
  simpl.
  right.
  exact H.
Qed.

(** ** Well-formedness Helpers *)

(** Well-formedness preserved for rules in list *)
Lemma wf_rule_In : forall r rules,
  (forall r', In r' rules -> wf_rule r') ->
  In r rules ->
  wf_rule r.
Proof.
  intros r rules H_all H_in.
  apply H_all.
  exact H_in.
Qed.

(** ** Search Helpers *)

(** Generalized can_apply_beyond_length for rules in a list *)
Lemma can_apply_beyond_length_general : forall rules r s pos,
  (forall r', In r' rules -> wf_rule r') ->
  In r rules ->
  (pos >= length s)%nat ->
  can_apply_at r s pos = false.
Proof.
  intros rules r s pos H_wf_all H_in H_pos.
  apply can_apply_at_beyond_length.
  - apply wf_rule_In with (rules := rules); assumption.
  - exact H_pos.
Qed.

(** If apply_rule_at succeeds on a well-formed rule, position must be valid *)
Lemma apply_rule_at_pos_valid : forall r s pos s',
  wf_rule r ->
  apply_rule_at r s pos = Some s' ->
  (pos < length s)%nat.
Proof.
  intros r s pos s' H_wf H_apply.
  (* Proof by contradiction: assume pos >= length s *)
  destruct (lt_dec pos (length s)) as [H_lt | H_ge].
  - (* pos < length s - this is what we want to prove *)
    exact H_lt.
  - (* pos >= length s - show this leads to contradiction *)
    (* If pos >= length s, then apply_rule_at should return None for well-formed rules *)
    unfold apply_rule_at in H_apply.
    destruct (context_matches (context r) s pos) eqn:E_ctx; try discriminate.
    destruct (pattern_matches_at (pattern r) s pos) eqn:E_pat; try discriminate.
    (* But we know pattern_matches_at returns false when pos >= length s for non-empty patterns *)
    assert (H_pat_false: pattern_matches_at (pattern r) s pos = false).
    { apply pattern_matches_at_requires_space.
      - apply pattern_non_empty. exact H_wf.
      - lia. }
    rewrite H_pat_false in E_pat.
    discriminate.
Qed.

(** * Auxiliary Lemmas for find_first_match *)

(** Lemma: find_first_match returns Some only if can_apply_at is true at that position *)
Lemma find_first_match_some_implies_can_apply :
  forall r s fuel pos,
    find_first_match r s fuel = Some pos ->
    can_apply_at r s pos = true.
Proof.
  intros r s fuel.
  generalize dependent s.
  induction fuel as [| fuel' IH]; intros s pos H.
  - (* Base case: fuel = 0 *)
    simpl in H. discriminate H.
  - (* Inductive case *)
    simpl in H.
    unfold is_Some in H.
    destruct (apply_rule_at r s (length s - S fuel')%nat) eqn:E.
    + (* Match found *)
      injection H as H_eq.
      subst pos.
      unfold apply_rule_at in E.
      destruct (context_matches (context r) s (length s - S fuel')%nat) eqn:E_ctx; try discriminate.
      destruct (pattern_matches_at (pattern r) s (length s - S fuel')%nat) eqn:E_pat; try discriminate.
      unfold can_apply_at.
      rewrite E_ctx, E_pat.
      reflexivity.
    + (* No match, continue *)
      apply IH in H.
      exact H.
Qed.

(** Lemma: find_first_match searches from position (length s - fuel) onward *)
Lemma find_first_match_search_range :
  forall r s fuel pos,
    wf_rule r ->
    find_first_match r s fuel = Some pos ->
    (length s - fuel <= pos)%nat /\ (pos < length s)%nat.
Proof.
  intros r s fuel pos H_wf H_match.
  revert s pos H_match.
  induction fuel as [| fuel' IH]; intros s pos H.
  - (* Base case *)
    simpl in H. discriminate H.
  - (* Inductive case *)
    simpl in H.
    destruct (is_Some (apply_rule_at r s (length s - S fuel')%nat)) eqn:E.
    + (* Match found at (length s - S fuel') *)
      injection H as H_eq.
      split.
      * (* Show length s - S fuel' >= length s - fuel' *)
        rewrite <- H_eq. lia.
      * (* Show pos < length s *)
        rewrite <- H_eq.
        (* Position must be < length s *)
        (* When fuel = S fuel', we check position (length s - S fuel') *)
        (* Two cases: either S fuel' <= length s, or S fuel' > length s *)
        destruct (le_lt_dec (S fuel') (length s)) as [H_fuel_bound | H_fuel_large].
        ** (* S fuel' <= length s, so position = length s - S fuel' < length s *)
           lia.
        ** (* S fuel' > length s, so length s - S fuel' = 0 due to truncating subtraction *)
           assert (H_pos_zero: (length s - S fuel' = 0)%nat) by lia.
           rewrite H_pos_zero.
           (* Need to show 0 < length s *)
           (* If apply_rule_at succeeded at position 0, the string must be non-empty *)
           destruct s as [| phone rest] eqn:E_s.
           *** (* s = [], empty string *)
               (* Empty string with apply_rule_at succeeding contradicts well-formedness *)
               (* For well-formed rules, apply_rule_at on empty string at any position returns None *)
               unfold is_Some in E.
               simpl in E.
               (* apply_rule_at r [] 0 with non-empty pattern must be None *)
               assert (H_apply_false: apply_rule_at r [] 0 = None).
               { unfold apply_rule_at.
                 destruct (context_matches (context r) [] 0) eqn:E_ctx.
                 - (* Context matches, but pattern matching on empty string with non-empty pattern fails *)
                   assert (H_pat: pattern_matches_at (pattern r) [] 0 = false).
                   { apply pattern_matches_at_requires_space.
                     - apply pattern_non_empty. exact H_wf.
                     - simpl. lia. }
                   rewrite H_pat. reflexivity.
                 - reflexivity. }
               rewrite H_apply_false in E.
               simpl in E. discriminate E.
           *** (* s = phone :: rest, non-empty *)
               simpl. lia.
    + (* No match, continue *)
      apply (IH s pos) in H.
      destruct H as [H_lower H_upper].
      split; lia.
Qed.

(** Lemma: If find_first_match finds a position, no earlier position matches *)
Lemma find_first_match_is_first :
  forall r s fuel pos,
    find_first_match r s fuel = Some pos ->
    forall p, (p < pos)%nat -> (length s - fuel <= p)%nat -> can_apply_at r s p = false.
Proof.
  intros r s fuel.
  generalize dependent s.
  induction fuel as [| fuel' IH]; intros s pos H p H_less H_ge.
  - (* Base case *)
    simpl in H. discriminate H.
  - (* Inductive case *)
    simpl in H.
    destruct (is_Some (apply_rule_at r s (length s - S fuel')%nat)) eqn:E.
    + (* Match found at (length s - S fuel') *)
      injection H as H_eq.
      subst pos.
      (* p < length s - S fuel', but p >= length s - S fuel', contradiction *)
      assert (H_eq_p: (p = length s - S fuel' \/ p < length s - S fuel')%nat).
      { lia. }
      destruct H_eq_p as [H_eq | H_lt].
      * (* p = length s - S fuel' *)
        subst p.
        lia. (* Contradiction: p < pos but p = pos *)
      * (* p < length s - S fuel' *)
        (* But p >= length s - S fuel', contradiction *)
        lia.
    + (* No match at (length s - S fuel'), continue searching *)
      (* Need to show that can_apply_at at (length s - S fuel') is false *)
      assert (H_range: (length s - S fuel' <= p)%nat /\ (p < pos)%nat).
      { lia. }
      destruct H_range as [H_ge' H_lt'].
      assert (H_eq_or: (p = length s - S fuel' \/ p > length s - S fuel')%nat).
      { lia. }
      destruct H_eq_or as [H_eq | H_gt].
      * (* p = length s - S fuel' *)
        subst p.
        (* apply_rule_at returned None, so can_apply_at must be false *)
        unfold is_Some in E.
        destruct (apply_rule_at r s (length s - S fuel')%nat) eqn:E_apply; try discriminate.
        unfold apply_rule_at in E_apply.
        unfold can_apply_at.
        destruct (context_matches (context r) s (length s - S fuel')%nat) eqn:E_ctx.
        ** (* context matches *)
           destruct (pattern_matches_at (pattern r) s (length s - S fuel')%nat) eqn:E_pat.
           *** (* pattern also matches - but apply_rule_at returned None, contradiction *)
               discriminate E_apply.
           *** (* pattern doesn't match - can_apply_at returns false *)
               reflexivity.
        ** (* context doesn't match - can_apply_at returns false *)
           reflexivity.
      * (* p > length s - S fuel' *)
        apply (IH s pos H p H_lt').
        lia.
Qed.

(** Lemma: If can_apply_at is true at pos and false before, find_first_match finds pos *)
Lemma find_first_match_finds_first_true :
  forall r s fuel pos,
    (pos < length s)%nat ->
    (length s - fuel <= pos)%nat ->
    can_apply_at r s pos = true ->
    (forall p, (length s - fuel <= p)%nat -> (p < pos)%nat -> can_apply_at r s p = false) ->
    find_first_match r s fuel = Some pos.
Proof.
  intros r s fuel pos H_pos_valid H_fuel_bound H_can_apply H_first.

  (* Induction on fuel *)
  induction fuel as [| fuel' IH].
  - (* Base case: fuel = 0 *)
    (* length s - 0 <= pos, so length s <= pos *)
    simpl in H_fuel_bound.
    (* But pos < length s, contradiction *)
    lia.

  - (* Inductive case: fuel = S fuel' *)
    simpl.
    (* Current position: length s - S fuel' *)
    destruct (Nat.eq_dec pos (length s - S fuel')) as [H_pos_eq | H_pos_ne].

    + (* Case 1: pos = length s - S fuel', we should find it immediately *)
      subst pos.
      (* is_Some (apply_rule_at ...) = true because can_apply_at is true *)
      assert (H_is_some_true: is_Some (apply_rule_at r s (length s - S fuel')%nat) = true).
      { unfold is_Some.
        unfold apply_rule_at.
        unfold can_apply_at in H_can_apply.
        destruct (context_matches (context r) s (length s - S fuel')%nat) eqn:E_ctx;
        destruct (pattern_matches_at (pattern r) s (length s - S fuel')%nat) eqn:E_pat;
        try discriminate H_can_apply.
        reflexivity. }
      rewrite H_is_some_true.
      reflexivity.

    + (* Case 2: pos ≠ length s - S fuel' *)
      (* Since length s - S fuel' <= pos (from H_fuel_bound) and pos ≠ length s - S fuel',
         we have length s - S fuel' < pos *)
      assert (H_pos_gt: (length s - S fuel' < pos)%nat).
      { lia. }

      (* The current position (length s - S fuel') is in the range and < pos,
         so by H_first, can_apply_at must be false there *)
      assert (H_current_false: can_apply_at r s (length s - S fuel')%nat = false).
      { apply H_first.
        - (* Show length s - S fuel' >= length s - S fuel' *)
          lia.
        - (* Show length s - S fuel' < pos *)
          exact H_pos_gt. }

      (* is_Some (apply_rule_at ...) = false when can_apply_at is false *)
      assert (H_is_some_false: is_Some (apply_rule_at r s (length s - S fuel')%nat) = false).
      { unfold is_Some, apply_rule_at.
        unfold can_apply_at in H_current_false.
        destruct (context_matches (context r) s (length s - S fuel')%nat) eqn:E_ctx.
        - (* context matches *)
          simpl in H_current_false.
          destruct (pattern_matches_at (pattern r) s (length s - S fuel')%nat) eqn:E_pat.
          + (* pattern matches - contradiction *)
            discriminate H_current_false.
          + (* pattern doesn't match *)
            reflexivity.
        - (* context doesn't match *)
          reflexivity. }

      rewrite H_is_some_false.

      (* Use IH on fuel' *)
      apply IH.
      * (* Show length s - fuel' <= pos *)
        (* We have length s - S fuel' < pos from H_pos_gt *)
        (* length s - fuel' = length s - S fuel' + 1 when non-truncating *)
        (* So length s - S fuel' < pos implies length s - fuel' <= pos *)
        destruct (le_lt_dec (S fuel') (length s)) as [H_fuel_ok | H_fuel_large].
        ** (* S fuel' <= length s, non-truncating case *)
           (* length s - fuel' = (length s - S fuel') + 1 *)
           (* Since length s - S fuel' < pos, we have (length s - S fuel') + 1 <= pos *)
           lia.
        ** (* S fuel' > length s, both truncate to 0 *)
           assert (H_zero: (length s - fuel' = 0)%nat) by lia.
           rewrite H_zero.
           lia.
      * (* Show all positions in [length s - fuel', pos) have can_apply_at false *)
        intros p H_p_ge H_p_lt.
        apply H_first.
        ** (* Show length s - S fuel' <= p *)
           (* We have length s - fuel' <= p *)
           (* Since S fuel' > fuel', we have length s - S fuel' < length s - fuel' *)
           (* Therefore length s - S fuel' <= p *)
           transitivity (length s - fuel')%nat.
           *** (* length s - S fuel' <= length s - fuel' *)
               destruct (le_lt_dec (S fuel') (length s)) as [H_fuel_ok | H_fuel_large].
               **** lia.
               **** (* S fuel' > length s, both sides truncate to 0 *)
                    assert (H1: (length s - S fuel' = 0)%nat) by lia.
                    assert (H2: (length s - fuel' = 0)%nat) by lia.
                    rewrite H1, H2. lia.
           *** exact H_p_ge.
        ** exact H_p_lt.
Qed.

(** Lemma: find_first_match_from returns positions within bounds *)
Lemma find_first_match_from_upper_bound :
  forall r s start_pos n pos,
    find_first_match_from r s start_pos n = Some pos ->
    (pos < start_pos + n)%nat.
Proof.
  intros r s start_pos n.
  generalize dependent start_pos.
  induction n as [| n' IH]; intros start_pos pos H.
  - simpl in H. discriminate.
  - simpl in H.
    destruct (can_apply_at r s start_pos) eqn:E.
    + injection H as H_eq. subst. lia.
    + apply IH in H. lia.
Qed.

(** Lemma: find_first_match_from is "first" - no earlier position matches *)
Lemma find_first_match_from_is_first :
  forall r s start_pos n pos,
    find_first_match_from r s start_pos n = Some pos ->
    forall p, (start_pos <= p)%nat -> (p < pos)%nat -> can_apply_at r s p = false.
Proof.
  intros r s start_pos n.
  generalize dependent start_pos.
  induction n as [| n' IH]; intros start_pos pos H p H_ge H_lt.
  - simpl in H. discriminate.
  - simpl in H.
    destruct (can_apply_at r s start_pos) eqn:E.
    + (* Match found at start_pos *)
      injection H as H_eq. subst.
      (* p < pos = start_pos, but p >= start_pos, contradiction *)
      lia.
    + (* No match at start_pos, continue *)
      assert (H_eq_or: (p = start_pos \/ p > start_pos)%nat).
      { lia. }
      destruct H_eq_or as [H_eq | H_gt].
      * subst. exact E.
      * apply (IH (S start_pos) pos H p); lia.
Qed.

(** Helper: find_first_match_from returns positions where can_apply_at is true *)
Lemma find_first_match_from_implies_can_apply :
  forall r s start_pos n pos,
    find_first_match_from r s start_pos n = Some pos ->
    can_apply_at r s pos = true.
Proof.
  intros r s start_pos n.
  generalize dependent start_pos.
  induction n as [| n' IH]; intros start_pos pos H.
  - (* Base case: n = 0 *)
    simpl in H. discriminate.
  - (* Inductive case *)
    simpl in H.
    destruct (can_apply_at r s start_pos) eqn:E.
    + (* Found match at start_pos *)
      injection H as H_eq. subst. exact E.
    + (* Continue search *)
      apply (IH (S start_pos) pos H).
Qed.

(** Generalized equivalence lemma with arbitrary fuel and start position *)
Lemma find_first_match_equiv_general :
  forall r s fuel start_pos,
    wf_rule r ->
    start_pos = (length s - fuel)%nat ->
    (fuel <= length s)%nat ->
    find_first_match r s fuel = find_first_match_from r s start_pos (fuel + 1)%nat.
Proof.
  intros r s fuel start_pos H_wf H_start H_fuel_bound.
  subst start_pos.

  (* Induction on fuel *)
  induction fuel as [| fuel' IH].

  - (* Base case: fuel = 0 *)
    simpl.
    (* LHS: None *)
    (* RHS: find_first_match_from r s (length s) 1 *)
    assert (H_zero: (length s - 0 = length s)%nat) by lia.
    rewrite H_zero.
    simpl.
    (* Position length s is out of bounds, so can_apply_at returns false *)
    assert (H_out_of_bounds: can_apply_at r s (length s) = false).
    { apply can_apply_at_beyond_length; try assumption. lia. }
    rewrite H_out_of_bounds.
    reflexivity.

  - (* Inductive case: fuel = S fuel' *)
    simpl.
    (* Both check position (length s - S fuel') *)
    (* Note: S fuel' + 1 simplifies to S (S fuel') *)

    (* Case split on whether rule applies at current position *)
    destruct (can_apply_at r s (length s - S fuel')%nat) eqn:E_apply.

    + (* Rule applies at current position *)
      (* LHS: is_Some (apply_rule_at ...) should be true *)
      unfold is_Some, apply_rule_at, can_apply_at in *.
      destruct (context_matches (context r) s (length s - S fuel')%nat) eqn:E_ctx;
      destruct (pattern_matches_at (pattern r) s (length s - S fuel')%nat) eqn:E_pat;
      try discriminate E_apply.
      reflexivity.

    + (* Rule doesn't apply at current position *)
      (* LHS: is_Some (apply_rule_at ...) should be false *)
      (* RHS: find_first_match_from recurses *)
      unfold is_Some, apply_rule_at in *.
      unfold can_apply_at in E_apply.

      (* Both functions recurse to next position *)
      (* Need to relate: find_first_match r s fuel'
                    and: find_first_match_from r s (S (length s - S fuel')) (S fuel') *)

      (* Show S (length s - S fuel') = length s - fuel' *)
      assert (H_pos_shift: (S (length s - S fuel') = length s - fuel')%nat).
      { destruct (le_lt_dec (S fuel') (length s)) as [H_ok | H_large].
        - lia.
        - (* S fuel' > length s contradicts H_fuel_bound *)
          lia. }

      (* Rewrite based on can_apply_at being false *)
      destruct (context_matches (context r) s (length s - S fuel')%nat) eqn:E_ctx.
      * (* Context matches but pattern doesn't *)
        destruct (pattern_matches_at (pattern r) s (length s - S fuel')%nat) eqn:E_pat.
        ** (* Both true - contradiction with E_apply *)
           simpl in E_apply. discriminate E_apply.
        ** (* Context true, pattern false *)
           rewrite H_pos_shift.
           rewrite IH; try lia.
           reflexivity.
      * (* Context doesn't match *)
        rewrite H_pos_shift.
        rewrite IH; try lia.
        reflexivity.
Qed.

(** Lemma: find_first_match and find_first_match_from starting at 0 are equivalent *)
Lemma find_first_match_equiv_from_zero :
  forall r s,
    wf_rule r ->
    find_first_match r s (length s) = find_first_match_from r s 0 (length s - 0 + 1)%nat.
Proof.
  intros r s H_wf.
  (* Simplify: length s - 0 + 1 = S (length s) *)
  assert (H_simpl: (length s - 0 + 1 = S (length s))%nat) by lia.
  rewrite H_simpl.

  (* Use generalized equivalence with fuel = length s *)
  (* Note: length s - length s = 0, and length s + 1 = S (length s) *)
  assert (H_eq: find_first_match r s (length s) =
                find_first_match_from r s (length s - length s)%nat (length s + 1)%nat).
  { apply find_first_match_equiv_general; try assumption.
    - reflexivity.
    - lia. }

  (* Simplify: length s - length s = 0, length s + 1 = S (length s) *)
  assert (H_zero: (length s - length s = 0)%nat) by lia.
  assert (H_succ: (length s + 1 = S (length s))%nat) by lia.
  rewrite H_zero, H_succ in H_eq.
  exact H_eq.
Qed.

(** Lemma: Reverse direction - from find_first_match_from to find_first_match *)
Lemma find_first_match_equiv_from_zero_reverse :
  forall r s pos,
    wf_rule r ->
    find_first_match_from r s 0 (length s - 0 + 1)%nat = Some pos ->
    find_first_match r s (length s) = Some pos.
Proof.
  intros r s pos H_wf H_from.
  assert (H_equiv: find_first_match r s (length s) =
                   find_first_match_from r s 0 (length s - 0 + 1)%nat).
  { apply find_first_match_equiv_from_zero. exact H_wf. }
  rewrite H_equiv.
  exact H_from.
Qed.

(** Lemma: Bidirectional equivalence between find_first_match and find_first_match_from from 0 *)
Lemma find_first_match_from_zero_bidirectional :
  forall r s,
    wf_rule r ->
    find_first_match r s (length s) = find_first_match_from r s 0 (length s - 0 + 1)%nat.
Proof.
  intros r s H_wf.
  apply find_first_match_equiv_from_zero.
  exact H_wf.
Qed.

(** Helper lemma: If find_first_match_from returns None, then all positions in the range fail *)
Lemma find_first_match_from_none_implies_all_fail :
  forall r s start_pos remaining,
    wf_rule r ->
    find_first_match_from r s start_pos remaining = None ->
    forall p, (start_pos <= p < start_pos + remaining)%nat ->
    can_apply_at r s p = false.
Proof.
  intros r s start_pos remaining H_wf.
  revert start_pos.
  induction remaining as [| remaining' IH]; intros start_pos H_none p H_range.
  - (* Base case: remaining = 0 *)
    (* Range [start_pos, start_pos + 0) is empty, so H_range is contradictory *)
    lia.
  - (* Inductive case: remaining = S remaining' *)
    simpl in H_none.
    destruct (can_apply_at r s start_pos) eqn:E_start.
    + (* can_apply_at r s start_pos = true *)
      (* But find_first_match_from would return Some start_pos, contradicting H_none *)
      discriminate H_none.
    + (* can_apply_at r s start_pos = false *)
      (* The recursive call returned None *)
      (* Check if p = start_pos or p > start_pos *)
      destruct (Nat.eq_dec p start_pos) as [H_eq | H_neq].
      * (* p = start_pos *)
        subst p.
        exact E_start.
      * (* p <> start_pos, so start_pos < p *)
        (* Use IH on the tail range [start_pos + 1, start_pos + 1 + remaining') *)
        assert (H_p_range': (S start_pos <= p < S start_pos + remaining')%nat) by lia.
        apply (IH (S start_pos) H_none p H_p_range').
Qed.

(** Helper: If find_first_match with large fuel returns None, then so does find_first_match at length s *)
Lemma find_first_match_large_fuel_implies_length :
  forall r s fuel,
    wf_rule r ->
    (fuel >= length s)%nat ->
    find_first_match r s fuel = None ->
    find_first_match r s (length s) = None.
Proof.
  intros r s fuel H_wf H_fuel_ge H_none.
  (* Both search the same range starting from 0 when fuel >= length s *)
  destruct (find_first_match r s (length s)) eqn:E_len; [| reflexivity].
  (* Suppose find_first_match r s (length s) = Some n *)
  exfalso.
  (* Then n is in range [0, length s) *)
  assert (H_range: (length s - length s <= n < length s)%nat).
  { eapply find_first_match_search_range; eauto. }
  assert (H_start: (length s - length s = 0)%nat) by lia.
  rewrite H_start in H_range.
  (* So 0 <= n < length s *)
  (* Also, find_first_match r s fuel searches from (length s - fuel) *)
  assert (H_fuel_start: (length s - fuel = 0)%nat) by lia.
  (* Convert both to find_first_match_from *)
  assert (H_equiv_len: find_first_match r s (length s) =
                       find_first_match_from r s 0 (S (length s))).
  {
    assert (H_tmp: find_first_match r s (length s) =
                   find_first_match_from r s 0 (length s - 0 + 1)%nat).
    { apply find_first_match_equiv_from_zero. exact H_wf. }
    rewrite H_tmp.
    f_equal. lia.
  }
  rewrite H_equiv_len in E_len.
  (* Now we have: find_first_match_from r s 0 (S (length s)) = Some n *)
  (* And: find_first_match r s fuel = None *)
  (* Need to show: find_first_match r s fuel would find n, contradicting H_none *)

  (* We know can_apply_at r s n = true *)
  assert (H_n_applies: can_apply_at r s n = true).
  { eapply find_first_match_from_implies_can_apply. exact E_len. }

  (* Prove by induction on fuel that if fuel >= length s and can_apply_at r s n = true
     for some n < length s, then find_first_match r s fuel <> None *)
  clear E_len H_equiv_len H_start.
  revert H_fuel_ge H_none n H_range H_n_applies.

  induction fuel as [| fuel' IH]; intros H_fuel_ge H_none n H_n_range H_n_applies.
  - (* fuel = 0 *)
    (* 0 >= length s, but we have n < length s, so length s > 0 *)
    (* This means 0 >= length s > 0, contradiction *)
    exfalso. lia.

  - (* fuel = S fuel' *)
    simpl in H_none.
    (* find_first_match checks position (length s - S fuel') *)
    destruct (is_Some (apply_rule_at r s (length s - S fuel')%nat)) eqn:E_check.
    + (* Match found: find_first_match would return Some, contradicting H_none *)
      discriminate H_none.
    + (* No match at current position, recursed to fuel' *)
      (* Check if n is the position we just checked *)
      assert (H_fuel_start': (length s - S fuel' = 0)%nat) by lia.
      destruct (Nat.eq_dec n (length s - S fuel')%nat) as [H_n_eq | H_n_neq].
      * (* n = length s - S fuel' *)
        (* But we checked this position and found no match (E_check = false) *)
        (* Yet can_apply_at r s n = true, contradiction *)
        rewrite H_n_eq in H_n_applies.
        unfold is_Some in E_check.
        destruct (apply_rule_at r s (length s - S fuel')%nat) eqn:E_apply; [discriminate E_check |].
        (* apply_rule_at returned None, but can_apply_at should be false then *)
        unfold apply_rule_at in E_apply.
        unfold can_apply_at in H_n_applies.
        destruct (context_matches (context r) s (length s - S fuel')%nat) eqn:E_ctx;
        destruct (pattern_matches_at (pattern r) s (length s - S fuel')%nat) eqn:E_pat;
        try discriminate E_apply; try discriminate H_n_applies.
      * (* n <> length s - S fuel' *)
        (* Use IH if fuel' >= length s *)
        destruct (le_lt_dec (length s) fuel') as [H_fuel'_ge | H_fuel'_lt].
        ** (* fuel' >= length s: apply IH *)
           eapply IH; eauto; lia.
        ** (* fuel' < length s: analyze this case *)
           (* We have: S fuel' >= length s and fuel' < length s *)
           (* So: length s <= S fuel' and fuel' < length s *)
           (* Thus: length s = S fuel' or length s < S fuel' *)
           (* Since fuel' < length s, we have length s = S fuel' *)
           assert (H_len_eq: length s = S fuel') by lia.
           (* So length s - S fuel' = 0 *)
           rewrite H_len_eq in H_fuel_start'.
           (* And n < length s = S fuel' *)
           (* Since n <> 0 (= length s - S fuel'), and n < S fuel', we have 0 < n < S fuel' *)
           (* But fuel' = length s - 1, so the recursive call with fuel' doesn't cover n >= 1 *)
           (* Actually, let me reconsider: find_first_match r s fuel' searches from length s - fuel' *)
           (* length s - fuel' = S fuel' - fuel' = 1 when length s = S fuel' *)
           (* So it searches from position 1 onward *)
           (* If n >= 1, it's in range. If n = 0, we already ruled that out *)
           rewrite H_len_eq in H_n_range.
           assert (H_n_ge_1: (1 <= n)%nat) by lia.
           (* Now fuel' searches from position (S fuel' - fuel') = 1 *)
           (* And n >= 1, so n is checked by fuel' *)
           (* Apply IH with adjusted bounds *)
           assert (H_fuel'_ge': (fuel' >= length s - 1)%nat) by lia.
           (* But IH requires fuel' >= length s, which we don't have *)
           (* Different approach: show directly that fuel' finds n *)
           exfalso.
           (* We need to show find_first_match r s fuel' would find n *)
           (* fuel' searches from (length s - fuel') = (S fuel' - fuel') = 1 *)
           (* And n >= 1 and n < S fuel', so n is in range [1, S fuel') *)
           (* Use contrapositive of find_first_match_finds_first_true *)
           assert (H_in_range: (length s - fuel' <= n < length s)%nat) by lia.
           (* If can_apply_at r s n = true and n is in search range, *)
           (* then either find_first_match finds n or something earlier *)
           (* To use find_first_match_finds_first_true, we need to show no earlier matches *)
           (* But we don't know that, so let's use the simpler fact: *)
           (* If there's ANY match in the search range, find_first_match cannot be None *)
           (* We'll reason directly about the recursive definition *)
           assert (H_fuel'_bound: (length s - fuel' <= n)%nat) by lia.
           (* Since fuel' = length s - 1, we have length s - fuel' = 1 *)
           (* And since n >= 1, the search covers n *)
           (* find_first_match with fuel' will check positions from length s - fuel' to length s *)
           (* Since can_apply_at r s n = true and n is in this range, *)
           (* find_first_match must find n or something earlier *)
           (* Derive contradiction using simpl on the definition *)
           clear IH H_fuel'_ge'.
           generalize dependent H_none.
           generalize dependent H_n_applies.
           generalize dependent H_n_range.
           generalize dependent n.
           revert H_len_eq.

           (* Use the fact that n is in range and can_apply *)
           {
             induction fuel' as [| fuel'' IH']; intros H_len_eq n H_n_neq H_n_ge1 H_in_range H_fuel_bound H_n_lt H_n_applies H_ffm_none.
             - (* fuel' = 0: length s = S 0 = 1, so n < 1, so n = 0 *)
               assert (H_n_eq: n = 0) by lia.
               subst n.
               (* But length s - 0 = 1, so n = 0 < 1 is not in range [1, 1) - empty range *)
               lia.
             - (* fuel' = S fuel'': length s = S (S fuel'') *)
               simpl in H_ffm_none.
               (* Check if n is the current position *)
               destruct (Nat.eq_dec n (length s - S (S fuel''))%nat) as [H_n_is_curr | H_n_not_curr].
               + (* n = length s - S (S fuel'') *)
                 rewrite H_n_is_curr in H_n_applies.
                 (* can_apply_at at this position is true, so apply_rule_at must return Some *)
                 (* But from H_none, we know the recursive structure shows it didn't find a match here *)
                 (* Simplify H_none to see what happened at this position *)
                 (* Both can_apply_at r s n = true and find_first_match returned None *)
                 (* can_apply_at r s n = true means the rule CAN apply at position n *)
                 (* But find_first_match r s (S (S fuel'')) checked position n (= length s - S (S fuel'')) *)
                 (* and didn't find it (returned None) *)
                 (* This is a contradiction *)
                 (* Use can_apply_at to show is_Some must be true *)
                 assert (H_must_match: is_Some (apply_rule_at r s (length s - S (S fuel''))%nat) = true).
                 { unfold is_Some. unfold can_apply_at in H_n_applies.
                   unfold apply_rule_at.
                   destruct (context_matches (context r) s (length s - S (S fuel''))%nat); [| simpl in H_n_applies; congruence].
                   destruct (pattern_matches_at (pattern r) s (length s - S (S fuel''))%nat); [| simpl in H_n_applies; congruence].
                   reflexivity. }
                 (* Now H_must_match says is_Some ... = true *)
                 (* H_none (after simpl at line 960) has the form (if is_Some ... then ... else ...) = None *)
                 (* Use congruence to derive the contradiction *)
                 congruence.
               + (* n <> length s - S (S fuel'') *)
                 (* n must be in the range searched by the recursive call *)
                 destruct (is_Some (apply_rule_at r s (length s - S (S fuel''))%nat)) eqn:E_check2.
                 * (* Found something at current position *)
                   congruence.
                 * (* Continue to fuel'' *)
                   (* find_first_match r s (S fuel'') = None (from H_none) *)
                   (* By H_len_eq: length s = S (S fuel''), so length s - S fuel'' > 0 *)
                   (* Convert find_first_match to find_first_match_from *)
                   (* First prove the preconditions for find_first_match_equiv_general *)
                   assert (H_fuel''_le: (S fuel'' <= length s)%nat).
                   { rewrite H_len_eq. lia. }
                   assert (H_start_eq: (length s - S fuel'' = length s - S fuel'')%nat).
                   { reflexivity. }
                   assert (H_equiv_fuel'': find_first_match r s (S fuel'') =
                           find_first_match_from r s (length s - S fuel'') (S fuel'' + 1)).
                   { apply find_first_match_equiv_general; auto. }
                   (* After simpl at line 960, and destruct at line 986 with E_check2 = false, *)
                   (* H_ffm_none directly has the type: find_first_match r s (S fuel'') = None *)
                   (* Convert find_first_match to find_first_match_from using the equivalence *)
                   assert (H_from_none: find_first_match_from r s (length s - S fuel'') (S fuel'' + 1) = None).
                   { rewrite <- H_equiv_fuel''. exact H_ffm_none. }
                   (* Now H_from_none: find_first_match_from r s (length s - S fuel'') (S fuel'' + 1) = None *)
                   (* This means all positions in [length s - S fuel'', length s - S fuel'' + (S fuel'' + 1)) have can_apply_at = false *)
                   (* Use find_first_match_from_none_implies_all_fail *)
                   assert (H_all_fail: forall p, (length s - S fuel'' <= p < length s - S fuel'' + (S fuel'' + 1))%nat -> can_apply_at r s p = false).
                   { intros p H_p_range.
                     eapply (find_first_match_from_none_implies_all_fail r s (length s - S fuel'') (S fuel'' + 1)); eauto. }
                   (* By H_len_eq: length s - S fuel'' + (S fuel'' + 1) > length s, but we need it = length s *)
                   (* Actually: (length s - S fuel'') + (S fuel'' + 1) = length s - S fuel'' + S fuel'' + 1 *)
                   (* = length s + 1 (if length s >= S fuel'') *)
                   (* But we want the range [start, length s), so we should use (S fuel'' + 1) - 1 = S fuel'' *)
                   (* Let me directly prove the range property for n *)
                   (* We have: length s - S fuel'' <= p < length s - S fuel'' + (S fuel'' + 1) *)
                   (* And: length s = S (S fuel''), so length s - S fuel'' = S (S fuel'') - S fuel'' *)
                   (* And: (S (S fuel'')) - S fuel'' + (S fuel'' + 1) = something >= S (S fuel'') *)
                   (* So the upper bound covers at least to length s *)
                   (* Simplify by noting that H_all_fail gives us can_apply_at r s p = false for all p in the range *)
                   (* We need can_apply_at r s n = false, and we know length s - S fuel'' <= n < length s from H_in_range *)
                   (* And the search range [length s - S fuel'', ...) definitely includes n *)
                   (* Also, length s - S fuel'' <= n since n is in the search range *)
                   (* From H_n_range: 0 <= n < length s *)
                   (* From H_len_eq: length s = S (S fuel'') *)
                   (* So length s - S fuel'' = S (S fuel'') - S fuel'' >= 1 *)
                   (* Since n <> length s - S (S fuel'') = 0, we have n >= 1 *)
                   assert (H_n_ge_start: (length s - S fuel'' <= n)%nat).
                   { rewrite H_len_eq. lia. }
                   (* Apply H_all_fail to n *)
                   assert (H_n_fail: can_apply_at r s n = false).
                   { apply H_all_fail. lia. }
                   (* But H_n_applies says can_apply_at r s n = true *)
                   congruence.
           }
Qed.
