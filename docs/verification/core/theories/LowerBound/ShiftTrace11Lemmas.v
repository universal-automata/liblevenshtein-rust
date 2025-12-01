(** * Shift Trace (1,1) Validity and NoDup Lemmas

    This module provides validity and NoDup preservation lemmas for shift_trace_11.

    Part of: Liblevenshtein.Core

    Decomposed from: TraceLowerBound.v (lines 1230-1580)
*)

From Stdlib Require Import String List Arith Ascii Bool Nat Lia.
Import ListNotations.

From Liblevenshtein.Core Require Import LowerBound.Definitions.
From Liblevenshtein.Core Require Import LowerBound.HasPredicates.
From Liblevenshtein.Core Require Import LowerBound.ShiftTrace11.
From Liblevenshtein.Core Require Import LowerBound.NoDupPreservation.

(** * Length Lemmas *)

(** Length of shift_trace_11 when (1,1) is present and NoDup holds *)
Lemma shift_trace_11_length : forall T,
  NoDup (touched_in_A T) ->
  NoDup (touched_in_B T) ->
  has_pair_11 T = true ->
  length (shift_trace_11 T) = length T - 1.
Proof.
  intros T HnodupA HnodupB H11.
  rewrite shift_trace_11_length_general.
  assert (H_count: count_11 T = 1).
  { pose proof (count_11_le_1_aux T HnodupA HnodupB) as Hle.
    (* count_11 T >= 1 because has_pair_11 T = true *)
    assert (Hge: count_11 T >= 1).
    { unfold has_pair_11 in H11. rewrite existsb_exists in H11.
      destruct H11 as [[i' j'] [Hin Hcheck]].
      apply andb_prop in Hcheck. destruct Hcheck as [Hi' Hj'].
      apply Nat.eqb_eq in Hi'. apply Nat.eqb_eq in Hj'. subst.
      clear -Hin.
      induction T as [| [i j] rest IH].
      - destruct Hin.
      - simpl count_11.
        destruct ((i =? 1) && (j =? 1)) eqn:E.
        + lia.
        + destruct Hin as [Heq | Hin'].
          * injection Heq as Hi Hj. subst.
            simpl in E. discriminate.
          * assert (H := IH Hin'). lia. }
    lia. }
  rewrite H_count. reflexivity.
Qed.

(** * Shift Trace Inverse Lemmas *)

(** Helper: given (i', j') in shift_trace_11 L, there exists (i'', j'') in L
    such that i' = i'' - 1 and j' = j'' - 1, and (i'', j'') ≠ (1, 1) *)
Lemma shift_trace_11_in_original : forall L i' j',
  (forall p, In p L -> fst p = 1 -> snd p = 1 -> False) ->
  In (i', j') (shift_trace_11 L) ->
  exists i'' j'', In (i'', j'') L /\
                  (i'' =? 1) && (j'' =? 1) = false /\
                  i' = i'' - 1 /\ j' = j'' - 1.
Proof.
  induction L as [| [i'' j''] L' IH']; intros i' j' Hno11 Hin.
  - simpl in Hin. destruct Hin.
  - simpl shift_trace_11 in Hin.
    destruct ((i'' =? 1) && (j'' =? 1)) eqn:E'.
    + (* (i'', j'') = (1,1), but this contradicts Hno11 *)
      apply andb_prop in E'. destruct E' as [Ei'' Ej''].
      apply Nat.eqb_eq in Ei''. apply Nat.eqb_eq in Ej''. subst.
      exfalso. apply (Hno11 (1, 1)).
      * left. reflexivity.
      * reflexivity.
      * reflexivity.
    + simpl in Hin.
      destruct Hin as [Heq | Hin'].
      * injection Heq as Hi' Hj'.
        exists i'', j''. split; [left; reflexivity | split; [exact E' | split; [symmetry; exact Hi' | symmetry; exact Hj']]].
      * assert (Hno11': forall p, In p L' -> fst p = 1 -> snd p = 1 -> False).
        { intros p Hp Hfst Hsnd. apply Hno11 with p; auto. right. exact Hp. }
        destruct (IH' i' j' Hno11' Hin') as [i''' [j''' [Hin''' [Hneq [Hi''' Hj''']]]]].
        exists i''', j'''. split; [right; exact Hin''' | split; [exact Hneq | split; [exact Hi''' | exact Hj''']]].
Qed.

(** * Validity of shift_trace_11 *)

(** Validity of shift_trace_11 - requires NoDup *)
Lemma shift_trace_11_valid : forall lenA lenB T,
  NoDup (touched_in_A T) ->
  NoDup (touched_in_B T) ->
  has_pair_11 T = true ->
  simple_valid_trace (S lenA) (S lenB) T = true ->
  simple_valid_trace lenA lenB (shift_trace_11 T) = true.
Proof.
  intros lenA lenB T.
  induction T as [| [i j] rest IH].
  - intros _ _ H11 _. simpl in H11. discriminate.
  - intros HnodupA HnodupB H11 Hvalid.
    simpl touched_in_A in HnodupA. simpl touched_in_B in HnodupB.
    inversion HnodupA as [| x xs Hnot_in_A Hnodup_restA Heq1]. subst.
    inversion HnodupB as [| y ys Hnot_in_B Hnodup_restB Heq2]. subst.

    unfold simple_valid_trace in Hvalid. simpl forallb in Hvalid.
    apply andb_prop in Hvalid. destruct Hvalid as [Hhead Hrest_valid].

    simpl shift_trace_11.
    destruct ((i =? 1) && (j =? 1)) eqn:E.
    + (* (i,j) = (1,1), skipped - recurse on rest *)
      apply andb_prop in E. destruct E as [Ei Ej].
      apply Nat.eqb_eq in Ei. apply Nat.eqb_eq in Ej. subst.
      clear IH.
      (* rest has no (1,1) because 1 is not in touched_in_A rest *)
      assert (Hno11_rest: forall p, In p rest -> fst p = 1 -> snd p = 1 -> False).
      { intros [ia ja] Hpin Hfst Hsnd. simpl in Hfst, Hsnd. subst.
        eapply not_in_touched_A; eauto. }

      unfold simple_valid_trace. rewrite forallb_forall.
      intros [i' j'] Hin'.
      destruct (shift_trace_11_in_original rest i' j' Hno11_rest Hin')
        as [i'' [j'' [Hin'' [Hneq [Hi' Hj']]]]].
      subst i' j'.

      unfold simple_valid_trace in Hrest_valid.
      rewrite forallb_forall in Hrest_valid.
      specialize (Hrest_valid (i'', j'') Hin'').
      apply andb_prop in Hrest_valid. destruct Hrest_valid as [Hv1 Hj''_le].
      apply andb_prop in Hv1. destruct Hv1 as [Hv2 Hj''_ge].
      apply andb_prop in Hv2. destruct Hv2 as [Hi''_ge Hi''_le].
      assert (Hi''_ge': i'' >= 1).
      { destruct i''; simpl in Hi''_ge; [discriminate | lia]. }
      apply Nat.leb_le in Hi''_le.
      assert (Hj''_ge': j'' >= 1).
      { destruct j''; simpl in Hj''_ge; [discriminate | lia]. }
      apply Nat.leb_le in Hj''_le.

      assert (Hi''_neq1: i'' <> 1) by (eapply not_in_touched_A; eauto).
      assert (Hj''_neq1: j'' <> 1) by (eapply not_in_touched_B; eauto).

      (* i'' >= 2 and j'' >= 2, so i'' - 1 >= 1 and j'' - 1 >= 1 *)
      assert (Hi''_ge2: i'' >= 2) by lia.
      assert (Hj''_ge2: j'' >= 2) by lia.
      apply andb_true_intro. split.
      apply andb_true_intro. split.
      apply andb_true_intro. split.
      * destruct i'' as [| [| i''']]; [lia | lia | simpl; reflexivity].
      * apply Nat.leb_le. lia.
      * destruct j'' as [| [| j''']]; [lia | lia | simpl; reflexivity].
      * apply Nat.leb_le. lia.
    + (* (i,j) ≠ (1,1), included as (i-1, j-1) *)
      assert (Hrest11: has_pair_11 rest = true).
      { unfold has_pair_11 in H11. simpl existsb in H11.
        rewrite E in H11. unfold has_pair_11. exact H11. }

      unfold simple_valid_trace. simpl forallb.
      apply andb_true_intro. split.
      * (* Show (i-1, j-1) is valid *)
        apply andb_prop in Hhead. destruct Hhead as [Hv1 Hj_le].
        apply andb_prop in Hv1. destruct Hv1 as [Hv2 Hj_ge].
        apply andb_prop in Hv2. destruct Hv2 as [Hi_ge Hi_le].
        assert (Hi_ge': i >= 1).
        { destruct i; simpl in Hi_ge; [discriminate | lia]. }
        apply Nat.leb_le in Hi_le.
        assert (Hj_ge': j >= 1).
        { destruct j; simpl in Hj_ge; [discriminate | lia]. }
        apply Nat.leb_le in Hj_le.

        (* Since (1,1) is in rest, i ≠ 1 and j ≠ 1 by NoDup *)
        assert (Hi_neq1: i <> 1).
        { intro Hsub. subst i.
          assert (H: exists p, In p rest /\ fst p = 1 /\ snd p = 1).
          { clear -Hrest11.
            unfold has_pair_11 in Hrest11.
            rewrite existsb_exists in Hrest11.
            destruct Hrest11 as [[i' j'] [Hin Hcheck]].
            apply andb_prop in Hcheck. destruct Hcheck as [Hi' Hj'].
            apply Nat.eqb_eq in Hi'. apply Nat.eqb_eq in Hj'. subst.
            exists (1, 1). split; [exact Hin | split; reflexivity]. }
          destruct H as [[i' j'] [Hin [Hi' Hj']]]. simpl in Hi', Hj'. subst.
          apply Hnot_in_A.
          clear -Hin.
          induction rest as [| [a b] rest' IH'].
          - destruct Hin.
          - destruct Hin as [Heq | Hin'].
            + injection Heq as Ha Hb. subst.
              simpl. left. reflexivity.
            + simpl. right. apply IH'. exact Hin'. }
        assert (Hj_neq1: j <> 1).
        { intro Hsub. subst j.
          assert (H: exists p, In p rest /\ fst p = 1 /\ snd p = 1).
          { clear -Hrest11.
            unfold has_pair_11 in Hrest11.
            rewrite existsb_exists in Hrest11.
            destruct Hrest11 as [[i' j'] [Hin Hcheck]].
            apply andb_prop in Hcheck. destruct Hcheck as [Hi' Hj'].
            apply Nat.eqb_eq in Hi'. apply Nat.eqb_eq in Hj'. subst.
            exists (1, 1). split; [exact Hin | split; reflexivity]. }
          destruct H as [[i' j'] [Hin [Hi' Hj']]]. simpl in Hi', Hj'. subst.
          apply Hnot_in_B.
          clear -Hin.
          induction rest as [| [a b] rest' IH'].
          - destruct Hin.
          - destruct Hin as [Heq | Hin'].
            + injection Heq as Ha Hb. subst.
              simpl. left. reflexivity.
            + simpl. right. apply IH'. exact Hin'. }

        assert (Hi_ge2: i >= 2) by lia.
        assert (Hj_ge2: j >= 2) by lia.
        apply andb_true_intro. split.
        apply andb_true_intro. split.
        apply andb_true_intro. split.
        -- destruct i as [| [| i']]; [lia | lia | simpl; reflexivity].
        -- apply Nat.leb_le. lia.
        -- destruct j as [| [| j']]; [lia | lia | simpl; reflexivity].
        -- apply Nat.leb_le. lia.
      * (* Show shift_trace_11 rest is valid *)
        apply IH.
        -- exact Hnodup_restA.
        -- exact Hnodup_restB.
        -- exact Hrest11.
        -- unfold simple_valid_trace. exact Hrest_valid.
Qed.

(** * NoDup Preservation for shift_trace_11 *)

(** Helper: in_shifted -> in_original for touched_in_A
    Uses Forall bounds instead of validity to avoid parameter scope issues *)
Lemma in_shifted_11_implies_succ_in_original_A : forall T x,
  Forall (fun '(i, j) => i >= 1 /\ j >= 1) T ->
  In x (touched_in_A (shift_trace_11 T)) ->
  In (S x) (touched_in_A T).
Proof.
  induction T as [| [i j] rest IH]; intros x Hbounds Hin.
  - simpl in Hin. destruct Hin.
  - rewrite Forall_cons_iff in Hbounds. destruct Hbounds as [[Hi Hj] Hrest].
    simpl shift_trace_11 in Hin.
    destruct ((i =? 1) && (j =? 1)) eqn:E.
    + (* (i, j) = (1, 1): skipped *)
      simpl touched_in_A. right.
      apply IH; assumption.
    + simpl touched_in_A in Hin.
      destruct Hin as [Heq | Hin'].
      * simpl touched_in_A. left. lia.
      * simpl touched_in_A. right.
        apply IH; assumption.
Qed.

(** Extract bounds from validity *)
Lemma valid_trace_forall_bounds : forall lenA lenB T,
  simple_valid_trace lenA lenB T = true ->
  Forall (fun '(i, j) => i >= 1 /\ j >= 1) T.
Proof.
  intros lenA lenB T Hvalid.
  unfold simple_valid_trace in Hvalid.
  rewrite forallb_forall in Hvalid.
  apply Forall_forall. intros [i j] Hin.
  specialize (Hvalid (i, j) Hin).
  (* Structure: (1 <=? i) && (i <=? lenA) && (1 <=? j) && (j <=? lenB) *)
  apply andb_prop in Hvalid. destruct Hvalid as [Hv1 Hj_upper].
  apply andb_prop in Hv1. destruct Hv1 as [Hv2 Hj_lower].
  apply andb_prop in Hv2. destruct Hv2 as [Hi_lower Hi_upper].
  apply Nat.leb_le in Hi_lower.
  apply Nat.leb_le in Hj_lower.
  split; lia.
Qed.

(** NoDup preservation for shift_trace_11 *)
Lemma shift_trace_11_NoDup_A : forall lenA lenB T,
  simple_valid_trace (S lenA) (S lenB) T = true ->
  NoDup (touched_in_A T) ->
  NoDup (touched_in_A (shift_trace_11 T)).
Proof.
  intros lenA lenB T Hvalid Hnodup.
  assert (Hbounds: Forall (fun '(i, j) => i >= 1 /\ j >= 1) T).
  { apply valid_trace_forall_bounds with (lenA := S lenA) (lenB := S lenB). exact Hvalid. }
  revert Hvalid Hnodup Hbounds.
  induction T as [| [i j] rest IH]; intros Hvalid Hnodup Hbounds.
  - simpl. constructor.
  - simpl touched_in_A in Hnodup.
    inversion Hnodup as [| x xs Hnot_in Hnodup_rest Heq]. subst.
    unfold simple_valid_trace in Hvalid. simpl forallb in Hvalid.
    apply andb_prop in Hvalid. destruct Hvalid as [Hhead Hrest_valid].
    rewrite Forall_cons_iff in Hbounds. destruct Hbounds as [[Hi Hj] Hrest_bounds].
    simpl shift_trace_11.
    destruct ((i =? 1) && (j =? 1)) eqn:E.
    + (* (i, j) = (1, 1): skip it *)
      apply IH.
      * unfold simple_valid_trace. exact Hrest_valid.
      * exact Hnodup_rest.
      * exact Hrest_bounds.
    + (* (i, j) ≠ (1, 1): include shifted *)
      simpl touched_in_A.
      constructor.
      * (* Show i - 1 not in touched_in_A (shift_trace_11 rest) *)
        intro Hcontra.
        assert (Hin_orig: In i (touched_in_A rest)).
        { replace i with (S (i - 1)) by lia.
          apply in_shifted_11_implies_succ_in_original_A.
          - exact Hrest_bounds.
          - exact Hcontra. }
        apply Hnot_in. exact Hin_orig.
      * apply IH.
        -- unfold simple_valid_trace. exact Hrest_valid.
        -- exact Hnodup_rest.
        -- exact Hrest_bounds.
Qed.

Lemma shift_trace_11_NoDup_B : forall lenA lenB T,
  simple_valid_trace (S lenA) (S lenB) T = true ->
  NoDup (touched_in_B T) ->
  NoDup (touched_in_B (shift_trace_11 T)).
Proof.
  intros lenA lenB T Hvalid Hnodup.
  induction T as [| [i j] rest IH].
  - simpl. constructor.
  - simpl touched_in_B in Hnodup.
    inversion Hnodup as [| x xs Hnot_in Hnodup_rest Heq]. subst.
    unfold simple_valid_trace in Hvalid. simpl forallb in Hvalid.
    apply andb_prop in Hvalid. destruct Hvalid as [Hhead Hrest_valid].
    simpl shift_trace_11.
    destruct ((i =? 1) && (j =? 1)) eqn:E.
    + (* (i, j) = (1, 1): skip it *)
      apply IH.
      * unfold simple_valid_trace. exact Hrest_valid.
      * exact Hnodup_rest.
    + (* (i, j) ≠ (1, 1): include shifted *)
      simpl touched_in_B.
      constructor.
      * (* Show j - 1 not in touched_in_B (shift_trace_11 rest) *)
        intro Hcontra.
        assert (Hin_orig: In j (touched_in_B rest)).
        { apply andb_prop in Hhead. destruct Hhead as [Hv1 _].
          apply andb_prop in Hv1. destruct Hv1 as [_ Hj_ge].
          assert (Hj_ge': j >= 1).
          { destruct j; simpl in Hj_ge; [discriminate | lia]. }
          replace j with (S (j - 1)) by lia.
          clear -Hcontra Hrest_valid.
          induction rest as [| [i' j'] rest' IH'].
          - simpl in Hcontra. destruct Hcontra.
          - unfold simple_valid_trace in Hrest_valid. simpl forallb in Hrest_valid.
            apply andb_prop in Hrest_valid. destruct Hrest_valid as [Hhead' Hrest'].
            simpl shift_trace_11 in Hcontra.
            destruct ((i' =? 1) && (j' =? 1)) eqn:E'.
            + simpl touched_in_B. right.
              apply IH'.
              * unfold simple_valid_trace. exact Hrest'.
              * exact Hcontra.
            + simpl touched_in_B in Hcontra.
              destruct Hcontra as [Heq | Hcontra'].
              * simpl touched_in_B. left.
                apply andb_prop in Hhead'. destruct Hhead' as [Hv1' _].
                apply andb_prop in Hv1'. destruct Hv1' as [_ Hj'_ge].
                assert (Hj'_ge': j' >= 1).
                { destruct j'; simpl in Hj'_ge; [discriminate | lia]. }
                lia.
              * simpl touched_in_B. right.
                apply IH'.
                -- unfold simple_valid_trace. exact Hrest'.
                -- exact Hcontra'. }
        apply Hnot_in. exact Hin_orig.
      * apply IH.
        -- unfold simple_valid_trace. exact Hrest_valid.
        -- exact Hnodup_rest.
Qed.

