(** * NoDup Preservation under Shift Operations

    This module provides lemmas showing that the NoDup property is preserved
    when applying shift operations to traces.

    Part of: Liblevenshtein.Core

    Decomposed from: TraceLowerBound.v (lines 1023-1320)
*)

From Stdlib Require Import String List Arith Ascii Bool Nat Lia.
Import ListNotations.

From Liblevenshtein.Core Require Import LowerBound.Definitions.
From Liblevenshtein.Core Require Import LowerBound.HasPredicates.
From Liblevenshtein.Core Require Import LowerBound.ShiftTraceA.
From Liblevenshtein.Core Require Import LowerBound.ShiftTraceB.
From Liblevenshtein.Core Require Import LowerBound.PigeonholeBounds.

(** * Successor Membership Lemmas *)

(** Helper: if x is in touched_in_A (shift_trace_A T), then x+1 is in touched_in_A T *)
Lemma in_shifted_implies_succ_in_original_A : forall lenA lenB T x,
  simple_valid_trace lenA lenB T = true ->
  In x (touched_in_A (shift_trace_A T)) ->
  In (S x) (touched_in_A T).
Proof.
  intros lenA lenB T.
  induction T as [| [i j] rest IH]; intros x Hvalid Hin.
  - simpl in Hin. destruct Hin.
  - simpl shift_trace_A in Hin.
    destruct (i =? 1) eqn:Ei.
    + apply Nat.eqb_eq in Ei. subst i.
      simpl touched_in_A. right.
      assert (Hrest_valid: simple_valid_trace lenA lenB rest = true).
      { unfold simple_valid_trace in *. rewrite forallb_forall in *.
        intros y Hy. apply Hvalid. right. exact Hy. }
      apply IH; assumption.
    + apply Nat.eqb_neq in Ei.
      simpl touched_in_A in Hin.
      destruct Hin as [Heq | Hin'].
      * simpl touched_in_A. left.
        assert (Hi_ge_1: 1 <= i).
        { unfold simple_valid_trace in Hvalid. rewrite forallb_forall in Hvalid.
          specialize (Hvalid (i, j) (in_eq _ _)).
          apply andb_prop in Hvalid. destruct Hvalid as [Hvalid' _].
          apply andb_prop in Hvalid'. destruct Hvalid' as [Hvalid'' _].
          apply andb_prop in Hvalid''. destruct Hvalid'' as [H1 _].
          apply Nat.leb_le in H1. exact H1. }
        lia.
      * simpl touched_in_A. right.
        assert (Hrest_valid: simple_valid_trace lenA lenB rest = true).
        { unfold simple_valid_trace in *. rewrite forallb_forall in *.
          intros y Hy. apply Hvalid. right. exact Hy. }
        apply IH; assumption.
Qed.

Lemma in_shifted_implies_succ_in_original_B : forall lenA lenB T x,
  simple_valid_trace lenA lenB T = true ->
  In x (touched_in_B (shift_trace_B T)) ->
  In (S x) (touched_in_B T).
Proof.
  intros lenA lenB T.
  induction T as [| [i j] rest IH]; intros x Hvalid Hin.
  - simpl in Hin. destruct Hin.
  - simpl shift_trace_B in Hin.
    destruct (j =? 1) eqn:Ej.
    + apply Nat.eqb_eq in Ej. subst j.
      simpl touched_in_B. right.
      assert (Hrest_valid: simple_valid_trace lenA lenB rest = true).
      { unfold simple_valid_trace in *. rewrite forallb_forall in *.
        intros y Hy. apply Hvalid. right. exact Hy. }
      apply IH; assumption.
    + apply Nat.eqb_neq in Ej.
      simpl touched_in_B in Hin.
      destruct Hin as [Heq | Hin'].
      * simpl touched_in_B. left.
        assert (Hj_ge_1: 1 <= j).
        { unfold simple_valid_trace in Hvalid. rewrite forallb_forall in Hvalid.
          specialize (Hvalid (i, j) (in_eq _ _)).
          apply andb_prop in Hvalid. destruct Hvalid as [Hvalid' _].
          apply andb_prop in Hvalid'. destruct Hvalid' as [_ H3].
          apply Nat.leb_le in H3. exact H3. }
        lia.
      * simpl touched_in_B. right.
        assert (Hrest_valid: simple_valid_trace lenA lenB rest = true).
        { unfold simple_valid_trace in *. rewrite forallb_forall in *.
          intros y Hy. apply Hvalid. right. exact Hy. }
        apply IH; assumption.
Qed.

(** * NoDup Preservation for shift_trace_A *)

(** NoDup preservation under shift_trace_A (requires validity for index >= 1) *)
Lemma shift_trace_A_NoDup_A : forall lenA lenB T,
  simple_valid_trace lenA lenB T = true ->
  NoDup (touched_in_A T) ->
  NoDup (touched_in_A (shift_trace_A T)).
Proof.
  intros lenA lenB T.
  induction T as [| [i j] rest IH]; intros Hvalid Hnodup.
  - simpl. constructor.
  - simpl touched_in_A in Hnodup.
    inversion Hnodup as [| x xs Hnot_in Hnodup_rest Heq]. subst x xs.
    simpl shift_trace_A.
    destruct (i =? 1) eqn:Ei.
    + assert (Hrest_valid: simple_valid_trace lenA lenB rest = true).
      { unfold simple_valid_trace in *. rewrite forallb_forall in *.
        intros y Hy. apply Hvalid. right. exact Hy. }
      apply IH; assumption.
    + apply Nat.eqb_neq in Ei.
      simpl touched_in_A.
      assert (Hrest_valid: simple_valid_trace lenA lenB rest = true).
      { unfold simple_valid_trace in *. rewrite forallb_forall in *.
        intros y Hy. apply Hvalid. right. exact Hy. }
      constructor.
      * intro Hcontra.
        assert (Hin_orig: In i (touched_in_A rest)).
        { assert (Hi_ge_1: 1 <= i).
          { unfold simple_valid_trace in Hvalid. rewrite forallb_forall in Hvalid.
            specialize (Hvalid (i, j) (in_eq _ _)).
            apply andb_prop in Hvalid. destruct Hvalid as [Hvalid' _].
            apply andb_prop in Hvalid'. destruct Hvalid' as [Hvalid'' _].
            apply andb_prop in Hvalid''. destruct Hvalid'' as [H1 _].
            apply Nat.leb_le in H1. exact H1. }
          replace i with (S (i - 1)) by lia.
          apply in_shifted_implies_succ_in_original_A with (lenA := lenA) (lenB := lenB).
          - exact Hrest_valid.
          - exact Hcontra. }
        apply Hnot_in. exact Hin_orig.
      * apply IH; assumption.
Qed.

(** NoDup preservation for B under shift_trace_A (when has_A1 = false) *)
Lemma shift_trace_A_NoDup_B : forall T,
  NoDup (touched_in_B T) ->
  has_A1 T = false ->
  NoDup (touched_in_B (shift_trace_A T)).
Proof.
  intros T Hnodup Hno_A1.
  rewrite touched_in_B_shift_trace_A by exact Hno_A1.
  exact Hnodup.
Qed.

(** Helper: if j is in touched_in_B (shift_trace_A T), then j is in touched_in_B T *)
Lemma in_shifted_B_implies_in_original_B : forall T j,
  In j (touched_in_B (shift_trace_A T)) -> In j (touched_in_B T).
Proof.
  induction T as [| [i k] rest IH]; intros j Hin.
  - simpl in Hin. destruct Hin.
  - simpl shift_trace_A in Hin.
    destruct (i =? 1) eqn:Ei.
    + simpl touched_in_B. right. apply IH. exact Hin.
    + simpl in Hin. destruct Hin as [Heq | Hin'].
      * simpl touched_in_B. left. exact Heq.
      * simpl touched_in_B. right. apply IH. exact Hin'.
Qed.

(** NoDup preservation for B under shift_trace_A (general - no has_A1 requirement) *)
Lemma shift_trace_A_NoDup_B_general : forall T,
  NoDup (touched_in_B T) ->
  NoDup (touched_in_B (shift_trace_A T)).
Proof.
  induction T as [| [i j] rest IH]; intros Hnodup.
  - constructor.
  - simpl shift_trace_A.
    destruct (i =? 1) eqn:Ei.
    + simpl touched_in_B in Hnodup.
      inversion Hnodup as [| x xs Hnot_in Hnodup_rest Heq]. subst.
      apply IH. exact Hnodup_rest.
    + simpl touched_in_B.
      simpl touched_in_B in Hnodup.
      inversion Hnodup as [| x xs Hnot_in Hnodup_rest Heq]. subst.
      constructor.
      * intro Hcontra.
        apply Hnot_in.
        apply in_shifted_B_implies_in_original_B. exact Hcontra.
      * apply IH. exact Hnodup_rest.
Qed.

(** * NoDup Preservation for shift_trace_B *)

(** NoDup preservation for B under shift_trace_B (requires validity) *)
Lemma shift_trace_B_NoDup_B : forall lenA lenB T,
  simple_valid_trace lenA lenB T = true ->
  NoDup (touched_in_B T) ->
  NoDup (touched_in_B (shift_trace_B T)).
Proof.
  intros lenA lenB T.
  induction T as [| [i j] rest IH]; intros Hvalid Hnodup.
  - simpl. constructor.
  - simpl touched_in_B in Hnodup.
    inversion Hnodup as [| x xs Hnot_in Hnodup_rest Heq]. subst x xs.
    simpl shift_trace_B.
    destruct (j =? 1) eqn:Ej.
    + assert (Hrest_valid: simple_valid_trace lenA lenB rest = true).
      { unfold simple_valid_trace in *. rewrite forallb_forall in *.
        intros y Hy. apply Hvalid. right. exact Hy. }
      apply IH; assumption.
    + apply Nat.eqb_neq in Ej.
      simpl touched_in_B.
      assert (Hrest_valid: simple_valid_trace lenA lenB rest = true).
      { unfold simple_valid_trace in *. rewrite forallb_forall in *.
        intros y Hy. apply Hvalid. right. exact Hy. }
      constructor.
      * intro Hcontra.
        assert (Hin_orig: In j (touched_in_B rest)).
        { assert (Hj_ge_1: 1 <= j).
          { unfold simple_valid_trace in Hvalid. rewrite forallb_forall in Hvalid.
            specialize (Hvalid (i, j) (in_eq _ _)).
            apply andb_prop in Hvalid. destruct Hvalid as [Hvalid' _].
            apply andb_prop in Hvalid'. destruct Hvalid' as [_ H3].
            apply Nat.leb_le in H3. exact H3. }
          replace j with (S (j - 1)) by lia.
          apply in_shifted_implies_succ_in_original_B with (lenA := lenA) (lenB := lenB).
          - exact Hrest_valid.
          - exact Hcontra. }
        apply Hnot_in. exact Hin_orig.
      * apply IH; assumption.
Qed.

(** NoDup preservation for A under shift_trace_B (when has_B1 = false) *)
Lemma shift_trace_B_NoDup_A : forall T,
  NoDup (touched_in_A T) ->
  has_B1 T = false ->
  NoDup (touched_in_A (shift_trace_B T)).
Proof.
  intros T Hnodup Hno_B1.
  rewrite touched_in_A_shift_trace_B by exact Hno_B1.
  exact Hnodup.
Qed.

(** * Helper Lemmas for Touched Positions *)

(** Helper: if k not in touched_in_A L, then no pair in L has first component k *)
Lemma not_in_touched_A : forall L k,
  ~ In k (touched_in_A L) ->
  forall i j, In (i, j) L -> i <> k.
Proof.
  induction L as [| [a b] L' IH']; intros k Hnot_in i j Hin.
  - destruct Hin.
  - simpl touched_in_A in Hnot_in.
    destruct Hin as [Heq | Hin'].
    + injection Heq as Ha Hb. subst.
      intro Hsub. subst. apply Hnot_in. left. reflexivity.
    + apply IH' with j; auto.
      intro H. apply Hnot_in. right. exact H.
Qed.

(** Helper: if k not in touched_in_B L, then no pair in L has second component k *)
Lemma not_in_touched_B : forall L k,
  ~ In k (touched_in_B L) ->
  forall i j, In (i, j) L -> j <> k.
Proof.
  induction L as [| [a b] L' IH']; intros k Hnot_in i j Hin.
  - destruct Hin.
  - simpl touched_in_B in Hnot_in.
    destruct Hin as [Heq | Hin'].
    + injection Heq as Ha Hb. subst.
      intro Hsub. subst. apply Hnot_in. left. reflexivity.
    + apply IH' with i; auto.
      intro H. apply Hnot_in. right. exact H.
Qed.

