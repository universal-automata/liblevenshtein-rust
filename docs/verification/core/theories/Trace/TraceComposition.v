(** * Trace Composition

    This module defines trace composition and proves key properties needed
    for the triangle inequality. Trace composition takes two traces T1: A→B
    and T2: B→C and produces a composed trace T: A→C.

    Part of: Liblevenshtein.Core

    Decomposed from: Distance.v (lines 1220-2190)
*)

From Coq Require Import String List Arith Ascii Bool Nat Lia.
Import ListNotations.

From Liblevenshtein.Core Require Import Core.Definitions.
From Liblevenshtein.Core Require Import Trace.TraceBasics.
From Liblevenshtein.Core Require Import Trace.TouchedPositions.

(** * Trace Composition Definition *)

(**
   Trace composition.

   If T1 is a trace from A to B and T2 is a trace from B to C,
   then T1 ∘ T2 is defined as the trace from A to C where:

   (i, k) ∈ T1 ∘ T2  iff  ∃j such that (i,j) ∈ T1 and (j,k) ∈ T2

   This represents composing the transformations: A → B → C becomes A → C
*)
Definition compose_trace {A B C : list Char} (T1 : Trace A B) (T2 : Trace B C) : Trace A C :=
  fold_left (fun acc p1 =>
    let '(i, j) := p1 in
    (* Find all pairs (j, k) in T2 where first component matches j *)
    let matches := filter (fun p2 => let '(j2, k) := p2 in j =? j2) T2 in
    (* Add (i, k) for each match *)
    fold_left (fun acc2 p2 =>
      let '(_, k) := p2 in
      (i, k) :: acc2
    ) matches acc
  ) T1 [].

(** * Helper Lemmas for Trace Composition *)

(**
   Helper: Membership in fold_left for the inner fold pattern used in compose_trace.

   When we fold over matches to build pairs (i,k), an element appears in the result
   if it was already in the accumulator or it's one of the newly added pairs.
*)
Lemma In_fold_left_cons_pairs :
  forall (i : nat) (matches : list (nat * nat)) (acc : list (nat * nat)) (k : nat),
    In (i, k) (fold_left (fun acc2 p2 => let '(_, k') := p2 in (i, k') :: acc2) matches acc) <->
    In (i, k) acc \/ exists j, In (j, k) matches.
Proof.
  intros i matches.
  induction matches as [| [j' k'] matches' IH]; intros acc k.
  - (* Base case: matches = [] *)
    simpl.
    split; intro H.
    + left. exact H.
    + destruct H as [H | [j H]].
      * exact H.
      * contradiction.
  - (* Inductive case: matches = (j', k') :: matches' *)
    simpl.
    rewrite IH.
    split; intro H.
    + destruct H as [H | [j H]].
      * (* (i,k) was in the new acc after adding (i,k') *)
        simpl in H.
        destruct H as [H | H].
        -- (* (i,k) = (i,k') *)
           inversion H; subst.
           right. exists j'. left. reflexivity.
        -- (* (i,k) was in original acc *)
           left. exact H.
      * (* exists j witness in matches' *)
        right. exists j. right. exact H.
    + destruct H as [H | [j H]].
      * (* (i,k) in original acc *)
        left. simpl. right. exact H.
      * (* exists j witness in full matches *)
        simpl in H.
        destruct H as [H | H].
        -- (* j = j', k was paired with j' *)
           inversion H; subst.
           left. simpl. left. reflexivity.
        -- (* j witness is in matches' *)
           right. exists j. exact H.
Qed.

(**
   Helper: Connection between filter and membership.

   A pair (j,k) is in the filtered list iff it's in T2 and j matches the filter criterion.
*)
Lemma In_filter_eq :
  forall (j_target : nat) (T2 : list (nat * nat)) (j k : nat),
    In (j, k) (filter (fun p2 => let '(j2, _) := p2 in j_target =? j2) T2) <->
    In (j, k) T2 /\ j_target = j.
Proof.
  intros j_target T2 j k.
  rewrite filter_In.
  split; intro H.
  - destruct H as [H_in H_eq].
    simpl in H_eq.
    apply Nat.eqb_eq in H_eq.
    split; assumption.
  - destruct H as [H_in H_eq].
    split.
    + exact H_in.
    + simpl. apply Nat.eqb_eq. exact H_eq.
Qed.

(**
   Helper: The inner fold preserves membership from accumulator.

   Any pair in the accumulator remains in the result.
*)
Lemma In_fold_preserves_acc :
  forall (i' : nat) (matches acc : list (nat * nat)) (p : nat * nat),
    In p acc ->
    In p (fold_left (fun acc2 p2 => let '(_, k') := p2 in (i', k') :: acc2) matches acc).
Proof.
  intros i' matches.
  induction matches as [| [j_m k_m] matches' IH]; intros acc p H_in.
  - (* Base: matches = [] *)
    simpl. exact H_in.
  - (* Inductive: matches = (j_m, k_m) :: matches' *)
    simpl.
    apply IH.
    simpl. right. exact H_in.
Qed.

(**
   Helper: If i ≠ i', then pairs (i, k) in the fold result must have been in acc.

   The fold only adds pairs of form (i', k'), so pairs with a different first component
   must have come from the accumulator.
*)
Lemma In_fold_diff_first :
  forall (i i' : nat) (matches acc : list (nat * nat)) (k : nat),
    i <> i' ->
    In (i, k) (fold_left (fun acc2 p2 => let '(_, k') := p2 in (i', k') :: acc2) matches acc) ->
    In (i, k) acc.
Proof.
  intros i i' matches.
  induction matches as [| [j_m k_m] matches' IH]; intros acc k H_neq H_in.
  - (* Base: matches = [] *)
    simpl in H_in. exact H_in.
  - (* Inductive: matches = (j_m, k_m) :: matches' *)
    simpl in H_in.
    apply IH in H_in; [| exact H_neq].
    simpl in H_in.
    destruct H_in as [H_eq | H_in].
    + (* (i, k) = (i', k_m) - contradiction since i ≠ i' *)
      inversion H_eq; subst.
      exfalso. apply H_neq. reflexivity.
    + (* (i, k) was in original acc *)
      exact H_in.
Qed.

(**
   Helper: Membership in the outer fold_left of compose_trace.

   This lemma characterizes when a pair appears in the accumulating result
   of the composition fold operation.
*)
Lemma In_compose_trace_fold :
  forall (T1 : list (nat * nat)) (T2 : list (nat * nat)) (acc : list (nat * nat)) (i k : nat),
    In (i, k) (fold_left (fun acc' p1 =>
      let '(i', j) := p1 in
      let matches := filter (fun p2 => let '(j2, _) := p2 in j =? j2) T2 in
      fold_left (fun acc2 p2 => let '(_, k') := p2 in (i', k') :: acc2) matches acc'
    ) T1 acc) <->
    In (i, k) acc \/ exists j, In (i, j) T1 /\ In (j, k) T2.
Proof.
  intros T1 T2.
  induction T1 as [| [i' j'] T1' IH]; intros acc i k.
  - (* Base case: T1 = [] *)
    simpl.
    split; intro H.
    + left. exact H.
    + destruct H as [H | [j [H _]]].
      * exact H.
      * contradiction.
  - (* Inductive case: T1 = (i',j') :: T1' *)
    simpl.
    split; intro H.
    + (* Forward: membership in result -> witness or in acc *)
      rewrite IH in H.
      destruct H as [H | [j [H_in1 H_in2]]].
      * (* (i,k) is in the new accumulator after processing (i',j') *)
        (* Key insight: the inner fold ONLY adds pairs of form (i', k').
           So if In (i,k) holds in the result, either:
           - (i,k) was already in acc, OR
           - i = i' and k came from a match *)
        destruct (Nat.eq_dec i i') as [H_eq | H_neq].
        -- (* Case: i = i' *)
           subst i'.
           set (matches := filter (fun p2 : nat * nat => let '(j2, _) := p2 in j' =? j2) T2) in H.
           pose proof (In_fold_left_cons_pairs i matches acc k) as H_inner.
           rewrite H_inner in H. clear H_inner.
           destruct H as [H_acc | [j_m H_match]].
           ++ (* Was in acc *)
              left. exact H_acc.
           ++ (* Came from match *)
              unfold matches in H_match.
              rewrite In_filter_eq in H_match.
              destruct H_match as [H_in_T2 H_j_eq].
              subst j_m.
              (* We have (j', k) ∈ T2, and the pair (i, j') is in the current position of T1 *)
              right. exists j'. split.
              ** left. reflexivity.
              ** exact H_in_T2.
        -- (* Case: i ≠ i' *)
           (* The fold only adds pairs (i', k'), so In (i, k) must have been in acc *)
           set (matches := filter (fun p2 : nat * nat => let '(j2, _) := p2 in j' =? j2) T2) in H.
           apply In_fold_diff_first in H; [| exact H_neq].
           left. exact H.
      * (* There's a witness in T1' *)
        right. exists j. split.
        -- right. exact H_in1.
        -- exact H_in2.
    + (* Backward: witness or in acc -> membership in result *)
      rewrite IH.
      destruct H as [H | [j [H_in1 H_in2]]].
      * (* Was in original acc *)
        (* Since (i,k) is in acc, it remains in the fold result *)
        set (matches := filter (fun p2 : nat * nat => let '(j2, _) := p2 in j' =? j2) T2).
        left.
        apply In_fold_preserves_acc.
        exact H.
      * (* There's a witness *)
        simpl in H_in1.
        destruct H_in1 as [H_eq | H_in1].
        -- (* Witness is (i',j') itself *)
           inversion H_eq; subst.
           (* Now i=i', j=j', and we have (j',k) ∈ T2 *)
           (* We need to show (i,k) is in fold result after processing (i,j') *)
           (* The filter will find (j',k) in T2, and fold will add (i,k) *)
           set (matches := filter (fun p2 : nat * nat => let '(j2, _) := p2 in j =? j2) T2).
           pose proof (In_fold_left_cons_pairs i matches acc k) as H_inner.
           left.
           rewrite H_inner.
           right. exists j.
           unfold matches.
           rewrite In_filter_eq.
           split; [exact H_in2 | reflexivity].
        -- (* Witness is in T1' *)
           right. exists j. split; assumption.
Qed.

(**
   Characterization of membership in composed trace.

   A pair (i,k) appears in the composed trace iff there exists some j
   such that (i,j) is in T1 and (j,k) is in T2.
*)
Lemma In_compose_trace :
  forall (A B C : list Char) (T1 : Trace A B) (T2 : Trace B C) (i k : nat),
    In (i, k) (compose_trace T1 T2) <->
    exists j, In (i, j) T1 /\ In (j, k) T2.
Proof.
  intros A B C T1 T2 i k.
  unfold compose_trace.
  rewrite In_compose_trace_fold with (acc := []).
  split; intro H.
  - (* Forward direction *)
    destruct H as [H | H].
    + (* In empty list - contradiction *)
      contradiction.
    + (* Exists witness *)
      exact H.
  - (* Backward direction *)
    right. exact H.
Qed.

(** * Valid Pair Composition *)

(**
   Valid pairs compose transitively.

   If (i,j) is valid for strings of length |A| and |B|,
   and (j,k) is valid for strings of length |B| and |C|,
   then (i,k) is valid for strings of length |A| and |C|.
*)
Lemma valid_pair_compose :
  forall (lenA lenB lenC : nat) (i j k : nat),
    valid_pair lenA lenB (i, j) = true ->
    valid_pair lenB lenC (j, k) = true ->
    valid_pair lenA lenC (i, k) = true.
Proof.
  intros lenA lenB lenC i j k H1 H2.
  unfold valid_pair in *.
  simpl in *.
  apply andb_true_iff in H1 as [H1_left H1_jB].
  apply andb_true_iff in H1_left as [H1_left2 H1_jlow].
  apply andb_true_iff in H1_left2 as [H1_ilow H1_ihigh].
  apply andb_true_iff in H2 as [H2_left H2_kC].
  apply andb_true_iff in H2_left as [H2_left2 H2_klow].
  apply andb_true_iff in H2_left2 as [H2_jlow H2_jB].
  apply andb_true_intro. split.
  - apply andb_true_intro. split.
    + apply andb_true_intro. split.
      * exact H1_ilow.
      * exact H1_ihigh.
    + exact H2_klow.
  - exact H2_kC.
Qed.

(** * Order Preservation Lemmas *)

(**
   Extract order preservation from compatible_pairs.

   If two pairs are compatible and have different components, then their
   first and second components preserve the same order.
*)
Lemma compatible_pairs_order :
  forall (i1 j1 i2 j2 : nat),
    i1 <> i2 ->
    j1 <> j2 ->
    compatible_pairs (i1, j1) (i2, j2) = true ->
    (i1 < i2 <-> j1 < j2).
Proof.
  intros i1 j1 i2 j2 H_i_neq H_j_neq H_compat.
  unfold compatible_pairs in H_compat.
  simpl in H_compat.
  destruct (i1 =? i2) eqn:H_i_eq.
  - apply Nat.eqb_eq in H_i_eq.
    exfalso. apply H_i_neq. exact H_i_eq.
  - destruct (j1 =? j2) eqn:H_j_eq.
    + apply Nat.eqb_eq in H_j_eq.
      exfalso. apply H_j_neq. exact H_j_eq.
    + simpl in H_compat.
      destruct (i1 <? i2) eqn:H_i_ltb.
      * apply Nat.ltb_lt in H_i_ltb.
        apply Nat.ltb_lt in H_compat.
        split; intro; assumption.
      * apply Nat.ltb_ge in H_i_ltb.
        apply Nat.ltb_lt in H_compat.
        assert (H_i2_lt: i2 < i1).
        { apply Nat.eqb_neq in H_i_eq. lia. }
        split; intro H; exfalso; lia.
Qed.

(**
   Valid traces have unique first components.

   If a valid trace contains two pairs with the same first component,
   they must have the same second component.
*)
Lemma valid_trace_unique_first :
  forall (T : list (nat * nat)) (i j1 j2 : nat),
    is_valid_trace_aux T = true ->
    In (i, j1) T ->
    In (i, j2) T ->
    j1 = j2.
Proof.
  intros T i j1 j2 H_valid H_in1 H_in2.
  induction T as [| [i' j'] T' IH].
  - contradiction.
  - simpl in H_valid.
    apply andb_true_iff in H_valid as [H_forall H_valid'].
    simpl in H_in1, H_in2.
    destruct H_in1 as [H_eq1 | H_in1]; destruct H_in2 as [H_eq2 | H_in2].
    + inversion H_eq1; inversion H_eq2; subst. reflexivity.
    + inversion H_eq1; subst. clear H_eq1.
      rewrite forallb_forall in H_forall.
      specialize (H_forall (i, j2) H_in2).
      unfold compatible_pairs in H_forall. simpl in H_forall.
      rewrite Nat.eqb_refl in H_forall. simpl in H_forall.
      destruct (j1 =? j2) eqn:H_j_eq.
      * apply Nat.eqb_eq in H_j_eq. exact H_j_eq.
      * discriminate H_forall.
    + inversion H_eq2; subst. clear H_eq2.
      rewrite forallb_forall in H_forall.
      specialize (H_forall (i, j1) H_in1).
      unfold compatible_pairs in H_forall. simpl in H_forall.
      rewrite Nat.eqb_refl in H_forall. simpl in H_forall.
      destruct (j2 =? j1) eqn:H_j_eq.
      * apply Nat.eqb_eq in H_j_eq. symmetry. exact H_j_eq.
      * discriminate H_forall.
    + apply IH; assumption.
Qed.

(**
   Valid traces have unique second components.

   If a valid trace contains two pairs with the same second component,
   they must have the same first component.
*)
Lemma valid_trace_unique_second :
  forall (T : list (nat * nat)) (i1 i2 j : nat),
    is_valid_trace_aux T = true ->
    In (i1, j) T ->
    In (i2, j) T ->
    i1 = i2.
Proof.
  intros T i1 i2 j H_valid H_in1 H_in2.
  induction T as [| [i' j'] T' IH].
  - contradiction.
  - simpl in H_valid.
    apply andb_true_iff in H_valid as [H_forall H_valid'].
    simpl in H_in1, H_in2.
    destruct H_in1 as [H_eq1 | H_in1]; destruct H_in2 as [H_eq2 | H_in2].
    + inversion H_eq1; inversion H_eq2; subst. reflexivity.
    + inversion H_eq1; subst. clear H_eq1.
      rewrite forallb_forall in H_forall.
      specialize (H_forall (i2, j) H_in2).
      unfold compatible_pairs in H_forall. simpl in H_forall.
      destruct (i1 =? i2) eqn:H_i_eq.
      * apply Nat.eqb_eq in H_i_eq. exact H_i_eq.
      * rewrite Nat.eqb_refl in H_forall. simpl in H_forall.
        discriminate H_forall.
    + inversion H_eq2; subst. clear H_eq2.
      rewrite forallb_forall in H_forall.
      specialize (H_forall (i1, j) H_in1).
      unfold compatible_pairs in H_forall. simpl in H_forall.
      destruct (i2 =? i1) eqn:H_i_eq.
      * apply Nat.eqb_eq in H_i_eq. symmetry. exact H_i_eq.
      * rewrite Nat.eqb_refl in H_forall. simpl in H_forall.
        discriminate H_forall.
    + apply IH; assumption.
Qed.

(**
   Order preservation in valid traces.

   If two distinct pairs are in a valid trace, their first and second
   components preserve the same ordering relationship.
*)
Lemma valid_trace_order_preserved :
  forall (T : list (nat * nat)) (i1 j1 i2 j2 : nat),
    is_valid_trace_aux T = true ->
    In (i1, j1) T ->
    In (i2, j2) T ->
    i1 <> i2 ->
    (i1 < i2 <-> j1 < j2).
Proof.
  intros T i1 j1 i2 j2 H_valid H_in1 H_in2 H_neq.
  assert (H_j_neq: j1 <> j2).
  { intro H_j_eq. subst j2.
    assert (H_eq: i1 = i2).
    { apply (valid_trace_unique_second T i1 i2 j1 H_valid H_in1 H_in2). }
    contradiction. }
  induction T as [| [i' j'] T' IH].
  - contradiction.
  - simpl in H_valid.
    apply andb_true_iff in H_valid as [H_forall H_valid'].
    simpl in H_in1, H_in2.
    destruct H_in1 as [H_eq1 | H_in1]; destruct H_in2 as [H_eq2 | H_in2].
    + inversion H_eq1; inversion H_eq2; subst.
      exfalso. apply H_neq. reflexivity.
    + inversion H_eq1; subst. clear H_eq1.
      rewrite forallb_forall in H_forall.
      specialize (H_forall (i2, j2) H_in2).
      apply compatible_pairs_order; assumption.
    + inversion H_eq2; subst. clear H_eq2.
      rewrite forallb_forall in H_forall.
      specialize (H_forall (i1, j1) H_in1).
      assert (H_neq_sym: i2 <> i1) by (intro; symmetry in H; contradiction).
      assert (H_j_neq_sym: j2 <> j1) by (intro; symmetry in H; contradiction).
      apply compatible_pairs_order in H_forall; [| exact H_neq_sym | exact H_j_neq_sym].
      split; intro H.
      * assert (H_not_i2_lt: ~ (i2 < i1)) by lia.
        assert (H_not_j2_lt: ~ (j2 < j1)).
        { intro H_j2_lt. apply H_not_i2_lt. apply H_forall. exact H_j2_lt. }
        lia.
      * assert (H_not_j2_lt: ~ (j2 < j1)) by lia.
        assert (H_not_i2_lt: ~ (i2 < i1)).
        { intro H_i2_lt. apply H_not_j2_lt. apply H_forall. exact H_i2_lt. }
        lia.
    + apply IH; assumption.
Qed.

(** * Validity Preservation Lemmas *)

(**
   Extract pairwise compatibility from valid trace.
*)
Lemma is_valid_trace_aux_In_compatible :
  forall (T : list (nat * nat)) (p1 p2 : nat * nat),
    is_valid_trace_aux T = true ->
    In p1 T ->
    In p2 T ->
    compatible_pairs p1 p2 = true.
Proof.
  intros T p1 p2 H_valid H_in1 H_in2.
  induction T as [| p T' IH].
  - contradiction.
  - simpl in H_valid.
    apply andb_true_iff in H_valid as [H_forall H_valid'].
    simpl in H_in1, H_in2.
    destruct H_in1 as [H_eq1 | H_in1]; destruct H_in2 as [H_eq2 | H_in2].
    + subst p1 p2.
      unfold compatible_pairs.
      destruct p as [i j]. simpl.
      rewrite Nat.eqb_refl. rewrite Nat.eqb_refl.
      reflexivity.
    + subst p1.
      rewrite forallb_forall in H_forall.
      apply H_forall. exact H_in2.
    + subst p2.
      rewrite forallb_forall in H_forall.
      assert (H_compat: compatible_pairs p p1 = true).
      { apply H_forall. exact H_in1. }
      unfold compatible_pairs in *.
      destruct p as [i_p j_p].
      destruct p1 as [i1 j1].
      simpl in *.
      destruct (i_p =? i1) eqn:H_i_eq; destruct (j_p =? j1) eqn:H_j_eq.
      * apply Nat.eqb_eq in H_i_eq, H_j_eq. subst i1 j1.
        rewrite Nat.eqb_refl. rewrite Nat.eqb_refl. reflexivity.
      * simpl in H_compat. discriminate.
      * simpl in H_compat. discriminate.
      * simpl in H_compat.
        destruct (i1 =? i_p) eqn:H_i_eq2.
        -- apply Nat.eqb_eq in H_i_eq2.
           apply Nat.eqb_neq in H_i_eq.
           exfalso. apply H_i_eq. symmetry. exact H_i_eq2.
        -- destruct (j1 =? j_p) eqn:H_j_eq2.
           ++ apply Nat.eqb_eq in H_j_eq2.
              apply Nat.eqb_neq in H_j_eq.
              exfalso. apply H_j_eq. symmetry. exact H_j_eq2.
           ++ simpl.
              destruct (i_p <? i1) eqn:H_i_lt.
              ** apply Nat.ltb_lt in H_i_lt.
                 apply Nat.ltb_lt in H_compat.
                 destruct (i1 <? i_p) eqn:H_i1_lt.
                 --- apply Nat.ltb_lt in H_i1_lt. exfalso. lia.
                 --- apply Nat.ltb_lt. exact H_compat.
              ** apply Nat.ltb_ge in H_i_lt.
                 apply Nat.ltb_lt in H_compat.
                 assert (H_i1_lt: i1 < i_p).
                 { apply Nat.eqb_neq in H_i_eq. lia. }
                 apply Nat.ltb_lt in H_i1_lt.
                 rewrite H_i1_lt.
                 apply Nat.ltb_lt. exact H_compat.
    + apply IH; assumption.
Qed.

(**
   Build valid trace from pairwise compatibility.
*)
Lemma is_valid_trace_aux_from_pairwise :
  forall (T : list (nat * nat)),
    (forall p1 p2, In p1 T -> In p2 T -> compatible_pairs p1 p2 = true) ->
    is_valid_trace_aux T = true.
Proof.
  induction T as [| p ps IH].
  - intro H_pairwise. reflexivity.
  - intro H_pairwise.
    simpl.
    apply andb_true_iff. split.
    + apply forallb_forall.
      intros p' H_in_ps.
      apply H_pairwise.
      * left. reflexivity.
      * right. exact H_in_ps.
    + apply IH.
      intros p1 p2 H_in1 H_in2.
      apply H_pairwise.
      * right. exact H_in1.
      * right. exact H_in2.
Qed.

(**
   Compatible pairs compose transitively.
*)
Lemma compatible_pairs_compose :
  forall (T1 T2 : list (nat * nat)) (i1 j1 k1 i2 j2 k2 : nat),
    is_valid_trace_aux T1 = true ->
    is_valid_trace_aux T2 = true ->
    In (i1, j1) T1 ->
    In (i2, j2) T1 ->
    In (j1, k1) T2 ->
    In (j2, k2) T2 ->
    compatible_pairs (i1, k1) (i2, k2) = true.
Proof.
  intros T1 T2 i1 j1 k1 i2 j2 k2 H_valid1 H_valid2 H_in11 H_in12 H_in21 H_in22.
  unfold compatible_pairs. simpl.
  destruct (Nat.eq_dec i1 i2) as [H_i_eq | H_i_neq].
  - subst i2.
    destruct (Nat.eq_dec k1 k2) as [H_k_eq | H_k_neq].
    + subst k2. rewrite Nat.eqb_refl. rewrite Nat.eqb_refl. reflexivity.
    + assert (H_j_eq: j1 = j2).
      { apply (valid_trace_unique_first T1 i1 j1 j2 H_valid1 H_in11 H_in12). }
      subst j2.
      assert (H_k_eq: k1 = k2).
      { apply (valid_trace_unique_first T2 j1 k1 k2 H_valid2 H_in21 H_in22). }
      exfalso. apply H_k_neq. exact H_k_eq.
  - destruct (Nat.eq_dec k1 k2) as [H_k_eq | H_k_neq].
    + subst k2.
      assert (H_j_eq: j1 = j2).
      { apply (valid_trace_unique_second T2 j1 j2 k1 H_valid2 H_in21 H_in22). }
      subst j2.
      assert (H_i_eq: i1 = i2).
      { apply (valid_trace_unique_second T1 i1 i2 j1 H_valid1 H_in11 H_in12). }
      exfalso. apply H_i_neq. exact H_i_eq.
    + assert (H_order1: i1 < i2 <-> j1 < j2).
      { apply (valid_trace_order_preserved T1 i1 j1 i2 j2 H_valid1 H_in11 H_in12 H_i_neq). }
      destruct (Nat.eq_dec j1 j2) as [H_j_eq | H_j_neq].
      * subst j2.
        assert (H_i_eq: i1 = i2).
        { apply (valid_trace_unique_second T1 i1 i2 j1 H_valid1 H_in11 H_in12). }
        exfalso. apply H_i_neq. exact H_i_eq.
      * assert (H_order2: j1 < j2 <-> k1 < k2).
        { apply (valid_trace_order_preserved T2 j1 k1 j2 k2 H_valid2 H_in21 H_in22 H_j_neq). }
        destruct (i1 =? i2) eqn:H_i_eqb.
        -- apply Nat.eqb_eq in H_i_eqb. exfalso. apply H_i_neq. exact H_i_eqb.
        -- destruct (k1 =? k2) eqn:H_k_eqb.
           ++ apply Nat.eqb_eq in H_k_eqb. exfalso. apply H_k_neq. exact H_k_eqb.
           ++ simpl.
              destruct (i1 <? i2) eqn:H_i_ltb.
              ** destruct (k1 <? k2) eqn:H_k_ltb.
                 --- reflexivity.
                 --- apply Nat.ltb_lt in H_i_ltb.
                     apply Nat.ltb_ge in H_k_ltb.
                     apply H_order1 in H_i_ltb as H_j_lt.
                     apply H_order2 in H_j_lt as H_k_lt.
                     exfalso. lia.
              ** destruct (k1 <? k2) eqn:H_k_ltb.
                 --- apply Nat.ltb_ge in H_i_ltb.
                     apply Nat.ltb_lt in H_k_ltb.
                     assert (H_j_lt: j1 < j2) by (apply H_order2; exact H_k_ltb).
                     assert (H_i_lt: i1 < i2) by (apply H_order1; exact H_j_lt).
                     exfalso. lia.
                 --- apply Nat.ltb_ge in H_i_ltb.
                     apply Nat.ltb_ge in H_k_ltb.
                     assert (H_i2_lt: i2 < i1).
                     { apply Nat.eqb_neq in H_i_eqb. lia. }
                     assert (H_j2_lt: j2 < j1).
                     { destruct H_order1 as [H_fwd H_bwd].
                       assert (H_not_i_lt: ~ (i1 < i2)) by lia.
                       assert (H_not_j_lt: ~ (j1 < j2)).
                       { intro H_j_lt. apply H_not_i_lt. apply H_bwd. exact H_j_lt. }
                       lia. }
                     assert (H_k2_lt: k2 < k1).
                     { destruct H_order2 as [H_fwd H_bwd].
                       assert (H_not_j_lt: ~ (j1 < j2)) by lia.
                       assert (H_not_k_lt: ~ (k1 < k2)).
                       { intro H_k_lt. apply H_not_j_lt. apply H_bwd. exact H_k_lt. }
                       lia. }
                     apply Nat.ltb_lt. exact H_k2_lt.
Qed.

(**
   Pairs in composed trace are pairwise compatible.
*)
Lemma compose_trace_pairwise_compatible :
  forall (A B C : list Char) (T1 : Trace A B) (T2 : Trace B C)
         (p1 p2 : nat * nat),
    is_valid_trace_aux T1 = true ->
    is_valid_trace_aux T2 = true ->
    In p1 (compose_trace T1 T2) ->
    In p2 (compose_trace T1 T2) ->
    compatible_pairs p1 p2 = true.
Proof.
  intros A B C T1 T2 p1 p2 H_valid1 H_valid2 H_in1 H_in2.
  destruct p1 as [i1 k1].
  destruct p2 as [i2 k2].
  apply In_compose_trace in H_in1 as [j1 [H_in1_T1 H_in1_T2]].
  apply In_compose_trace in H_in2 as [j2 [H_in2_T1 H_in2_T2]].
  eapply compatible_pairs_compose.
  - exact H_valid1.
  - exact H_valid2.
  - exact H_in1_T1.
  - exact H_in2_T1.
  - exact H_in1_T2.
  - exact H_in2_T2.
Qed.

(** * Touched Position Inclusion Lemmas *)

(**
   Helper: If i is in touched_in_A, then there exists k such that (i,k) is in the trace.
*)
Lemma In_touched_in_A_exists_pair :
  forall (A B : list Char) (T : Trace A B) (i : nat),
    In i (touched_in_A A B T) ->
    exists k, In (i, k) T.
Proof.
  intros A B T i H_in.
  induction T as [| [i' k'] T' IH].
  - simpl in H_in. contradiction.
  - simpl in H_in.
    destruct H_in as [H_eq | H_in'].
    + subst i. exists k'. left. reflexivity.
    + apply IH in H_in' as [k H_in_pair].
      exists k. right. exact H_in_pair.
Qed.

(**
   Touched positions in A are preserved in composition.
*)
Lemma touched_in_A_incl :
  forall (A B C : list Char) (T1 : Trace A B) (T2 : Trace B C),
    incl (touched_in_A A C (compose_trace T1 T2)) (touched_in_A A B T1).
Proof.
  intros A B C T1 T2.
  unfold incl.
  intros i H_in.
  apply In_touched_in_A_exists_pair in H_in as [k H_in_comp].
  apply In_compose_trace in H_in_comp as [j [H_in_T1 H_in_T2]].
  clear H_in_T2 k.
  induction T1 as [| [i1 j1] T1' IH_T1].
  - simpl in H_in_T1. contradiction.
  - simpl in H_in_T1.
    destruct H_in_T1 as [H_eq_pair | H_in_T1'].
    + injection H_eq_pair as H_i H_j. subst i1.
      simpl. left. reflexivity.
    + simpl. right. apply IH_T1. exact H_in_T1'.
Qed.

(**
   Helper: If k is in touched_in_B, then there exists i such that (i,k) is in the trace.
*)
Lemma In_touched_in_B_exists_pair :
  forall (A B : list Char) (T : Trace A B) (k : nat),
    In k (touched_in_B A B T) ->
    exists i, In (i, k) T.
Proof.
  intros A B T k H_in.
  induction T as [| [i' k'] T' IH].
  - simpl in H_in. contradiction.
  - simpl in H_in.
    destruct H_in as [H_eq | H_in'].
    + subst k. exists i'. left. reflexivity.
    + apply IH in H_in' as [i H_in_pair].
      exists i. right. exact H_in_pair.
Qed.

(**
   Touched positions in C are preserved in composition.
*)
Lemma touched_in_B_incl :
  forall (A B C : list Char) (T1 : Trace A B) (T2 : Trace B C),
    incl (touched_in_B A C (compose_trace T1 T2)) (touched_in_B B C T2).
Proof.
  intros A B C T1 T2.
  unfold incl.
  intros k H_in.
  apply In_touched_in_B_exists_pair in H_in as [i H_in_comp].
  apply In_compose_trace in H_in_comp as [j [H_in_T1 H_in_T2]].
  clear H_in_T1 i.
  induction T2 as [| [j2 k2] T2' IH_T2].
  - simpl in H_in_T2. contradiction.
  - simpl in H_in_T2.
    destruct H_in_T2 as [H_eq_pair | H_in_T2'].
    + injection H_eq_pair as H_j H_k. subst k2.
      simpl. left. reflexivity.
    + simpl. right. apply IH_T2. exact H_in_T2'.
Qed.
