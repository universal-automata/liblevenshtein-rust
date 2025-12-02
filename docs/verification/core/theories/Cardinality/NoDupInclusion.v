(** * NoDup and Inclusion Lemmas for Cardinality Bounds

    This module provides fundamental lemmas about lists with no duplicates,
    list intersection, and the inclusion-exclusion principle for bounded lists.

    Part of: Liblevenshtein.Core

    Decomposed from: Distance.v (lines 2220-2520)
*)

From Coq Require Import String List Arith Bool Nat Lia.
Import ListNotations.

(** * NoDup Split Lemma *)

(** If a is in l and l has no duplicates, we can split l into l1 ++ a :: l2
    where a is not in l1 or l2. *)
Lemma NoDup_split :
  forall {A : Type} (a : A) (l : list A),
    In a l ->
    NoDup l ->
    exists l1 l2, l = l1 ++ a :: l2 /\ ~ In a l1 /\ ~ In a l2.
Proof.
  intros A a l H_in H_nodup.
  induction l as [| b l' IH].
  - contradiction.
  - destruct H_in as [H_eq | H_in'].
    + subst b.
      exists [], l'.
      split; [reflexivity | split].
      * simpl. intros [].
      * inversion H_nodup. exact H1.
    + inversion H_nodup as [| ? ? H_not_in H_nodup'].
      apply IH in H_in' as [l1 [l2 [H_eq [H_not1 H_not2]]]]; [| exact H_nodup'].
      exists (b :: l1), l2.
      split; [| split].
      * simpl. rewrite H_eq. reflexivity.
      * simpl. intros [H_eq_b_a | H_in_b_l1].
        -- subst a.
           apply H_not_in.
           rewrite H_eq.
           apply in_or_app. right. left. reflexivity.
        -- apply H_not1. exact H_in_b_l1.
      * exact H_not2.
Qed.

(** * Inclusion Length Lemma *)

(** If l1 is included in l2 and both have NoDup, then length l1 ≤ length l2. *)
Lemma incl_length_NoDup :
  forall {A : Type} (l1 l2 : list A),
    NoDup l1 ->
    NoDup l2 ->
    incl l1 l2 ->
    length l1 <= length l2.
Proof.
  intros A l1.
  induction l1 as [| a l1' IH].
  - intros l2 H_nodup1 H_nodup2 H_incl.
    simpl. lia.
  - intros l2 H_nodup1 H_nodup2 H_incl.
    inversion H_nodup1 as [| ? ? H_not_in H_nodup1'].
    simpl.
    assert (H_a_in: In a l2).
    { apply H_incl. left. reflexivity. }
    apply NoDup_split in H_a_in as [l2_1 [l2_2 [H_eq [H_not1 H_not2]]]]; [| exact H_nodup2].
    rewrite H_eq.
    rewrite length_app. simpl. rewrite Nat.add_succ_r.
    apply le_n_S.
    rewrite <- length_app.
    apply (IH (l2_1 ++ l2_2)).
    + exact H_nodup1'.
    + rewrite H_eq in H_nodup2.
      apply NoDup_remove_1 in H_nodup2.
      exact H_nodup2.
    + intros y H_y_in.
      assert (H_y_in_l2: In y l2).
      { apply H_incl. right. exact H_y_in. }
      rewrite H_eq in H_y_in_l2.
      apply in_app_or in H_y_in_l2 as [H_in1 | [H_eq_y_a | H_in2]].
      * apply in_or_app. left. exact H_in1.
      * subst y. contradiction.
      * apply in_or_app. right. exact H_in2.
Qed.

(** * List Intersection *)

(** List intersection: elements of l1 that also appear in l2. *)
Definition list_inter (l1 l2 : list nat) : list nat :=
  filter (fun x => existsb (fun y => x =? y) l2) l1.

(** Membership in list_inter iff in both lists. *)
Lemma In_list_inter :
  forall x l1 l2,
    In x (list_inter l1 l2) <-> In x l1 /\ In x l2.
Proof.
  intros x l1 l2.
  unfold list_inter.
  rewrite filter_In.
  split.
  - intros [Hin1 Hexists].
    split.
    + exact Hin1.
    + apply existsb_exists in Hexists.
      destruct Hexists as [y [Hin2 Heq]].
      apply Nat.eqb_eq in Heq.
      subst. exact Hin2.
  - intros [Hin1 Hin2].
    split.
    + exact Hin1.
    + apply existsb_exists.
      exists x.
      split.
      * exact Hin2.
      * apply Nat.eqb_eq. reflexivity.
Qed.

(** When the head element is not in l2, list_inter skips it. *)
Lemma list_inter_not_in_head :
  forall (x : nat) (l1 l2 : list nat),
    existsb (fun y => x =? y) l2 = false ->
    list_inter (x :: l1) l2 = list_inter l1 l2.
Proof.
  intros x l1 l2 Hnot_in.
  unfold list_inter.
  simpl.
  rewrite Hnot_in.
  reflexivity.
Qed.

(** NoDup is preserved by list_inter (since it's a sublist of l1). *)
Lemma NoDup_list_inter :
  forall l1 l2,
    NoDup l1 -> NoDup (list_inter l1 l2).
Proof.
  intros l1 l2 Hnodup.
  unfold list_inter.
  apply NoDup_filter.
  exact Hnodup.
Qed.

(** Length of list intersection is bounded by the smaller list. *)
Lemma list_inter_length_bound :
  forall l1 l2,
    NoDup l1 ->
    length (list_inter l1 l2) <= length l1.
Proof.
  intros l1 l2 Hnodup.
  unfold list_inter.
  apply (filter_length_le _ l1).
Qed.

(** Inclusion-exclusion bound for two NoDup lists bounded by [1..n].
    |l1| + |l2| <= n + |l1 ∩ l2| *)
Lemma NoDup_incl_exclusion :
  forall l1 l2 n,
    NoDup l1 -> NoDup l2 ->
    (forall x, In x l1 -> 1 <= x <= n) ->
    (forall x, In x l2 -> 1 <= x <= n) ->
    length l1 + length l2 <= n + length (list_inter l1 l2).
Proof.
  intros l1 l2 n Hnodup1 Hnodup2 Hbound1 Hbound2.
  (* Split l1 into intersection and difference - length identity *)
  assert (H_split: length l1 = length (list_inter l1 l2) +
                                length (filter (fun x => negb (existsb (fun y => x =? y) l2)) l1)).
  { clear Hnodup1 Hnodup2 Hbound1 Hbound2.
    induction l1 as [|a l1' IH].
    - simpl. reflexivity.
    - simpl.
      destruct (existsb (fun y => a =? y) l2) eqn:Hexists.
      + simpl. rewrite IH. lia.
      + simpl. rewrite IH. lia. }
  set (diff := filter (fun x => negb (existsb (fun y => x =? y) l2)) l1).
  assert (Hdiff_disjoint: forall x, In x diff -> ~ In x l2).
  { intros x Hin.
    unfold diff in Hin.
    rewrite filter_In in Hin.
    destruct Hin as [_ Hneg].
    intro Hin2.
    rewrite negb_true_iff in Hneg.
    assert (Hexists: existsb (fun y => x =? y) l2 = true).
    { apply existsb_exists.
      exists x. split.
      - exact Hin2.
      - apply Nat.eqb_refl. }
    rewrite Hexists in Hneg.
    discriminate. }
  assert (Hdiff_bound: forall x, In x diff -> 1 <= x <= n).
  { intros x Hin.
    unfold diff in Hin.
    rewrite filter_In in Hin.
    destruct Hin as [Hin _].
    apply Hbound1. exact Hin. }
  assert (Hdiff_nodup: NoDup diff).
  { unfold diff.
    apply NoDup_filter.
    exact Hnodup1. }
  (* Key: diff ++ l2 has NoDup and all elements in [1..n] *)
  assert (H_union_nodup: NoDup (diff ++ l2)).
  { apply NoDup_app.
    - exact Hdiff_nodup.
    - exact Hnodup2.
    - intros x Hdiff_in Hl2_in.
      apply (Hdiff_disjoint x Hdiff_in Hl2_in). }
  assert (H_union_bound: forall x, In x (diff ++ l2) -> 1 <= x <= n).
  { intros x Hin.
    apply in_app_or in Hin as [Hin_diff | Hin_l2].
    - apply Hdiff_bound. exact Hin_diff.
    - apply Hbound2. exact Hin_l2. }
  (* Union is subset of [1..n], so |union| <= n *)
  assert (H_union_le_n: length (diff ++ l2) <= n).
  { (* All elements are in [1..n], so |union| <= n *)
    transitivity (length (seq 1 n)).
    - apply NoDup_incl_length.
      + exact H_union_nodup.
      + intros x Hin.
        specialize (H_union_bound x Hin).
        apply in_seq. lia.
    - rewrite seq_length. lia. }
  rewrite length_app in H_union_le_n.
  unfold diff in H_union_le_n.
  rewrite H_split.
  lia.
Qed.
