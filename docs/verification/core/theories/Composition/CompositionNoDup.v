(** * NoDup Preservation for Trace Composition

    This module proves that trace composition preserves the NoDup property
    using a counting-based approach.

    Part of: Liblevenshtein.Core

    Decomposed from: Distance.v (lines 3149-3515)
*)

From Coq Require Import String List Arith Ascii Bool Nat Lia.
Import ListNotations.

From Liblevenshtein.Core Require Import Core.Definitions.
From Liblevenshtein.Core Require Import Trace.TraceBasics.
From Liblevenshtein.Core Require Import Trace.TraceComposition.
From Liblevenshtein.Core Require Import Composition.WitnessLemmas.

(** * NoDup and Map Fst Infrastructure *)

(**
   Helper: NoDup (map fst l) implies NoDup l for pairs.

   If no first component repeats, then pairs at different positions must be different.
*)
Lemma NoDup_map_fst_implies_NoDup :
  forall (l : list (nat * nat)),
    NoDup (map fst l) ->
    NoDup l.
Proof.
  intros l Hnodup_fst.
  induction l as [| [a b] l' IH].
  - constructor.
  - simpl in Hnodup_fst.
    inversion Hnodup_fst as [| ? ? Hnotin HnodupTail]. subst.
    constructor.
    + intro Hin.
      apply Hnotin.
      apply in_map_iff.
      exists (a, b). split; [reflexivity | exact Hin].
    + apply IH. exact HnodupTail.
Qed.

(**
   Helper: map fst of T1 has NoDup when T1 has valid compatible pairs.

   This follows from the fact that compatible_pairs forbids same first component
   with different second components.
*)
Lemma trace_map_fst_NoDup :
  forall (A B : list Char) (T1 : Trace A B),
    is_valid_trace_aux T1 = true ->
    NoDup T1 ->
    NoDup (map fst T1).
Proof.
  intros A B T1 Haux Hnodup.
  induction T1 as [| [i j] T1' IH].
  - constructor.
  - simpl.
    inversion Hnodup as [| ? ? Hnotin_pair HnodupTail]. subst.
    simpl in Haux.
    destruct T1' as [| [i' j'] T1''].
    + constructor.
      { intro contra. inversion contra. }
      { constructor. }
    + assert (Haux_orig: is_valid_trace_aux ((i, j) :: (i', j') :: T1'') = true).
      { exact Haux. }
      apply andb_true_iff in Haux as [Hcompat Hrest].
      assert (HauxTail: is_valid_trace_aux ((i', j') :: T1'') = true).
      { exact Hrest. }
      constructor.
      { intro Hin_i.
        apply in_map_iff in Hin_i as [[i'' j''] [Heq Hin_pair]].
        simpl in Heq. subst i''.
        destruct (Nat.eq_dec j j'') as [Heq_j | Hneq_j].
        - subst j''.
          apply Hnotin_pair. exact Hin_pair.
        - assert (Hcompat': compatible_pairs (i, j) (i, j'') = true).
          { eapply is_valid_trace_aux_In_compatible.
            - exact Haux_orig.
            - left. reflexivity.
            - right. exact Hin_pair. }
          unfold compatible_pairs in Hcompat'.
          assert (Hi_refl: (i =? i) = true) by apply Nat.eqb_refl.
          assert (Hj_neq: (j =? j'') = false) by (apply Nat.eqb_neq; exact Hneq_j).
          rewrite Hi_refl, Hj_neq in Hcompat'.
          discriminate Hcompat'. }
      { apply IH.
        - exact HauxTail.
        - exact HnodupTail. }
Qed.

(** * Counting Infrastructure *)

(** Count pairs with first component i *)
Fixpoint count_fst_compose (i : nat) (l : list (nat * nat)) : nat :=
  match l with
  | [] => 0
  | (a, _) :: l' => (if a =? i then 1 else 0) + count_fst_compose i l'
  end.

(** Relationship between count_fst_compose and In on map fst *)
Lemma count_fst_compose_In :
  forall (l : list (nat * nat)) (i : nat),
    count_fst_compose i l >= 1 <-> In i (map fst l).
Proof.
  intros l i. induction l as [| [a b] l' IH]; simpl.
  - split; [lia | contradiction].
  - destruct (a =? i) eqn:Hai.
    + apply Nat.eqb_eq in Hai. subst. split; [intro; left; reflexivity | intro; lia].
    + apply Nat.eqb_neq in Hai. split.
      * intro H. right. apply IH. lia.
      * intro H. destruct H as [H | H]; [simpl in H; lia | apply IH in H; lia].
Qed.

(** Derive NoDup from count bound *)
Lemma NoDup_count_fst_compose_le_1 :
  forall (l : list (nat * nat)),
    (forall i, count_fst_compose i l <= 1) -> NoDup (map fst l).
Proof.
  intros l H. induction l as [| [a b] l' IH]; simpl.
  - constructor.
  - constructor.
    + intro Hin. specialize (H a). simpl in H. rewrite Nat.eqb_refl in H.
      apply count_fst_compose_In in Hin. lia.
    + apply IH. intro i. specialize (H i). simpl in H. destruct (a =? i); lia.
Qed.

(** Inner fold count tracking - using exact syntax from compose_trace *)
Lemma count_fst_compose_inner_fold :
  forall (a i : nat) (matches : list (nat * nat)) (acc : list (nat * nat)),
    count_fst_compose i (fold_left (fun acc2 p2 => let '(_, k) := p2 in (a, k) :: acc2) matches acc)
    = count_fst_compose i acc + (if a =? i then length matches else 0).
Proof.
  intros a i matches.
  induction matches as [| [j' k'] matches' IH]; intro acc.
  - simpl. destruct (a =? i); lia.
  - simpl. rewrite IH. simpl. destruct (a =? i) eqn:Hai; lia.
Qed.

(** filter returns [] if element not in map fst - using exact syntax from compose_trace *)
Lemma filter_fst_eq_nil_compose :
  forall (l : list (nat * nat)) (a : nat),
    ~In a (map fst l) ->
    filter (fun p2 => let '(j2, _) := p2 in a =? j2) l = [].
Proof.
  intros l a Hnotin.
  induction l as [| [c d] l']; simpl in *.
  - reflexivity.
  - destruct (a =? c) eqn:Hac.
    + apply Nat.eqb_eq in Hac. subst.
      exfalso. apply Hnotin. left. reflexivity.
    + apply IHl'. intro H. apply Hnotin. right. exact H.
Qed.

(** Filter length bound from NoDup - using exact syntax from compose_trace *)
Lemma NoDup_map_fst_filter_le_1_compose :
  forall (T2 : list (nat * nat)) (j : nat),
    NoDup (map fst T2) ->
    length (filter (fun p2 => let '(j2, _) := p2 in j =? j2) T2) <= 1.
Proof.
  intros T2 j Hnodup.
  induction T2 as [| [a b] T2' IH]; simpl in *.
  - lia.
  - inversion Hnodup as [| ? ? Hnotin Hnodup']; subst.
    destruct (j =? a) eqn:Hja.
    + apply Nat.eqb_eq in Hja. subst. simpl.
      rewrite filter_fst_eq_nil_compose by exact Hnotin.
      simpl. lia.
    + apply IH. exact Hnodup'.
Qed.

(** Count bound for compose fold - using exact syntax from compose_trace *)
Lemma count_fst_compose_bound :
  forall (T1 T2 : list (nat * nat)) (i : nat),
    (forall j, length (filter (fun p2 => let '(j2, _) := p2 in j =? j2) T2) <= 1) ->
    forall acc,
      count_fst_compose i (fold_left (fun acc' p1 =>
        let '(i', j) := p1 in
        let matches := filter (fun p2 => let '(j2, _) := p2 in j =? j2) T2 in
        fold_left (fun acc2 p2 => let '(_, k) := p2 in (i', k) :: acc2) matches acc'
      ) T1 acc)
      <= count_fst_compose i T1 + count_fst_compose i acc.
Proof.
  intros T1 T2 i Hfilter_bound.
  induction T1 as [| [a j] T1' IH]; intro acc; simpl.
  - lia.
  - set (inner_result := fold_left (fun acc2 p2 => let '(_, k) := p2 in (a, k) :: acc2)
                           (filter (fun p2 => let '(j2, _) := p2 in j =? j2) T2) acc).
    assert (Hinner: count_fst_compose i inner_result <= count_fst_compose i acc + (if a =? i then 1 else 0)).
    { unfold inner_result. rewrite count_fst_compose_inner_fold.
      pose proof (Hfilter_bound j) as Hfilt.
      destruct (a =? i) eqn:Hai.
      - assert (length (filter (fun p2 => let '(j2, _) := p2 in j =? j2) T2) <= 1) by exact Hfilt.
        lia.
      - lia. }
    specialize (IH inner_result).
    set (fold_result := fold_left (fun acc' p1 =>
                   let '(i', j0) := p1 in
                   let matches := filter (fun p2 => let '(j2, _) := p2 in j0 =? j2) T2 in
                   fold_left (fun acc2 p2 => let '(_, k) := p2 in (i', k) :: acc2) matches acc') T1' inner_result) in *.
    assert (H1: count_fst_compose i fold_result <= count_fst_compose i T1' + count_fst_compose i inner_result) by exact IH.
    destruct (a =? i) eqn:Hai.
    + lia.
    + assert (H2: count_fst_compose i inner_result <= count_fst_compose i acc).
      { rewrite Nat.add_0_r in Hinner. exact Hinner. }
      lia.
Qed.

(** Count bound from NoDup on map fst *)
Lemma NoDup_map_fst_count_le_1_compose :
  forall (T1 : list (nat * nat)) (i : nat),
    NoDup (map fst T1) ->
    count_fst_compose i T1 <= 1.
Proof.
  intros T1 i Hnodup.
  induction T1 as [| [a b] T1' IH]; simpl in *.
  - lia.
  - inversion Hnodup as [| ? ? Hnotin Hnodup']; subst.
    destruct (a =? i) eqn:Hai.
    + apply Nat.eqb_eq in Hai. subst.
      assert (Hzero: count_fst_compose i T1' = 0).
      { destruct (count_fst_compose i T1') eqn:Hc; [reflexivity|].
        exfalso. apply Hnotin.
        clear IH Hnodup Hnodup' Hnotin.
        induction T1' as [| [c d] T1'']; simpl in *.
        + discriminate.
        + destruct (c =? i) eqn:Hci.
          * apply Nat.eqb_eq in Hci. subst. left. reflexivity.
          * right. apply IHT1''. exact Hc. }
      lia.
    + apply IH. exact Hnodup'.
Qed.

(** * Core NoDup Theorems *)

(** Core theorem: compose_trace preserves NoDup on map fst (with type parameters) *)
Lemma compose_trace_map_fst_NoDup_simple :
  forall (A B C : list Char) (T1 : Trace A B) (T2 : Trace B C),
    NoDup (map fst T1) ->
    NoDup (map fst T2) ->
    NoDup (map fst (compose_trace T1 T2)).
Proof.
  intros A B C T1 T2 Hnodup1 Hnodup2.
  apply NoDup_count_fst_compose_le_1.
  intro i.
  assert (Hfilter: forall j, length (filter (fun p2 => let '(j2, _) := p2 in j =? j2) T2) <= 1).
  { intro j. apply NoDup_map_fst_filter_le_1_compose. exact Hnodup2. }
  unfold compose_trace.
  pose proof (count_fst_compose_bound T1 T2 i Hfilter []) as Hbound.
  simpl in Hbound.
  rewrite Nat.add_0_r in Hbound.
  assert (Hcount_T1: count_fst_compose i T1 <= 1).
  { apply NoDup_map_fst_count_le_1_compose. exact Hnodup1. }
  eapply Nat.le_trans.
  - exact Hbound.
  - exact Hcount_T1.
Qed.

(**
   Helper: map fst of compose_trace has NoDup.

   Each first component i in compose_trace comes from some (i, j) in T1.
   Since map fst T1 has NoDup, each i appears at most once.
*)
Lemma compose_trace_map_fst_NoDup :
  forall (A B C : list Char) (T1 : Trace A B) (T2 : Trace B C),
    is_valid_trace_aux T1 = true ->
    is_valid_trace_aux T2 = true ->
    NoDup T1 ->
    NoDup T2 ->
    NoDup (map fst (compose_trace T1 T2)).
Proof.
  intros A B C T1 T2 Haux1 Haux2 Hnodup1 Hnodup2.
  assert (HnodupFst1: NoDup (map fst T1)).
  { apply trace_map_fst_NoDup with (B := B); assumption. }
  assert (HnodupFst2: NoDup (map fst T2)).
  { apply trace_map_fst_NoDup with (B := C); assumption. }
  apply compose_trace_map_fst_NoDup_simple; assumption.
Qed.

(**
   Lemma: Witness uniqueness and NoDup imply NoDup for composed traces.

   This lemma captures a key structural property: when traces T1 and T2 have
   unique witnesses (via is_valid_trace_aux) and no duplicate pairs (via NoDup),
   their composition also has no duplicates.
*)
Lemma compose_trace_NoDup_axiom :
  forall (A B C : list Char) (T1 : Trace A B) (T2 : Trace B C),
    is_valid_trace_aux T1 = true ->
    is_valid_trace_aux T2 = true ->
    NoDup T1 ->
    NoDup T2 ->
    NoDup (compose_trace T1 T2).
Proof.
  intros A B C T1 T2 Haux1 Haux2 Hnodup1 Hnodup2.
  apply NoDup_map_fst_implies_NoDup.
  apply compose_trace_map_fst_NoDup; assumption.
Qed.
