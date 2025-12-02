(** * Cost Bounds for Trace Composition

    This module provides lemmas for bounding the cost of composed traces,
    including witness extraction and injectivity infrastructure.

    Part of: Liblevenshtein.Core

    Decomposed from: Distance.v (lines 4070-6908)
*)

From Coq Require Import String List Arith Ascii Bool Nat Lia.
Import ListNotations.

From Liblevenshtein.Core Require Import Core.Definitions.
From Liblevenshtein.Core Require Import Trace.TraceBasics.
From Liblevenshtein.Core Require Import Trace.TraceCost.
From Liblevenshtein.Core Require Import Trace.TraceComposition.
From Liblevenshtein.Core Require Import Composition.WitnessLemmas.
From Liblevenshtein.Core Require Import Composition.CompositionNoDup.
From Liblevenshtein.Core Require Import Composition.CompositionValidity.
From Liblevenshtein.Core Require Import Cardinality.NoDupInclusion.
From Liblevenshtein.Core Require Import Cardinality.NoDupPreservation.
From Liblevenshtein.Core Require Import Trace.TouchedPositions.
From Liblevenshtein.Core Require Import Triangle.SubstCostTriangle.

(** * Witness Pair Injectivity *)

(**
   Definition: A pair (i,k) uniquely determines its witness j in the composition.

   For the mapping comp → T1: if (i1,k1) and (i2,k2) both map to the same (i,j) in T1,
   then they must be the same pair.
*)
Lemma witness_pair_injective_T1 :
  forall (A B C : list Char) (T1 : Trace A B) (T2 : Trace B C) (i k1 k2 j : nat),
    is_valid_trace_aux T1 = true ->
    is_valid_trace_aux T2 = true ->
    In (i, k1) (compose_trace T1 T2) ->
    In (i, k2) (compose_trace T1 T2) ->
    In (i, j) T1 ->
    In (j, k1) T2 ->
    In (j, k2) T2 ->
    k1 = k2.
Proof.
  intros A B C T1 T2 i k1 k2 j Hval1 Hval2 Hin_comp1 Hin_comp2 Hin1 Hin2_k1 Hin2_k2.
  eapply witness_k_unique_in_T2.
  - exact Hval2.
  - exact Hin2_k1.
  - exact Hin2_k2.
Qed.

(**
   Symmetric: If two pairs share the same witness in T2, they must be identical.
*)
Lemma witness_pair_injective_T2 :
  forall (A B C : list Char) (T1 : Trace A B) (T2 : Trace B C) (i1 i2 k j : nat),
    is_valid_trace_aux T1 = true ->
    is_valid_trace_aux T2 = true ->
    In (i1, k) (compose_trace T1 T2) ->
    In (i2, k) (compose_trace T1 T2) ->
    In (i1, j) T1 ->
    In (i2, j) T1 ->
    In (j, k) T2 ->
    i1 = i2.
Proof.
  intros A B C T1 T2 i1 i2 k j Hval1 Hval2 Hin_comp1 Hin_comp2 Hin1_i1 Hin1_i2 Hin2.
  eapply valid_trace_unique_second.
  - exact Hval1.
  - exact Hin1_i1.
  - exact Hin1_i2.
Qed.

(**
   Main injectivity result: Distinct pairs in comp have distinct witnesses.

   If (i1,k1) ≠ (i2,k2), then their witness pairs (i1,j1), (j1,k1) and (i2,j2), (j2,k2)
   cannot both be equal.
*)
Lemma compose_witness_distinct :
  forall (A B C : list Char) (T1 : Trace A B) (T2 : Trace B C)
         (i1 k1 i2 k2 j1 j2 : nat),
    is_valid_trace_aux T1 = true ->
    is_valid_trace_aux T2 = true ->
    In (i1, k1) (compose_trace T1 T2) ->
    In (i2, k2) (compose_trace T1 T2) ->
    In (i1, j1) T1 ->
    In (j1, k1) T2 ->
    In (i2, j2) T1 ->
    In (j2, k2) T2 ->
    (i1, k1) <> (i2, k2) ->
    ((i1, j1) <> (i2, j2) \/ (j1, k1) <> (j2, k2)).
Proof.
  intros A B C T1 T2 i1 k1 i2 k2 j1 j2 Hval1 Hval2
         Hin_comp1 Hin_comp2 Hin1_1 Hin2_1 Hin1_2 Hin2_2 Hneq.
  destruct (pair_eq_dec (i1, j1) (i2, j2)) as [Heq_ij | Hneq_ij].
  - inversion Heq_ij; subst i2 j2.
    assert (Hk_eq: k1 = k2).
    {
      eapply witness_pair_injective_T1 with (i := i1) (j := j1).
      - exact Hval1.
      - exact Hval2.
      - exact Hin_comp1.
      - exact Hin_comp2.
      - exact Hin1_1.
      - exact Hin2_1.
      - exact Hin2_2.
    }
    subst k2.
    contradiction Hneq.
    reflexivity.
  - left. exact Hneq_ij.
Qed.

(** * Injectivity Infrastructure *)

(**
   Definition: A function is injective if distinct inputs map to distinct outputs.
*)
Definition injective {A B : Type} (f : A -> B) : Prop :=
  forall x y, f x = f y -> x = y.

(**
   Lemma: Injective mapping preserves NoDup property.

   If we map a NoDup list through an injective function, the result has NoDup.
*)
Lemma map_injective_NoDup :
  forall {A B : Type} (f : A -> B) (l : list A),
    injective f ->
    NoDup l ->
    NoDup (map f l).
Proof.
  intros A B f l Hinj Hnodup.
  induction Hnodup as [| x l' Hnotin Hnodup' IH].
  - simpl. constructor.
  - simpl. constructor.
    + intro Hin_fx.
      apply in_map_iff in Hin_fx as [y [Heq_fy Hin_y]].
      apply Hinj in Heq_fy. subst y.
      contradiction.
    + exact IH.
Qed.

(**
   Key lemma: Injective function from list with NoDup into list with NoDup
   preserves cardinality bound.

   If f maps all elements of l1 into l2, and f is injective, then |l1| ≤ |l2|.
*)
Lemma injective_image_bounded :
  forall {A B : Type} (f : A -> B) (l1 : list A) (l2 : list B),
    (forall x, In x l1 -> In (f x) l2) ->
    injective f ->
    NoDup l1 ->
    NoDup l2 ->
    length l1 <= length l2.
Proof.
  intros A B f l1 l2 Himage Hinj Hnodup1 Hnodup2.
  assert (Hincl: incl (map f l1) l2).
  {
    intros y Hin_y.
    apply in_map_iff in Hin_y as [x [Heq Hin_x]].
    subst y.
    apply Himage. exact Hin_x.
  }
  assert (Hnodup_map: NoDup (map f l1)).
  {
    apply map_injective_NoDup; assumption.
  }
  assert (Hlen_map: length (map f l1) <= length l2).
  {
    eapply incl_length_NoDup; eauto.
  }
  rewrite map_length in Hlen_map.
  exact Hlen_map.
Qed.

(** * Helper Lemmas *)

(**
   Helper: filter preserves length bound.
*)
Lemma filter_length_le :
  forall {A : Type} (f : A -> bool) (l : list A),
    length (filter f l) <= length l.
Proof.
  intros A f l.
  induction l as [| a l' IH].
  - simpl. lia.
  - simpl. destruct (f a); simpl; lia.
Qed.

(**
   Helper: fold_left with cons increases length.
*)
Lemma fold_left_cons_length :
  forall (i : nat) (l : list (nat * nat)) (acc : list (nat * nat)),
    length (fold_left (fun acc2 p2 =>
      let '(_, k) := p2 in (i, k) :: acc2) l acc) =
    length acc + length l.
Proof.
  intros i l.
  induction l as [| [j k] l' IH]; intro acc.
  - simpl. lia.
  - simpl. rewrite IH. simpl. lia.
Qed.

(**
   Helper: NoDup on map fst means unique second components.
*)
Lemma NoDup_fst_unique_snd :
  forall (T : list (nat * nat)) (a b c : nat),
    NoDup (map fst T) ->
    In (a, b) T ->
    In (a, c) T ->
    b = c.
Proof.
  intros T.
  induction T as [| [x y] T' IH]; intros a b c HnodupFst Hin_ab Hin_ac.
  - inversion Hin_ab.
  - simpl in HnodupFst.
    inversion HnodupFst as [| ? ? Hnotin_x HnodupT']. subst.
    destruct Hin_ab as [Heq_ab | Hin_ab_tail].
    + inversion Heq_ab. subst x y.
      destruct Hin_ac as [Heq_ac | Hin_ac_tail].
      * inversion Heq_ac. reflexivity.
      * exfalso.
        apply Hnotin_x.
        apply in_map_iff.
        exists (a, c). split; simpl; auto.
    + destruct Hin_ac as [Heq_ac | Hin_ac_tail].
      * inversion Heq_ac. subst x y.
        exfalso.
        apply Hnotin_x.
        apply in_map_iff.
        exists (a, b). split; simpl; auto.
      * eapply IH; eauto.
Qed.

(**
   Helper: For NoDup list of pairs, filtering by first component gives ≤ 1 match.
*)
Lemma filter_first_component_NoDup :
  forall (T : list (nat * nat)) (j : nat),
    NoDup (map fst T) ->
    length (filter (fun p => let '(j2, _) := p in j =? j2) T) <= 1.
Proof.
  intros T j HnodupFst.
  induction T as [| [a b] T' IH].
  - simpl. lia.
  - simpl in HnodupFst.
    inversion HnodupFst as [| ? ? Hnotin HnodupT']; subst.
    assert (IH': length (filter (fun p : nat * nat => let '(j2, _) := p in j =? j2) T') <= 1).
    { apply IH. exact HnodupT'. }
    simpl.
    destruct (j =? a) eqn:Heq.
    + apply Nat.eqb_eq in Heq. subst a.
      assert (Hfilter_empty: filter (fun p : nat * nat => let '(j2, _) := p in j =? j2) T' = []).
      {
        destruct (filter (fun p : nat * nat => let '(j2, _) := p in j =? j2) T') as [| p rest] eqn:Hfilter.
        - reflexivity.
        - exfalso.
          assert (Hin_p: In p (filter (fun p : nat * nat => let '(j2, _) := p in j =? j2) T')).
          { rewrite Hfilter. left. reflexivity. }
          apply filter_In in Hin_p as [Hin_T' Hmatch].
          destruct p as [j2 k2].
          simpl in Hmatch.
          apply Nat.eqb_eq in Hmatch. subst j2.
          assert (Hin_j: In j (map fst T')).
          { apply in_map_iff. exists (j, k2). split; auto. }
          contradiction.
      }
      rewrite Hfilter_empty.
      simpl. lia.
    + exact IH'.
Qed.

(** * Witness Extraction Functions *)

(**
   Definition: Extract witness from T1 for a composition element.

   For (i,k) ∈ compose_trace T1 T2, extract the (i,j) ∈ T1 used in its construction.
*)
Definition witness_to_T1 (A B C : list Char) (T1 : Trace A B) (T2 : Trace B C)
  (ik : nat * nat) : nat * nat :=
  let '(i, k) := ik in
  match find (fun p1 => let '(i1, _) := p1 in i =? i1) T1 with
  | Some (i', j) => (i', j)
  | None => (0, 0)
  end.

(**
   Definition: Extract witness from T2 for a composition element.

   For (i,k) ∈ compose_trace T1 T2, extract the (j,k) ∈ T2 used in its construction.
*)
Definition witness_to_T2 (A B C : list Char) (T1 : Trace A B) (T2 : Trace B C)
  (ik : nat * nat) : nat * nat :=
  let '(i, k) := ik in
  match witness_j_for_comp A B C T1 T2 ik with
  | Some j =>
      match find (fun p2 => let '(j2, k2) := p2 in (j =? j2) && (k =? k2)) T2 with
      | Some jk => jk
      | None => (0, 0)
      end
  | None => (0, 0)
  end.

(**
   Lemma: witness_to_T1 extracts a valid element of T1.
*)
Lemma witness_to_T1_correct :
  forall (A B C : list Char) (T1 : Trace A B) (T2 : Trace B C) (ik : nat * nat),
    In ik (compose_trace T1 T2) ->
    In (witness_to_T1 A B C T1 T2 ik) T1.
Proof.
  intros A B C T1 T2 [i k] Hin_comp.
  apply In_compose_trace in Hin_comp as [j [Hin1 Hin2]].
  unfold witness_to_T1.
  simpl.
  assert (Hexists: exists y, find (fun p1 : nat * nat => let '(i1, _) := p1 in i =? i1) T1 = Some y /\
                             (fun p1 : nat * nat => let '(i1, _) := p1 in i =? i1) y = true).
  { apply in_find_some with (x := (i, j)).
    - exact Hin1.
    - simpl. apply Nat.eqb_refl. }
  destruct Hexists as [[i' j'] [Hfind_eq _]].
  rewrite Hfind_eq.
  apply find_some_in_iff in Hfind_eq as [Hin_i'j' _].
  exact Hin_i'j'.
Qed.

(**
   Lemma: witness_to_T2 extracts a valid element of T2.
*)
Lemma witness_to_T2_correct :
  forall (A B C : list Char) (T1 : Trace A B) (T2 : Trace B C) (ik : nat * nat),
    is_valid_trace_aux T1 = true ->
    is_valid_trace_aux T2 = true ->
    In ik (compose_trace T1 T2) ->
    In (witness_to_T2 A B C T1 T2 ik) T2.
Proof.
  intros A B C T1 T2 [i k] Hval1 Hval2 Hin_comp.
  assert (Hin_comp_copy: In (i, k) (compose_trace T1 T2)) by exact Hin_comp.
  apply In_compose_trace in Hin_comp as [j [Hin1 Hin2]].
  assert (Hwitness: witness_j_for_comp A B C T1 T2 (i, k) = Some j).
  { apply extract_witness_j_correct with (i := i) (k := k) (j := j).
    - exact Hval1.
    - exact Hval2.
    - exact Hin_comp_copy.
    - exact Hin1.
    - exact Hin2. }
  unfold witness_to_T2.
  rewrite Hwitness.
  simpl.
  assert (Hexists: exists y, find (fun p2 : nat * nat => let '(j2, k2) := p2 in (j =? j2) && (k =? k2)) T2 = Some y /\
                             (fun p2 : nat * nat => let '(j2, k2) := p2 in (j =? j2) && (k =? k2)) y = true).
  { apply in_find_some with (x := (j, k)).
    - exact Hin2.
    - simpl. rewrite Nat.eqb_refl, Nat.eqb_refl. reflexivity. }
  destruct Hexists as [[j' k'] [Hfind_eq _]].
  rewrite Hfind_eq.
  apply find_some_in_iff in Hfind_eq as [Hin_j'k' _].
  exact Hin_j'k'.
Qed.

(** * Fold Left Infrastructure *)

(** Helper: fold_left with addition preserves initial value ordering. *)
Lemma fold_left_add_init_monotone :
  forall {A : Type} (l : list A) (f : A -> nat) (init1 init2 : nat),
    init1 <= init2 ->
    fold_left (fun acc x => acc + f x) l init1 <=
    fold_left (fun acc x => acc + f x) l init2.
Proof.
  intros AA l f init1 init2 H_init.
  generalize dependent init2.
  generalize dependent init1.
  induction l as [| a l' IH].
  - intros init1 init2 H_init. simpl. exact H_init.
  - intros init1 init2 H_init. simpl. apply IH. lia.
Qed.

(** Helper: Fold_left with cons increases sum. *)
Lemma fold_left_sum_cons_le :
  forall {A : Type} (f : A -> nat) (x : A) (l : list A),
    fold_left (fun acc y => acc + f y) l 0 <=
    fold_left (fun acc y => acc + f y) (x :: l) 0.
Proof.
  intros AA f x l.
  simpl. replace (0 + f x) with (f x) by lia.
  apply fold_left_add_init_monotone. lia.
Qed.

(** Helper: fold_left with addition distributes over initial accumulator. *)
Lemma fold_left_add_init_shift :
  forall {A : Type} (f : A -> nat) (l : list A) (init : nat),
    fold_left (fun acc y => acc + f y) l init =
    init + fold_left (fun acc y => acc + f y) l 0.
Proof.
  intros AA f l init.
  generalize dependent init.
  induction l as [| x l' IH].
  - intro init. simpl. lia.
  - intro init. simpl. rewrite IH. rewrite (IH (f x)). lia.
Qed.

(** Helper: fold_left over l1 ++ [x] ++ l2 can be decomposed. *)
Lemma fold_left_sum_insert_middle :
  forall {A : Type} (f : A -> nat) (x : A) (l1 l2 : list A),
    fold_left (fun acc y => acc + f y) (l1 ++ x :: l2) 0 =
    fold_left (fun acc y => acc + f y) l1 0 + f x + fold_left (fun acc y => acc + f y) l2 0.
Proof.
  intros AA f x l1 l2.
  rewrite fold_left_app. simpl.
  rewrite fold_left_add_init_shift. lia.
Qed.

(** Corollary: fold_left over l1 ++ l2 sums the individual folds. *)
Lemma fold_left_app_sum :
  forall {A : Type} (f : A -> nat) (l1 l2 : list A),
    fold_left (fun acc y => acc + f y) (l1 ++ l2) 0 =
    fold_left (fun acc y => acc + f y) l1 0 + fold_left (fun acc y => acc + f y) l2 0.
Proof.
  intros AA f l1 l2.
  rewrite fold_left_app.
  rewrite fold_left_add_init_shift. lia.
Qed.

(** Helper: Adding the same value to both sides of an inequality preserves it. *)
Lemma add_middle_preserves_le :
  forall a b c d : nat,
    a + b <= c ->
    a + d + b <= d + c.
Proof. intros. lia. Qed.

(** Helper: fold_left with triangle inequality bound (generalized). *)
Lemma fold_left_triangle_bound_gen :
  forall {A : Type} (l : list A)
         (fAC fAB fBC : A -> nat) (init1 init2 init3 : nat),
    init1 <= init2 + init3 ->
    (forall x, In x l -> fAC x <= fAB x + fBC x) ->
    fold_left (fun acc x => acc + fAC x) l init1 <=
    fold_left (fun acc x => acc + fAB x) l init2 +
    fold_left (fun acc x => acc + fBC x) l init3.
Proof.
  intros AA l.
  induction l as [| x l' IH]; intros fAC fAB fBC init1 init2 init3 H_init H_tri.
  - simpl. exact H_init.
  - simpl.
    apply IH.
    + assert (Hx: fAC x <= fAB x + fBC x). { apply H_tri. left. reflexivity. }
      pose proof (Nat.add_le_mono _ _ _ _ H_init Hx) as H.
      assert (Heq: init2 + init3 + (fAB x + fBC x) = (init2 + fAB x) + (init3 + fBC x)) by ring.
      rewrite Heq in H. exact H.
    + intros y Hy. apply H_tri. right. exact Hy.
Qed.

(** Helper: fold_left with triangle inequality bound. *)
Lemma fold_left_triangle_bound :
  forall {A : Type} (l : list A)
         (fAC fAB fBC : A -> nat),
    (forall x, In x l -> fAC x <= fAB x + fBC x) ->
    fold_left (fun acc x => acc + fAC x) l 0 <=
    fold_left (fun acc x => acc + fAB x) l 0 +
    fold_left (fun acc x => acc + fBC x) l 0.
Proof.
  intros AA l fAC fAB fBC H_triangle.
  apply (fold_left_triangle_bound_gen l fAC fAB fBC 0 0 0).
  - lia.
  - exact H_triangle.
Qed.

(** Sum over a subset is bounded by sum over the superset. *)
Lemma fold_left_sum_bound_subset :
  forall (f : nat * nat -> nat) (sub super : list (nat * nat)),
    NoDup sub ->
    NoDup super ->
    (forall x, In x sub -> In x super) ->
    fold_left (fun sum ik => sum + f ik) sub 0 <=
    fold_left (fun sum ik => sum + f ik) super 0.
Proof.
  intros f sub super H_NoDup_sub H_NoDup_super H_subset.
  generalize dependent sub.
  induction super as [| x super' IH].
  - intros sub H_NoDup_sub H_subset.
    destruct sub as [| y sub'].
    + simpl. lia.
    + exfalso. specialize (H_subset y (or_introl eq_refl)).
      simpl in H_subset. exact H_subset.
  - intros sub H_NoDup_sub H_subset.
    inversion H_NoDup_super as [| x' super'' H_x_not_in_super' H_NoDup_super']; subst.
    destruct (in_dec pair_eq_dec x sub) as [H_x_in_sub | H_x_not_in_sub].
    + apply in_split in H_x_in_sub as [sub1 [sub2 H_sub_eq]].
      assert (H_NoDup_decomposed: NoDup (sub1 ++ x :: sub2)).
      { rewrite <- H_sub_eq. exact H_NoDup_sub. }
      assert (H_NoDup_rest: NoDup (sub1 ++ sub2)).
      { apply NoDup_remove_1 in H_NoDup_decomposed. exact H_NoDup_decomposed. }
      assert (H_x_not_in_rest: ~In x (sub1 ++ sub2)).
      { assert (H_NoDup_decomposed2: NoDup (sub1 ++ x :: sub2)).
        { rewrite <- H_sub_eq. exact H_NoDup_sub. }
        apply NoDup_remove_2 in H_NoDup_decomposed2. exact H_NoDup_decomposed2. }
      assert (H_rest_subset: forall y, In y (sub1 ++ sub2) -> In y super').
      { intros y H_in_rest.
        assert (H_y_in_sub: In y (sub1 ++ x :: sub2)).
        { apply in_or_app. apply in_app_or in H_in_rest as [H1 | H2].
          - left. exact H1.
          - right. right. exact H2. }
        rewrite <- H_sub_eq in H_y_in_sub.
        specialize (H_subset y H_y_in_sub).
        simpl in H_subset.
        destruct H_subset as [H_eq | H_in_super']; [| exact H_in_super'].
        subst y. contradiction. }
      specialize (IH H_NoDup_super' (sub1 ++ sub2) H_NoDup_rest H_rest_subset).
      rewrite H_sub_eq.
      rewrite fold_left_sum_insert_middle.
      simpl. replace (0 + f x) with (f x) by lia.
      rewrite fold_left_app_sum in IH.
      assert (H_rhs_eq: fold_left (fun sum ik => sum + f ik) super' (f x) =
                        f x + fold_left (fun sum ik => sum + f ik) super' 0).
      { apply fold_left_add_init_shift. }
      rewrite H_rhs_eq.
      apply add_middle_preserves_le.
      exact IH.
    + assert (H_sub_in_super': forall y, In y sub -> In y super').
      { intros y H_y_in_sub.
        specialize (H_subset y H_y_in_sub).
        simpl in H_subset.
        destruct H_subset as [H_eq | H_in_super']; [| exact H_in_super'].
        subst y. contradiction. }
      specialize (IH H_NoDup_super' sub H_NoDup_sub H_sub_in_super').
      transitivity (fold_left (fun sum ik => sum + f ik) super' 0).
      * exact IH.
      * apply fold_left_sum_cons_le.
Qed.

(** Image of witness_to_T1 over compose_trace is a subset of T1. *)
Lemma witness_T1_image_subset :
  forall (A B C : list Char) (T1 : Trace A B) (T2 : Trace B C),
    is_valid_trace A B T1 = true ->
    is_valid_trace B C T2 = true ->
    forall ik, In ik (compose_trace T1 T2) ->
      In (witness_to_T1 A B C T1 T2 ik) T1.
Proof.
  intros A B C T1 T2 Hval1 Hval2 ik Hik.
  apply witness_to_T1_correct; assumption.
Qed.

(** Image of witness_to_T2 over compose_trace is a subset of T2. *)
Lemma witness_T2_image_subset :
  forall (A B C : list Char) (T1 : Trace A B) (T2 : Trace B C),
    is_valid_trace A B T1 = true ->
    is_valid_trace B C T2 = true ->
    forall ik, In ik (compose_trace T1 T2) ->
      In (witness_to_T2 A B C T1 T2 ik) T2.
Proof.
  intros A B C T1 T2 Hval1 Hval2 ik Hik.
  unfold is_valid_trace in Hval1, Hval2.
  apply andb_prop in Hval1 as [Hval1_rest Hnodup1].
  apply andb_prop in Hval1_rest as [Hvalid1 Hval1_aux].
  apply andb_prop in Hval2 as [Hval2_rest Hnodup2].
  apply andb_prop in Hval2_rest as [Hvalid2 Hval2_aux].
  apply witness_to_T2_correct; assumption.
Qed.

(** Triangle inequality for witness costs. *)
Lemma witness_cost_triangle_bound :
  forall (A B C : list Char) (T1 : Trace A B) (T2 : Trace B C) (ik : nat * nat),
    is_valid_trace_aux T1 = true ->
    is_valid_trace_aux T2 = true ->
    In ik (compose_trace T1 T2) ->
    let '(i, k) := ik in
    subst_cost (nth (i-1) A default_char) (nth (k-1) C default_char) <=
    (let '(i', j) := witness_to_T1 A B C T1 T2 ik in
     subst_cost (nth (i'-1) A default_char) (nth (j-1) B default_char)) +
    (let '(j', k') := witness_to_T2 A B C T1 T2 ik in
     subst_cost (nth (j'-1) B default_char) (nth (k'-1) C default_char)).
Proof.
  intros A B C T1 T2 ik Hval1 Hval2 Hik.
  destruct ik as [i k].
  remember (witness_to_T1 A B C T1 T2 (i, k)) as w1 eqn:Hw1.
  remember (witness_to_T2 A B C T1 T2 (i, k)) as w2 eqn:Hw2.
  destruct w1 as [i' j]. destruct w2 as [j' k']. simpl.
  apply In_compose_trace in Hik as [jw [Hin1 Hin2]].
  assert (Hik_copy: In (i, k) (compose_trace T1 T2)).
  { apply In_compose_trace. exists jw. split; assumption. }
  unfold witness_to_T1 in Hw1. simpl in Hw1.
  assert (Hfind1_ex: exists p, find (fun p1 => let '(i1, _) := p1 in i =? i1) T1 = Some p).
  { destruct (in_find_some (fun p1 => let '(i1, _) := p1 in i =? i1) T1 (i, jw)) as [p [Hf _]].
    - exact Hin1.
    - simpl. apply Nat.eqb_refl.
    - exists p. exact Hf. }
  destruct Hfind1_ex as [[i'' jw''] Hfind1].
  assert (Hfind1_copy: find (fun p1 => let '(i1, _) := p1 in i =? i1) T1 = Some (i'', jw'')) by exact Hfind1.
  rewrite Hfind1 in Hw1. inversion Hw1. subst i' j.
  apply find_some_in_iff in Hfind1 as [_ Hpred1]. simpl in Hpred1.
  apply Nat.eqb_eq in Hpred1. subst i''.
  assert (Hjw_eq: jw'' = jw).
  { apply (valid_trace_unique_first T1 i jw'' jw Hval1).
    - apply find_some_in_iff in Hfind1_copy as [Hin_find _]. exact Hin_find.
    - exact Hin1. }
  subst jw''.
  unfold witness_to_T2 in Hw2.
  assert (Hwitj: witness_j_for_comp A B C T1 T2 (i, k) = Some jw).
  { apply extract_witness_j_correct with (i := i) (k := k) (j := jw); auto. }
  rewrite Hwitj in Hw2. simpl in Hw2.
  assert (Hfind2_ex: exists p, find (fun p2 => let '(j2, k2) := p2 in (jw =? j2) && (k =? k2)) T2 = Some p).
  { destruct (in_find_some (fun p2 => let '(j2, k2) := p2 in (jw =? j2) && (k =? k2)) T2 (jw, k)) as [p [Hf _]].
    - exact Hin2.
    - simpl. rewrite Nat.eqb_refl, Nat.eqb_refl. reflexivity.
    - exists p. exact Hf. }
  destruct Hfind2_ex as [[jw2 k2] Hfind2].
  rewrite Hfind2 in Hw2. inversion Hw2. subst j' k'.
  apply find_some_in_iff in Hfind2 as [_ Hpred2]. simpl in Hpred2.
  apply Bool.andb_true_iff in Hpred2 as [Hj_eq Hk_eq].
  apply Nat.eqb_eq in Hj_eq. apply Nat.eqb_eq in Hk_eq. subst jw2 k2.
  apply subst_cost_triangle.
Qed.

(** * Witness Injectivity Lemmas *)

(**
   Lemma: witness_to_T1 is injective.

   Distinct pairs in the composition have distinct witnesses in T1.
*)
Lemma witness_to_T1_injective :
  forall (A B C : list Char) (T1 : Trace A B) (T2 : Trace B C) (ik1 ik2 : nat * nat),
    is_valid_trace_aux T1 = true ->
    is_valid_trace_aux T2 = true ->
    In ik1 (compose_trace T1 T2) ->
    In ik2 (compose_trace T1 T2) ->
    witness_to_T1 A B C T1 T2 ik1 = witness_to_T1 A B C T1 T2 ik2 ->
    ik1 = ik2.
Proof.
  intros A B C T1 T2 [i1 k1] [i2 k2] Hval1 Hval2 Hin1_comp Hin2_comp Heq_witness.
  apply In_compose_trace in Hin1_comp as [j1 [Hin1_T1 Hin1_T2]].
  apply In_compose_trace in Hin2_comp as [j2 [Hin2_T1 Hin2_T2]].
  unfold witness_to_T1 in Heq_witness.
  simpl in Heq_witness.
  destruct (in_find_some (fun p1 : nat * nat => let '(i, _) := p1 in i1 =? i) T1 (i1, j1)) as [[i1' j1'] [Hfind1 _]].
  { exact Hin1_T1. }
  { simpl. apply Nat.eqb_refl. }
  destruct (in_find_some (fun p1 : nat * nat => let '(i, _) := p1 in i2 =? i) T1 (i2, j2)) as [[i2' j2'] [Hfind2 _]].
  { exact Hin2_T1. }
  { simpl. apply Nat.eqb_refl. }
  rewrite Hfind1, Hfind2 in Heq_witness.
  inversion Heq_witness. subst i2' j2'.
  apply find_some_in_iff in Hfind1 as [Hin1' Hpred1].
  apply find_some_in_iff in Hfind2 as [Hin2' Hpred2].
  simpl in Hpred1, Hpred2.
  apply Nat.eqb_eq in Hpred1. apply Nat.eqb_eq in Hpred2.
  subst i1' i2.
  assert (Hj1'_eq: j1' = j1).
  { eapply witness_j_unique_in_T1.
    - exact Hval1.
    - exact Hin1'.
    - exact Hin1_T1. }
  subst j1'.
  assert (Hj2_eq: j2 = j1).
  { eapply witness_j_unique_in_T1.
    - exact Hval1.
    - exact Hin2_T1.
    - exact Hin2'. }
  subst j2.
  assert (Hk_eq: k1 = k2).
  { eapply witness_k_unique_in_T2.
    - exact Hval2.
    - exact Hin1_T2.
    - exact Hin2_T2. }
  subst k2.
  reflexivity.
Qed.

(**
   Lemma: witness_to_T2 is injective.

   Symmetric to witness_to_T1_injective.
*)
Lemma witness_to_T2_injective :
  forall (A B C : list Char) (T1 : Trace A B) (T2 : Trace B C) (ik1 ik2 : nat * nat),
    is_valid_trace_aux T1 = true ->
    is_valid_trace_aux T2 = true ->
    In ik1 (compose_trace T1 T2) ->
    In ik2 (compose_trace T1 T2) ->
    witness_to_T2 A B C T1 T2 ik1 = witness_to_T2 A B C T1 T2 ik2 ->
    ik1 = ik2.
Proof.
  intros A B C T1 T2 [i1 k1] [i2 k2] Hval1 Hval2 Hin1_comp Hin2_comp Heq_witness.
  apply In_compose_trace in Hin1_comp as [j1 [Hin1_T1 Hin1_T2]].
  apply In_compose_trace in Hin2_comp as [j2 [Hin2_T1 Hin2_T2]].
  assert (Hin1_comp_copy: In (i1, k1) (compose_trace T1 T2)) by (apply In_compose_trace; exists j1; auto).
  assert (Hin2_comp_copy: In (i2, k2) (compose_trace T1 T2)) by (apply In_compose_trace; exists j2; auto).
  assert (Hw1: witness_j_for_comp A B C T1 T2 (i1, k1) = Some j1).
  { apply extract_witness_j_correct with (i := i1) (k := k1) (j := j1); auto. }
  assert (Hw2: witness_j_for_comp A B C T1 T2 (i2, k2) = Some j2).
  { apply extract_witness_j_correct with (i := i2) (k := k2) (j := j2); auto. }
  unfold witness_to_T2 in Heq_witness.
  rewrite Hw1, Hw2 in Heq_witness.
  simpl in Heq_witness.
  destruct (in_find_some (fun p2 : nat * nat => let '(j, k) := p2 in (j1 =? j) && (k1 =? k)) T2 (j1, k1)) as [[j1' k1'] [Hfind1 _]].
  { exact Hin1_T2. }
  { simpl. rewrite Nat.eqb_refl, Nat.eqb_refl. reflexivity. }
  destruct (in_find_some (fun p2 : nat * nat => let '(j, k) := p2 in (j2 =? j) && (k2 =? k)) T2 (j2, k2)) as [[j2' k2'] [Hfind2 _]].
  { exact Hin2_T2. }
  { simpl. rewrite Nat.eqb_refl, Nat.eqb_refl. reflexivity. }
  rewrite Hfind1, Hfind2 in Heq_witness.
  inversion Heq_witness. subst j2' k2'.
  apply find_some_in_iff in Hfind1 as [Hin1' Hpred1].
  apply find_some_in_iff in Hfind2 as [Hin2' Hpred2].
  simpl in Hpred1, Hpred2.
  apply andb_true_iff in Hpred1 as [Hj1_eq Hk1_eq].
  apply andb_true_iff in Hpred2 as [Hj2_eq Hk2_eq].
  apply Nat.eqb_eq in Hj1_eq, Hk1_eq, Hj2_eq, Hk2_eq.
  subst j1' k1' j2 k2.
  assert (Hi_eq: i1 = i2).
  { eapply valid_trace_unique_second.
    - exact Hval1.
    - exact Hin1_T1.
    - exact Hin2_T1. }
  subst i2.
  reflexivity.
Qed.

(**
   Helper: map preserves NoDup when f is injective on the list elements.
*)
Lemma map_injective_on_list_NoDup :
  forall {A B : Type} (f : A -> B) (l : list A),
    (forall x y, In x l -> In y l -> f x = f y -> x = y) ->
    NoDup l ->
    NoDup (map f l).
Proof.
  intros A0 B0 f l Hinj_on_l Hnodup.
  induction Hnodup as [| x l' Hnotin Hnodup' IH].
  - simpl. constructor.
  - simpl.
    constructor.
    + intro Hin_fx.
      apply in_map_iff in Hin_fx as [y [Heq_fy Hin_y]].
      assert (Heq_xy: x = y).
      { apply Hinj_on_l.
        - left. reflexivity.
        - right. exact Hin_y.
        - symmetry. exact Heq_fy. }
      subst y.
      contradiction.
    + apply IH.
      intros x' y' Hin_x' Hin_y' Heq_fx'y'.
      apply Hinj_on_l; try assumption.
      * right. exact Hin_x'.
      * right. exact Hin_y'.
Qed.

(** * Fold Left Map Infrastructure *)

(**
   Lemma: fold_left over a composition f ∘ g equals fold_left over the mapped list.
*)
Lemma fold_left_sum_map_eq :
  forall {A B : Type} (f : B -> nat) (g : A -> B) (l : list A) (init : nat),
    fold_left (fun acc x => acc + f (g x)) l init =
    fold_left (fun acc y => acc + f y) (map g l) init.
Proof.
  intros A0 B0 f g l.
  induction l as [| x l' IH]; intros init.
  - simpl. reflexivity.
  - simpl. apply IH.
Qed.

(**
   Lemma: Equivalence between pattern matching and let-destruct syntax in fold_left.
*)
Lemma fold_left_pair_let_eq :
  forall (f : nat -> nat -> nat) (l : list (nat * nat)) (init : nat),
    fold_left (fun acc ik => acc + (let '(i, j) := ik in f i j)) l init =
    fold_left (fun acc '(i, j) => acc + f i j) l init.
Proof.
  intros f l.
  induction l as [| [i j] l' IH]; intros init.
  - reflexivity.
  - simpl. apply IH.
Qed.

(**
   Variant: when let wraps the entire body (including acc +).
   This matches the form used in trace_cost definitions.
*)
Lemma fold_left_pair_let_body_eq :
  forall (f : nat -> nat -> nat) (l : list (nat * nat)) (init : nat),
    fold_left (fun acc p => let '(i, j) := p in acc + f i j) l init =
    fold_left (fun acc '(i, j) => acc + f i j) l init.
Proof.
  intros f l.
  induction l as [| [i j] l' IH]; intros init.
  - reflexivity.
  - simpl. apply IH.
Qed.

(** * Composition Size and Subset Lemmas *)

(** Helper: NoDup subset implies length inequality. *)
Lemma NoDup_subset_length_le :
  forall {A : Type} (xs ys : list A),
    NoDup xs ->
    NoDup ys ->
    (forall x, In x xs -> In x ys) ->
    length xs <= length ys.
Proof.
  intros A0 xs ys H_nodup_xs H_nodup_ys H_subset.
  apply NoDup_incl_length.
  - exact H_nodup_xs.
  - unfold incl. exact H_subset.
Qed.

(** Composition sources are subset of T1 sources. *)
Lemma touched_comp_A_subset_T1_A :
  forall (A B C : list Char) (T1 : Trace A B) (T2 : Trace B C) (i : nat),
    In i (touched_in_A A C (compose_trace T1 T2)) ->
    In i (touched_in_A A B T1).
Proof.
  intros A B C T1 T2 i H_in.
  unfold touched_in_A in H_in.
  assert (H_pair: exists k, In (i, k) (compose_trace T1 T2)).
  { clear -H_in.
    generalize dependent i.
    induction (compose_trace T1 T2) as [| [i' k'] comp' IH].
    - intros i H. simpl in H. contradiction.
    - intros i H. simpl in H.
      destruct H as [H_eq | H_rest].
      + exists k'. left. rewrite H_eq. reflexivity.
      + destruct (IH i H_rest) as [k H_in_rest].
        exists k. right. exact H_in_rest. }
  destruct H_pair as [k H_in_comp].
  apply In_compose_trace in H_in_comp as [j [H_in_T1 _]].
  clear -H_in_T1.
  induction T1 as [| [i' j'] T1' IH].
  - simpl in H_in_T1. contradiction.
  - simpl in H_in_T1. simpl.
    destruct H_in_T1 as [H_eq | H_rest].
    + injection H_eq as H_i H_j. left. exact H_i.
    + right. apply IH. exact H_rest.
Qed.

(** Composition targets are subset of T2 targets. *)
Lemma touched_comp_C_subset_T2_C :
  forall (A B C : list Char) (T1 : Trace A B) (T2 : Trace B C) (k : nat),
    In k (touched_in_B A C (compose_trace T1 T2)) ->
    In k (touched_in_B B C T2).
Proof.
  intros A B C T1 T2 k H_in.
  assert (H_pair: exists i, In (i, k) (compose_trace T1 T2)).
  { clear -H_in.
    generalize dependent k.
    induction (compose_trace T1 T2) as [| [i' k'] comp' IH].
    - intros k H. simpl in H. contradiction.
    - intros k H. simpl in H.
      destruct H as [H_eq | H_rest].
      + exists i'. left. rewrite H_eq. reflexivity.
      + destruct (IH k H_rest) as [i H_in_rest].
        exists i. right. exact H_in_rest. }
  destruct H_pair as [i H_in_comp].
  apply In_compose_trace in H_in_comp as [j [_ H_in_T2]].
  clear -H_in_T2.
  induction T2 as [| [j' k'] T2' IH].
  - simpl in H_in_T2. contradiction.
  - simpl in H_in_T2. simpl.
    destruct H_in_T2 as [H_eq | H_rest].
    + injection H_eq as H_j H_k. left. exact H_k.
    + right. apply IH. exact H_rest.
Qed.

(** Composition sources have length ≤ T1 sources. *)
Lemma touched_comp_A_length_le :
  forall (A B C : list Char) (T1 : Trace A B) (T2 : Trace B C),
    is_valid_trace A B T1 = true ->
    is_valid_trace B C T2 = true ->
    length (touched_in_A A C (compose_trace T1 T2)) <= length (touched_in_A A B T1).
Proof.
  intros A B C T1 T2 H_valid1 H_valid2.
  assert (H_nodup_T1: NoDup (touched_in_A A B T1)).
  { apply touched_in_A_NoDup. exact H_valid1. }
  assert (H_nodup_comp: NoDup (touched_in_A A C (compose_trace T1 T2))).
  { apply touched_in_A_NoDup.
    apply compose_trace_preserves_validity; assumption. }
  apply NoDup_subset_length_le.
  - exact H_nodup_comp.
  - exact H_nodup_T1.
  - intros i H_in.
    apply (touched_comp_A_subset_T1_A A B C T1 T2).
    exact H_in.
Qed.

(** Composition targets have length ≤ T2 targets. *)
Lemma touched_comp_C_length_le :
  forall (A B C : list Char) (T1 : Trace A B) (T2 : Trace B C),
    is_valid_trace A B T1 = true ->
    is_valid_trace B C T2 = true ->
    length (touched_in_B A C (compose_trace T1 T2)) <= length (touched_in_B B C T2).
Proof.
  intros A B C T1 T2 H_valid1 H_valid2.
  assert (H_nodup_T2: NoDup (touched_in_B B C T2)).
  { apply touched_in_B_NoDup. exact H_valid2. }
  assert (H_nodup_comp: NoDup (touched_in_B A C (compose_trace T1 T2))).
  { apply touched_in_B_NoDup.
    apply compose_trace_preserves_validity; assumption. }
  apply NoDup_subset_length_le.
  - exact H_nodup_comp.
  - exact H_nodup_T2.
  - intros k H_in.
    apply (touched_comp_C_subset_T2_C A B C T1 T2).
    exact H_in.
Qed.

(** * Pigeonhole and Size Bound Lemmas *)

(** Helper: existsb_touched_in_A_In - convert existsb to In *)
Lemma existsb_touched_in_A_In :
  forall (B C : list Char) (T : Trace B C) (j : nat),
    existsb (fun y => j =? y) (touched_in_A B C T) = true ->
    In j (touched_in_A B C T).
Proof.
  intros B C T j Hexists.
  apply existsb_exists in Hexists as [y [Hin Heq]].
  apply Nat.eqb_eq in Heq. subst. exact Hin.
Qed.

(** Helper: When j is in touched_in_A T, filter for j is non-empty. *)
Lemma in_touched_in_A_filter_nonempty :
  forall (B C : list Char) (T : Trace B C) (j : nat),
    In j (touched_in_A B C T) ->
    length (filter (fun p2 => let '(j2, _) := p2 in j =? j2) T) >= 1.
Proof.
  intros B C T j Hin.
  induction T as [| [j' k'] T' IH].
  - simpl in Hin. contradiction.
  - simpl in Hin. simpl.
    destruct Hin as [Heq | Hrest].
    + subst j'. rewrite Nat.eqb_refl. simpl. lia.
    + specialize (IH Hrest).
      destruct (j =? j') eqn:Hjj'; simpl; lia.
Qed.

(** Composition length >= intersection length. *)
Lemma compose_trace_length_ge_inter :
  forall (A B C : list Char) (T1 : Trace A B) (T2 : Trace B C),
    length (compose_trace T1 T2) >= length (list_inter (touched_in_B A B T1) (touched_in_A B C T2)).
Proof.
  intros A B C T1 T2.
  unfold compose_trace.
  assert (Hgen: forall acc,
    length (fold_left (fun acc' p1 =>
                         let '(i, j) := p1 in
                         let matches := filter (fun p2 => let '(j2, _) := p2 in j =? j2) T2 in
                         fold_left (fun acc2 p2 => let '(_, k) := p2 in (i, k) :: acc2) matches acc')
                      T1 acc) >=
    length acc + length (list_inter (touched_in_B A B T1) (touched_in_A B C T2))).
  { induction T1 as [| [i j] T1' IH]; intros acc.
    - simpl. lia.
    - simpl.
      destruct (existsb (fun y => j =? y) (touched_in_A B C T2)) eqn:Hj_in_T2.
      + simpl.
        apply existsb_touched_in_A_In in Hj_in_T2.
        assert (H_filter_ge1: length (filter (fun p2 => let '(j2, _) := p2 in j =? j2) T2) >= 1).
        { apply in_touched_in_A_filter_nonempty. exact Hj_in_T2. }
        set (matches := filter (fun p2 => let '(j2, _) := p2 in j =? j2) T2).
        set (inner_acc := fold_left (fun acc2 p2 => let '(_, k) := p2 in (i, k) :: acc2) matches acc).
        assert (H_inner_len: length inner_acc = length matches + length acc).
        { unfold inner_acc, matches.
          clear IH H_filter_ge1 Hj_in_T2.
          generalize acc as acc0.
          induction (filter (fun p2 : nat * nat => let '(j2, _) := p2 in j =? j2) T2) as [| [j' k'] ms IH]; intros acc0.
          - simpl. lia.
          - simpl. rewrite IH. simpl. lia. }
        specialize (IH inner_acc).
        unfold inner_acc, matches in *.
        lia.
      + simpl.
        set (matches := filter (fun p2 => let '(j2, _) := p2 in j =? j2) T2).
        set (inner_acc := fold_left (fun acc2 p2 => let '(_, k) := p2 in (i, k) :: acc2) matches acc).
        assert (H_inner_ge: length inner_acc >= length acc).
        { unfold inner_acc, matches.
          clear IH.
          generalize acc as acc0.
          induction (filter (fun p2 : nat * nat => let '(j2, _) := p2 in j =? j2) T2) as [| [j' k'] ms IH]; intros acc0.
          - simpl. lia.
          - simpl. specialize (IH ((i, k') :: acc0)). simpl in IH. lia. }
        specialize (IH inner_acc).
        unfold inner_acc, matches in *.
        lia. }
  specialize (Hgen []).
  simpl in Hgen.
  exact Hgen.
Qed.

(** Helper for pigeonhole: extract bounds from validity. *)
Lemma in_touched_in_B_valid_bound :
  forall (A B : list Char) (T : Trace A B) (j : nat),
    is_valid_trace A B T = true ->
    In j (touched_in_B A B T) ->
    1 <= j <= length B.
Proof.
  intros A B T j Hvalid Hj.
  split.
  - (* j >= 1 *)
    induction T as [| [i' j'] T' IH].
    + simpl in Hj. contradiction.
    + simpl in Hj.
      destruct Hj as [Heq | Hrest].
      * subst j'.
        unfold is_valid_trace in Hvalid.
        apply andb_true_iff in Hvalid as [Hvalid' _].
        apply andb_true_iff in Hvalid' as [Hbounds _].
        simpl in Hbounds.
        apply andb_true_iff in Hbounds as [Hbounds _].
        unfold valid_pair in Hbounds.
        (* valid_pair is: ((1 <=? i) && (i <=? lenA) && (1 <=? j) && (j <=? lenB))
           Left-associative: (((1 <=? i) && (i <=? lenA)) && (1 <=? j)) && (j <=? lenB) *)
        apply andb_true_iff in Hbounds as [Hbounds _].  (* splits off j <=? lenB *)
        apply andb_true_iff in Hbounds as [_ Hj_lb].    (* gives 1 <=? j *)
        (* 1 <=? j reduces to match j with 0 => false | S _ => true end *)
        destruct j as [| j''].
        -- simpl in Hj_lb. discriminate.
        -- lia.
      * apply IH; [| exact Hrest].
        unfold is_valid_trace in Hvalid |- *.
        apply andb_true_iff in Hvalid as [Hvalid' Hnodup].
        apply andb_true_iff in Hvalid' as [Hbounds Haux].
        simpl in Hbounds, Haux, Hnodup.
        apply andb_true_iff in Hbounds as [_ Hbounds'].
        apply andb_true_iff.
        split; [| simpl in Hnodup; apply andb_true_iff in Hnodup as [_ Hnodup']; exact Hnodup'].
        apply andb_true_iff. split; [exact Hbounds' |].
        destruct T' as [| [i'' j''] T''].
        -- reflexivity.
        -- simpl in Haux. apply andb_true_iff in Haux as [_ Haux']. exact Haux'.
  - (* j <= length B *)
    apply touched_in_B_all_le with (A := A) (T := T).
    + exact Hvalid.
    + exact Hj.
Qed.

(** Helper for pigeonhole: extract bounds from validity (touched_in_A). *)
Lemma in_touched_in_A_valid_bound :
  forall (B C : list Char) (T : Trace B C) (j : nat),
    is_valid_trace B C T = true ->
    In j (touched_in_A B C T) ->
    1 <= j <= length B.
Proof.
  intros B C T j Hvalid Hj.
  split.
  - (* j >= 1 *)
    induction T as [| [j' k'] T' IH].
    + simpl in Hj. contradiction.
    + simpl in Hj.
      destruct Hj as [Heq | Hrest].
      * subst j'.
        unfold is_valid_trace in Hvalid.
        apply andb_true_iff in Hvalid as [Hvalid' _].
        apply andb_true_iff in Hvalid' as [Hbounds _].
        simpl in Hbounds.
        apply andb_true_iff in Hbounds as [Hbounds _].
        unfold valid_pair in Hbounds.
        (* valid_pair is: ((1 <=? j) && (j <=? lenB) && (1 <=? k) && (k <=? lenC))
           We want 1 <=? j, which is the leftmost after 3 splits *)
        apply andb_true_iff in Hbounds as [Hbounds _].  (* splits off k <=? lenC *)
        apply andb_true_iff in Hbounds as [Hbounds _].  (* splits off 1 <=? k *)
        apply andb_true_iff in Hbounds as [Hj_lb _].    (* gives 1 <=? j *)
        (* 1 <=? j reduces to match j with 0 => false | S _ => true end *)
        destruct j as [| j''].
        -- simpl in Hj_lb. discriminate.
        -- lia.
      * apply IH; [| exact Hrest].
        unfold is_valid_trace in Hvalid |- *.
        apply andb_true_iff in Hvalid as [Hvalid' Hnodup].
        apply andb_true_iff in Hvalid' as [Hbounds Haux].
        simpl in Hbounds, Haux, Hnodup.
        apply andb_true_iff in Hbounds as [_ Hbounds'].
        apply andb_true_iff.
        split; [| simpl in Hnodup; apply andb_true_iff in Hnodup as [_ Hnodup']; exact Hnodup'].
        apply andb_true_iff. split; [exact Hbounds' |].
        destruct T' as [| [j'' k''] T''].
        -- reflexivity.
        -- simpl in Haux. apply andb_true_iff in Haux as [_ Haux']. exact Haux'.
  - (* j <= length B *)
    apply touched_in_A_all_le with (B := C) (T := T).
    + exact Hvalid.
    + exact Hj.
Qed.

(** Pigeonhole bound on composition size. *)
Lemma composition_size_pigeonhole :
  forall (A B C : list Char) (T1 : Trace A B) (T2 : Trace B C),
    is_valid_trace A B T1 = true ->
    is_valid_trace B C T2 = true ->
    length (touched_in_B A B T1) + length (touched_in_A B C T2) <=
    length B + length (compose_trace T1 T2).
Proof.
  intros A B C T1 T2 HvalT1 HvalT2.
  assert (H_nodup_T1B: NoDup (touched_in_B A B T1)).
  { apply touched_in_B_NoDup. exact HvalT1. }
  assert (H_nodup_T2B: NoDup (touched_in_A B C T2)).
  { apply touched_in_A_NoDup. exact HvalT2. }
  assert (H_T1B_bound: forall j, In j (touched_in_B A B T1) -> 1 <= j <= length B).
  { intros j Hj. apply in_touched_in_B_valid_bound with (A := A) (T := T1); assumption. }
  assert (H_T2B_bound: forall j, In j (touched_in_A B C T2) -> 1 <= j <= length B).
  { intros j Hj. apply in_touched_in_A_valid_bound with (C := C) (T := T2); assumption. }
  assert (H_inter_bound: length (touched_in_B A B T1) + length (touched_in_A B C T2) <=
                         length B + length (list_inter (touched_in_B A B T1) (touched_in_A B C T2))).
  { apply NoDup_incl_exclusion; assumption. }
  assert (H_comp_ge_inter: length (compose_trace T1 T2) >= length (list_inter (touched_in_B A B T1) (touched_in_A B C T2))).
  { apply compose_trace_length_ge_inter. }
  lia.
Qed.

(** Delete/insert cost bound for composition. *)
Lemma trace_composition_delete_insert_bound :
  forall (A B C : list Char) (T1 : Trace A B) (T2 : Trace B C),
    is_valid_trace A B T1 = true ->
    is_valid_trace B C T2 = true ->
    (length A - length (touched_in_A A C (compose_trace T1 T2))) +
    (length C - length (touched_in_B A C (compose_trace T1 T2)))
    <=
    (length A - length (touched_in_A A B T1)) +
    (length B - length (touched_in_B A B T1)) +
    (length B - length (touched_in_A B C T2)) +
    (length C - length (touched_in_B B C T2)).
Proof.
  intros A B C T1 T2 HvalT1 HvalT2.
  set (comp_A := touched_in_A A C (compose_trace T1 T2)).
  set (comp_C := touched_in_B A C (compose_trace T1 T2)).
  set (T1_A := touched_in_A A B T1).
  set (T1_B := touched_in_B A B T1).
  set (T2_B := touched_in_A B C T2).
  set (T2_C := touched_in_B B C T2).
  assert (Hlen_A: length comp_A <= length T1_A).
  { apply (touched_comp_A_length_le A B C T1 T2 HvalT1 HvalT2). }
  assert (Hlen_C: length comp_C <= length T2_C).
  { apply (touched_comp_C_length_le A B C T1 T2 HvalT1 HvalT2). }
  assert (Hpigeonhole: length T1_B + length T2_B <= length B + length (compose_trace T1 T2)).
  { unfold T1_B, T2_B.
    apply (composition_size_pigeonhole A B C T1 T2 HvalT1 HvalT2). }
  assert (HT1eq: length T1_A = length T1_B).
  { unfold T1_A, T1_B.
    rewrite (touched_length_eq_A A B T1).
    rewrite (touched_length_eq_B A B T1).
    reflexivity. }
  assert (HT2eq: length T2_B = length T2_C).
  { unfold T2_B, T2_C.
    rewrite (touched_length_eq_A B C T2).
    rewrite (touched_length_eq_B B C T2).
    reflexivity. }
  assert (Hcomp_len_A: length comp_A = length (compose_trace T1 T2)).
  { unfold comp_A. apply touched_length_eq_A. }
  assert (Hcomp_len_C: length comp_C = length (compose_trace T1 T2)).
  { unfold comp_C. apply touched_length_eq_B. }
  assert (HT1A_le_A: length T1_A <= length A).
  { unfold T1_A. apply touched_in_A_length_bound. exact HvalT1. }
  assert (HT1B_le_B: length T1_B <= length B).
  { unfold T1_B. apply touched_in_B_length_bound. exact HvalT1. }
  assert (HT2B_le_B: length T2_B <= length B).
  { unfold T2_B. apply touched_in_A_length_bound. exact HvalT2. }
  assert (HT2C_le_C: length T2_C <= length C).
  { unfold T2_C. apply touched_in_B_length_bound. exact HvalT2. }
  unfold comp_A, comp_C, T1_A, T1_B, T2_B, T2_C in *.
  lia.
Qed.

(** Change cost composition bound via triangle inequality. *)
Lemma change_cost_compose_bound :
  forall (A B C : list Char) (T1 : Trace A B) (T2 : Trace B C),
    is_valid_trace A B T1 = true ->
    is_valid_trace B C T2 = true ->
    fold_left (fun acc '(i, j) =>
      acc + subst_cost (nth (i-1) A default_char) (nth (j-1) C default_char)
    ) (compose_trace T1 T2) 0
    <=
    fold_left (fun acc '(i, j) =>
      acc + subst_cost (nth (i-1) A default_char) (nth (j-1) B default_char)
    ) T1 0 +
    fold_left (fun acc '(i, j) =>
      acc + subst_cost (nth (i-1) B default_char) (nth (j-1) C default_char)
    ) T2 0.
Proof.
  intros A B C T1 T2 H_valid1 H_valid2.
  assert (H_aux1: is_valid_trace_aux T1 = true).
  { unfold is_valid_trace in H_valid1.
    apply andb_true_iff in H_valid1 as [H_rest _].
    apply andb_true_iff in H_rest as [_ H_aux].
    exact H_aux. }
  assert (H_aux2: is_valid_trace_aux T2 = true).
  { unfold is_valid_trace in H_valid2.
    apply andb_true_iff in H_valid2 as [H_rest _].
    apply andb_true_iff in H_rest as [_ H_aux].
    exact H_aux. }
  assert (H_triangle: forall ik,
    In ik (compose_trace T1 T2) ->
    let '(i, k) := ik in
    subst_cost (nth (i-1) A default_char) (nth (k-1) C default_char) <=
    (fun ik' => let '(i', j) := witness_to_T1 A B C T1 T2 ik' in
                subst_cost (nth (i'-1) A default_char) (nth (j-1) B default_char)) ik +
    (fun ik' => let '(j', k') := witness_to_T2 A B C T1 T2 ik' in
                subst_cost (nth (j'-1) B default_char) (nth (k'-1) C default_char)) ik).
  { intros ik Hik. destruct ik as [i k].
    apply (witness_cost_triangle_bound A B C T1 T2 (i,k) H_aux1 H_aux2 Hik). }
  set (fAC := fun '(i, k) =>
              subst_cost (nth (i-1) A default_char) (nth (k-1) C default_char)).
  set (fAB := fun ik : nat * nat => let '(i', j) := witness_to_T1 A B C T1 T2 ik in
              subst_cost (nth (i'-1) A default_char) (nth (j-1) B default_char)).
  set (fBC := fun ik : nat * nat => let '(j', k') := witness_to_T2 A B C T1 T2 ik in
              subst_cost (nth (j'-1) B default_char) (nth (k'-1) C default_char)).
  assert (H_split:
    fold_left (fun acc ik => acc + fAC ik) (compose_trace T1 T2) 0
    <=
    fold_left (fun acc ik => acc + fAB ik) (compose_trace T1 T2) 0 +
    fold_left (fun acc ik => acc + fBC ik) (compose_trace T1 T2) 0).
  { apply fold_left_triangle_bound.
    intros ik Hik. unfold fAC, fAB, fBC.
    destruct ik as [i k]. exact (H_triangle (i, k) Hik). }
  set (costT1 := fun '(i, j) =>
                 subst_cost (nth (i-1) A default_char) (nth (j-1) B default_char)).
  set (costT2 := fun '(j, k) =>
                 subst_cost (nth (j-1) B default_char) (nth (k-1) C default_char)).
  assert (H_map1:
    fold_left (fun acc ik => acc + costT1 (witness_to_T1 A B C T1 T2 ik))
              (compose_trace T1 T2) 0
    =
    fold_left (fun acc p => acc + costT1 p)
              (map (witness_to_T1 A B C T1 T2) (compose_trace T1 T2)) 0).
  { apply fold_left_sum_map_eq. }
  assert (H_map2:
    fold_left (fun acc ik => acc + costT2 (witness_to_T2 A B C T1 T2 ik))
              (compose_trace T1 T2) 0
    =
    fold_left (fun acc p => acc + costT2 p)
              (map (witness_to_T2 A B C T1 T2) (compose_trace T1 T2)) 0).
  { apply fold_left_sum_map_eq. }
  assert (Hnodup_T1: NoDup T1).
  { apply is_valid_trace_implies_NoDup; exact H_valid1. }
  assert (Hnodup_T2: NoDup T2).
  { apply is_valid_trace_implies_NoDup; exact H_valid2. }
  assert (Hnodup_comp: NoDup (compose_trace T1 T2)).
  { apply compose_trace_NoDup_axiom; assumption. }
  assert (Hnodup_map1: NoDup (map (witness_to_T1 A B C T1 T2) (compose_trace T1 T2))).
  { apply map_injective_on_list_NoDup.
    - intros x y Hx Hy Heq.
      apply (witness_to_T1_injective A B C T1 T2 x y H_aux1 H_aux2 Hx Hy Heq).
    - exact Hnodup_comp. }
  assert (Hnodup_map2: NoDup (map (witness_to_T2 A B C T1 T2) (compose_trace T1 T2))).
  { apply map_injective_on_list_NoDup.
    - intros x y Hx Hy Heq.
      apply (witness_to_T2_injective A B C T1 T2 x y H_aux1 H_aux2 Hx Hy Heq).
    - exact Hnodup_comp. }
  assert (H_bound1:
    fold_left (fun acc p => acc + costT1 p)
              (map (witness_to_T1 A B C T1 T2) (compose_trace T1 T2)) 0
    <=
    fold_left (fun acc p => acc + costT1 p) T1 0).
  { apply fold_left_sum_bound_subset.
    - exact Hnodup_map1.
    - exact Hnodup_T1.
    - intros p Hin.
      apply in_map_iff in Hin as [ik [Heq Hik_in]].
      subst p.
      apply witness_T1_image_subset; assumption. }
  assert (H_bound2:
    fold_left (fun acc p => acc + costT2 p)
              (map (witness_to_T2 A B C T1 T2) (compose_trace T1 T2)) 0
    <=
    fold_left (fun acc p => acc + costT2 p) T2 0).
  { apply fold_left_sum_bound_subset.
    - exact Hnodup_map2.
    - exact Hnodup_T2.
    - intros p Hin.
      apply in_map_iff in Hin as [ik [Heq Hik_in]].
      subst p.
      apply witness_T2_image_subset; assumption. }
  assert (H_fAB_to_map:
    fold_left (fun acc ik => acc + fAB ik) (compose_trace T1 T2) 0 =
    fold_left (fun acc p => acc + costT1 p) (map (witness_to_T1 A B C T1 T2) (compose_trace T1 T2)) 0).
  { unfold fAB. rewrite <- H_map1. reflexivity. }
  assert (H_fBC_to_map:
    fold_left (fun acc ik => acc + fBC ik) (compose_trace T1 T2) 0 =
    fold_left (fun acc p => acc + costT2 p) (map (witness_to_T2 A B C T1 T2) (compose_trace T1 T2)) 0).
  { unfold fBC. rewrite <- H_map2. reflexivity. }
  rewrite H_fAB_to_map, H_fBC_to_map in H_split.
  unfold costT1 in H_bound1, H_split.
  unfold costT2 in H_bound2, H_split.
  unfold fAC in H_split.
  (* Convert from intermediate forms to the goal's pattern form *)
  rewrite <- (fold_left_pair_let_eq
    (fun i j => subst_cost (nth (i-1) A default_char) (nth (j-1) C default_char))
    (compose_trace T1 T2) 0).
  rewrite <- (fold_left_pair_let_eq
    (fun i j => subst_cost (nth (i-1) A default_char) (nth (j-1) B default_char))
    T1 0).
  rewrite <- (fold_left_pair_let_eq
    (fun i j => subst_cost (nth (i-1) B default_char) (nth (j-1) C default_char))
    T2 0).
  refine (Nat.le_trans _ _ _ H_split _).
  apply Nat.add_le_mono; [exact H_bound1 | exact H_bound2].
Qed.

(** * Main Cost Bound Theorem *)

(**
   Trace composition cost bound (Lemma 1 from Wagner-Fischer)

   The cost of a composed trace is bounded by the sum of the individual costs.
   This is the key lemma enabling the triangle inequality proof.

   cost(T1 ∘ T2) ≤ cost(T1) + cost(T2)
*)
Lemma trace_composition_cost_bound :
  forall (A B C : list Char) (T1 : Trace A B) (T2 : Trace B C),
    is_valid_trace A B T1 = true ->
    is_valid_trace B C T2 = true ->
    trace_cost A C (compose_trace T1 T2) <= trace_cost A B T1 + trace_cost B C T2.
Proof.
  intros A B C T1 T2 H_valid1 H_valid2.
  assert (H_aux1: is_valid_trace_aux T1 = true).
  { unfold is_valid_trace in H_valid1.
    apply andb_true_iff in H_valid1 as [H_rest _].
    apply andb_true_iff in H_rest as [_ H_aux].
    exact H_aux. }
  assert (H_aux2: is_valid_trace_aux T2 = true).
  { unfold is_valid_trace in H_valid2.
    apply andb_true_iff in H_valid2 as [H_rest _].
    apply andb_true_iff in H_rest as [_ H_aux].
    exact H_aux. }
  remember (compose_trace T1 T2) as comp eqn:E_comp.
  unfold trace_cost.
  remember (fold_left (fun acc p =>
    let '(i, j) := p in
    acc + subst_cost (nth (i-1) A default_char) (nth (j-1) C default_char)
  ) comp 0) as cc_comp eqn:E_cc_comp.
  remember (length A - length (touched_in_A A C comp)) as dc_comp eqn:E_dc_comp.
  remember (length C - length (touched_in_B A C comp)) as ic_comp eqn:E_ic_comp.
  remember (fold_left (fun acc p =>
    let '(i, j) := p in
    acc + subst_cost (nth (i-1) A default_char) (nth (j-1) B default_char)
  ) T1 0) as cc1 eqn:E_cc1.
  remember (length A - length (touched_in_A A B T1)) as dc1 eqn:E_dc1.
  remember (length B - length (touched_in_B A B T1)) as ic1 eqn:E_ic1.
  remember (fold_left (fun acc p =>
    let '(i, j) := p in
    acc + subst_cost (nth (i-1) B default_char) (nth (j-1) C default_char)
  ) T2 0) as cc2 eqn:E_cc2.
  remember (length B - length (touched_in_A B C T2)) as dc2 eqn:E_dc2.
  remember (length C - length (touched_in_B B C T2)) as ic2 eqn:E_ic2.
  assert (H_cc: cc_comp <= cc1 + cc2).
  { subst cc_comp cc1 cc2 comp.
    (* The goal has let form from trace_cost; change_cost_compose_bound uses pattern form.
       These are definitionally equal, so we can use refine with type ascription. *)
    refine ((fun (H : fold_left (fun acc '(i, j) =>
              acc + subst_cost (nth (i-1) A default_char) (nth (j-1) C default_char))
            (compose_trace T1 T2) 0 <=
            fold_left (fun acc '(i, j) =>
              acc + subst_cost (nth (i-1) A default_char) (nth (j-1) B default_char))
            T1 0 +
            fold_left (fun acc '(i, j) =>
              acc + subst_cost (nth (i-1) B default_char) (nth (j-1) C default_char))
            T2 0) => H) _).
    apply change_cost_compose_bound; assumption. }
  assert (H_di: dc_comp + ic_comp <= dc1 + ic1 + dc2 + ic2).
  { rewrite E_dc_comp, E_ic_comp, E_dc1, E_ic1, E_dc2, E_ic2, E_comp.
    apply trace_composition_delete_insert_bound; assumption. }
  assert (H_intermediate: cc_comp + (dc_comp + ic_comp) <= (cc1 + cc2) + (dc1 + ic1 + dc2 + ic2)).
  { apply Nat.add_le_mono; [exact H_cc | exact H_di]. }
  rewrite Nat.add_assoc in H_intermediate.
  eapply Nat.le_trans; [exact H_intermediate |].
  apply Nat.eq_le_incl.
  lia.
Qed.
