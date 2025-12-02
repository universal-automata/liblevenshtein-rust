(** * NoDup Preservation for Touched Positions

    This module proves that the touched_in_A and touched_in_B functions
    preserve the NoDup property when applied to valid traces.

    Part of: Liblevenshtein.Core

    Decomposed from: Distance.v (lines 2562-3090)
*)

From Coq Require Import String List Arith Ascii Bool Nat Lia.
Import ListNotations.

From Liblevenshtein.Core Require Import Core.Definitions.
From Liblevenshtein.Core Require Import Trace.TraceBasics.
From Liblevenshtein.Core Require Import Trace.TouchedPositions.
From Liblevenshtein.Core Require Import Trace.TraceComposition.
From Liblevenshtein.Core Require Import Cardinality.NoDupInclusion.

(** * Length Bounds for Touched Positions *)

(**
   Length of touched positions is bounded by trace length.

   Each pair in the trace contributes one position to touched_in_A.
*)
Lemma touched_length_bound_A :
  forall (A B : list Char) (T : Trace A B),
    length (touched_in_A A B T) <= length T.
Proof.
  intros A B T.
  induction T as [| [i j] T' IH].
  - (* Base: T = [] *)
    simpl. lia.
  - (* Inductive: T = (i,j) :: T' *)
    simpl.
    lia.
Qed.

(**
   Length of touched positions in B is bounded by trace length.

   Each pair in the trace contributes one position to touched_in_B.
*)
Lemma touched_length_bound_B :
  forall (A B : list Char) (T : Trace A B),
    length (touched_in_B A B T) <= length T.
Proof.
  intros A B T.
  induction T as [| [i j] T' IH].
  - (* Base: T = [] *)
    simpl. lia.
  - (* Inductive: T = (i,j) :: T' *)
    simpl.
    lia.
Qed.

(**
   Length of touched positions equals trace length.

   Since each pair contributes exactly one element to touched_in_A/B,
   the lengths are equal (not just bounded).
*)
Lemma touched_length_eq_A :
  forall (A B : list Char) (T : Trace A B),
    length (touched_in_A A B T) = length T.
Proof.
  intros A B T.
  induction T as [| [i j] T' IH].
  - simpl. reflexivity.
  - simpl. f_equal. exact IH.
Qed.

Lemma touched_length_eq_B :
  forall (A B : list Char) (T : Trace A B),
    length (touched_in_B A B T) = length T.
Proof.
  intros A B T.
  induction T as [| [i j] T' IH].
  - simpl. reflexivity.
  - simpl. f_equal. exact IH.
Qed.

(** * Range Bounds for Touched Positions *)

(**
   For valid traces, all touched A-positions are in range [1, |A|].
   Combined with NoDup, this bounds the length of touched_in_A by |A|.
*)
Lemma touched_in_A_all_le :
  forall (A B : list Char) (T : Trace A B),
    is_valid_trace A B T = true ->
    forall i, In i (touched_in_A A B T) -> i <= length A.
Proof.
  intros A B T Hvalid i Hin.
  unfold is_valid_trace in Hvalid.
  apply andb_true_iff in Hvalid as [Hvalid Hnodup].
  apply andb_true_iff in Hvalid as [Hbounds Hcompat].
  rewrite forallb_forall in Hbounds.
  revert Hbounds Hcompat Hnodup Hin.
  induction T as [| [i' j'] T' IH]; intros Hbounds Hcompat Hnodup Hin.
  - simpl in Hin. contradiction.
  - simpl in Hin.
    destruct Hin as [Heq | Hin'].
    + subst i'.
      specialize (Hbounds (i, j')).
      assert (Hin_pair: In (i, j') ((i, j') :: T')) by (left; reflexivity).
      specialize (Hbounds Hin_pair).
      unfold valid_pair in Hbounds.
      apply andb_true_iff in Hbounds as [Hbounds Hj_ub].
      apply andb_true_iff in Hbounds as [Hbounds Hj_lb].
      apply andb_true_iff in Hbounds as [Hi_lb Hi_ub].
      apply Nat.leb_le. exact Hi_ub.
    + apply IH; clear IH.
      * intros p Hp. apply Hbounds. right. exact Hp.
      * simpl in Hcompat. apply andb_true_iff in Hcompat as [_ Hcompat']. exact Hcompat'.
      * simpl in Hnodup. apply andb_true_iff in Hnodup as [_ Hnodup']. exact Hnodup'.
      * exact Hin'.
Qed.

Lemma touched_in_B_all_le :
  forall (A B : list Char) (T : Trace A B),
    is_valid_trace A B T = true ->
    forall j, In j (touched_in_B A B T) -> j <= length B.
Proof.
  intros A B T Hvalid j Hin.
  unfold is_valid_trace in Hvalid.
  apply andb_true_iff in Hvalid as [Hvalid Hnodup].
  apply andb_true_iff in Hvalid as [Hbounds Hcompat].
  rewrite forallb_forall in Hbounds.
  revert Hbounds Hcompat Hnodup Hin.
  induction T as [| [i' j'] T' IH]; intros Hbounds Hcompat Hnodup Hin.
  - simpl in Hin. contradiction.
  - simpl in Hin.
    destruct Hin as [Heq | Hin'].
    + subst j'.
      specialize (Hbounds (i', j)).
      assert (Hin_pair: In (i', j) ((i', j) :: T')) by (left; reflexivity).
      specialize (Hbounds Hin_pair).
      unfold valid_pair in Hbounds.
      apply andb_true_iff in Hbounds as [Hbounds Hj_ub].
      apply andb_true_iff in Hbounds as [Hbounds Hj_lb].
      apply andb_true_iff in Hbounds as [Hi_lb Hi_ub].
      apply Nat.leb_le. exact Hj_ub.
    + apply IH; clear IH.
      * intros p Hp. apply Hbounds. right. exact Hp.
      * simpl in Hcompat. apply andb_true_iff in Hcompat as [_ Hcompat']. exact Hcompat'.
      * simpl in Hnodup. apply andb_true_iff in Hnodup as [_ Hnodup']. exact Hnodup'.
      * exact Hin'.
Qed.

(** * Witness Existence Lemmas *)

(**
   Helper: If a value is in the touched list, the corresponding pair exists in the trace.
*)
Lemma in_touched_in_A_exists_pair :
  forall (A B : list Char) (T : Trace A B) (i : nat),
    In i (touched_in_A A B T) -> exists j, In (i, j) T.
Proof.
  intros A B T i H_in.
  induction T as [| [i' j'] T' IH].
  - simpl in H_in. contradiction.
  - simpl in H_in.
    destruct H_in as [H_eq | H_rest].
    + exists j'. subst i'. left. reflexivity.
    + destruct (IH H_rest) as [j'' H_in_T'].
      exists j''. right. exact H_in_T'.
Qed.

Lemma in_touched_in_B_exists_pair :
  forall (A B : list Char) (T : Trace A B) (j : nat),
    In j (touched_in_B A B T) -> exists i, In (i, j) T.
Proof.
  intros A B T j H_in.
  induction T as [| [i' j'] T' IH].
  - simpl in H_in. contradiction.
  - simpl in H_in.
    destruct H_in as [H_eq | H_rest].
    + exists i'. subst j'. left. reflexivity.
    + destruct (IH H_rest) as [i'' H_in_T'].
      exists i''. right. exact H_in_T'.
Qed.

(** * NoDup Preservation for Touched Positions *)

(**
   Valid traces have no duplicate first components.

   Since is_valid_trace now enforces NoDup on pairs, and valid_trace_unique_first
   shows that pairs with the same first component must be identical, we can prove
   that the list of first components has no duplicates.
*)
Lemma touched_in_A_NoDup :
  forall (A B : list Char) (T : Trace A B),
    is_valid_trace A B T = true ->
    NoDup (touched_in_A A B T).
Proof.
  intros A B T H_valid.
  (* Get NoDup T from the strengthened is_valid_trace *)
  assert (H_nodup_T: NoDup T) by (apply is_valid_trace_implies_NoDup; exact H_valid).
  (* Also extract is_valid_trace_aux for later use *)
  unfold is_valid_trace in H_valid.
  apply andb_true_iff in H_valid as [H_rest H_nodup_dec].
  apply andb_true_iff in H_rest as [H_bounds H_valid_aux].

  induction T as [| [i j] T' IH].
  - (* Base: T = [] *)
    simpl. constructor.

  - (* Inductive: T = (i,j) :: T' *)
    simpl.
    inversion H_nodup_T as [| ? ? H_not_in_T' H_nodup_T'].
    constructor.
    + (* Show i ∉ touched_in_A A B T' *)
      intro H_in_touched.
      (* Use helper lemma to get witness pair *)
      apply in_touched_in_A_exists_pair in H_in_touched.
      destruct H_in_touched as [j' H_in_pair].
      (* Now use valid_trace_unique_first: since (i,j) and (i,j') are both in T,
         and they have the same first component, they must be identical *)
      assert (H_j_eq: j = j').
      {
        apply (valid_trace_unique_first ((i,j) :: T') i j j' H_valid_aux).
        - left. reflexivity.
        - right. exact H_in_pair.
      }
      subst j'.
      (* So (i,j) ∈ T', contradicting H_not_in_T' *)
      exact (H_not_in_T' H_in_pair).
    + (* Show NoDup (touched_in_A A B T') *)
      apply IH.
      * (* Extract valid_pair bounds for T' from H_bounds *)
        simpl in H_bounds.
        apply andb_true_iff in H_bounds as [_ H_bounds_T'].
        exact H_bounds_T'.
      * (* Extract is_valid_trace_aux T' from H_valid_aux *)
        simpl in H_valid_aux.
        apply andb_true_iff in H_valid_aux as [_ H_valid_T'].
        exact H_valid_T'.
      * (* Extract NoDup_dec T' from H_nodup_dec *)
        simpl in H_nodup_dec.
        apply andb_true_iff in H_nodup_dec as [_ H_nodup_dec_T'].
        exact H_nodup_dec_T'.
      * (* NoDup T' *)
        exact H_nodup_T'.
Qed.

(**
   Valid traces have no duplicate second components.

   Symmetric to touched_in_A_NoDup, using valid_trace_unique_second instead.
*)
Lemma touched_in_B_NoDup :
  forall (A B : list Char) (T : Trace A B),
    is_valid_trace A B T = true ->
    NoDup (touched_in_B A B T).
Proof.
  intros A B T H_valid.
  (* Get NoDup T from the strengthened is_valid_trace *)
  assert (H_nodup_T: NoDup T) by (apply is_valid_trace_implies_NoDup; exact H_valid).
  (* Also extract is_valid_trace_aux for later use *)
  unfold is_valid_trace in H_valid.
  apply andb_true_iff in H_valid as [H_rest H_nodup_dec].
  apply andb_true_iff in H_rest as [H_bounds H_valid_aux].

  induction T as [| [i j] T' IH].
  - (* Base: T = [] *)
    simpl. constructor.

  - (* Inductive: T = (i,j) :: T' *)
    simpl.
    inversion H_nodup_T as [| ? ? H_not_in_T' H_nodup_T'].
    constructor.
    + (* Show j ∉ touched_in_B A B T' *)
      intro H_in_touched.
      (* Use helper lemma to get witness pair *)
      apply in_touched_in_B_exists_pair in H_in_touched.
      destruct H_in_touched as [i' H_in_pair].
      (* Now use valid_trace_unique_second: since (i,j) and (i',j) are both in T,
         and they have the same second component, they must be identical *)
      assert (H_i_eq: i = i').
      {
        apply (valid_trace_unique_second ((i,j) :: T') i i' j H_valid_aux).
        - left. reflexivity.
        - right. exact H_in_pair.
      }
      subst i'.
      (* So (i,j) ∈ T', contradicting H_not_in_T' *)
      exact (H_not_in_T' H_in_pair).
    + (* Show NoDup (touched_in_B A B T') *)
      apply IH.
      * (* Extract valid_pair bounds for T' from H_bounds *)
        simpl in H_bounds.
        apply andb_true_iff in H_bounds as [_ H_bounds_T'].
        exact H_bounds_T'.
      * (* Extract is_valid_trace_aux T' from H_valid_aux *)
        simpl in H_valid_aux.
        apply andb_true_iff in H_valid_aux as [_ H_valid_T'].
        exact H_valid_T'.
      * (* Extract NoDup_dec T' from H_nodup_dec *)
        simpl in H_nodup_dec.
        apply andb_true_iff in H_nodup_dec as [_ H_nodup_dec_T'].
        exact H_nodup_dec_T'.
      * (* NoDup T' *)
        exact H_nodup_T'.
Qed.

(** * Touched Position Length Bounds *)

(**
   For valid traces, touched_in_A length is bounded by string length.
   This follows from NoDup + all elements in range [1, |A|].

   Uses incl_length_NoDup: if NoDup l1, NoDup l2, incl l1 l2 then |l1| <= |l2|.
   Since touched_in_A T ⊆ [1..n] and has NoDup, |touched_in_A T| <= n.
*)
Lemma touched_in_A_length_bound :
  forall (A B : list Char) (T : Trace A B),
    is_valid_trace A B T = true ->
    length (touched_in_A A B T) <= length A.
Proof.
  intros A B T Hvalid.
  assert (Hnodup: NoDup (touched_in_A A B T)).
  { apply touched_in_A_NoDup. exact Hvalid. }
  (* Use length equality and bound on T *)
  rewrite touched_length_eq_A.
  (* Prove: length T <= length A *)
  (* Each pair (i,j) in T has i in [1, |A|], and first components are unique *)
  (* So length T = length (map fst T) <= length A *)
  assert (Hmap_eq: map fst T = touched_in_A A B T).
  {
    clear Hvalid Hnodup.
    induction T as [| [i j] T' IH].
    - simpl. reflexivity.
    - simpl. f_equal. exact IH.
  }
  rewrite <- Hmap_eq in Hnodup.
  rewrite <- (map_length fst T).
  (* Now: length (map fst T) <= length A, with NoDup (map fst T) *)
  (* and all elements of map fst T are in [1, |A|] *)
  (* Use incl_length_NoDup with seq 1 (length A) *)
  assert (Hincl: incl (map fst T) (seq 1 (length A))).
  {
    intros i Hin.
    apply in_map_iff in Hin as [[i' j'] [Heq Hin']].
    simpl in Heq. subst i'.
    apply in_seq.
    split.
    - (* 1 <= i: from valid_pair *)
      unfold is_valid_trace in Hvalid.
      apply andb_true_iff in Hvalid as [Hvalid _].
      apply andb_true_iff in Hvalid as [Hbounds _].
      rewrite forallb_forall in Hbounds.
      specialize (Hbounds (i, j') Hin').
      unfold valid_pair in Hbounds.
      repeat (apply andb_true_iff in Hbounds as [Hbounds ?]).
      apply Nat.leb_le in Hbounds. exact Hbounds.
    - (* i < 1 + length A, i.e., i <= length A: from valid_pair *)
      unfold is_valid_trace in Hvalid.
      apply andb_true_iff in Hvalid as [Hvalid _].
      apply andb_true_iff in Hvalid as [Hbounds _].
      rewrite forallb_forall in Hbounds.
      specialize (Hbounds (i, j') Hin').
      unfold valid_pair in Hbounds.
      apply andb_true_iff in Hbounds as [Hbounds Hj_ub].
      apply andb_true_iff in Hbounds as [Hbounds Hj_lb].
      apply andb_true_iff in Hbounds as [Hi_lb Hi_ub].
      apply Nat.leb_le in Hi_ub. lia.
  }
  assert (Hnodup_seq: NoDup (seq 1 (length A))).
  { apply seq_NoDup. }
  assert (Hlen_seq: length (seq 1 (length A)) = length A).
  { apply seq_length. }
  rewrite <- Hlen_seq.
  apply incl_length_NoDup; assumption.
Qed.

Lemma touched_in_B_length_bound :
  forall (A B : list Char) (T : Trace A B),
    is_valid_trace A B T = true ->
    length (touched_in_B A B T) <= length B.
Proof.
  intros A B T Hvalid.
  assert (Hnodup: NoDup (touched_in_B A B T)).
  { apply touched_in_B_NoDup. exact Hvalid. }
  rewrite touched_length_eq_B.
  assert (Hmap_eq: map snd T = touched_in_B A B T).
  {
    clear Hvalid Hnodup.
    induction T as [| [i j] T' IH].
    - simpl. reflexivity.
    - simpl. f_equal. exact IH.
  }
  rewrite <- Hmap_eq in Hnodup.
  rewrite <- (map_length snd T).
  assert (Hincl: incl (map snd T) (seq 1 (length B))).
  {
    intros j Hin.
    apply in_map_iff in Hin as [[i' j'] [Heq Hin']].
    simpl in Heq. subst j'.
    apply in_seq.
    split.
    - unfold is_valid_trace in Hvalid.
      apply andb_true_iff in Hvalid as [Hvalid _].
      apply andb_true_iff in Hvalid as [Hbounds _].
      rewrite forallb_forall in Hbounds.
      specialize (Hbounds (i', j) Hin').
      unfold valid_pair in Hbounds.
      repeat (apply andb_true_iff in Hbounds as [Hbounds ?]).
      apply Nat.leb_le in H0. exact H0.
    - unfold is_valid_trace in Hvalid.
      apply andb_true_iff in Hvalid as [Hvalid _].
      apply andb_true_iff in Hvalid as [Hbounds _].
      rewrite forallb_forall in Hbounds.
      specialize (Hbounds (i', j) Hin').
      unfold valid_pair in Hbounds.
      repeat (apply andb_true_iff in Hbounds as [Hbounds ?]).
      apply Nat.leb_le in H. lia.
  }
  assert (Hnodup_seq: NoDup (seq 1 (length B))).
  { apply seq_NoDup. }
  assert (Hlen_seq: length (seq 1 (length B)) = length B).
  { apply seq_length. }
  rewrite <- Hlen_seq.
  apply incl_length_NoDup; assumption.
Qed.
