(** * Optimal Trace Validity

    This module proves that the optimal trace is valid according to is_valid_trace.

    Part of: Liblevenshtein.Core

    Decomposed from: Distance.v (lines 7128-7657)
*)

From Coq Require Import String List Arith Ascii Bool Nat Lia Wf_nat.
Import ListNotations.

From Liblevenshtein.Core Require Import Core.Definitions.
From Liblevenshtein.Core Require Import Core.LevDistance.
From Liblevenshtein.Core Require Import Trace.TraceBasics.
From Liblevenshtein.Core Require Import OptimalTrace.Construction.

(** * Unfold Lemma *)

(** Unfold lemma for optimal_trace_pair *)
Lemma optimal_trace_pair_unfold : forall A B,
  optimal_trace_pair (A, B) =
  match A, B with
  | [], _ => []
  | _, [] => []
  | c1 :: s1', c2 :: s2' =>
      let cost_del := lev_distance s1' (c2 :: s2') + 1 in
      let cost_ins := lev_distance (c1 :: s1') s2' + 1 in
      let cost_sub := lev_distance s1' s2' + subst_cost c1 c2 in
      if (cost_sub <=? cost_del) && (cost_sub <=? cost_ins)
      then (1, 1) :: map (fun '(i, j) => (S i, S j)) (optimal_trace_pair (s1', s2'))
      else if cost_del <=? cost_ins
      then map (fun '(i, j) => (S i, j)) (optimal_trace_pair (s1', (c2 :: s2')))
      else map (fun '(i, j) => (i, S j)) (optimal_trace_pair ((c1 :: s1'), s2'))
  end.
Proof.
  intros A' B'.
  rewrite optimal_trace_pair_equation.
  destruct A', B'; reflexivity.
Qed.

(** * Valid Indices Properties *)

(** Valid indices for optimal_trace_pair *)
Lemma optimal_trace_pair_valid_indices :
  forall A B, valid_indices (optimal_trace_pair (A, B)).
Proof.
  intros A' B'.
  remember (length A' + length B') as n eqn:Hn.
  revert A' B' Hn.
  induction n as [n IH] using lt_wf_ind.
  intros A' B' Hn.
  rewrite optimal_trace_pair_unfold.
  destruct A' as [| c1 s1'], B' as [| c2 s2'].
  - constructor.
  - constructor.
  - constructor.
  - cbv zeta.
    destruct ((lev_distance s1' s2' + subst_cost c1 c2 <=? lev_distance s1' (c2 :: s2') + 1) &&
              (lev_distance s1' s2' + subst_cost c1 c2 <=? lev_distance (c1 :: s1') s2' + 1)) eqn:E_sub.
    + constructor.
      * split; lia.
      * assert (IH_sub: valid_indices (optimal_trace_pair (s1', s2'))).
        { apply (IH (length s1' + length s2')). subst n. simpl. lia. reflexivity. }
        unfold valid_indices in *.
        rewrite Forall_forall in *.
        intros [i' j'] Hin.
        rewrite in_map_iff in Hin.
        destruct Hin as [[i j] [Heq Hin_orig]].
        injection Heq as Hi' Hj'. subst i' j'.
        specialize (IH_sub (i, j) Hin_orig).
        destruct IH_sub as [Hi Hj].
        split; lia.
    + destruct (lev_distance s1' (c2 :: s2') + 1 <=? lev_distance (c1 :: s1') s2' + 1) eqn:E_del.
      * assert (IH_del: valid_indices (optimal_trace_pair (s1', (c2 :: s2')))).
        { apply (IH (length s1' + length (c2 :: s2'))). subst n. simpl. lia. reflexivity. }
        unfold valid_indices in *.
        rewrite Forall_forall in *.
        intros [i' j'] Hin.
        rewrite in_map_iff in Hin.
        destruct Hin as [[i j] [Heq Hin_orig]].
        injection Heq as Hi' Hj'. subst i' j'.
        specialize (IH_del (i, j) Hin_orig).
        destruct IH_del as [Hi Hj].
        split; lia.
      * assert (IH_ins: valid_indices (optimal_trace_pair ((c1 :: s1'), s2'))).
        { apply (IH (length (c1 :: s1') + length s2')). subst n. simpl. lia. reflexivity. }
        unfold valid_indices in *.
        rewrite Forall_forall in *.
        intros [i' j'] Hin.
        rewrite in_map_iff in Hin.
        destruct Hin as [[i j] [Heq Hin_orig]].
        injection Heq as Hi' Hj'. subst i' j'.
        specialize (IH_ins (i, j) Hin_orig).
        destruct IH_ins as [Hi Hj].
        split; lia.
Qed.

(** Corollaries for specific preconditions *)
Lemma optimal_trace_pair_i_valid : forall A B,
  Forall (fun '(i, _) => i >= 1) (optimal_trace_pair (A, B)).
Proof.
  intros A' B'.
  pose proof (optimal_trace_pair_valid_indices A' B') as Hvalid.
  unfold valid_indices in Hvalid.
  eapply Forall_impl. 2: exact Hvalid.
  intros [i j] [Hi Hj]. exact Hi.
Qed.

Lemma optimal_trace_pair_j_valid : forall A B,
  Forall (fun '(_, j) => j >= 1) (optimal_trace_pair (A, B)).
Proof.
  intros A' B'.
  pose proof (optimal_trace_pair_valid_indices A' B') as Hvalid.
  unfold valid_indices in Hvalid.
  eapply Forall_impl. 2: exact Hvalid.
  intros [i j] [Hi Hj]. exact Hj.
Qed.

(** Trace length bound *)
Lemma optimal_trace_pair_length_bound : forall A B,
  length (optimal_trace_pair (A, B)) <= min (length A) (length B).
Proof.
  intros A' B'.
  remember (length A' + length B') as n eqn:Hn.
  revert A' B' Hn.
  induction n as [n IH] using lt_wf_ind.
  intros A' B' Hn.
  rewrite optimal_trace_pair_unfold.
  destruct A' as [| c1 s1'], B' as [| c2 s2'].
  - simpl. lia.
  - simpl. lia.
  - simpl. lia.
  - cbv zeta.
    destruct ((lev_distance s1' s2' + subst_cost c1 c2 <=? lev_distance s1' (c2 :: s2') + 1) &&
              (lev_distance s1' s2' + subst_cost c1 c2 <=? lev_distance (c1 :: s1') s2' + 1)) eqn:E_sub.
    + simpl length. rewrite length_map.
      assert (IH_sub: length (optimal_trace_pair (s1', s2')) <= min (length s1') (length s2')).
      { apply (IH (length s1' + length s2')). subst n. simpl. lia. reflexivity. }
      lia.
    + destruct (lev_distance s1' (c2 :: s2') + 1 <=? lev_distance (c1 :: s1') s2' + 1) eqn:E_del.
      * rewrite length_map. simpl length.
        assert (IH_del: length (optimal_trace_pair (s1', (c2 :: s2'))) <= min (length s1') (length (c2 :: s2'))).
        { apply (IH (length s1' + length (c2 :: s2'))). subst n. simpl. lia. reflexivity. }
        simpl in IH_del. lia.
      * rewrite length_map. simpl length.
        assert (IH_ins: length (optimal_trace_pair ((c1 :: s1'), s2')) <= min (length (c1 :: s1')) (length s2')).
        { apply (IH (length (c1 :: s1') + length s2')). subst n. simpl. lia. reflexivity. }
        destruct s2' as [| c3 s3'].
        -- simpl in IH_ins. simpl. lia.
        -- simpl in IH_ins. simpl. lia.
Qed.

(** Complete bounds for optimal_trace_pair: all indices satisfy valid_pair *)
Lemma optimal_trace_pair_bounds : forall A B,
  Forall (fun '(i, j) => 1 <= i <= length A /\ 1 <= j <= length B)
         (optimal_trace_pair (A, B)).
Proof.
  intros A' B'.
  remember (length A' + length B') as n eqn:Hn.
  revert A' B' Hn.
  induction n as [n IH] using lt_wf_ind.
  intros A' B' Hn.
  rewrite optimal_trace_pair_unfold.
  destruct A' as [| c1 s1'], B' as [| c2 s2'].
  - constructor.
  - constructor.
  - constructor.
  - cbv zeta.
    destruct ((lev_distance s1' s2' + subst_cost c1 c2 <=? lev_distance s1' (c2 :: s2') + 1) &&
              (lev_distance s1' s2' + subst_cost c1 c2 <=? lev_distance (c1 :: s1') s2' + 1)) eqn:E_sub.
    + assert (IH_sub: Forall (fun '(i, j) => 1 <= i <= length s1' /\ 1 <= j <= length s2')
                             (optimal_trace_pair (s1', s2'))).
      { apply (IH (length s1' + length s2')). subst n. simpl. lia. reflexivity. }
      rewrite Forall_forall in *.
      intros [i' j'] Hin.
      simpl in Hin. destruct Hin as [Heq | Hin_tail].
      * injection Heq as Hi' Hj'. subst i' j'. simpl length. lia.
      * rewrite in_map_iff in Hin_tail.
        destruct Hin_tail as [[i j] [Heq Hin_orig]].
        injection Heq as Hi' Hj'. subst i' j'.
        specialize (IH_sub (i, j) Hin_orig).
        simpl in IH_sub. destruct IH_sub as [[Hi_lo Hi_hi] [Hj_lo Hj_hi]].
        simpl length. lia.
    + destruct (lev_distance s1' (c2 :: s2') + 1 <=? lev_distance (c1 :: s1') s2' + 1) eqn:E_del.
      * assert (IH_del: Forall (fun '(i, j) => 1 <= i <= length s1' /\ 1 <= j <= length (c2 :: s2'))
                               (optimal_trace_pair (s1', (c2 :: s2')))).
        { apply (IH (length s1' + length (c2 :: s2'))). subst n. simpl. lia. reflexivity. }
        rewrite Forall_forall in *.
        intros [i' j'] Hin.
        rewrite in_map_iff in Hin.
        destruct Hin as [[i j] [Heq Hin_orig]].
        injection Heq as Hi' Hj'. subst i' j'.
        specialize (IH_del (i, j) Hin_orig).
        simpl in IH_del. destruct IH_del as [[Hi_lo Hi_hi] [Hj_lo Hj_hi]].
        simpl length in *. lia.
      * assert (IH_ins: Forall (fun '(i, j) => 1 <= i <= length (c1 :: s1') /\ 1 <= j <= length s2')
                               (optimal_trace_pair ((c1 :: s1'), s2'))).
        { apply (IH (length (c1 :: s1') + length s2')). subst n. simpl. lia. reflexivity. }
        rewrite Forall_forall in *.
        intros [i' j'] Hin.
        rewrite in_map_iff in Hin.
        destruct Hin as [[i j] [Heq Hin_orig]].
        injection Heq as Hi' Hj'. subst i' j'.
        specialize (IH_ins (i, j) Hin_orig).
        simpl in IH_ins. destruct IH_ins as [[Hi_lo Hi_hi] [Hj_lo Hj_hi]].
        simpl length in *. lia.
Qed.

(** * Compatible Pairs Shift Lemmas *)

(** Helper: compatible_pairs is preserved by shifting both indices *)
Lemma compatible_pairs_shift_SS : forall p1 p2,
  compatible_pairs p1 p2 = true ->
  compatible_pairs (let '(i, j) := p1 in (S i, S j)) (let '(i, j) := p2 in (S i, S j)) = true.
Proof.
  intros [i1 j1] [i2 j2] H.
  unfold compatible_pairs in *.
  simpl. simpl in H.
  exact H.
Qed.

(** Helper: compatible_pairs is preserved by shifting first index *)
Lemma compatible_pairs_shift_S_id : forall p1 p2,
  compatible_pairs p1 p2 = true ->
  compatible_pairs (let '(i, j) := p1 in (S i, j)) (let '(i, j) := p2 in (S i, j)) = true.
Proof.
  intros [i1 j1] [i2 j2] H.
  unfold compatible_pairs in *.
  simpl. simpl in H.
  exact H.
Qed.

(** Helper: compatible_pairs is preserved by shifting second index *)
Lemma compatible_pairs_shift_id_S : forall p1 p2,
  compatible_pairs p1 p2 = true ->
  compatible_pairs (let '(i, j) := p1 in (i, S j)) (let '(i, j) := p2 in (i, S j)) = true.
Proof.
  intros [i1 j1] [i2 j2] H.
  unfold compatible_pairs in *.
  simpl. simpl in H.
  exact H.
Qed.

(** Helper: (1,1) is compatible with any (S i, S j) where i >= 1, j >= 1 *)
Lemma compatible_pairs_one_one_with_SS : forall i j,
  i >= 1 -> j >= 1 ->
  compatible_pairs (1, 1) (S i, S j) = true.
Proof.
  intros i j Hi Hj.
  destruct i as [| i']; [lia |].
  destruct j as [| j']; [lia |].
  unfold compatible_pairs. simpl.
  reflexivity.
Qed.

(** All elements in optimal_trace_pair have indices >= 1 *)
Lemma optimal_trace_pair_indices_ge_1 : forall A B,
  Forall (fun '(i, j) => i >= 1 /\ j >= 1) (optimal_trace_pair (A, B)).
Proof.
  intros A B.
  remember (length A + length B) as n eqn:Hn.
  revert A B Hn.
  induction n as [n IH] using lt_wf_ind.
  intros A B Hn.
  rewrite optimal_trace_pair_unfold.
  destruct A as [| c1 s1'], B as [| c2 s2'].
  - constructor.
  - constructor.
  - constructor.
  - cbv zeta.
    destruct ((lev_distance s1' s2' + subst_cost c1 c2 <=? lev_distance s1' (c2 :: s2') + 1) &&
              (lev_distance s1' s2' + subst_cost c1 c2 <=? lev_distance (c1 :: s1') s2' + 1)) eqn:E_sub.
    + constructor.
      * split; lia.
      * rewrite Forall_map. apply Forall_impl with (P := fun '(i, j) => i >= 1 /\ j >= 1).
        -- intros [i j] [Hi Hj]. split; lia.
        -- apply (IH (length s1' + length s2')). subst n. simpl. lia. reflexivity.
    + destruct (lev_distance s1' (c2 :: s2') + 1 <=? lev_distance (c1 :: s1') s2' + 1) eqn:E_del.
      * rewrite Forall_map. apply Forall_impl with (P := fun '(i, j) => i >= 1 /\ j >= 1).
        -- intros [i j] [Hi Hj]. split; lia.
        -- apply (IH (length s1' + length (c2 :: s2'))). subst n. simpl. lia. reflexivity.
      * rewrite Forall_map. apply Forall_impl with (P := fun '(i, j) => i >= 1 /\ j >= 1).
        -- intros [i j] [Hi Hj]. split; lia.
        -- apply (IH (length (c1 :: s1') + length s2')). subst n. simpl. lia. reflexivity.
Qed.

(** * is_valid_trace_aux Preservation *)

(** is_valid_trace_aux is preserved by mapping with SS shift *)
Lemma is_valid_trace_aux_map_SS : forall T,
  is_valid_trace_aux T = true ->
  is_valid_trace_aux (map (fun '(i, j) => (S i, S j)) T) = true.
Proof.
  induction T as [| [i j] rest IH]; intros H.
  - reflexivity.
  - simpl in H. apply andb_true_iff in H as [Hforall Hrest].
    simpl. apply andb_true_iff. split.
    + rewrite forallb_forall in Hforall |- *.
      intros [i' j'] Hin.
      rewrite in_map_iff in Hin.
      destruct Hin as [[i'' j''] [Heq Hin_orig]].
      injection Heq as Hi Hj. subst i' j'.
      specialize (Hforall (i'', j'') Hin_orig).
      apply (compatible_pairs_shift_SS (i, j) (i'', j'')). exact Hforall.
    + apply IH. exact Hrest.
Qed.

(** is_valid_trace_aux for (1,1) :: map SS shift with valid T *)
Lemma is_valid_trace_aux_cons_one_one_map_SS : forall T,
  is_valid_trace_aux T = true ->
  Forall (fun '(i, j) => i >= 1 /\ j >= 1) T ->
  is_valid_trace_aux ((1, 1) :: map (fun '(i, j) => (S i, S j)) T) = true.
Proof.
  intros T Haux Hge.
  simpl. apply andb_true_iff. split.
  - rewrite forallb_forall. intros [i' j'] Hin.
    rewrite in_map_iff in Hin.
    destruct Hin as [[i j] [Heq Hin_orig]].
    injection Heq as Hi Hj. subst i' j'.
    rewrite Forall_forall in Hge.
    specialize (Hge (i, j) Hin_orig).
    destruct Hge as [Hi Hj].
    apply compatible_pairs_one_one_with_SS; lia.
  - apply is_valid_trace_aux_map_SS. exact Haux.
Qed.

(** is_valid_trace_aux is preserved by mapping with S_id shift *)
Lemma is_valid_trace_aux_map_S_id : forall T,
  is_valid_trace_aux T = true ->
  is_valid_trace_aux (map (fun '(i, j) => (S i, j)) T) = true.
Proof.
  induction T as [| [i j] rest IH]; intros H.
  - reflexivity.
  - simpl in H. apply andb_true_iff in H as [Hforall Hrest].
    simpl. apply andb_true_iff. split.
    + rewrite forallb_forall in Hforall |- *.
      intros [i' j'] Hin.
      rewrite in_map_iff in Hin.
      destruct Hin as [[i'' j''] [Heq Hin_orig]].
      injection Heq as Hi Hj. subst i' j'.
      specialize (Hforall (i'', j'') Hin_orig).
      apply (compatible_pairs_shift_S_id (i, j) (i'', j'')). exact Hforall.
    + apply IH. exact Hrest.
Qed.

(** is_valid_trace_aux is preserved by mapping with id_S shift *)
Lemma is_valid_trace_aux_map_id_S : forall T,
  is_valid_trace_aux T = true ->
  is_valid_trace_aux (map (fun '(i, j) => (i, S j)) T) = true.
Proof.
  induction T as [| [i j] rest IH]; intros H.
  - reflexivity.
  - simpl in H. apply andb_true_iff in H as [Hforall Hrest].
    simpl. apply andb_true_iff. split.
    + rewrite forallb_forall in Hforall |- *.
      intros [i' j'] Hin.
      rewrite in_map_iff in Hin.
      destruct Hin as [[i'' j''] [Heq Hin_orig]].
      injection Heq as Hi Hj. subst i' j'.
      specialize (Hforall (i'', j'') Hin_orig).
      apply (compatible_pairs_shift_id_S (i, j) (i'', j'')). exact Hforall.
    + apply IH. exact Hrest.
Qed.

(** is_valid_trace_aux holds for optimal_trace_pair *)
Lemma optimal_trace_pair_aux_valid : forall A B,
  is_valid_trace_aux (optimal_trace_pair (A, B)) = true.
Proof.
  intros A' B'.
  remember (length A' + length B') as n eqn:Hn.
  revert A' B' Hn.
  induction n as [n IH] using lt_wf_ind.
  intros A' B' Hn.
  rewrite optimal_trace_pair_unfold.
  destruct A' as [| c1 s1'], B' as [| c2 s2'].
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - cbv zeta.
    destruct ((lev_distance s1' s2' + subst_cost c1 c2 <=? lev_distance s1' (c2 :: s2') + 1) &&
              (lev_distance s1' s2' + subst_cost c1 c2 <=? lev_distance (c1 :: s1') s2' + 1)) eqn:E_sub.
    + apply is_valid_trace_aux_cons_one_one_map_SS.
      * apply (IH (length s1' + length s2')). subst n. simpl. lia. reflexivity.
      * apply optimal_trace_pair_indices_ge_1.
    + destruct (lev_distance s1' (c2 :: s2') + 1 <=? lev_distance (c1 :: s1') s2' + 1) eqn:E_del.
      * apply is_valid_trace_aux_map_S_id.
        apply (IH (length s1' + length (c2 :: s2'))). subst n. simpl. lia. reflexivity.
      * apply is_valid_trace_aux_map_id_S.
        apply (IH (length (c1 :: s1') + length s2')). subst n. simpl. lia. reflexivity.
Qed.

(** * NoDup Properties *)

(** NoDup is preserved by injective maps on pairs *)
Lemma NoDup_map_pair_injective : forall (f : nat * nat -> nat * nat) T,
  (forall p1 p2, f p1 = f p2 -> p1 = p2) ->
  NoDup T -> NoDup (map f T).
Proof.
  intros f T Hinj Hnodup.
  induction Hnodup as [| [i j] rest Hnotin Hnodup IH].
  - constructor.
  - simpl. constructor.
    + intro Hin. apply in_map_iff in Hin.
      destruct Hin as [[i' j'] [Heq Hin']].
      apply Hinj in Heq. injection Heq as Hi Hj. subst i' j'.
      contradiction.
    + exact IH.
Qed.

(** SS shift is injective *)
Lemma SS_shift_injective : forall p1 p2,
  (let '(i, j) := p1 in (S i, S j)) = (let '(i, j) := p2 in (S i, S j)) -> p1 = p2.
Proof.
  intros [i1 j1] [i2 j2] H.
  injection H as Hi Hj. f_equal; lia.
Qed.

(** S_id shift is injective *)
Lemma S_id_shift_injective : forall (p1 p2 : nat * nat),
  (let '(i, j) := p1 in (S i, j)) = (let '(i, j) := p2 in (S i, j)) -> p1 = p2.
Proof.
  intros [i1 j1] [i2 j2] H.
  injection H as Hi Hj. f_equal; lia.
Qed.

(** id_S shift is injective *)
Lemma id_S_shift_injective : forall (p1 p2 : nat * nat),
  (let '(i, j) := p1 in (i, S j)) = (let '(i, j) := p2 in (i, S j)) -> p1 = p2.
Proof.
  intros [i1 j1] [i2 j2] H.
  injection H as Hi Hj. f_equal; lia.
Qed.

(** NoDup is preserved for (1,1) :: map SS T when all elements of T have indices >= 1 *)
Lemma NoDup_cons_one_one_map_SS : forall T,
  NoDup T ->
  Forall (fun '(i, j) => i >= 1 /\ j >= 1) T ->
  NoDup ((1, 1) :: map (fun '(i, j) => (S i, S j)) T).
Proof.
  intros T Hnodup Hge.
  constructor.
  - intro Hin. rewrite in_map_iff in Hin.
    destruct Hin as [[i j] [Heq Hin']].
    injection Heq as Hi Hj.
    rewrite Forall_forall in Hge.
    specialize (Hge (i, j) Hin').
    destruct Hge as [Hi_ge Hj_ge].
    lia.
  - apply NoDup_map_pair_injective.
    + exact SS_shift_injective.
    + exact Hnodup.
Qed.

(** NoDup holds for optimal_trace_pair *)
Lemma optimal_trace_pair_NoDup : forall A B,
  NoDup (optimal_trace_pair (A, B)).
Proof.
  intros A' B'.
  remember (length A' + length B') as n eqn:Hn.
  revert A' B' Hn.
  induction n as [n IH] using lt_wf_ind.
  intros A' B' Hn.
  rewrite optimal_trace_pair_unfold.
  destruct A' as [| c1 s1'], B' as [| c2 s2'].
  - constructor.
  - constructor.
  - constructor.
  - cbv zeta.
    destruct ((lev_distance s1' s2' + subst_cost c1 c2 <=? lev_distance s1' (c2 :: s2') + 1) &&
              (lev_distance s1' s2' + subst_cost c1 c2 <=? lev_distance (c1 :: s1') s2' + 1)) eqn:E_sub.
    + apply NoDup_cons_one_one_map_SS.
      * apply (IH (length s1' + length s2')). subst n. simpl. lia. reflexivity.
      * apply optimal_trace_pair_indices_ge_1.
    + destruct (lev_distance s1' (c2 :: s2') + 1 <=? lev_distance (c1 :: s1') s2' + 1) eqn:E_del.
      * apply NoDup_map_pair_injective.
        -- exact S_id_shift_injective.
        -- apply (IH (length s1' + length (c2 :: s2'))). subst n. simpl. lia. reflexivity.
      * apply NoDup_map_pair_injective.
        -- exact id_S_shift_injective.
        -- apply (IH (length (c1 :: s1') + length s2')). subst n. simpl. lia. reflexivity.
Qed.

(** * Main Validity Theorem *)

(**
   Optimal trace validity (is_valid_trace = true)

   The optimal trace satisfies is_valid_trace because:
   1. All indices are within bounds [1, |A|] × [1, |B|] (by construction)
   2. Pairs are compatible (monotonicity enforced by DP structure)
   3. No duplicate pairs (each step advances at least one index)
*)
Lemma optimal_trace_valid :
  forall (A B : list Char),
    is_valid_trace A B (optimal_trace A B) = true.
Proof.
  intros A B.
  unfold is_valid_trace, optimal_trace.
  apply andb_true_iff. split.
  apply andb_true_iff. split.
  - (* forallb valid_pair *)
    pose proof (optimal_trace_pair_bounds A B) as Hbounds.
    rewrite forallb_forall.
    intros [i j] Hin.
    rewrite Forall_forall in Hbounds.
    specialize (Hbounds (i, j) Hin).
    destruct Hbounds as [[Hi_lo Hi_hi] [Hj_lo Hj_hi]].
    unfold valid_pair.
    repeat (apply andb_true_iff; split).
    + apply Nat.leb_le. lia.
    + apply Nat.leb_le. lia.
    + apply Nat.leb_le. lia.
    + apply Nat.leb_le. lia.
  - (* is_valid_trace_aux *)
    apply optimal_trace_pair_aux_valid.
  - (* NoDup_dec *)
    apply NoDup_dec_correct.
    apply optimal_trace_pair_NoDup.
Qed.
