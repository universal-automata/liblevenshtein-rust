(** * Anti-Chain Properties for Levenshtein Automata States

    This module defines the anti-chain property which ensures that no position
    in a state subsumes another. This is critical for state minimization.

    Part of: Liblevenshtein.Core.Automaton

    Rust Reference: src/transducer/state.rs:107-125 (online subsumption)

    Key Definitions:
    - is_antichain: No position subsumes another in the list
    - antichain_insert: Insert maintaining anti-chain property

    Key Theorems:
    - antichain_insert_preserves: Insert maintains anti-chain
    - antichain_size_bounded: Size ≤ (query_len + 1) × (n + 1) × 2
*)

From Stdlib Require Import Arith Bool List Nat Lia.
Import ListNotations.

From Liblevenshtein.Core Require Import Automaton.Position.
From Liblevenshtein.Core Require Import Automaton.Subsumption.

(** * Anti-Chain Definition *)

(** A list of positions forms an anti-chain if no distinct positions
    have a subsumption relationship. *)
Definition is_antichain (alg : Algorithm) (qlen : nat) (positions : list Position) : Prop :=
  forall p1 p2, In p1 positions -> In p2 positions -> p1 <> p2 ->
    subsumes alg qlen p1 p2 = false.

(** Boolean check for anti-chain property *)
Fixpoint is_antichain_b_aux (alg : Algorithm) (qlen : nat) (p : Position) (rest : list Position) : bool :=
  match rest with
  | [] => true
  | p' :: rest' =>
      negb (position_eqb p p') &&
      negb (subsumes alg qlen p p') &&
      negb (subsumes alg qlen p' p) &&
      is_antichain_b_aux alg qlen p rest'
  end.

Fixpoint is_antichain_b (alg : Algorithm) (qlen : nat) (positions : list Position) : bool :=
  match positions with
  | [] => true
  | p :: rest =>
      is_antichain_b_aux alg qlen p rest && is_antichain_b alg qlen rest
  end.

(** * Empty List is Anti-Chain *)

Lemma antichain_nil : forall alg qlen,
  is_antichain alg qlen [].
Proof.
  intros alg qlen p1 p2 H1 H2 Hneq.
  inversion H1.
Qed.

(** * Singleton is Anti-Chain *)

Lemma antichain_singleton : forall alg qlen p,
  is_antichain alg qlen [p].
Proof.
  intros alg qlen p p1 p2 H1 H2 Hneq.
  destruct H1 as [H1 | H1]; destruct H2 as [H2 | H2];
  try inversion H1; try inversion H2; subst.
  - contradiction.
Qed.

(** * Subsumption-Free Insertion *)

(** Check if a position is subsumed by any in the list *)
Fixpoint subsumed_by_any (alg : Algorithm) (qlen : nat) (p : Position) (positions : list Position) : bool :=
  match positions with
  | [] => false
  | p' :: rest =>
      if subsumes alg qlen p' p then true
      else subsumed_by_any alg qlen p rest
  end.

(** Remove positions subsumed by a given position *)
Fixpoint remove_subsumed (alg : Algorithm) (qlen : nat) (p : Position) (positions : list Position) : list Position :=
  match positions with
  | [] => []
  | p' :: rest =>
      if subsumes alg qlen p p' then remove_subsumed alg qlen p rest
      else p' :: remove_subsumed alg qlen p rest
  end.

(** Insert a position while maintaining anti-chain property *)
Definition antichain_insert (alg : Algorithm) (qlen : nat) (p : Position) (positions : list Position) : list Position :=
  if subsumed_by_any alg qlen p positions then
    positions  (* p is subsumed, don't insert *)
  else
    p :: remove_subsumed alg qlen p positions.  (* Insert p, remove subsumed *)

(** * Helper Lemmas *)

Lemma in_remove_subsumed : forall alg qlen p p' positions,
  In p' (remove_subsumed alg qlen p positions) ->
  In p' positions /\ subsumes alg qlen p p' = false.
Proof.
  intros alg qlen p p' positions H.
  induction positions as [| q rest IH].
  - simpl in H. inversion H.
  - simpl in H.
    destruct (subsumes alg qlen p q) eqn:Hsub.
    + (* q was removed *)
      destruct IH as [Hin Hnsub]; auto.
      split; auto. right. auto.
    + (* q was kept *)
      simpl in H. destruct H as [Heq | Hin].
      * subst. split; [left; reflexivity | assumption].
      * destruct IH as [Hin' Hnsub]; auto.
        split; auto. right. auto.
Qed.

Lemma not_in_remove_subsumed_if_subsumed : forall alg qlen p p' positions,
  subsumes alg qlen p p' = true ->
  ~ In p' (remove_subsumed alg qlen p positions).
Proof.
  intros alg qlen p p' positions Hsub Hin.
  apply in_remove_subsumed in Hin.
  destruct Hin as [_ Hnsub].
  rewrite Hsub in Hnsub. discriminate.
Qed.

Lemma remove_subsumed_preserves : forall alg qlen p positions p1 p2,
  is_antichain alg qlen positions ->
  In p1 (remove_subsumed alg qlen p positions) ->
  In p2 (remove_subsumed alg qlen p positions) ->
  p1 <> p2 ->
  subsumes alg qlen p1 p2 = false.
Proof.
  intros alg qlen p positions p1 p2 Hac H1 H2 Hneq.
  apply in_remove_subsumed in H1.
  apply in_remove_subsumed in H2.
  destruct H1 as [H1in _], H2 as [H2in _].
  apply Hac; assumption.
Qed.

(** * Main Preservation Theorem *)

Lemma subsumed_by_any_correct : forall alg qlen p positions,
  subsumed_by_any alg qlen p positions = true <->
  exists p', In p' positions /\ subsumes alg qlen p' p = true.
Proof.
  intros alg qlen p positions.
  split.
  - (* -> *)
    induction positions as [| q rest IH].
    + simpl. discriminate.
    + simpl. destruct (subsumes alg qlen q p) eqn:Hsub.
      * intros _. exists q. split; [left; reflexivity | assumption].
      * intros H. destruct IH as [p' [Hin Hsub']]; auto.
        exists p'. split; [right; assumption | assumption].
  - (* <- *)
    intros [p' [Hin Hsub]].
    induction positions as [| q rest IH].
    + inversion Hin.
    + simpl in Hin. destruct Hin as [Heq | Hin].
      * subst. simpl. rewrite Hsub. reflexivity.
      * simpl. destruct (subsumes alg qlen q p) eqn:Hsub'.
        -- reflexivity.
        -- apply IH. assumption.
Qed.

Lemma antichain_insert_preserves : forall alg qlen p positions,
  is_antichain alg qlen positions ->
  is_antichain alg qlen (antichain_insert alg qlen p positions).
Proof.
  intros alg qlen p positions Hac.
  unfold antichain_insert.
  destruct (subsumed_by_any alg qlen p positions) eqn:Hsub.
  - (* p is subsumed, positions unchanged *)
    assumption.
  - (* p not subsumed, insert p and remove subsumed *)
    intros p1 p2 H1 H2 Hneq.
    simpl in H1, H2.
    destruct H1 as [Heq1 | Hin1]; destruct H2 as [Heq2 | Hin2].
    + (* p1 = p, p2 = p *)
      subst. contradiction.
    + (* p1 = p, p2 in remove_subsumed *)
      subst.
      apply in_remove_subsumed in Hin2.
      destruct Hin2 as [_ Hnsub].
      assumption.
    + (* p1 in remove_subsumed, p2 = p *)
      subst p2.
      (* We need to show subsumes alg qlen p1 p = false *)
      (* Since subsumed_by_any = false, no position in positions subsumes p *)
      apply in_remove_subsumed in Hin1.
      destruct Hin1 as [Hin1' _].
      (* We need a lemma that subsumed_by_any = false implies no subsumption *)
      destruct (subsumes alg qlen p1 p) eqn:Hcheck; auto.
      exfalso.
      assert (Hbad : subsumed_by_any alg qlen p positions = true).
      { apply subsumed_by_any_correct. exists p1. split; assumption. }
      rewrite Hsub in Hbad. discriminate.
    + (* Both in remove_subsumed *)
      apply remove_subsumed_preserves with p positions; assumption.
Qed.

(** * Membership After Insert *)

Lemma in_antichain_insert : forall alg qlen p positions,
  In p (antichain_insert alg qlen p positions) \/
  subsumed_by_any alg qlen p positions = true.
Proof.
  intros alg qlen p positions.
  unfold antichain_insert.
  destruct (subsumed_by_any alg qlen p positions) eqn:Hsub.
  - right. reflexivity.
  - left. simpl. left. reflexivity.
Qed.

Lemma in_remove_subsumed_if_not_subsumed : forall alg qlen p p' positions,
  In p' positions ->
  subsumes alg qlen p p' = false ->
  In p' (remove_subsumed alg qlen p positions).
Proof.
  intros alg qlen p p'.
  induction positions as [| q rest IH]; intros Hin Hnsub.
  - inversion Hin.
  - simpl in Hin. simpl.
    destruct (subsumes alg qlen p q) eqn:Hsubq.
    + (* q is removed, p' must be in rest *)
      destruct Hin as [Heq | Hin'].
      * subst. rewrite Hnsub in Hsubq. discriminate.
      * apply IH; assumption.
    + (* q is kept *)
      destruct Hin as [Heq | Hin'].
      * subst. left. reflexivity.
      * right. apply IH; assumption.
Qed.

Lemma in_antichain_insert_old : forall alg qlen p p' positions,
  In p' positions ->
  subsumes alg qlen p p' = false ->
  In p' (antichain_insert alg qlen p positions).
Proof.
  intros alg qlen p p' positions Hin Hnsub.
  unfold antichain_insert.
  destruct (subsumed_by_any alg qlen p positions) eqn:Hsub.
  - assumption.
  - simpl. right.
    apply in_remove_subsumed_if_not_subsumed; assumption.
Qed.

(** * Size Bounds *)

(** For Standard algorithm, the maximum number of positions is bounded by
    (query_length + 1) * (max_distance + 1) since each position (i, e) is unique.
    For algorithms with special flag, multiply by 2. *)

Definition max_positions (alg : Algorithm) (query_length max_distance : nat) : nat :=
  let base := (query_length + 1) * (max_distance + 1) in
  match alg with
  | Standard => base
  | Transposition => 2 * base  (* special flag doubles possibilities *)
  | MergeAndSplit => 2 * base
  end.

(** Note: A full proof of antichain_size_bounded requires showing that
    positions in an antichain must have distinct (i,e,s) triples up to
    subsumption equivalence. This is complex and deferred. *)

(** * NoDup Properties *)

(** Note: An antichain as defined here doesn't directly imply NoDup because
    the antichain property only applies to distinct positions (p1 <> p2).
    For Standard and Transposition algorithms, subsumption is reflexive,
    so antichain alone doesn't prevent duplicates.

    For this reason, we define well_formed_antichain below which explicitly
    requires both the antichain property and NoDup. *)

(** A stronger property: positions have distinct keys *)
Definition positions_distinct (positions : list Position) : Prop :=
  NoDup positions.

(** For a proper anti-chain invariant, we typically maintain both:
    1. is_antichain - no subsumption between distinct elements
    2. NoDup - no duplicate positions *)

Definition well_formed_antichain (alg : Algorithm) (qlen : nat) (positions : list Position) : Prop :=
  is_antichain alg qlen positions /\ NoDup positions.

Lemma well_formed_nil : forall alg qlen,
  well_formed_antichain alg qlen [].
Proof.
  intros alg qlen.
  split.
  - apply antichain_nil.
  - constructor.
Qed.

(** * Sorted Anti-Chain (for efficient State representation) *)

(** A sorted anti-chain maintains positions in lexicographic order *)
Fixpoint is_sorted (positions : list Position) : Prop :=
  match positions with
  | [] => True
  | [_] => True
  | p1 :: ((p2 :: _) as rest) => position_lt p1 p2 /\ is_sorted rest
  end.

Lemma sorted_nil : is_sorted [].
Proof. simpl. exact I. Qed.

Lemma sorted_singleton : forall p, is_sorted [p].
Proof. intros p. simpl. exact I. Qed.

Lemma sorted_cons_inv : forall p1 p2 rest,
  is_sorted (p1 :: p2 :: rest) ->
  position_lt p1 p2 /\ is_sorted (p2 :: rest).
Proof.
  intros p1 p2 rest H.
  simpl in H. exact H.
Qed.

(** Helper: In a sorted list, the head is less than all elements in the tail *)
Lemma sorted_head_lt_all : forall p1 p2 rest p,
  is_sorted (p1 :: p2 :: rest) ->
  In p (p2 :: rest) ->
  position_lt p1 p.
Proof.
  intros p1 p2 rest.
  revert p1 p2.
  induction rest as [| p3 rest' IH]; intros p1 p2 p Hsorted Hin.
  - simpl in Hin. destruct Hin as [Heq | Hin].
    + subst. apply sorted_cons_inv in Hsorted. destruct Hsorted as [Hlt _]. exact Hlt.
    + contradiction.
  - apply sorted_cons_inv in Hsorted.
    destruct Hsorted as [Hlt12 Hsorted'].
    simpl in Hin. destruct Hin as [Heq | Hin'].
    + subst. exact Hlt12.
    + (* p is in p3 :: rest' *)
      apply sorted_cons_inv in Hsorted'.
      destruct Hsorted' as [Hlt23 Hsorted''].
      pose proof (IH p2 p3 p) as IHapp.
      assert (Hsorted23 : is_sorted (p2 :: p3 :: rest')).
      { simpl. split; assumption. }
      specialize (IHapp Hsorted23 Hin').
      apply position_lt_trans with p2; assumption.
Qed.

Lemma sorted_implies_nodup : forall positions,
  is_sorted positions -> NoDup positions.
Proof.
  intros positions.
  induction positions as [| p1 rest IH].
  - intros _. constructor.
  - intros Hsorted.
    constructor.
    + (* p1 not in rest *)
      destruct rest as [| p2 rest'].
      * simpl. auto.
      * intros Hin.
        pose proof (sorted_head_lt_all p1 p2 rest' p1 Hsorted Hin) as Hlt.
        apply position_lt_irrefl in Hlt. exact Hlt.
    + (* NoDup rest *)
      destruct rest as [| p2 rest'].
      * constructor.
      * apply sorted_cons_inv in Hsorted.
        destruct Hsorted as [_ Hsorted'].
        apply IH. exact Hsorted'.
Qed.

(** Sorted anti-chain is well-formed *)
Lemma sorted_antichain_well_formed : forall alg qlen positions,
  is_sorted positions ->
  is_antichain alg qlen positions ->
  well_formed_antichain alg qlen positions.
Proof.
  intros alg qlen positions Hsorted Hac.
  split.
  - exact Hac.
  - apply sorted_implies_nodup. exact Hsorted.
Qed.

(** * Final Position Preservation *)

(** Key insight: A non-final position cannot subsume a final position (by the
    subsumption fix). Therefore, all final positions survive remove_subsumed
    when the inserted position is non-final. *)

(** If position q is not subsumed by p, then q survives in remove_subsumed *)
Lemma remove_subsumed_keeps_unsubsumed : forall alg qlen p q positions,
  In q positions ->
  subsumes alg qlen p q = false ->
  In q (remove_subsumed alg qlen p positions).
Proof.
  intros alg qlen p q positions Hin Hnsub.
  induction positions as [| r rest IH].
  - inversion Hin.
  - simpl in Hin. destruct Hin as [Heq | Hin'].
    + (* q = r *)
      subst r. simpl. rewrite Hnsub. left. reflexivity.
    + (* q in rest *)
      simpl. destruct (subsumes alg qlen p r) eqn:Hsub_r.
      * (* r is subsumed - still in rest *)
        apply IH. exact Hin'.
      * (* r is not subsumed - q in rest *)
        right. apply IH. exact Hin'.
Qed.

(** Final positions (using subsumption finality check) in the input survive
    remove_subsumed when p is non-final.
    This uses the critical property that non-final cannot subsume final. *)
Lemma remove_subsumed_preserves_final_subsumption : forall alg qlen p q positions,
  position_is_final_for_subsumption qlen q = true ->
  position_is_final_for_subsumption qlen p = false ->
  In q positions ->
  In q (remove_subsumed alg qlen p positions).
Proof.
  intros alg qlen p q positions Hq_final Hp_non_final Hin.
  apply remove_subsumed_keeps_unsubsumed.
  - exact Hin.
  - (* p cannot subsume q because p is non-final and q is final *)
    apply non_final_cannot_subsume_final; assumption.
Qed.

(** Existsb final (using subsumption finality check) is preserved when
    inserting a non-final position *)
Lemma remove_subsumed_preserves_existsb_final_subsumption : forall alg qlen p positions,
  position_is_final_for_subsumption qlen p = false ->
  existsb (position_is_final_for_subsumption qlen) positions = true ->
  existsb (position_is_final_for_subsumption qlen) (remove_subsumed alg qlen p positions) = true.
Proof.
  intros alg qlen p positions Hp_non_final Hexists.
  rewrite existsb_exists in Hexists.
  rewrite existsb_exists.
  destruct Hexists as [q [Hin Hq_final]].
  exists q. split.
  - apply remove_subsumed_preserves_final_subsumption; assumption.
  - exact Hq_final.
Qed.
