(** * Trace Definitions and Validity

    A trace is a formalization of how an edit sequence transforms string A
    into string B, abstracting away the order of operations and focusing on
    the correspondence between character positions.

    Part of: Liblevenshtein.Core

    Decomposed from: Distance.v (lines 840-1160)
*)

From Coq Require Import String List Arith Ascii Bool Nat Lia.
Import ListNotations.

From Liblevenshtein.Core Require Import Core.Definitions.

(** * Trace Type Definition *)

(** A trace is represented as a list of pairs (i, j) where 1 <= i <= |A|, 1 <= j <= |B| *)
Definition Trace (A B : list Char) := list (nat * nat).

(** * Validity Predicates *)

(** Check if a pair is valid for given string lengths *)
Definition valid_pair (lenA lenB : nat) (p : nat * nat) : bool :=
  let (i, j) := p in
  (1 <=? i) && (i <=? lenA) && (1 <=? j) && (j <=? lenB).

(** Check if two pairs are compatible (don't violate trace conditions) *)
Definition compatible_pairs (p1 p2 : nat * nat) : bool :=
  let '(i1, j1) := p1 in
  let '(i2, j2) := p2 in
  if (i1 =? i2) && (j1 =? j2) then true
  else if (i1 =? i2) || (j1 =? j2) then false
  else if i1 <? i2 then j1 <? j2 else j2 <? j1.

(** Check if a list of pairs forms a valid trace *)
Fixpoint is_valid_trace_aux (pairs : list (nat * nat)) : bool :=
  match pairs with
  | [] => true
  | p :: ps =>
      (forallb (compatible_pairs p) ps) && is_valid_trace_aux ps
  end.

(** * Monotonicity *)

(** A trace is monotonic if matching preserves order *)
Definition trace_monotonic (T : list (nat * nat)) : Prop :=
  forall i1 j1 i2 j2,
    In (i1, j1) T -> In (i2, j2) T -> i1 < i2 -> j1 < j2.

(** * Bridge Lemmas *)

(** Helper: compatible_pairs enforces order *)
Lemma compatible_pairs_monotonic_helper : forall i1 j1 i2 j2,
  compatible_pairs (i1, j1) (i2, j2) = true ->
  i1 <> i2 ->
  j1 <> j2 ->
  (i1 < i2 -> j1 < j2).
Proof.
  intros i1 j1 i2 j2 Hcompat Hneq_i Hneq_j Hlt_i.
  unfold compatible_pairs in Hcompat.
  destruct (i1 =? i2) eqn:Ei; destruct (j1 =? j2) eqn:Ej; simpl in Hcompat.
  - apply Nat.eqb_eq in Ei. contradiction.
  - discriminate.
  - discriminate.
  - destruct (i1 <? i2) eqn:Elt.
    + apply Nat.ltb_lt in Hcompat. exact Hcompat.
    + apply Nat.ltb_nlt in Elt. lia.
Qed.

(** Helper: forallb compatible_pairs implies monotonicity for first element *)
Lemma forallb_compatible_monotonic : forall p T,
  forallb (compatible_pairs p) T = true ->
  let '(i1, j1) := p in
  forall i2 j2, In (i2, j2) T -> i1 <> i2 -> j1 <> j2 -> i1 < i2 -> j1 < j2.
Proof.
  intros [i1 j1] T Hforall.
  rewrite forallb_forall in Hforall.
  intros i2 j2 Hin Hneq_i Hneq_j Hlt.
  specialize (Hforall (i2, j2) Hin).
  apply (compatible_pairs_monotonic_helper i1 j1 i2 j2); assumption.
Qed.

(** Helper: is_valid_trace_aux implies all pairs are pairwise compatible *)
Lemma is_valid_trace_aux_pairwise_compat : forall T p1 p2,
  is_valid_trace_aux T = true ->
  In p1 T -> In p2 T -> p1 <> p2 ->
  compatible_pairs p1 p2 = true \/ compatible_pairs p2 p1 = true.
Proof.
  induction T as [| q rest IH]; intros p1 p2 Hvalid Hin1 Hin2 Hneq.
  - destruct Hin1.
  - simpl in Hvalid.
    apply andb_true_iff in Hvalid. destruct Hvalid as [Hforall Hrest].
    destruct Hin1 as [Heq1 | Hin1'], Hin2 as [Heq2 | Hin2'].
    + subst. contradiction.
    + subst. left.
      rewrite forallb_forall in Hforall.
      apply Hforall. exact Hin2'.
    + subst. right.
      rewrite forallb_forall in Hforall.
      apply Hforall. exact Hin1'.
    + apply IH; assumption.
Qed.

(** Helper: compatible_pairs is symmetric for the "different indices" case *)
Lemma compatible_pairs_different_implies_order : forall i1 j1 i2 j2,
  i1 <> i2 -> j1 <> j2 ->
  compatible_pairs (i1, j1) (i2, j2) = true ->
  (i1 < i2 <-> j1 < j2).
Proof.
  intros i1 j1 i2 j2 Hneq_i Hneq_j Hcompat.
  unfold compatible_pairs in Hcompat.
  apply Nat.eqb_neq in Hneq_i. rewrite Hneq_i in Hcompat. simpl in Hcompat.
  apply Nat.eqb_neq in Hneq_j. rewrite Hneq_j in Hcompat. simpl in Hcompat.
  destruct (i1 <? i2) eqn:Elt.
  - split.
    + intros _. apply Nat.ltb_lt. exact Hcompat.
    + intros. apply Nat.ltb_lt. exact Elt.
  - split.
    + intros H. apply Nat.ltb_nlt in Elt. lia.
    + intros H. apply Nat.ltb_lt in Hcompat. lia.
Qed.

(** BRIDGE LEMMA: is_valid_trace_aux implies monotonicity *)
Lemma is_valid_trace_aux_implies_monotonic : forall T,
  NoDup T ->
  is_valid_trace_aux T = true ->
  trace_monotonic T.
Proof.
  intros T Hnodup Hvalid.
  unfold trace_monotonic.
  intros i1 j1 i2 j2 Hin1 Hin2 Hlt_i.
  destruct (Nat.eq_dec j1 j2) as [Heq_j | Hneq_j].
  - subst j2.
    assert (Hneq_pair: (i1, j1) <> (i2, j1)).
    { intro Heq. injection Heq as Hi. lia. }
    destruct (is_valid_trace_aux_pairwise_compat T (i1, j1) (i2, j1) Hvalid Hin1 Hin2 Hneq_pair) as [H | H].
    + unfold compatible_pairs in H.
      destruct (i1 =? i2) eqn:Ei.
      * apply Nat.eqb_eq in Ei. lia.
      * simpl in H. rewrite Nat.eqb_refl in H. simpl in H. discriminate.
    + unfold compatible_pairs in H.
      destruct (i2 =? i1) eqn:Ei.
      * apply Nat.eqb_eq in Ei. lia.
      * simpl in H. rewrite Nat.eqb_refl in H. simpl in H. discriminate.
  - assert (Hneq: (i1, j1) <> (i2, j2)).
    { intro Heq. injection Heq as Hi Hj. lia. }
    assert (Hneq_i: i1 <> i2) by lia.
    destruct (is_valid_trace_aux_pairwise_compat T (i1, j1) (i2, j2) Hvalid Hin1 Hin2 Hneq) as [H | H].
    + pose proof (compatible_pairs_different_implies_order i1 j1 i2 j2 Hneq_i Hneq_j H) as Hiff.
      tauto.
    + assert (Hneq_i': i2 <> i1) by lia.
      assert (Hneq_j': j2 <> j1) by lia.
      pose proof (compatible_pairs_different_implies_order i2 j2 i1 j1 Hneq_i' Hneq_j' H) as Hiff.
      assert (Hnot: ~ i2 < i1) by lia.
      rewrite Hiff in Hnot. lia.
Qed.

(** * NoDup Decision Procedure *)

(** Decidable equality for nat * nat pairs *)
Definition pair_eq_dec (p1 p2 : nat * nat) : {p1 = p2} + {p1 <> p2}.
Proof.
  decide equality; apply Nat.eq_dec.
Defined.

(** Decidable NoDup check *)
Fixpoint NoDup_dec {A : Type} (eq_dec : forall x y : A, {x = y} + {x <> y})
                   (l : list A) : bool :=
  match l with
  | [] => true
  | x :: xs =>
      negb (existsb (fun y => if eq_dec x y then true else false) xs) &&
      NoDup_dec eq_dec xs
  end.

(** Correctness of NoDup_dec *)
Lemma NoDup_dec_correct :
  forall {A : Type} (eq_dec : forall x y : A, {x = y} + {x <> y}) (l : list A),
    NoDup_dec eq_dec l = true <-> NoDup l.
Proof.
  intros A eq_dec l.
  split.
  - induction l as [| x xs IH].
    + intro. constructor.
    + intro H.
      simpl in H.
      apply andb_true_iff in H as [H_not_in H_dec_xs].
      constructor.
      * intro H_in.
        apply negb_true_iff in H_not_in.
        assert (H_should_exist: existsb (fun y => if eq_dec x y then true else false) xs = true).
        { rewrite existsb_exists. exists x. split; [exact H_in |].
          destruct (eq_dec x x) as [_ | H_neq]; [reflexivity | exfalso; apply H_neq; reflexivity]. }
        rewrite H_should_exist in H_not_in. discriminate.
      * apply IH. exact H_dec_xs.

  - induction l as [| x xs IH].
    + intro. simpl. reflexivity.
    + intro H.
      inversion H as [| ? ? H_not_in H_nodup_xs].
      simpl.
      apply andb_true_iff.
      split.
      * apply negb_true_iff.
        apply Bool.not_true_iff_false.
        intro H_ex.
        rewrite existsb_exists in H_ex.
        destruct H_ex as [y [H_y_in H_eq]].
        destruct (eq_dec x y) as [H_xy | H_neq].
        -- subst y. contradiction.
        -- discriminate H_eq.
      * apply IH. exact H_nodup_xs.
Qed.

(** * Full Validity Check *)

Definition is_valid_trace (A B : list Char) (T : Trace A B) : bool :=
  (forallb (valid_pair (length A) (length B)) T) &&
  is_valid_trace_aux T &&
  NoDup_dec pair_eq_dec T.

(** Valid traces have NoDup *)
Lemma is_valid_trace_implies_NoDup :
  forall (A B : list Char) (T : Trace A B),
    is_valid_trace A B T = true -> NoDup T.
Proof.
  intros A B T H_valid.
  unfold is_valid_trace in H_valid.
  apply andb_true_iff in H_valid as [H_rest H_nodup].
  apply andb_true_iff in H_rest as [H_bounds H_compat].
  apply NoDup_dec_correct in H_nodup. exact H_nodup.
Qed.

(** Valid traces are monotonic *)
Lemma is_valid_trace_implies_monotonic :
  forall (A B : list Char) (T : Trace A B),
    is_valid_trace A B T = true -> trace_monotonic T.
Proof.
  intros A B T H_valid.
  assert (H_nodup: NoDup T) by (apply is_valid_trace_implies_NoDup; exact H_valid).
  unfold is_valid_trace in H_valid.
  apply andb_true_iff in H_valid as [H_rest H_nodup_dec].
  apply andb_true_iff in H_rest as [H_bounds H_valid_aux].
  apply is_valid_trace_aux_implies_monotonic; assumption.
Qed.
