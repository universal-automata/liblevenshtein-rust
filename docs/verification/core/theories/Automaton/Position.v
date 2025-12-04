(** * Automaton Position Type

    This module defines the Position type for Levenshtein automata, representing
    a location (term_index, num_errors, is_special) in the automaton state.

    Part of: Liblevenshtein.Core.Automaton

    Rust Reference: src/transducer/position.rs:20-32

    Key Types:
    - Position: Record with term_index, num_errors, is_special
    - Algorithm: Standard | Transposition | MergeAndSplit

    Key Lemmas:
    - position_eq_dec: Decidable equality for positions
    - position_lt_trans: Transitivity of position ordering
*)

From Stdlib Require Import Arith Bool List Nat Lia.
Import ListNotations.

(** * Algorithm Type *)

(** The algorithm variant for Levenshtein distance computation. *)
Inductive Algorithm : Type :=
  | Standard      (* Standard Levenshtein: Insert, Delete, Substitute *)
  | Transposition (* Damerau-Levenshtein: + Transpose adjacent chars *)
  | MergeAndSplit (* Linguistic: + Merge (2->1) and Split (1->2) *)
  .

Definition algorithm_eq_dec (a1 a2 : Algorithm) : {a1 = a2} + {a1 <> a2}.
Proof.
  decide equality.
Defined.

Definition algorithm_eqb (a1 a2 : Algorithm) : bool :=
  match a1, a2 with
  | Standard, Standard => true
  | Transposition, Transposition => true
  | MergeAndSplit, MergeAndSplit => true
  | _, _ => false
  end.

Lemma algorithm_eqb_eq : forall a1 a2,
  algorithm_eqb a1 a2 = true <-> a1 = a2.
Proof.
  intros a1 a2. destruct a1, a2; simpl; split; intros H; try reflexivity; try discriminate.
Qed.

(** * Position Type *)

(** A position in the Levenshtein automaton.

    - term_index: Number of characters consumed from query (0 to query_length)
    - num_errors: Number of edit operations accumulated (0 to max_distance)
    - is_special: Flag for extended algorithms (transposition-in-progress, split-in-progress)
*)
Record Position : Type := mkPosition {
  term_index : nat;
  num_errors : nat;
  is_special : bool
}.

(** Smart constructor for non-special positions *)
Definition std_pos (i e : nat) : Position :=
  mkPosition i e false.

(** Smart constructor for special positions *)
Definition special_pos (i e : nat) : Position :=
  mkPosition i e true.

(** * Position Equality *)

Definition position_eqb (p1 p2 : Position) : bool :=
  (term_index p1 =? term_index p2) &&
  (num_errors p1 =? num_errors p2) &&
  (Bool.eqb (is_special p1) (is_special p2)).

Lemma position_eqb_eq : forall p1 p2,
  position_eqb p1 p2 = true <-> p1 = p2.
Proof.
  intros [i1 e1 s1] [i2 e2 s2].
  unfold position_eqb. simpl.
  rewrite andb_true_iff, andb_true_iff.
  rewrite Nat.eqb_eq, Nat.eqb_eq, Bool.eqb_true_iff.
  split.
  - intros [[Hi He] Hs]. subst. reflexivity.
  - intros H. injection H as Hi He Hs. subst. auto.
Qed.

Lemma position_eqb_refl : forall p,
  position_eqb p p = true.
Proof.
  intros p. apply position_eqb_eq. reflexivity.
Qed.

(** Decidable equality for positions *)
Definition position_eq_dec (p1 p2 : Position) : {p1 = p2} + {p1 <> p2}.
Proof.
  destruct p1 as [i1 e1 s1], p2 as [i2 e2 s2].
  destruct (Nat.eq_dec i1 i2) as [Hi | Hi].
  - destruct (Nat.eq_dec e1 e2) as [He | He].
    + destruct (Bool.bool_dec s1 s2) as [Hs | Hs].
      * left. subst. reflexivity.
      * right. intros H. injection H. intros. contradiction.
    + right. intros H. injection H. intros. contradiction.
  - right. intros H. injection H. intros. contradiction.
Defined.

(** * Position Ordering (Lexicographic) *)

(** Lexicographic ordering as a proposition *)
Definition position_lt (p1 p2 : Position) : Prop :=
  let i1 := term_index p1 in
  let i2 := term_index p2 in
  let e1 := num_errors p1 in
  let e2 := num_errors p2 in
  let s1 := is_special p1 in
  let s2 := is_special p2 in
  (i1 < i2) \/
  (i1 = i2 /\ ((e1 < e2) \/
               (e1 = e2 /\ s1 = false /\ s2 = true))).

Definition position_le (p1 p2 : Position) : Prop :=
  position_lt p1 p2 \/ p1 = p2.

(** * Ordering Properties *)

Lemma position_lt_irrefl : forall p, ~ position_lt p p.
Proof.
  intros [i e s]. unfold position_lt. simpl.
  intros [H | [_ [H | [_ [Hs1 Hs2]]]]].
  - lia.
  - lia.
  - subst s. discriminate.
Qed.

Lemma position_lt_asymm : forall p1 p2,
  position_lt p1 p2 -> ~ position_lt p2 p1.
Proof.
  intros [i1 e1 s1] [i2 e2 s2].
  unfold position_lt. simpl.
  intros H1 H2.
  destruct H1 as [Hi1 | [Heqi [He1 | [Heqe [Hs1 Hs2]]]]];
  destruct H2 as [Hi2 | [Heqi2 [He2 | [Heqe2 [Hs1' Hs2']]]]];
  try lia; subst; try discriminate.
Qed.

Lemma position_lt_trans : forall p1 p2 p3,
  position_lt p1 p2 -> position_lt p2 p3 -> position_lt p1 p3.
Proof.
  intros [i1 e1 s1] [i2 e2 s2] [i3 e3 s3].
  unfold position_lt. simpl.
  intros H1 H2.
  destruct H1 as [Hi12 | [Heqi12 [He12 | [Heqe12 [Hs1 Hs2]]]]].
  - (* i1 < i2 *)
    destruct H2 as [Hi23 | [Heqi23 _]].
    + left. lia.
    + left. lia.
  - (* i1 = i2, e1 < e2 *)
    subst i2.
    destruct H2 as [Hi23 | [Heqi23 [He23 | [Heqe23 _]]]].
    + left. lia.
    + right. split. lia. left. lia.
    + right. split. lia. left. lia.
  - (* i1 = i2, e1 = e2, s1=false, s2=true *)
    subst i2 e2.
    destruct H2 as [Hi23 | [Heqi23 [He23 | [Heqe23 [Hs2' Hs3]]]]].
    + left. lia.
    + right. split. lia. left. lia.
    + subst s2. discriminate.
Qed.

(** * Position Trichotomy *)

Lemma position_lt_trichotomy : forall p1 p2,
  position_lt p1 p2 \/ p1 = p2 \/ position_lt p2 p1.
Proof.
  intros [i1 e1 s1] [i2 e2 s2].
  unfold position_lt. simpl.
  destruct (Nat.lt_trichotomy i1 i2) as [Hi | [Hi | Hi]].
  - left. left. lia.
  - subst i2.
    destruct (Nat.lt_trichotomy e1 e2) as [He | [He | He]].
    + left. right. split. reflexivity. left. lia.
    + subst e2.
      destruct s1, s2.
      * right. left. reflexivity.
      * right. right. right. split. reflexivity. right. split. reflexivity. auto.
      * left. right. split. reflexivity. right. split. reflexivity. auto.
      * right. left. reflexivity.
    + right. right. right. split. reflexivity. left. lia.
  - right. right. left. lia.
Qed.

(** * Boolean ordering function (for computational use) *)

Definition position_ltb (p1 p2 : Position) : bool :=
  let i1 := term_index p1 in
  let i2 := term_index p2 in
  let e1 := num_errors p1 in
  let e2 := num_errors p2 in
  let s1 := is_special p1 in
  let s2 := is_special p2 in
  (i1 <? i2) ||
  ((i1 =? i2) && ((e1 <? e2) ||
                  ((e1 =? e2) && (negb s1 && s2)))).

Lemma position_ltb_lt : forall p1 p2,
  position_ltb p1 p2 = true <-> position_lt p1 p2.
Proof.
  intros [i1 e1 s1] [i2 e2 s2].
  unfold position_ltb, position_lt. simpl.
  rewrite orb_true_iff.
  rewrite Nat.ltb_lt.
  split.
  - intros [Hi | Hrest].
    + left. lia.
    + rewrite andb_true_iff in Hrest.
      destruct Hrest as [Heqi Hrest].
      apply Nat.eqb_eq in Heqi.
      right. split. lia.
      rewrite orb_true_iff in Hrest.
      destruct Hrest as [He | Hse].
      * left. apply Nat.ltb_lt in He. lia.
      * rewrite andb_true_iff in Hse.
        destruct Hse as [Heqe Hns].
        rewrite andb_true_iff in Hns.
        destruct Hns as [Hns1 Hs2].
        apply Nat.eqb_eq in Heqe.
        apply negb_true_iff in Hns1.
        right. split. lia.
        destruct s1; try discriminate.
        destruct s2; try discriminate.
        auto.
  - intros [Hi | [Heqi [He | [Heqe [Hs1 Hs2]]]]].
    + left. lia.
    + right. apply andb_true_iff. split.
      * apply Nat.eqb_eq. lia.
      * apply orb_true_iff. left. apply Nat.ltb_lt. lia.
    + right. apply andb_true_iff. split.
      * apply Nat.eqb_eq. lia.
      * apply orb_true_iff. right.
        apply andb_true_iff. split.
        -- apply Nat.eqb_eq. lia.
        -- apply andb_true_iff. split.
           ++ subst s1. reflexivity.
           ++ subst s2. reflexivity.
Qed.

(** * Utility Functions *)

(** Absolute difference for natural numbers *)
Definition abs_diff (m n : nat) : nat :=
  if m <=? n then n - m else m - n.

Lemma abs_diff_comm : forall m n, abs_diff m n = abs_diff n m.
Proof.
  intros m n. unfold abs_diff.
  destruct (m <=? n) eqn:Hmn, (n <=? m) eqn:Hnm.
  - apply Nat.leb_le in Hmn. apply Nat.leb_le in Hnm.
    assert (m = n) by lia. subst. reflexivity.
  - reflexivity.
  - reflexivity.
  - apply Nat.leb_gt in Hmn. apply Nat.leb_gt in Hnm. lia.
Qed.

Lemma abs_diff_self : forall n, abs_diff n n = 0.
Proof.
  intros n. unfold abs_diff. rewrite Nat.leb_refl. lia.
Qed.

Lemma abs_diff_le : forall m n d,
  abs_diff m n <= d <-> (n <= m + d /\ m <= n + d).
Proof.
  intros m n d. unfold abs_diff.
  destruct (m <=? n) eqn:Hmn.
  - apply Nat.leb_le in Hmn. lia.
  - apply Nat.leb_gt in Hmn. lia.
Qed.

(** * Examples *)

Example position_example_1 : std_pos 5 2 = mkPosition 5 2 false.
Proof. reflexivity. Qed.

Example position_example_2 : special_pos 3 1 = mkPosition 3 1 true.
Proof. reflexivity. Qed.

Example position_lt_example : position_lt (std_pos 3 1) (std_pos 3 2).
Proof.
  unfold position_lt, std_pos. simpl.
  right. split. reflexivity. left. lia.
Qed.

Example position_eq_example : position_eqb (std_pos 5 2) (std_pos 5 2) = true.
Proof. reflexivity. Qed.
