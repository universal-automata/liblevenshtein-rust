(** * Monotonicity Preservation Lemmas

    This module provides lemmas for preserving trace monotonicity under shift operations.

    Part of: Liblevenshtein.Core

    Decomposed from: TraceLowerBound.v (lines 1580-1870)
*)

From Stdlib Require Import String List Arith Ascii Bool Nat Lia.
Import ListNotations.

From Liblevenshtein.Core Require Import LowerBound.Definitions.
From Liblevenshtein.Core Require Import LowerBound.HasPredicates.
From Liblevenshtein.Core Require Import LowerBound.ShiftTraceA.
From Liblevenshtein.Core Require Import LowerBound.ShiftTraceB.
From Liblevenshtein.Core Require Import LowerBound.ShiftTrace11.

(** * Shift Trace Inverse Lemmas *)

(** Helper: If (i, j) is in shift_trace_A T, there exists (a, j) in T with a <> 1 and i = a - 1 *)
Lemma in_shift_trace_A_inverse : forall T i j,
  In (i, j) (shift_trace_A T) -> exists a, In (a, j) T /\ a <> 1 /\ i = a - 1.
Proof.
  induction T as [| [a b] rest IH]; intros i j Hin.
  - simpl in Hin. destruct Hin.
  - simpl shift_trace_A in Hin.
    destruct (a =? 1) eqn:Ea.
    + apply IH in Hin. destruct Hin as [a' [Hin_rest [Hneq Heq]]].
      exists a'. split; [right; exact Hin_rest | split; assumption].
    + destruct Hin as [Heq | Hin'].
      * injection Heq as Hi Hj. subst.
        exists a. split; [left; reflexivity |].
        apply Nat.eqb_neq in Ea. split; [exact Ea | reflexivity].
      * apply IH in Hin'. destruct Hin' as [a' [Hin_rest [Hneq Heq]]].
        exists a'. split; [right; exact Hin_rest | split; assumption].
Qed.

(** Helper: If (i, j) is in shift_trace_B T, there exists (i, b) in T with b <> 1 and j = b - 1 *)
Lemma in_shift_trace_B_inverse : forall T i j,
  In (i, j) (shift_trace_B T) -> exists b, In (i, b) T /\ b <> 1 /\ j = b - 1.
Proof.
  induction T as [| [a b] rest IH]; intros i j Hin.
  - simpl in Hin. destruct Hin.
  - simpl shift_trace_B in Hin.
    destruct (b =? 1) eqn:Eb.
    + apply IH in Hin. destruct Hin as [b' [Hin_rest [Hneq Heq]]].
      exists b'. split; [right; exact Hin_rest | split; assumption].
    + destruct Hin as [Heq | Hin'].
      * injection Heq as Hi Hj. subst.
        exists b. split; [left; reflexivity |].
        apply Nat.eqb_neq in Eb. split; [exact Eb | reflexivity].
      * apply IH in Hin'. destruct Hin' as [b' [Hin_rest [Hneq Heq]]].
        exists b'. split; [right; exact Hin_rest | split; assumption].
Qed.

(** Helper: If (i, j) is in shift_trace_11 T, there exists (a, b) in T with (a,b) <> (1,1) *)
Lemma in_shift_trace_11_inverse : forall T i j,
  In (i, j) (shift_trace_11 T) ->
  exists a b, In (a, b) T /\ (a <> 1 \/ b <> 1) /\ i = a - 1 /\ j = b - 1.
Proof.
  induction T as [| [a b] rest IH]; intros i j Hin.
  - simpl in Hin. destruct Hin.
  - simpl shift_trace_11 in Hin.
    destruct ((a =? 1) && (b =? 1)) eqn:Eab.
    + apply IH in Hin. destruct Hin as [a' [b' [Hin_rest [Hcond [Hi Hj]]]]].
      exists a', b'. split; [right; exact Hin_rest | split; [exact Hcond | split; assumption]].
    + destruct Hin as [Heq | Hin'].
      * injection Heq as Hi Hj. subst.
        exists a, b. split; [left; reflexivity |].
        apply Bool.andb_false_iff in Eab.
        destruct Eab as [Ea | Eb].
        -- apply Nat.eqb_neq in Ea. split; [left; exact Ea | split; reflexivity].
        -- apply Nat.eqb_neq in Eb. split; [right; exact Eb | split; reflexivity].
      * apply IH in Hin'. destruct Hin' as [a' [b' [Hin_rest [Hcond [Hi Hj]]]]].
        exists a', b'. split; [right; exact Hin_rest | split; [exact Hcond | split; assumption]].
Qed.

(** * Helper for natural subtraction *)

Lemma nat_sub_lt_implies_lt : forall a1 a2, a1 - 1 < a2 - 1 -> a1 < a2.
Proof.
  intros a1 a2. destruct a1, a2; simpl; intros H; try lia.
Qed.

(** * Monotonicity Preservation Lemmas *)

(** Monotonicity preservation for shift_trace_A *)
Lemma shift_trace_A_monotonic : forall T,
  trace_monotonic T -> trace_monotonic (shift_trace_A T).
Proof.
  intros T Hmono.
  unfold trace_monotonic in *.
  intros i1 j1 i2 j2 Hin1 Hin2 Hlt.
  apply in_shift_trace_A_inverse in Hin1.
  apply in_shift_trace_A_inverse in Hin2.
  destruct Hin1 as [a1 [Hin1' [Hneq1 Heq1]]].
  destruct Hin2 as [a2 [Hin2' [Hneq2 Heq2]]].
  subst i1 i2.
  assert (Hlt': a1 < a2).
  { destruct a1; destruct a2; simpl in Hlt; try lia. }
  apply Hmono with (i1 := a1) (i2 := a2); assumption.
Qed.

(** Monotonicity preservation for shift_trace_B *)
Lemma shift_trace_B_monotonic : forall T,
  trace_monotonic T -> trace_monotonic (shift_trace_B T).
Proof.
  intros T Hmono.
  unfold trace_monotonic in *.
  intros i1 j1 i2 j2 Hin1 Hin2 Hlt.
  apply in_shift_trace_B_inverse in Hin1.
  apply in_shift_trace_B_inverse in Hin2.
  destruct Hin1 as [b1 [Hin1' [Hneq1 Heq1]]].
  destruct Hin2 as [b2 [Hin2' [Hneq2 Heq2]]].
  subst j1 j2.
  assert (Hj: b1 < b2).
  { apply Hmono with (i1 := i1) (i2 := i2); assumption. }
  destruct b1; destruct b2; simpl; try lia.
Qed.

(** Monotonicity preservation for shift_trace_11 (requires validity for indices >= 1) *)
Lemma shift_trace_11_monotonic : forall T,
  trace_monotonic T ->
  (forall i j, In (i, j) T -> i >= 1 /\ j >= 1) ->
  trace_monotonic (shift_trace_11 T).
Proof.
  intros T Hmono Hvalid.
  unfold trace_monotonic in *.
  intros i1 j1 i2 j2 Hin1 Hin2 Hlt.
  apply in_shift_trace_11_inverse in Hin1.
  apply in_shift_trace_11_inverse in Hin2.
  destruct Hin1 as [a1 [b1 [Hin1' [Hcond1 [Heq_i1 Heq_j1]]]]].
  destruct Hin2 as [a2 [b2 [Hin2' [Hcond2 [Heq_i2 Heq_j2]]]]].
  subst i1 j1 i2 j2.
  pose proof (Hvalid a1 b1 Hin1') as [Ha1_ge Hb1_ge].
  pose proof (Hvalid a2 b2 Hin2') as [Ha2_ge Hb2_ge].
  assert (Ha: a1 < a2). { apply nat_sub_lt_implies_lt. exact Hlt. }
  assert (Hb: b1 < b2). { apply Hmono with (i1 := a1) (i2 := a2); assumption. }
  lia.
Qed.

(** * Helper: Pair Membership Lemmas *)

(** Helper: if (i, j) is in T, then i is in touched_in_A T *)
Lemma in_pair_in_A : forall T i j,
  In (i, j) T -> In i (touched_in_A T).
Proof.
  induction T as [| [a b] rest IHT]; intros i j Hin.
  - destruct Hin.
  - destruct Hin as [Heq | Hin'].
    + injection Heq as <- <-. simpl. left. reflexivity.
    + simpl. right. apply IHT with j. exact Hin'.
Qed.

(** Helper: if (i, j) is in T, then j is in touched_in_B T *)
Lemma in_pair_in_B : forall T i j,
  In (i, j) T -> In j (touched_in_B T).
Proof.
  induction T as [| [a b] rest IHT]; intros i j Hin.
  - destruct Hin.
  - destruct Hin as [Heq | Hin'].
    + injection Heq as <- <-. simpl. left. reflexivity.
    + simpl. right. apply IHT with i. exact Hin'.
Qed.

(** Helper: when (1,1) is in trace, 1 is in touched_in_A *)
Lemma has_pair_11_in_A : forall T,
  has_pair_11 T = true -> In 1 (touched_in_A T).
Proof.
  induction T as [| [i j] rest IH]; intros H11.
  - simpl in H11. discriminate.
  - unfold has_pair_11 in H11. simpl existsb in H11.
    destruct ((i =? 1) && (j =? 1)) eqn:E.
    + apply andb_prop in E. destruct E as [Ei _].
      apply Nat.eqb_eq in Ei. subst i.
      simpl. left. reflexivity.
    + simpl. right.
      apply IH. unfold has_pair_11. exact H11.
Qed.

Lemma has_pair_11_in_B : forall T,
  has_pair_11 T = true -> In 1 (touched_in_B T).
Proof.
  induction T as [| [i j] rest IH]; intros H11.
  - simpl in H11. discriminate.
  - unfold has_pair_11 in H11. simpl existsb in H11.
    destruct ((i =? 1) && (j =? 1)) eqn:E.
    + apply andb_prop in E. destruct E as [_ Ej].
      apply Nat.eqb_eq in Ej. subst j.
      simpl. left. reflexivity.
    + simpl. right.
      apply IH. unfold has_pair_11. exact H11.
Qed.

