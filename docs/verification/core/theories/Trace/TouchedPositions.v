(** * Touched Positions in Traces

    This module defines functions to extract which positions in strings A and B
    are touched by a trace, along with key lemmas about these positions.

    Part of: Liblevenshtein.Core

    Decomposed from: Distance.v (lines 1160-1187)
*)

From Coq Require Import String List Arith Ascii Bool Nat Lia.
Import ListNotations.

From Liblevenshtein.Core Require Import Core.Definitions.
From Liblevenshtein.Core Require Import Trace.TraceBasics.

(** * Touched Position Extraction *)

(** Calculate which positions in A are touched by the trace *)
Fixpoint touched_in_A (A B : list Char) (T : Trace A B) : list nat :=
  match T with
  | [] => []
  | (i, _) :: rest => i :: touched_in_A A B rest
  end.

(** Calculate which positions in B are touched by the trace *)
Fixpoint touched_in_B (A B : list Char) (T : Trace A B) : list nat :=
  match T with
  | [] => []
  | (_, j) :: rest => j :: touched_in_B A B rest
  end.

(** * Key Lemmas *)

(** Length of touched_in_A equals trace length *)
Lemma touched_in_A_length :
  forall (A B : list Char) (T : Trace A B),
    length (touched_in_A A B T) = length T.
Proof.
  intros A B T.
  induction T as [| [i j] rest IH].
  - reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

(** Length of touched_in_B equals trace length *)
Lemma touched_in_B_length :
  forall (A B : list Char) (T : Trace A B),
    length (touched_in_B A B T) = length T.
Proof.
  intros A B T.
  induction T as [| [i j] rest IH].
  - reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

(** If i is in touched_in_A, then there exists j such that (i,j) is in T *)
Lemma In_touched_in_A_exists_pair :
  forall (A B : list Char) (T : Trace A B) i,
    In i (touched_in_A A B T) -> exists j, In (i, j) T.
Proof.
  intros A B T i.
  induction T as [| [i' j'] rest IH].
  - simpl. intro H. destruct H.
  - simpl. intro H. destruct H as [Heq | Hin].
    + subst i'. exists j'. left. reflexivity.
    + destruct (IH Hin) as [j Hj]. exists j. right. exact Hj.
Qed.

(** If j is in touched_in_B, then there exists i such that (i,j) is in T *)
Lemma In_touched_in_B_exists_pair :
  forall (A B : list Char) (T : Trace A B) j,
    In j (touched_in_B A B T) -> exists i, In (i, j) T.
Proof.
  intros A B T j.
  induction T as [| [i' j'] rest IH].
  - simpl. intro H. destruct H.
  - simpl. intro H. destruct H as [Heq | Hin].
    + subst j'. exists i'. left. reflexivity.
    + destruct (IH Hin) as [i Hi]. exists i. right. exact Hi.
Qed.

(** If (i,j) is in T, then i is in touched_in_A *)
Lemma In_pair_implies_touched_A :
  forall (A B : list Char) (T : Trace A B) i j,
    In (i, j) T -> In i (touched_in_A A B T).
Proof.
  intros A B T i j.
  induction T as [| [i' j'] rest IH].
  - simpl. intro H. destruct H.
  - simpl. intro H. destruct H as [Heq | Hin].
    + injection Heq as Hi Hj. subst. left. reflexivity.
    + right. apply IH. exact Hin.
Qed.

(** If (i,j) is in T, then j is in touched_in_B *)
Lemma In_pair_implies_touched_B :
  forall (A B : list Char) (T : Trace A B) i j,
    In (i, j) T -> In j (touched_in_B A B T).
Proof.
  intros A B T i j.
  induction T as [| [i' j'] rest IH].
  - simpl. intro H. destruct H.
  - simpl. intro H. destruct H as [Heq | Hin].
    + injection Heq as Hi Hj. subst. left. reflexivity.
    + right. apply IH. exact Hin.
Qed.

(** touched_in_A of empty trace is empty *)
Lemma touched_in_A_nil :
  forall (A B : list Char),
    touched_in_A A B [] = [].
Proof.
  reflexivity.
Qed.

(** touched_in_B of empty trace is empty *)
Lemma touched_in_B_nil :
  forall (A B : list Char),
    touched_in_B A B [] = [].
Proof.
  reflexivity.
Qed.
