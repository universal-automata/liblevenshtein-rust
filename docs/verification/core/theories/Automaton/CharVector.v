(** * Characteristic Vector for Levenshtein Automata

    This module defines the characteristic vector β(c, query) which indicates
    at which positions in the query a character c matches.

    Part of: Liblevenshtein.Core.Automaton

    Rust Reference: src/transducer/transition.rs:38-68

    Key Definitions:
    - characteristic_vector: β(c, query, window, offset)
    - char_matches_at: Direct matching predicate

    Key Theorems:
    - char_vector_correct: Vector reflects actual character matches
    - char_vector_length: Vector has expected length
*)

From Stdlib Require Import Arith Bool List Nat Lia Ascii.
Import ListNotations.

From Liblevenshtein.Core Require Import Core.Definitions.

(** * Character Type *)

(** We use the Char type from Core.Definitions *)

(** Helper lemmas for char_eq *)
Lemma char_eq_refl : forall c, char_eq c c = true.
Proof.
  intros c. unfold char_eq.
  destruct (ascii_dec c c) as [_ | Hneq].
  - reflexivity.
  - exfalso. apply Hneq. reflexivity.
Qed.

Lemma char_eq_eq : forall c1 c2, char_eq c1 c2 = true <-> c1 = c2.
Proof.
  intros c1 c2. unfold char_eq.
  destruct (ascii_dec c1 c2) as [Heq | Hneq].
  - split; intros _; [exact Heq | reflexivity].
  - split; [discriminate | intros Heq; contradiction].
Qed.

(** * Characteristic Vector *)

(** Check if character c matches query at position i *)
Definition char_matches_at (c : Char) (query : list Char) (i : nat) : bool :=
  match nth_error query i with
  | Some c' => char_eq c c'
  | None => false
  end.

(** Build characteristic vector for a window of the query.
    Returns a list of booleans indicating where c matches in query[offset..offset+window-1] *)
Fixpoint characteristic_vector_aux (c : Char) (query : list Char) (offset remaining : nat) : list bool :=
  match remaining with
  | 0 => []
  | S n => char_matches_at c query offset :: characteristic_vector_aux c query (S offset) n
  end.

(** Main characteristic vector function.
    For position i with max_distance n, we need to look at query positions i..i+2n
    (the window of possible transitions). *)
Definition characteristic_vector (c : Char) (query : list Char) (offset window : nat) : list bool :=
  characteristic_vector_aux c query offset window.

(** * Basic Properties *)

Lemma char_vector_length : forall c query offset window,
  length (characteristic_vector c query offset window) = window.
Proof.
  intros c query offset window.
  unfold characteristic_vector.
  revert offset.
  induction window as [| n IH]; intros offset.
  - simpl. reflexivity.
  - simpl. f_equal. apply IH.
Qed.

Lemma char_vector_nth : forall c query offset window i,
  i < window ->
  nth_error (characteristic_vector c query offset window) i =
  Some (char_matches_at c query (offset + i)).
Proof.
  intros c query offset window.
  unfold characteristic_vector.
  revert offset.
  induction window as [| n IH]; intros offset i Hi.
  - lia.
  - simpl. destruct i as [| i'].
    + simpl. f_equal. f_equal. lia.
    + simpl. rewrite IH by lia.
      f_equal. f_equal. lia.
Qed.

(** * Correctness *)

Lemma char_vector_correct : forall c query offset window i,
  i < window ->
  nth i (characteristic_vector c query offset window) false =
  char_matches_at c query (offset + i).
Proof.
  intros c query offset window i Hi.
  pose proof (char_vector_nth c query offset window i Hi) as H.
  (* H : nth_error cv i = Some (char_matches_at ...) *)
  (* Goal: nth i cv false = char_matches_at ... *)
  eapply nth_error_nth. exact H.
Qed.

(** * Matching Predicate *)

(** Propositional version of character matching *)
Definition CharMatchesAt (c : Char) (query : list Char) (i : nat) : Prop :=
  exists c', nth_error query i = Some c' /\ c = c'.

Lemma char_matches_at_iff : forall c query i,
  char_matches_at c query i = true <-> CharMatchesAt c query i.
Proof.
  intros c query i.
  unfold char_matches_at, CharMatchesAt.
  split.
  - intros H.
    destruct (nth_error query i) as [c' |] eqn:Hnth.
    + exists c'. split; auto.
      apply char_eq_eq. exact H.
    + discriminate H.
  - intros [c' [Hnth Heq]].
    rewrite Hnth. subst. apply char_eq_refl.
Qed.

Lemma char_matches_at_false_iff : forall c query i,
  char_matches_at c query i = false <-> ~ CharMatchesAt c query i.
Proof.
  intros c query i.
  split.
  - intros H [c' [Hnth Heq]].
    unfold char_matches_at in H.
    rewrite Hnth in H. subst.
    rewrite char_eq_refl in H. discriminate.
  - intros H.
    destruct (char_matches_at c query i) eqn:Hmatch.
    + exfalso. apply H. apply char_matches_at_iff. exact Hmatch.
    + reflexivity.
Qed.

(** * Window Operations *)

(** Get the window of query characters relevant to a position *)
Definition get_window (query : list Char) (offset window : nat) : list Char :=
  firstn window (skipn offset query).

Lemma get_window_length : forall query offset window,
  length (get_window query offset window) = min window (length query - offset).
Proof.
  intros query offset window.
  unfold get_window.
  rewrite firstn_length, skipn_length.
  reflexivity.
Qed.

Lemma get_window_nth : forall query offset window i,
  i < window ->
  i < length query - offset ->
  nth_error (get_window query offset window) i = nth_error query (offset + i).
Proof.
  intros query offset window i Hi1 Hi2.
  unfold get_window.
  rewrite nth_error_firstn.
  destruct (i <? window) eqn:Hlt.
  - rewrite nth_error_skipn. reflexivity.
  - apply Nat.ltb_ge in Hlt. lia.
Qed.

(** * Transition Relevant Properties *)

(** For a position at index i with max_distance n, the relevant query
    positions for transitions are i to i + 2n (inclusive).
    This accounts for:
    - Match at i (advance both)
    - Insert (advance dict only, check positions i+1, i+2, ...)
    - Delete (advance query only, look ahead to i+1, i+2, ...)
    - Substitute at i (advance both)
*)

(** Standard window size for position i with max n errors *)
Definition standard_window (i n : nat) : nat := 2 * n + 1.

(** Transposition window needs to see one more position *)
Definition transposition_window (i n : nat) : nat := 2 * n + 2.

(** * Examples *)

Example char_vector_example_1 :
  (* For query "abc" and character 'b' starting at offset 0 with window 3 *)
  (* We expect [false; true; false] *)
  let query := [Ascii.ascii_of_nat 97; Ascii.ascii_of_nat 98; Ascii.ascii_of_nat 99] in (* "abc" *)
  let c := Ascii.ascii_of_nat 98 in (* 'b' *)
  characteristic_vector c query 0 3 = [false; true; false].
Proof. reflexivity. Qed.

Example char_vector_example_2 :
  (* For query "aaa" and character 'a' starting at offset 0 with window 3 *)
  (* We expect [true; true; true] *)
  let query := [Ascii.ascii_of_nat 97; Ascii.ascii_of_nat 97; Ascii.ascii_of_nat 97] in (* "aaa" *)
  let c := Ascii.ascii_of_nat 97 in (* 'a' *)
  characteristic_vector c query 0 3 = [true; true; true].
Proof. reflexivity. Qed.

Example char_vector_example_3 :
  (* For query "ab" and character 'c' (no matches) *)
  let query := [Ascii.ascii_of_nat 97; Ascii.ascii_of_nat 98] in (* "ab" *)
  let c := Ascii.ascii_of_nat 99 in (* 'c' *)
  characteristic_vector c query 0 2 = [false; false].
Proof. reflexivity. Qed.

(** * Boundary Handling *)

(** When offset + window exceeds query length, remaining positions don't match *)
Lemma char_matches_beyond_query : forall c query i,
  i >= length query ->
  char_matches_at c query i = false.
Proof.
  intros c query i Hi.
  unfold char_matches_at.
  destruct (nth_error query i) eqn:Hnth.
  - (* nth_error returned Some - contradiction with i >= length *)
    assert (Hne : nth_error query i <> None) by (rewrite Hnth; discriminate).
    apply nth_error_Some in Hne. lia.
  - reflexivity.
Qed.
