(** * Damerau-Levenshtein Trace Infrastructure

    This module extends the trace infrastructure to support Damerau-Levenshtein
    distance, which includes transposition of adjacent characters as a single
    operation (cost 1) rather than two substitutions (cost 2).

    Part of: Liblevenshtein.Core

    Key differences from standard Levenshtein traces:
    - Trace elements can be either matches/substitutions OR transpositions
    - Transposition involves two consecutive positions in both strings
    - Validity must ensure transposed positions don't overlap with other elements
*)

From Coq Require Import String List Arith Ascii Bool Nat Lia.
From Coq Require Import Wf_nat.
Import ListNotations.

From Liblevenshtein.Core Require Import Core.Definitions.
From Liblevenshtein.Core Require Import Core.DamerauLevDistanceDef.

(** * Damerau-Levenshtein Trace Type *)

(** A DL trace element: either a single position match or a transposition of two positions *)
Inductive DLTraceElement :=
  | DLMatch (i j : nat)      (* Position i in A corresponds to position j in B *)
  | DLTranspose (i j : nat). (* Positions (i, i+1) in A swap to match (j, j+1) in B *)

Definition DLTrace := list DLTraceElement.

(** * Position Extraction *)

(** Extract all positions touched in A by a trace element *)
Definition element_positions_A (e : DLTraceElement) : list nat :=
  match e with
  | DLMatch i _ => [i]
  | DLTranspose i _ => [i; i + 1]
  end.

(** Extract all positions touched in B by a trace element *)
Definition element_positions_B (e : DLTraceElement) : list nat :=
  match e with
  | DLMatch _ j => [j]
  | DLTranspose _ j => [j; j + 1]
  end.

(** All positions touched in A by a trace *)
Fixpoint dl_touched_in_A (T : DLTrace) : list nat :=
  match T with
  | [] => []
  | e :: rest => element_positions_A e ++ dl_touched_in_A rest
  end.

(** All positions touched in B by a trace *)
Fixpoint dl_touched_in_B (T : DLTrace) : list nat :=
  match T with
  | [] => []
  | e :: rest => element_positions_B e ++ dl_touched_in_B rest
  end.

(** * Element Validity *)

(** Check if a single element is valid for given string lengths *)
Definition dl_valid_element (lenA lenB : nat) (e : DLTraceElement) : bool :=
  match e with
  | DLMatch i j =>
      (1 <=? i) && (i <=? lenA) && (1 <=? j) && (j <=? lenB)
  | DLTranspose i j =>
      (* Both positions (i, i+1) must be in bounds for A *)
      (* Both positions (j, j+1) must be in bounds for B *)
      (1 <=? i) && (i + 1 <=? lenA) && (1 <=? j) && (j + 1 <=? lenB)
  end.

(** * Position Compatibility *)

(** Check if a position is compatible with a trace element
    (i.e., the position is not touched by the element) *)
Definition pos_not_in_element_A (pos : nat) (e : DLTraceElement) : bool :=
  match e with
  | DLMatch i _ => negb (pos =? i)
  | DLTranspose i _ => negb (pos =? i) && negb (pos =? i + 1)
  end.

Definition pos_not_in_element_B (pos : nat) (e : DLTraceElement) : bool :=
  match e with
  | DLMatch _ j => negb (pos =? j)
  | DLTranspose _ j => negb (pos =? j) && negb (pos =? j + 1)
  end.

(** Check if two elements are compatible (don't touch overlapping positions) *)
Definition dl_compatible_elements (e1 e2 : DLTraceElement) : bool :=
  (* All positions in e1 must not overlap with positions in e2 *)
  let pos_A1 := element_positions_A e1 in
  let pos_B1 := element_positions_B e1 in
  let pos_A2 := element_positions_A e2 in
  let pos_B2 := element_positions_B e2 in
  (* No position in A touched by both elements *)
  forallb (fun p => forallb (fun q => negb (p =? q)) pos_A2) pos_A1 &&
  (* No position in B touched by both elements *)
  forallb (fun p => forallb (fun q => negb (p =? q)) pos_B2) pos_B1.

(** * Monotonicity *)

(** Get the minimum position in A touched by an element *)
Definition min_pos_A (e : DLTraceElement) : nat :=
  match e with
  | DLMatch i _ => i
  | DLTranspose i _ => i
  end.

(** Get the maximum position in A touched by an element *)
Definition max_pos_A (e : DLTraceElement) : nat :=
  match e with
  | DLMatch i _ => i
  | DLTranspose i _ => i + 1
  end.

(** Get the minimum position in B touched by an element *)
Definition min_pos_B (e : DLTraceElement) : nat :=
  match e with
  | DLMatch _ j => j
  | DLTranspose _ j => j
  end.

(** Get the maximum position in B touched by an element *)
Definition max_pos_B (e : DLTraceElement) : nat :=
  match e with
  | DLMatch _ j => j
  | DLTranspose _ j => j + 1
  end.

(** Check if two elements maintain monotonic order *)
Definition dl_monotonic_pair (e1 e2 : DLTraceElement) : bool :=
  (* e1 comes before e2: max of e1 < min of e2 in both A and B *)
  (* Or they're the same element *)
  (* Or e2 comes before e1 *)
  if max_pos_A e1 <? min_pos_A e2 then
    max_pos_B e1 <? min_pos_B e2
  else if max_pos_A e2 <? min_pos_A e1 then
    max_pos_B e2 <? min_pos_B e1
  else
    (* Overlapping ranges - only valid if same element (handled by NoDup) *)
    false.

(** Check pairwise monotonicity *)
Fixpoint dl_is_monotonic_aux (T : DLTrace) : bool :=
  match T with
  | [] => true
  | e :: rest =>
      forallb (fun e' => dl_compatible_elements e e' && dl_monotonic_pair e e') rest &&
      dl_is_monotonic_aux rest
  end.

(** * NoDup for Trace Elements *)

(** Decidable equality for DLTraceElement *)
Definition dl_element_eq_dec (e1 e2 : DLTraceElement) : {e1 = e2} + {e1 <> e2}.
Proof.
  destruct e1 as [i1 j1 | i1 j1], e2 as [i2 j2 | i2 j2].
  - destruct (Nat.eq_dec i1 i2), (Nat.eq_dec j1 j2); subst;
    try (left; reflexivity); right; intro H; injection H; intros; contradiction.
  - right. intro H. discriminate.
  - right. intro H. discriminate.
  - destruct (Nat.eq_dec i1 i2), (Nat.eq_dec j1 j2); subst;
    try (left; reflexivity); right; intro H; injection H; intros; contradiction.
Defined.

(** NoDup check for trace elements *)
Fixpoint dl_NoDup_dec (T : DLTrace) : bool :=
  match T with
  | [] => true
  | e :: rest =>
      negb (existsb (fun e' => if dl_element_eq_dec e e' then true else false) rest) &&
      dl_NoDup_dec rest
  end.

(** * Full Validity Check *)

Definition dl_is_valid_trace (A B : list Char) (T : DLTrace) : bool :=
  (* All elements are within bounds *)
  forallb (dl_valid_element (length A) (length B)) T &&
  (* Pairwise compatibility and monotonicity *)
  dl_is_monotonic_aux T &&
  (* No duplicate elements *)
  dl_NoDup_dec T.

(** * Trace Cost *)

(** Cost of a single trace element *)
Definition dl_element_cost (A B : list Char) (e : DLTraceElement) : nat :=
  match e with
  | DLMatch i j =>
      (* Cost is 0 if characters match, 1 otherwise *)
      subst_cost (nth (i - 1) A default_char) (nth (j - 1) B default_char)
  | DLTranspose i j =>
      (* Transposition cost is 1 if characters are correctly swapped *)
      (* A[i-1] = B[j], A[i] = B[j-1] => swap pattern *)
      if andb (char_eq (nth (i - 1) A default_char) (nth j B default_char))
              (char_eq (nth i A default_char) (nth (j - 1) B default_char))
      then 1
      else 100  (* Invalid transposition - should not occur in valid traces *)
  end.

(** Total element cost for a trace *)
Definition dl_change_cost (A B : list Char) (T : DLTrace) : nat :=
  fold_left (fun acc e => acc + dl_element_cost A B e) T 0.

(** Full trace cost *)
Definition dl_trace_cost (A B : list Char) (T : DLTrace) : nat :=
  let change_cost := dl_change_cost A B T in
  (* Deletions: positions in A not touched by any element *)
  let touched_A := dl_touched_in_A T in
  let delete_cost := length A - length touched_A in
  (* Insertions: positions in B not touched by any element *)
  let touched_B := dl_touched_in_B T in
  let insert_cost := length B - length touched_B in
  change_cost + delete_cost + insert_cost.

(** * Basic Lemmas *)

(** Auxiliary Lemma for subst_cost - must be defined before use *)
Lemma subst_cost_le_1 : forall c1 c2, subst_cost c1 c2 <= 1.
Proof.
  intros c1 c2. unfold subst_cost.
  destruct (char_eq c1 c2); lia.
Qed.

(** Empty trace cost *)
Lemma dl_trace_cost_empty :
  forall A B : list Char,
    dl_trace_cost A B [] = length A + length B.
Proof.
  intros A B.
  unfold dl_trace_cost. simpl. lia.
Qed.

(** Element cost is bounded *)
Lemma dl_element_cost_bound :
  forall A B e,
    dl_element_cost A B e <= 100.
Proof.
  intros A B e.
  destruct e as [i j | i j]; unfold dl_element_cost.
  - (* DLMatch *)
    pose proof (subst_cost_le_1 (nth (i - 1) A default_char) (nth (j - 1) B default_char)).
    unfold subst_cost in *. destruct char_eq; lia.
  - (* DLTranspose *)
    destruct (andb _ _); lia.
Qed.

(** Valid element cost for transposition is exactly 1 *)
Lemma dl_transpose_cost_valid :
  forall A B i j,
    char_eq (nth (i - 1) A default_char) (nth j B default_char) = true ->
    char_eq (nth i A default_char) (nth (j - 1) B default_char) = true ->
    dl_element_cost A B (DLTranspose i j) = 1.
Proof.
  intros A B i j H1 H2.
  unfold dl_element_cost.
  rewrite H1, H2. simpl. reflexivity.
Qed.

(** * Trace Construction from Distance *)

(** We need to show that optimal traces exist and their cost equals damerau_lev_distance.
    This is done by constructing traces via backtracking through the DP recursion. *)

(** Specification: distance is at most any valid trace cost *)
Lemma dl_distance_le_valid_trace_cost :
  forall A B T,
    dl_is_valid_trace A B T = true ->
    damerau_lev_distance A B <= dl_trace_cost A B T.
Proof.
  (* This requires showing that any valid trace corresponds to a valid edit sequence *)
  (* The proof follows by induction on the trace structure *)
  intros A B T Hvalid.
  (* We'll prove this after establishing trace-to-edit-sequence correspondence *)
Admitted. (* TODO: Complete after establishing edit sequence correspondence *)

(** Specification: there exists a trace achieving the distance *)
Lemma dl_optimal_trace_exists :
  forall A B,
    exists T,
      dl_is_valid_trace A B T = true /\
      dl_trace_cost A B T = damerau_lev_distance A B.
Proof.
  (* Construct optimal trace by backtracking through damerau_lev_pair recursion *)
  intros A B.
  (* We'll construct this trace explicitly by following the min4 branches *)
Admitted. (* TODO: Complete with explicit trace construction *)

(** End of DamerauTrace module *)
