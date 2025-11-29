(** * Lower Bound Proof: trace_cost >= lev_distance *)

From Stdlib Require Import String List Arith Ascii Bool Nat Lia Wf_nat FunctionalExtensionality.
From Stdlib Require Import Program.Wf.
From Stdlib Require Import Recdef.
Import ListNotations.

(* NoDup is in List, already imported *)

Definition Char := ascii.
Definition default_char : Char := Ascii.zero.
Definition min3 (a b c : nat) : nat := min a (min b c).
Definition char_eq (c1 c2 : Char) : bool := if ascii_dec c1 c2 then true else false.
Definition subst_cost (c1 c2 : Char) : nat := if char_eq c1 c2 then 0 else 1.

Definition lev_measure (p : list Char * list Char) : nat := length (fst p) + length (snd p).

Function lev_distance_pair (p : list Char * list Char) {measure lev_measure p} : nat :=
  match p with
  | ([], s2) => length s2
  | (s1, []) => length s1
  | (c1 :: s1', c2 :: s2') =>
      min3 (lev_distance_pair (s1', c2 :: s2') + 1)
           (lev_distance_pair (c1 :: s1', s2') + 1)
           (lev_distance_pair (s1', s2') + subst_cost c1 c2)
  end.
Proof. all: intros; unfold lev_measure; simpl; lia. Defined.

Definition lev_distance (s1 s2 : list Char) : nat := lev_distance_pair (s1, s2).

Lemma lev_distance_nil_nil : lev_distance [] [] = 0.
Proof. unfold lev_distance. rewrite lev_distance_pair_equation. reflexivity. Qed.

Lemma lev_distance_nil_l : forall s, lev_distance [] s = length s.
Proof. intro s. unfold lev_distance. rewrite lev_distance_pair_equation. reflexivity. Qed.

Lemma lev_distance_nil_r : forall s, lev_distance s [] = length s.
Proof. intro s. unfold lev_distance. rewrite lev_distance_pair_equation. destruct s; reflexivity. Qed.

Lemma lev_distance_cons_cons : forall c1 c2 s1 s2,
  lev_distance (c1 :: s1) (c2 :: s2) =
  min3 (lev_distance s1 (c2 :: s2) + 1) (lev_distance (c1 :: s1) s2 + 1) (lev_distance s1 s2 + subst_cost c1 c2).
Proof. intros. unfold lev_distance. rewrite lev_distance_pair_equation. reflexivity. Qed.

Definition Trace := list (nat * nat).

Fixpoint touched_in_A (T : Trace) : list nat :=
  match T with [] => [] | (i, _) :: rest => i :: touched_in_A rest end.

Fixpoint touched_in_B (T : Trace) : list nat :=
  match T with [] => [] | (_, j) :: rest => j :: touched_in_B rest end.

Definition trace_cost (lenA lenB : nat) (A B : list Char) (T : Trace) : nat :=
  let change_cost := fold_left (fun acc p =>
    let '(i, j) := p in acc + subst_cost (nth (i-1) A default_char) (nth (j-1) B default_char)) T 0 in
  change_cost + (lenA - length (touched_in_A T)) + (lenB - length (touched_in_B T)).

Lemma touched_in_A_length : forall T, length (touched_in_A T) = length T.
Proof. induction T as [| [i j] rest IH]; simpl; [reflexivity | rewrite IH; reflexivity]. Qed.

Lemma touched_in_B_length : forall T, length (touched_in_B T) = length T.
Proof. induction T as [| [i j] rest IH]; simpl; [reflexivity | rewrite IH; reflexivity]. Qed.

(** Simple validity: all indices within bounds *)
Definition simple_valid_trace (lenA lenB : nat) (T : Trace) : bool :=
  forallb (fun '(i, j) => (1 <=? i) && (i <=? lenA) && (1 <=? j) && (j <=? lenB)) T.

(** Monotonicity: A trace is monotonic if matching preserves order.
    For all pairs (i1, j1), (i2, j2) in T: i1 < i2 implies j1 < j2.
    This is REQUIRED for trace_cost_lower_bound to hold, because
    non-monotonic (crossing) traces can achieve lower cost than Levenshtein distance.

    Example: A = "ab", B = "ba" with T = [(1,2), (2,1)]
    - Cross-matching has trace_cost = 0 (both pairs have cost 0)
    - But lev_distance("ab", "ba") = 2

    Monotonicity eliminates cross-matching, making the theorem provable. *)
Definition trace_monotonic (T : Trace) : Prop :=
  forall i1 j1 i2 j2,
    In (i1, j1) T -> In (i2, j2) T -> i1 < i2 -> j1 < j2.

(** Key observation: trace_cost = change_cost + lenA + lenB - 2*|T| *)

Lemma trace_cost_formula : forall lenA lenB A B T,
  length T <= lenA ->
  length T <= lenB ->
  trace_cost lenA lenB A B T =
  fold_left (fun acc '(i, j) =>
    acc + subst_cost (nth (i-1) A default_char) (nth (j-1) B default_char)) T 0 +
  (lenA - length T) + (lenB - length T).
Proof.
  intros.
  unfold trace_cost.
  rewrite touched_in_A_length, touched_in_B_length.
  reflexivity.
Qed.

(** For an empty trace: trace_cost = lenA + lenB *)
Lemma trace_cost_nil : forall lenA lenB A B,
  trace_cost lenA lenB A B [] = lenA + lenB.
Proof.
  intros. unfold trace_cost. simpl. lia.
Qed.

(** Upper bound: lev_distance <= |A| + |B| - Direct proof *)
Lemma lev_distance_upper_bound : forall A B,
  lev_distance A B <= length A + length B.
Proof.
  intros A.
  induction A as [| c1 s1' IHA].
  - (* A = [] *)
    intro B. rewrite lev_distance_nil_l. simpl. lia.
  - (* A = c1 :: s1' *)
    intro B. induction B as [| c2 s2' IHB].
    + (* B = [] *)
      rewrite lev_distance_nil_r. simpl. lia.
    + (* B = c2 :: s2' *)
      rewrite lev_distance_cons_cons.
      unfold min3.
      (* We'll show min (min (del+1) (ins+1)) (sub + subst_cost) <= S|s1'| + S|s2'| *)
      (* Using that sub + subst_cost <= S|s1'| + S|s2'| *)
      assert (H3: lev_distance s1' s2' <= length s1' + length s2') by (apply IHA).
      assert (Hsub: subst_cost c1 c2 <= 1).
      { unfold subst_cost, char_eq. destruct ascii_dec; lia. }
      eapply Nat.le_trans. apply Nat.le_min_r.
      simpl length.
      (* Goal: lev_distance s1' s2' + subst_cost c1 c2 <= S (length s1') + S (length s2') *)
      assert (S (length s1') + S (length s2') = S (S (length s1' + length s2'))).
      { lia. }
      rewrite H. clear H.
      assert (lev_distance s1' s2' + subst_cost c1 c2 <= length s1' + length s2' + 1).
      { lia. }
      lia.
Qed.

(** Lower bound theorem (the key result) *)
(**
   Strategy: By strong induction on |A| + |B|.

   Key insight: For any valid trace T on (A, B):
   - trace_cost accounts for matched pairs (substitutions) and unmatched positions (deletions/insertions)
   - This is at least as large as the optimal edit distance

   Case analysis:
   - If A = [] or B = []: T must be empty (indices must be in bounds), so trace_cost = lenA + lenB = lev_distance
   - If A = c1::s1', B = c2::s2':
     * If 1 ∉ touched_in_A T: position 1 in A is not matched, counts as deletion (+1)
       - Rest of trace operates on indices >= 2 in A
       - Can shift and apply IH on s1', B
     * If 1 ∉ touched_in_B T: position 1 in B is not matched, counts as insertion (+1)
       - Rest of trace operates on indices >= 2 in B
       - Can shift and apply IH on A, s2'
     * If (1, 1) ∈ T: positions 1 in both matched
       - Subst cost = subst_cost c1 c2
       - Rest of trace operates on indices >= 2 in both
       - Can shift and apply IH on s1', s2'
     * If 1 ∈ touched_in_A but (1,1) ∉ T: (1, j) ∈ T for some j > 1
       - This is more complex, but we can still extract a bound
*)

(** Check if (1, 1) is in the trace *)
Definition has_pair_11 (T : Trace) : bool :=
  existsb (fun '(i, j) => (i =? 1) && (j =? 1)) T.

(** Check if 1 is in touched_in_A *)
Definition has_A1 (T : Trace) : bool :=
  existsb (fun i => i =? 1) (touched_in_A T).

(** Check if 1 is in touched_in_B *)
Definition has_B1 (T : Trace) : bool :=
  existsb (fun j => j =? 1) (touched_in_B T).

(** Key lemma: Monotonicity eliminates cross-matching.
    Cross-matching requires:
    - (1, j) with j >= 2 in T
    - (i, 1) with i >= 2 in T
    This creates a "crossing" where 1 < i but j > 1.
    By monotonicity: 1 < i implies j < 1. But j >= 2, contradiction! *)
Lemma monotonicity_eliminates_cross_matching :
  forall T i j,
    trace_monotonic T ->
    In (1, j) T -> j >= 2 ->
    In (i, 1) T -> i >= 2 ->
    False.
Proof.
  intros T i j Hmono H1j Hj_ge2 Hi1 Hi_ge2.
  unfold trace_monotonic in Hmono.
  assert (H: j < 1).
  { specialize (Hmono 1 j i 1 H1j Hi1).
    assert (H_lt: 1 < i) by lia.
    specialize (Hmono H_lt).
    exact Hmono. }
  lia.
Qed.

(** Helper: Extract (1, j) from touched_in_A containing 1 *)
Lemma touched_in_A_1_implies_pair : forall T,
  In 1 (touched_in_A T) -> exists j, In (1, j) T.
Proof.
  induction T as [| [a b] rest IH]; intros Hin.
  - simpl in Hin. destruct Hin.
  - simpl touched_in_A in Hin. simpl in Hin.
    destruct Hin as [Heq | Hin_rest].
    + subst. exists b. left. reflexivity.
    + destruct (IH Hin_rest) as [j' Hj'].
      exists j'. right. exact Hj'.
Qed.

(** Helper: Extract (i, 1) from touched_in_B containing 1 *)
Lemma touched_in_B_1_implies_pair : forall T,
  In 1 (touched_in_B T) -> exists i, In (i, 1) T.
Proof.
  induction T as [| [a b] rest IH]; intros Hin.
  - simpl in Hin. destruct Hin.
  - simpl touched_in_B in Hin. simpl in Hin.
    destruct Hin as [Heq | Hin_rest].
    + subst. exists a. left. reflexivity.
    + destruct (IH Hin_rest) as [i' Hi'].
      exists i'. right. exact Hi'.
Qed.

(** Helper: Pairs in valid trace have indices >= 1 *)
Lemma valid_trace_indices_ge1 : forall lenA lenB T i j,
  simple_valid_trace lenA lenB T = true ->
  In (i, j) T ->
  i >= 1 /\ j >= 1.
Proof.
  intros lenA lenB T i j Hvalid Hin.
  unfold simple_valid_trace in Hvalid.
  rewrite forallb_forall in Hvalid.
  specialize (Hvalid (i, j) Hin).
  apply andb_prop in Hvalid. destruct Hvalid as [Hvalid1 Hj_upper].
  apply andb_prop in Hvalid1. destruct Hvalid1 as [Hvalid2 Hj_lower].
  apply andb_prop in Hvalid2. destruct Hvalid2 as [Hi_lower Hi_upper].
  apply Nat.leb_le in Hi_lower. apply Nat.leb_le in Hj_lower.
  split; lia.
Qed.

(** Corollary: With monotonicity and validity, has_A1 = true AND has_B1 = true
    AND has_pair_11 = false is impossible. The cross-matching case branch is unreachable. *)
Lemma monotonic_cross_matching_impossible :
  forall lenA lenB T,
    simple_valid_trace lenA lenB T = true ->
    trace_monotonic T ->
    has_A1 T = true ->
    has_B1 T = true ->
    has_pair_11 T = false ->
    False.
Proof.
  intros lenA lenB T Hvalid Hmono HA1 HB1 H11.
  unfold has_A1 in HA1. unfold has_B1 in HB1. unfold has_pair_11 in H11.
  apply existsb_exists in HA1. destruct HA1 as [i1 [Hin_A1 Hi1_eq]].
  apply existsb_exists in HB1. destruct HB1 as [j1 [Hin_B1 Hj1_eq]].
  apply Nat.eqb_eq in Hi1_eq. apply Nat.eqb_eq in Hj1_eq.
  subst i1 j1.
  (* Now we have In 1 (touched_in_A T) and In 1 (touched_in_B T) *)
  (* Extract the pairs *)
  destruct (touched_in_A_1_implies_pair T Hin_A1) as [j H1j].
  destruct (touched_in_B_1_implies_pair T Hin_B1) as [i Hi1].
  (* Get bounds on i and j from validity *)
  pose proof (valid_trace_indices_ge1 lenA lenB T 1 j Hvalid H1j) as [_ Hj_ge1].
  pose proof (valid_trace_indices_ge1 lenA lenB T i 1 Hvalid Hi1) as [Hi_ge1 _].
  (* Now we have In (1, j) T and In (i, 1) T *)
  (* By has_pair_11 = false, either i <> 1 or j <> 1 *)
  destruct (Nat.eq_dec i 1) as [Ei | Ei].
  - (* i = 1: then (i, 1) = (1, 1) should violate has_pair_11 = false *)
    subst i.
    assert (Hhas11: existsb (fun '(i, j) => (i =? 1) && (j =? 1)) T = true).
    { apply existsb_exists. exists (1, 1). split; [exact Hi1 | reflexivity]. }
    rewrite Hhas11 in H11. discriminate.
  - (* i <> 1 *)
    destruct (Nat.eq_dec j 1) as [Ej | Ej].
    + (* j = 1: (1, j) = (1, 1) should violate has_pair_11 = false *)
      subst j.
      assert (Hhas11: existsb (fun '(i, j) => (i =? 1) && (j =? 1)) T = true).
      { apply existsb_exists. exists (1, 1). split; [exact H1j | reflexivity]. }
      rewrite Hhas11 in H11. discriminate.
    + (* i <> 1 and j <> 1: true cross-matching *)
      (* Use monotonicity_eliminates_cross_matching *)
      assert (Hi_ge2: i >= 2) by lia.
      assert (Hj_ge2: j >= 2) by lia.
      apply (monotonicity_eliminates_cross_matching T i j Hmono H1j Hj_ge2 Hi1 Hi_ge2).
Qed.

(** Filter out (1, 1) from trace and shift indices *)
Fixpoint shift_trace_11 (T : Trace) : Trace :=
  match T with
  | [] => []
  | (i, j) :: rest =>
      if (i =? 1) && (j =? 1)
      then shift_trace_11 rest  (* skip (1,1) *)
      else (i - 1, j - 1) :: shift_trace_11 rest  (* shift down *)
  end.

(** Count occurrences of (1,1) *)
Fixpoint count_11 (T : Trace) : nat :=
  match T with
  | [] => 0
  | (i, j) :: rest =>
      if (i =? 1) && (j =? 1) then 1 + count_11 rest else count_11 rest
  end.

(** count_11 is bounded by length *)
Lemma count_11_le_length : forall T, count_11 T <= length T.
Proof.
  induction T as [| [i j] rest IH].
  - simpl. lia.
  - simpl. destruct ((i =? 1) && (j =? 1)); lia.
Qed.

(** Fundamental length property *)
Lemma shift_trace_11_length_general : forall T,
  length (shift_trace_11 T) = length T - count_11 T.
Proof.
  induction T as [| [i j] rest IH].
  - simpl. reflexivity.
  - simpl shift_trace_11. simpl count_11.
    destruct ((i =? 1) && (j =? 1)) eqn:E.
    + (* (i,j) = (1,1), skipped *)
      simpl length.
      pose proof (count_11_le_length rest) as Hbound.
      lia.
    + (* (i,j) ≠ (1,1), included *)
      simpl length.
      rewrite IH.
      pose proof (count_11_le_length rest) as Hbound.
      lia.
Qed.

(** (1,1) can appear at most once if both projections are NoDup *)
Lemma count_11_le_1_aux : forall T,
  NoDup (touched_in_A T) -> NoDup (touched_in_B T) -> count_11 T <= 1.
Proof.
  induction T as [| [i j] rest IH]; intros HnodupA HnodupB.
  - simpl. lia.
  - simpl touched_in_A in HnodupA. simpl touched_in_B in HnodupB.
    inversion HnodupA as [| x xs Hnot_in_A Hnodup_restA Heq1]. subst.
    inversion HnodupB as [| y ys Hnot_in_B Hnodup_restB Heq2]. subst.
    simpl count_11.
    destruct ((i =? 1) && (j =? 1)) eqn:E.
    + (* (i,j) = (1,1) *)
      apply andb_prop in E. destruct E as [Ei Ej].
      apply Nat.eqb_eq in Ei. apply Nat.eqb_eq in Ej. subst i j.
      (* Now 1 is not in touched_in_A rest and 1 is not in touched_in_B rest *)
      (* So (1,1) cannot be in rest *)
      assert (Hcount_rest: count_11 rest = 0).
      { (* Generalized statement: any list where 1 not in A projection has count_11 = 0 *)
        assert (Hgen: forall L, ~ In 1 (touched_in_A L) -> count_11 L = 0).
        { clear IH Hnodup_restA Hnodup_restB Hnot_in_A Hnot_in_B rest HnodupA HnodupB.
          induction L as [| [i' j'] L' IHL'].
          - reflexivity.
          - intros Hnot_in.
            simpl count_11.
            destruct ((i' =? 1) && (j' =? 1)) eqn:E'.
            + (* (i', j') = (1,1), contradiction *)
              apply andb_prop in E'. destruct E' as [Ei' _].
              apply Nat.eqb_eq in Ei'. subst.
              exfalso. apply Hnot_in. simpl. left. reflexivity.
            + apply IHL'. intro H. apply Hnot_in. simpl. right. exact H. }
        apply Hgen. exact Hnot_in_A. }
      lia.
    + (* (i,j) ≠ (1,1), apply IH *)
      assert (Hle: count_11 rest <= 1) by (apply IH; assumption).
      lia.
Qed.

(** has_pair_11 implies count_11 >= 1 *)
Lemma has_pair_11_count : forall T,
  has_pair_11 T = true -> count_11 T >= 1.
Proof.
  induction T as [| [i j] rest IH].
  - simpl. intros H. discriminate.
  - intro H.
    simpl count_11.
    destruct ((i =? 1) && (j =? 1)) eqn:E.
    + lia.
    + assert (Hrest: count_11 rest >= 1).
      { apply IH.
        unfold has_pair_11 in H. simpl existsb in H.
        unfold has_pair_11.
        destruct (i =? 1) eqn:Ei, (j =? 1) eqn:Ej; simpl in E; try discriminate.
        - simpl in H. exact H.
        - simpl in H. exact H.
        - simpl in H. exact H. }
      lia.
Qed.

(** Filter to keep only pairs with i = 1 *)
Fixpoint filter_A1 (T : Trace) : Trace :=
  match T with
  | [] => []
  | (i, j) :: rest => if i =? 1 then (i, j) :: filter_A1 rest else filter_A1 rest
  end.

(** Filter to keep pairs with i > 1 and shift *)
Fixpoint shift_trace_A (T : Trace) : Trace :=
  match T with
  | [] => []
  | (i, j) :: rest =>
      if i =? 1 then shift_trace_A rest
      else (i - 1, j) :: shift_trace_A rest
  end.

(** Filter to keep pairs with j > 1 and shift *)
Fixpoint shift_trace_B (T : Trace) : Trace :=
  match T with
  | [] => []
  | (i, j) :: rest =>
      if j =? 1 then shift_trace_B rest
      else (i, j - 1) :: shift_trace_B rest
  end.

(** Helper lemmas for shift operations *)

(** has_A1 decomposes over cons *)
Lemma has_A1_cons : forall i j rest,
  has_A1 ((i, j) :: rest) = (i =? 1) || has_A1 rest.
Proof.
  intros. unfold has_A1. simpl. reflexivity.
Qed.

(** has_B1 decomposes over cons *)
Lemma has_B1_cons : forall i j rest,
  has_B1 ((i, j) :: rest) = (j =? 1) || has_B1 rest.
Proof.
  intros. unfold has_B1. simpl. reflexivity.
Qed.

(** When has_A1 T = false, shift_trace_A preserves length *)
Lemma shift_trace_A_length_no_A1 : forall T,
  has_A1 T = false -> length (shift_trace_A T) = length T.
Proof.
  induction T as [| [i j] rest IH]; intros H.
  - reflexivity.
  - rewrite has_A1_cons in H.
    apply orb_false_elim in H. destruct H as [Hi Hrest].
    simpl. rewrite Hi. simpl.
    f_equal. apply IH. exact Hrest.
Qed.

(** When has_A1 T = true and NoDup, length decreases by 1 *)
Lemma shift_trace_A_length_with_A1 : forall T,
  has_A1 T = true ->
  NoDup (touched_in_A T) ->
  length (shift_trace_A T) = length T - 1.
Proof.
  induction T as [| [i j] rest IH]; intros H_A1 Hnodup.
  - simpl in H_A1. discriminate.
  - unfold has_A1 in H_A1. simpl in H_A1.
    destruct (i =? 1) eqn:Ei.
    + simpl shift_trace_A. rewrite Ei.
      apply Nat.eqb_eq in Ei. subst i.
      simpl touched_in_A in Hnodup.
      inversion Hnodup as [| x xs Hnot_in Hnodup_rest Heq]. subst.
      assert (Hno_A1_rest: has_A1 rest = false).
      { unfold has_A1.
        destruct (existsb (fun i => i =? 1) (touched_in_A rest)) eqn:E.
        - apply existsb_exists in E. destruct E as [k [Hk Hk_eq]].
          apply Nat.eqb_eq in Hk_eq. subst k.
          exfalso. apply Hnot_in. exact Hk.
        - reflexivity. }
      rewrite shift_trace_A_length_no_A1 by exact Hno_A1_rest.
      simpl. lia.
    + simpl shift_trace_A. rewrite Ei. simpl.
      simpl touched_in_A in Hnodup.
      inversion Hnodup as [| x xs Hnot_in Hnodup_rest Heq]. subst.
      assert (H_A1_rest: has_A1 rest = true).
      { unfold has_A1. exact H_A1. }
      rewrite IH by assumption.
      destruct rest as [| p rest'].
      * simpl in H_A1. discriminate.
      * simpl. lia.
Qed.

(** When has_B1 T = false, shift_trace_B preserves length *)
Lemma shift_trace_B_length_no_B1 : forall T,
  has_B1 T = false -> length (shift_trace_B T) = length T.
Proof.
  induction T as [| [i j] rest IH]; intros H.
  - reflexivity.
  - rewrite has_B1_cons in H.
    apply orb_false_elim in H. destruct H as [Hj Hrest].
    simpl. rewrite Hj. simpl.
    f_equal. apply IH. exact Hrest.
Qed.

(** For accessing nth element: nth (i-1) (c::A) = nth (i-1-1) A when i >= 2 *)
Lemma nth_cons_shift : forall (A : list Char) c i d,
  i >= 2 -> nth (i - 1) (c :: A) d = nth (i - 1 - 1) A d.
Proof.
  intros A c i d Hi.
  destruct i as [| [| i']].
  - lia.
  - lia.
  - (* i = S (S i'), so i - 1 = S i' *)
    (* Goal: nth (S (S i') - 1) (c :: A) d = nth (S (S i') - 1 - 1) A d *)
    (* Simplifies to: nth (S i') (c :: A) d = nth i' A d *)
    simpl. f_equal. lia.
Qed.

(** After simpl, nth (i-1) (c::A) becomes a match. This handles that form. *)
Lemma nth_cons_match_eq : forall (A : list Char) c i d,
  i >= 2 ->
  (match i - 1 with | 0 => c | S m => nth m A d end) = nth (i - 1 - 1) A d.
Proof.
  intros A c i d Hi.
  destruct i as [| [| i']].
  - lia.
  - lia.
  - (* i = S (S i'), so i - 1 = S i' *)
    simpl. f_equal. lia.
Qed.

(** Helper: fold_left with shifted trace - generalized for any accumulator *)
Lemma fold_left_shift_A_aux : forall T A B c1 acc,
  has_A1 T = false ->
  Forall (fun '(i, j) => i >= 2 /\ j >= 1) T ->
  fold_left (fun acc0 '(i, j) =>
    acc0 + subst_cost (nth (i-1) (c1::A) default_char) (nth (j-1) B default_char)) T acc =
  fold_left (fun acc0 '(i, j) =>
    acc0 + subst_cost (nth (i-1) A default_char) (nth (j-1) B default_char)) (shift_trace_A T) acc.
Proof.
  induction T as [| [i j] rest IH]; intros A B c1 acc Hno_A1 Hbounds.
  - reflexivity.
  - rewrite has_A1_cons in Hno_A1.
    apply orb_false_elim in Hno_A1. destruct Hno_A1 as [Hi_neq1 Hno_A1_rest].
    rewrite Forall_cons_iff in Hbounds. destruct Hbounds as [[Hi Hj] Hrest].
    (* Unfold shift_trace_A on the cons *)
    simpl shift_trace_A. rewrite Hi_neq1.
    (* Now unfold fold_left on both sides *)
    simpl fold_left.
    (* After simpl, nth (i-1) (c1::A) becomes a match expression *)
    (* Use nth_cons_match_eq to handle this *)
    assert (Hshift: (match i - 1 with | 0 => c1 | S m => nth m A default_char end) =
                    nth (i - 1 - 1) A default_char).
    { apply nth_cons_match_eq. lia. }
    rewrite Hshift.
    apply IH; assumption.
Qed.

(** Change cost equality for shift_trace_A *)
Lemma change_cost_shift_A : forall T A B c1,
  has_A1 T = false ->
  Forall (fun '(i, j) => i >= 2 /\ j >= 1) T ->
  fold_left (fun acc '(i, j) =>
    acc + subst_cost (nth (i-1) (c1::A) default_char) (nth (j-1) B default_char)) T 0 =
  fold_left (fun acc '(i, j) =>
    acc + subst_cost (nth (i-1) A default_char) (nth (j-1) B default_char)) (shift_trace_A T) 0.
Proof.
  intros. apply fold_left_shift_A_aux; assumption.
Qed.

(** Validity of shift_trace_A *)
Lemma shift_trace_A_valid : forall lenA lenB T,
  has_A1 T = false ->
  simple_valid_trace (S lenA) lenB T = true ->
  simple_valid_trace lenA lenB (shift_trace_A T) = true.
Proof.
  intros lenA lenB T Hno_A1 Hvalid.
  unfold simple_valid_trace in *.
  rewrite forallb_forall in *.
  intros [i' j'] Hin.
  (* (i', j') is in shift_trace_A T means there was some (S i', j') in T *)
  (* Actually, (i', j') came from some (i, j) in T with i <> 1 and i' = i - 1 *)
  induction T as [| [i0 j0] rest IH].
  - simpl in Hin. destruct Hin.
  - rewrite has_A1_cons in Hno_A1.
    apply orb_false_elim in Hno_A1. destruct Hno_A1 as [Hi0_neq1 Hno_A1_rest].
    simpl in Hin. rewrite Hi0_neq1 in Hin. simpl in Hin.
    destruct Hin as [Heq | Hin'].
    + (* (i', j') = (i0 - 1, j0) *)
      injection Heq as Hi' Hj'.
      (* Now specialize Hvalid with (i0, j0) *)
      assert (Hin_orig: In (i0, j0) ((i0, j0) :: rest)) by (left; reflexivity).
      specialize (Hvalid (i0, j0) Hin_orig).
      (* Don't simpl - keep in leb form *)
      (* Hvalid: (1 <=? i0) && (i0 <=? S lenA) && (1 <=? j0) && (j0 <=? lenB) = true *)
      apply andb_prop in Hvalid. destruct Hvalid as [Hvalid1 Hj0_upper].
      apply andb_prop in Hvalid1. destruct Hvalid1 as [Hvalid2 Hj0_lower].
      apply andb_prop in Hvalid2. destruct Hvalid2 as [Hi0_lower Hi0_upper].
      apply Nat.leb_le in Hi0_lower.
      apply Nat.leb_le in Hi0_upper.
      apply Nat.leb_le in Hj0_lower.
      apply Nat.leb_le in Hj0_upper.
      apply Nat.eqb_neq in Hi0_neq1.
      (* Now show the shifted pair (i' = i0-1, j' = j0) is valid for (lenA, lenB) *)
      subst i' j'.
      repeat (apply andb_true_intro; split); apply Nat.leb_le; lia.
    + (* (i', j') is in shift_trace_A rest *)
      apply IH.
      { exact Hno_A1_rest. }
      { intros x Hx. apply Hvalid. right. exact Hx. }
      { exact Hin'. }
Qed.

(** General validity of shift_trace_A - doesn't require has_A1 = false *)
Lemma shift_trace_A_valid_general : forall lenA lenB T,
  simple_valid_trace (S lenA) (S lenB) T = true ->
  simple_valid_trace lenA (S lenB) (shift_trace_A T) = true.
Proof.
  intros lenA lenB T Hvalid.
  unfold simple_valid_trace in *.
  rewrite forallb_forall in *.
  intros [i' j'] Hin.
  induction T as [| [i j] rest IH].
  - simpl in Hin. destruct Hin.
  - simpl shift_trace_A in Hin.
    destruct (i =? 1) eqn:Ei.
    + apply IH.
      { intros x Hx. apply Hvalid. right. exact Hx. }
      { exact Hin. }
    + simpl in Hin. destruct Hin as [Heq | Hin'].
      * injection Heq as Hi' Hj'.
        assert (Hin_orig: In (i, j) ((i, j) :: rest)) by (left; reflexivity).
        specialize (Hvalid (i, j) Hin_orig).
        apply andb_prop in Hvalid. destruct Hvalid as [Hvalid1 Hj_upper].
        apply andb_prop in Hvalid1. destruct Hvalid1 as [Hvalid2 Hj_lower].
        apply andb_prop in Hvalid2. destruct Hvalid2 as [Hi_lower Hi_upper].
        apply Nat.leb_le in Hi_lower.
        apply Nat.leb_le in Hi_upper.
        apply Nat.leb_le in Hj_lower.
        apply Nat.leb_le in Hj_upper.
        apply Nat.eqb_neq in Ei.
        subst i' j'.
        repeat (apply andb_true_intro; split); apply Nat.leb_le; lia.
      * apply IH.
        { intros x Hx. apply Hvalid. right. exact Hx. }
        { exact Hin'. }
Qed.

(** For base cases: if lenA = 0 or lenB = 0, valid trace must be empty *)
Lemma valid_trace_empty_A : forall lenB T,
  simple_valid_trace 0 lenB T = true -> T = [].
Proof.
  intros lenB T Hvalid.
  destruct T as [| [i j] rest].
  - reflexivity.
  - unfold simple_valid_trace in Hvalid. simpl in Hvalid.
    (* The first element (i,j) must satisfy: (1 <=? i) && (i <=? 0) && ... = true *)
    (* But 1 <=? i && i <=? 0 can only be true if 1 <= i <= 0, which is impossible *)
    destruct i as [| i']; destruct j as [| j']; destruct lenB as [| lenB'];
      simpl in Hvalid; discriminate.
Qed.

Lemma valid_trace_empty_B : forall lenA T,
  simple_valid_trace lenA 0 T = true -> T = [].
Proof.
  intros lenA T Hvalid.
  destruct T as [| [i j] rest].
  - reflexivity.
  - (* The first element (i,j) must satisfy: (1 <=? j) && (j <=? 0) = true *)
    (* But this requires 1 <= j <= 0, which is impossible *)
    exfalso.
    unfold simple_valid_trace in Hvalid. simpl in Hvalid.
    (* The forallb contains (1 <=? j) && (j <=? 0) which is impossible *)
    (* For any j: if j = 0, then (1 <=? 0) = false; if j > 0, then (j <=? 0) = false *)
    destruct j as [| j'].
    + (* j = 0: (1 <=? 0) = false, so whole thing is false *)
      apply andb_prop in Hvalid. destruct Hvalid as [Hfirst _].
      apply andb_prop in Hfirst. destruct Hfirst as [Hfirst _].
      apply andb_prop in Hfirst. destruct Hfirst as [_ Hj_lower].
      simpl in Hj_lower. discriminate.
    + (* j = S j': (S j' <=? 0) = false, so whole thing is false *)
      apply andb_prop in Hvalid. destruct Hvalid as [Hfirst _].
      apply andb_prop in Hfirst. destruct Hfirst as [Hfirst Hj_le0].
      simpl in Hj_le0. discriminate.
Qed.

(** Helper: fold_left with shifted trace for B - generalized for any accumulator *)
Lemma fold_left_shift_B_aux : forall T A B c2 acc,
  has_B1 T = false ->
  Forall (fun '(i, j) => i >= 1 /\ j >= 2) T ->
  fold_left (fun acc0 '(i, j) =>
    acc0 + subst_cost (nth (i-1) A default_char) (nth (j-1) (c2::B) default_char)) T acc =
  fold_left (fun acc0 '(i, j) =>
    acc0 + subst_cost (nth (i-1) A default_char) (nth (j-1) B default_char)) (shift_trace_B T) acc.
Proof.
  induction T as [| [i j] rest IH]; intros A B c2 acc Hno_B1 Hbounds.
  - reflexivity.
  - rewrite has_B1_cons in Hno_B1.
    apply orb_false_elim in Hno_B1. destruct Hno_B1 as [Hj_neq1 Hno_B1_rest].
    rewrite Forall_cons_iff in Hbounds. destruct Hbounds as [[Hi Hj] Hrest].
    (* Unfold shift_trace_B on the cons *)
    simpl shift_trace_B. rewrite Hj_neq1.
    (* Now unfold fold_left on both sides *)
    simpl fold_left.
    (* After simpl, nth (j-1) (c2::B) becomes a match expression *)
    assert (Hshift: (match j - 1 with | 0 => c2 | S m => nth m B default_char end) =
                    nth (j - 1 - 1) B default_char).
    { apply nth_cons_match_eq. lia. }
    rewrite Hshift.
    apply IH; assumption.
Qed.

(** Change cost equality for shift_trace_B *)
Lemma change_cost_shift_B : forall T A B c2,
  has_B1 T = false ->
  Forall (fun '(i, j) => i >= 1 /\ j >= 2) T ->
  fold_left (fun acc '(i, j) =>
    acc + subst_cost (nth (i-1) A default_char) (nth (j-1) (c2::B) default_char)) T 0 =
  fold_left (fun acc '(i, j) =>
    acc + subst_cost (nth (i-1) A default_char) (nth (j-1) B default_char)) (shift_trace_B T) 0.
Proof.
  intros. apply fold_left_shift_B_aux; assumption.
Qed.

(** Validity of shift_trace_B *)
Lemma shift_trace_B_valid : forall lenA lenB T,
  has_B1 T = false ->
  simple_valid_trace lenA (S lenB) T = true ->
  simple_valid_trace lenA lenB (shift_trace_B T) = true.
Proof.
  intros lenA lenB T Hno_B1 Hvalid.
  unfold simple_valid_trace in *.
  rewrite forallb_forall in *.
  intros [i' j'] Hin.
  induction T as [| [i0 j0] rest IH].
  - simpl in Hin. destruct Hin.
  - rewrite has_B1_cons in Hno_B1.
    apply orb_false_elim in Hno_B1. destruct Hno_B1 as [Hj0_neq1 Hno_B1_rest].
    simpl in Hin. rewrite Hj0_neq1 in Hin. simpl in Hin.
    destruct Hin as [Heq | Hin'].
    + (* (i', j') = (i0, j0 - 1) *)
      injection Heq as Hi' Hj'.
      assert (Hin_orig: In (i0, j0) ((i0, j0) :: rest)) by (left; reflexivity).
      specialize (Hvalid (i0, j0) Hin_orig).
      apply andb_prop in Hvalid. destruct Hvalid as [Hvalid1 Hj0_upper].
      apply andb_prop in Hvalid1. destruct Hvalid1 as [Hvalid2 Hj0_lower].
      apply andb_prop in Hvalid2. destruct Hvalid2 as [Hi0_lower Hi0_upper].
      apply Nat.leb_le in Hi0_lower.
      apply Nat.leb_le in Hi0_upper.
      apply Nat.leb_le in Hj0_lower.
      apply Nat.leb_le in Hj0_upper.
      apply Nat.eqb_neq in Hj0_neq1.
      subst i' j'.
      repeat (apply andb_true_intro; split); apply Nat.leb_le; lia.
    + (* (i', j') is in shift_trace_B rest *)
      apply IH.
      { exact Hno_B1_rest. }
      { intros x Hx. apply Hvalid. right. exact Hx. }
      { exact Hin'. }
Qed.

(** When has_A1 = false, all indices in A are >= 2 *)
Lemma valid_no_A1_bounds : forall lenA lenB T,
  simple_valid_trace (S lenA) lenB T = true ->
  has_A1 T = false ->
  Forall (fun '(i, j) => i >= 2 /\ j >= 1) T.
Proof.
  induction T as [| [i j] rest IH]; intros Hvalid Hno_A1.
  - constructor.
  - constructor.
    + (* Show i >= 2 /\ j >= 1 for the head *)
      rewrite has_A1_cons in Hno_A1.
      apply orb_false_elim in Hno_A1. destruct Hno_A1 as [Hi_neq1 Hno_A1_rest].
      apply Nat.eqb_neq in Hi_neq1.
      (* From validity: 1 <= i <= S lenA and 1 <= j <= lenB *)
      unfold simple_valid_trace in Hvalid.
      simpl forallb in Hvalid.
      (* Destruct i to handle the match expression from (1 <=? i) *)
      destruct i as [| i'].
      { (* i = 0: (1 <=? 0) = false, so Hvalid is false = true *)
        exfalso. simpl in Hvalid. discriminate Hvalid. }
      { (* i = S i': now 1 <=? S i' = true, and we need S i' >= 2, i.e., i' >= 1 *)
        (* Need to also destruct j to handle (1 <=? j) match expression *)
        destruct j as [| j'].
        { (* j = 0: (1 <=? 0) = false *)
          exfalso.
          unfold simple_valid_trace in Hvalid.
          simpl forallb in Hvalid. simpl in Hvalid.
          (* After simpl: (i' <=? lenA) && false && forallb ... = true *)
          (* Need to show contradiction *)
          rewrite andb_false_r in Hvalid. discriminate Hvalid. }
        { simpl in Hvalid.
          (* After simpl with i = S i', j = S j':
             structure is: ((i' <=? lenA) && (j' <=? lenB)) && rest *)
          apply andb_prop in Hvalid. destruct Hvalid as [Hfirst Hrest].
          (* Hfirst: (i' <=? lenA) && (j' <=? lenB) = true *)
          apply andb_prop in Hfirst. destruct Hfirst as [Hi_upper Hj_upper].
          (* From Hi_neq1: S i' <> 1, so i' <> 0, meaning i' >= 1, so S i' >= 2 *)
          split; lia. } }
    + (* Apply IH for the rest *)
      rewrite has_A1_cons in Hno_A1.
      apply orb_false_elim in Hno_A1. destruct Hno_A1 as [_ Hno_A1_rest].
      unfold simple_valid_trace in Hvalid.
      simpl forallb in Hvalid.
      destruct i as [| i'].
      { simpl in Hvalid. discriminate Hvalid. }
      { destruct j as [| j'].
        { exfalso. simpl in Hvalid. rewrite andb_false_r in Hvalid. discriminate Hvalid. }
        { simpl in Hvalid.
          apply andb_prop in Hvalid. destruct Hvalid as [_ Hrest].
          apply IH.
          { unfold simple_valid_trace. exact Hrest. }
          { exact Hno_A1_rest. } } }
Qed.

(** When has_B1 = false, all indices in B are >= 2 *)
Lemma valid_no_B1_bounds : forall lenA lenB T,
  simple_valid_trace lenA (S lenB) T = true ->
  has_B1 T = false ->
  Forall (fun '(i, j) => i >= 1 /\ j >= 2) T.
Proof.
  induction T as [| [i j] rest IH]; intros Hvalid Hno_B1.
  - constructor.
  - constructor.
    + (* Show i >= 1 /\ j >= 2 for the head *)
      rewrite has_B1_cons in Hno_B1.
      apply orb_false_elim in Hno_B1. destruct Hno_B1 as [Hj_neq1 Hno_B1_rest].
      apply Nat.eqb_neq in Hj_neq1.
      unfold simple_valid_trace in Hvalid.
      simpl forallb in Hvalid.
      (* Destruct i and j to handle the match expressions *)
      destruct i as [| i'].
      { simpl in Hvalid. discriminate Hvalid. }
      { destruct j as [| j'].
        { exfalso. simpl in Hvalid. rewrite andb_false_r in Hvalid. discriminate Hvalid. }
        { simpl in Hvalid.
          apply andb_prop in Hvalid. destruct Hvalid as [Hfirst Hrest].
          apply andb_prop in Hfirst. destruct Hfirst as [Hi_upper Hj_upper].
          (* From Hj_neq1: S j' <> 1, so j' <> 0, meaning j' >= 1, so S j' >= 2 *)
          split; lia. } }
    + (* Apply IH for the rest *)
      rewrite has_B1_cons in Hno_B1.
      apply orb_false_elim in Hno_B1. destruct Hno_B1 as [_ Hno_B1_rest].
      unfold simple_valid_trace in Hvalid.
      simpl forallb in Hvalid.
      destruct i as [| i'].
      { simpl in Hvalid. discriminate Hvalid. }
      { destruct j as [| j'].
        { exfalso. simpl in Hvalid. rewrite andb_false_r in Hvalid. discriminate Hvalid. }
        { simpl in Hvalid.
          apply andb_prop in Hvalid. destruct Hvalid as [_ Hrest].
          apply IH.
          { unfold simple_valid_trace. exact Hrest. }
          { exact Hno_B1_rest. } } }
Qed.

(** ========== Pigeonhole lemmas for NoDup bounds ========== *)

(** Helper lemma: Convert leb to le for bounds - use forallb_forall *)
Lemma valid_trace_first_bounds : forall lenA lenB i j rest,
  simple_valid_trace lenA lenB ((i, j) :: rest) = true ->
  1 <= i /\ i <= lenA /\ 1 <= j /\ j <= lenB.
Proof.
  intros lenA lenB i j rest Hvalid.
  unfold simple_valid_trace in Hvalid.
  rewrite forallb_forall in Hvalid.
  specialize (Hvalid (i, j) (in_eq (i, j) rest)).
  apply andb_prop in Hvalid. destruct Hvalid as [Hvalid' H4].
  apply andb_prop in Hvalid'. destruct Hvalid' as [Hvalid'' H3].
  apply andb_prop in Hvalid''. destruct Hvalid'' as [H1 H2].
  apply Nat.leb_le in H1.
  apply Nat.leb_le in H2.
  apply Nat.leb_le in H3.
  apply Nat.leb_le in H4.
  repeat split; assumption.
Qed.

(** Get validity for rest *)
Lemma valid_trace_rest : forall lenA lenB x rest,
  simple_valid_trace lenA lenB (x :: rest) = true ->
  simple_valid_trace lenA lenB rest = true.
Proof.
  intros lenA lenB x rest Hvalid.
  unfold simple_valid_trace in *.
  rewrite forallb_forall in *.
  intros y Hy.
  apply Hvalid. right. exact Hy.
Qed.

(** Simple corollary for what we actually need *)
Lemma valid_trace_i_bounds : forall lenA lenB i j rest,
  simple_valid_trace lenA lenB ((i, j) :: rest) = true ->
  1 <= i <= lenA.
Proof.
  intros.
  pose proof (valid_trace_first_bounds lenA lenB i j rest H) as [H1 [H2 _]].
  split; assumption.
Qed.

Lemma valid_trace_j_bounds : forall lenA lenB i j rest,
  simple_valid_trace lenA lenB ((i, j) :: rest) = true ->
  1 <= j <= lenB.
Proof.
  intros.
  pose proof (valid_trace_first_bounds lenA lenB i j rest H) as [_ [_ [H1 H2]]].
  split; assumption.
Qed.

(** Helper: All elements in touched_in_A are in range [2, S lenA] when has_A1=false *)
Lemma touched_in_A_in_range : forall lenA lenB T,
  simple_valid_trace (S lenA) lenB T = true ->
  has_A1 T = false ->
  forall x, In x (touched_in_A T) -> 2 <= x <= S lenA.
Proof.
  intros lenA lenB T Hvalid Hno_A1.
  induction T as [| [i j] rest IH].
  - intros x Hin. simpl in Hin. destruct Hin.
  - intros x Hin.
    rewrite has_A1_cons in Hno_A1.
    apply orb_false_elim in Hno_A1. destruct Hno_A1 as [Hi_neq1 Hno_A1_rest].
    apply Nat.eqb_neq in Hi_neq1.
    pose proof (valid_trace_i_bounds (S lenA) lenB i j rest Hvalid) as [Hi_lo Hi_hi].
    pose proof (valid_trace_rest (S lenA) lenB (i, j) rest Hvalid) as Hrest.
    simpl in Hin. destruct Hin as [Heq | Hin'].
    + subst x. split; lia.
    + apply IH; assumption.
Qed.

(** Symmetric for B *)
Lemma touched_in_B_in_range : forall lenA lenB T,
  simple_valid_trace lenA (S lenB) T = true ->
  has_B1 T = false ->
  forall x, In x (touched_in_B T) -> 2 <= x <= S lenB.
Proof.
  intros lenA lenB T Hvalid Hno_B1.
  induction T as [| [i j] rest IH].
  - intros x Hin. simpl in Hin. destruct Hin.
  - intros x Hin.
    rewrite has_B1_cons in Hno_B1.
    apply orb_false_elim in Hno_B1. destruct Hno_B1 as [Hj_neq1 Hno_B1_rest].
    apply Nat.eqb_neq in Hj_neq1.
    pose proof (valid_trace_j_bounds lenA (S lenB) i j rest Hvalid) as [Hj_lo Hj_hi].
    pose proof (valid_trace_rest lenA (S lenB) (i, j) rest Hvalid) as Hrest.
    simpl in Hin. destruct Hin as [Heq | Hin'].
    + subst x. split; lia.
    + apply IH; assumption.
Qed.

(** Pigeonhole: NoDup list with elements in [a, b] has length <= b - a + 1 *)
Lemma NoDup_length_le_range : forall (l : list nat) a b,
  NoDup l ->
  (forall x, In x l -> a <= x <= b) ->
  a <= b + 1 ->
  length l <= b - a + 1.
Proof.
  intros l a b Hnodup Hrange Hab.
  assert (Hincl: incl l (seq a (b - a + 1))).
  { unfold incl. intros x Hin.
    specialize (Hrange x Hin).
    apply in_seq. lia. }
  pose proof (NoDup_incl_length Hnodup Hincl) as Hlen.
  rewrite length_seq in Hlen.
  exact Hlen.
Qed.

(** Key lemma: NoDup + validity + has_A1 = false implies |T| <= |s1'| *)
Lemma NoDup_A_bound : forall lenA lenB T,
  simple_valid_trace (S lenA) lenB T = true ->
  has_A1 T = false ->
  NoDup (touched_in_A T) ->
  length T <= lenA.
Proof.
  intros lenA lenB T Hvalid Hno_A1 Hnodup.
  pose proof (touched_in_A_in_range lenA lenB T Hvalid Hno_A1) as Hrange.
  rewrite <- touched_in_A_length.
  destruct lenA as [| lenA'].
  - (* lenA = 0: range is [2, 1] which is empty *)
    destruct T as [| [i j] rest] eqn:ET.
    + simpl. lia.
    + simpl touched_in_A.
      exfalso.
      assert (Hin: In i (i :: touched_in_A rest)) by (left; reflexivity).
      specialize (Hrange i Hin).
      lia.
  - (* lenA = S lenA' *)
    assert (Hlen: length (touched_in_A T) <= S (S lenA') - 2 + 1).
    { apply NoDup_length_le_range; try assumption; lia. }
    lia.
Qed.

(** Symmetric: NoDup + validity + has_B1 = false implies |T| <= |s2'| *)
Lemma NoDup_B_bound : forall lenA lenB T,
  simple_valid_trace lenA (S lenB) T = true ->
  has_B1 T = false ->
  NoDup (touched_in_B T) ->
  length T <= lenB.
Proof.
  intros lenA lenB T Hvalid Hno_B1 Hnodup.
  pose proof (touched_in_B_in_range lenA lenB T Hvalid Hno_B1) as Hrange.
  rewrite <- touched_in_B_length.
  destruct lenB as [| lenB'].
  - destruct T as [| [i j] rest] eqn:ET.
    + simpl. lia.
    + simpl touched_in_B.
      exfalso.
      assert (Hin: In j (j :: touched_in_B rest)) by (left; reflexivity).
      specialize (Hrange j Hin).
      lia.
  - assert (Hlen: length (touched_in_B T) <= S (S lenB') - 2 + 1).
    { apply NoDup_length_le_range; try assumption; lia. }
    lia.
Qed.

(** When has_A1 = false, shift_trace_A doesn't filter anything *)
Lemma touched_in_B_shift_trace_A : forall T,
  has_A1 T = false ->
  touched_in_B (shift_trace_A T) = touched_in_B T.
Proof.
  induction T as [| [i j] rest IH]; intros Hno_A1.
  - reflexivity.
  - rewrite has_A1_cons in Hno_A1.
    apply orb_false_elim in Hno_A1. destruct Hno_A1 as [Hi_neq1 Hno_A1_rest].
    simpl shift_trace_A. rewrite Hi_neq1.
    simpl touched_in_B.
    f_equal. apply IH. exact Hno_A1_rest.
Qed.

Lemma touched_in_A_shift_trace_B : forall T,
  has_B1 T = false ->
  touched_in_A (shift_trace_B T) = touched_in_A T.
Proof.
  induction T as [| [i j] rest IH]; intros Hno_B1.
  - reflexivity.
  - rewrite has_B1_cons in Hno_B1.
    apply orb_false_elim in Hno_B1. destruct Hno_B1 as [Hj_neq1 Hno_B1_rest].
    simpl shift_trace_B. rewrite Hj_neq1.
    simpl touched_in_A.
    f_equal. apply IH. exact Hno_B1_rest.
Qed.

(** Helper: if x is in touched_in_A (shift_trace_A T), then x+1 is in touched_in_A T *)
Lemma in_shifted_implies_succ_in_original_A : forall lenA lenB T x,
  simple_valid_trace lenA lenB T = true ->
  In x (touched_in_A (shift_trace_A T)) ->
  In (S x) (touched_in_A T).
Proof.
  intros lenA lenB T.
  induction T as [| [i j] rest IH]; intros x Hvalid Hin.
  - simpl in Hin. destruct Hin.
  - simpl shift_trace_A in Hin.
    destruct (i =? 1) eqn:Ei.
    + apply Nat.eqb_eq in Ei. subst i.
      simpl touched_in_A. right.
      assert (Hrest_valid: simple_valid_trace lenA lenB rest = true).
      { unfold simple_valid_trace in *. rewrite forallb_forall in *.
        intros y Hy. apply Hvalid. right. exact Hy. }
      apply IH; assumption.
    + apply Nat.eqb_neq in Ei.
      simpl touched_in_A in Hin.
      destruct Hin as [Heq | Hin'].
      * simpl touched_in_A. left.
        assert (Hi_ge_1: 1 <= i).
        { unfold simple_valid_trace in Hvalid. rewrite forallb_forall in Hvalid.
          specialize (Hvalid (i, j) (in_eq _ _)).
          apply andb_prop in Hvalid. destruct Hvalid as [Hvalid' _].
          apply andb_prop in Hvalid'. destruct Hvalid' as [Hvalid'' _].
          apply andb_prop in Hvalid''. destruct Hvalid'' as [H1 _].
          apply Nat.leb_le in H1. exact H1. }
        lia.
      * simpl touched_in_A. right.
        assert (Hrest_valid: simple_valid_trace lenA lenB rest = true).
        { unfold simple_valid_trace in *. rewrite forallb_forall in *.
          intros y Hy. apply Hvalid. right. exact Hy. }
        apply IH; assumption.
Qed.

Lemma in_shifted_implies_succ_in_original_B : forall lenA lenB T x,
  simple_valid_trace lenA lenB T = true ->
  In x (touched_in_B (shift_trace_B T)) ->
  In (S x) (touched_in_B T).
Proof.
  intros lenA lenB T.
  induction T as [| [i j] rest IH]; intros x Hvalid Hin.
  - simpl in Hin. destruct Hin.
  - simpl shift_trace_B in Hin.
    destruct (j =? 1) eqn:Ej.
    + apply Nat.eqb_eq in Ej. subst j.
      simpl touched_in_B. right.
      assert (Hrest_valid: simple_valid_trace lenA lenB rest = true).
      { unfold simple_valid_trace in *. rewrite forallb_forall in *.
        intros y Hy. apply Hvalid. right. exact Hy. }
      apply IH; assumption.
    + apply Nat.eqb_neq in Ej.
      simpl touched_in_B in Hin.
      destruct Hin as [Heq | Hin'].
      * simpl touched_in_B. left.
        assert (Hj_ge_1: 1 <= j).
        { unfold simple_valid_trace in Hvalid. rewrite forallb_forall in Hvalid.
          specialize (Hvalid (i, j) (in_eq _ _)).
          apply andb_prop in Hvalid. destruct Hvalid as [Hvalid' _].
          apply andb_prop in Hvalid'. destruct Hvalid' as [_ H3].
          apply Nat.leb_le in H3. exact H3. }
        lia.
      * simpl touched_in_B. right.
        assert (Hrest_valid: simple_valid_trace lenA lenB rest = true).
        { unfold simple_valid_trace in *. rewrite forallb_forall in *.
          intros y Hy. apply Hvalid. right. exact Hy. }
        apply IH; assumption.
Qed.

(** NoDup preservation under shift_trace_A (requires validity for index >= 1) *)
Lemma shift_trace_A_NoDup_A : forall lenA lenB T,
  simple_valid_trace lenA lenB T = true ->
  NoDup (touched_in_A T) ->
  NoDup (touched_in_A (shift_trace_A T)).
Proof.
  intros lenA lenB T.
  induction T as [| [i j] rest IH]; intros Hvalid Hnodup.
  - simpl. constructor.
  - simpl touched_in_A in Hnodup.
    inversion Hnodup as [| x xs Hnot_in Hnodup_rest Heq]. subst x xs.
    simpl shift_trace_A.
    destruct (i =? 1) eqn:Ei.
    + assert (Hrest_valid: simple_valid_trace lenA lenB rest = true).
      { unfold simple_valid_trace in *. rewrite forallb_forall in *.
        intros y Hy. apply Hvalid. right. exact Hy. }
      apply IH; assumption.
    + apply Nat.eqb_neq in Ei.
      simpl touched_in_A.
      assert (Hrest_valid: simple_valid_trace lenA lenB rest = true).
      { unfold simple_valid_trace in *. rewrite forallb_forall in *.
        intros y Hy. apply Hvalid. right. exact Hy. }
      constructor.
      * intro Hcontra.
        assert (Hin_orig: In i (touched_in_A rest)).
        { assert (Hi_ge_1: 1 <= i).
          { unfold simple_valid_trace in Hvalid. rewrite forallb_forall in Hvalid.
            specialize (Hvalid (i, j) (in_eq _ _)).
            apply andb_prop in Hvalid. destruct Hvalid as [Hvalid' _].
            apply andb_prop in Hvalid'. destruct Hvalid' as [Hvalid'' _].
            apply andb_prop in Hvalid''. destruct Hvalid'' as [H1 _].
            apply Nat.leb_le in H1. exact H1. }
          replace i with (S (i - 1)) by lia.
          apply in_shifted_implies_succ_in_original_A with (lenA := lenA) (lenB := lenB).
          - exact Hrest_valid.
          - exact Hcontra. }
        apply Hnot_in. exact Hin_orig.
      * apply IH; assumption.
Qed.

(** NoDup preservation for B under shift_trace_A (when has_A1 = false) *)
Lemma shift_trace_A_NoDup_B : forall T,
  NoDup (touched_in_B T) ->
  has_A1 T = false ->
  NoDup (touched_in_B (shift_trace_A T)).
Proof.
  intros T Hnodup Hno_A1.
  rewrite touched_in_B_shift_trace_A by exact Hno_A1.
  exact Hnodup.
Qed.

(** Helper: if j is in touched_in_B (shift_trace_A T), then j is in touched_in_B T *)
Lemma in_shifted_B_implies_in_original_B : forall T j,
  In j (touched_in_B (shift_trace_A T)) -> In j (touched_in_B T).
Proof.
  induction T as [| [i k] rest IH]; intros j Hin.
  - simpl in Hin. destruct Hin.
  - simpl shift_trace_A in Hin.
    destruct (i =? 1) eqn:Ei.
    + simpl touched_in_B. right. apply IH. exact Hin.
    + simpl in Hin. destruct Hin as [Heq | Hin'].
      * simpl touched_in_B. left. exact Heq.
      * simpl touched_in_B. right. apply IH. exact Hin'.
Qed.

(** NoDup preservation for B under shift_trace_A (general - no has_A1 requirement) *)
Lemma shift_trace_A_NoDup_B_general : forall T,
  NoDup (touched_in_B T) ->
  NoDup (touched_in_B (shift_trace_A T)).
Proof.
  induction T as [| [i j] rest IH]; intros Hnodup.
  - constructor.
  - simpl shift_trace_A.
    destruct (i =? 1) eqn:Ei.
    + simpl touched_in_B in Hnodup.
      inversion Hnodup as [| x xs Hnot_in Hnodup_rest Heq]. subst.
      apply IH. exact Hnodup_rest.
    + simpl touched_in_B.
      simpl touched_in_B in Hnodup.
      inversion Hnodup as [| x xs Hnot_in Hnodup_rest Heq]. subst.
      constructor.
      * intro Hcontra.
        apply Hnot_in.
        apply in_shifted_B_implies_in_original_B. exact Hcontra.
      * apply IH. exact Hnodup_rest.
Qed.

(** NoDup preservation for B under shift_trace_B (requires validity) *)
Lemma shift_trace_B_NoDup_B : forall lenA lenB T,
  simple_valid_trace lenA lenB T = true ->
  NoDup (touched_in_B T) ->
  NoDup (touched_in_B (shift_trace_B T)).
Proof.
  intros lenA lenB T.
  induction T as [| [i j] rest IH]; intros Hvalid Hnodup.
  - simpl. constructor.
  - simpl touched_in_B in Hnodup.
    inversion Hnodup as [| x xs Hnot_in Hnodup_rest Heq]. subst x xs.
    simpl shift_trace_B.
    destruct (j =? 1) eqn:Ej.
    + assert (Hrest_valid: simple_valid_trace lenA lenB rest = true).
      { unfold simple_valid_trace in *. rewrite forallb_forall in *.
        intros y Hy. apply Hvalid. right. exact Hy. }
      apply IH; assumption.
    + apply Nat.eqb_neq in Ej.
      simpl touched_in_B.
      assert (Hrest_valid: simple_valid_trace lenA lenB rest = true).
      { unfold simple_valid_trace in *. rewrite forallb_forall in *.
        intros y Hy. apply Hvalid. right. exact Hy. }
      constructor.
      * intro Hcontra.
        assert (Hin_orig: In j (touched_in_B rest)).
        { assert (Hj_ge_1: 1 <= j).
          { unfold simple_valid_trace in Hvalid. rewrite forallb_forall in Hvalid.
            specialize (Hvalid (i, j) (in_eq _ _)).
            apply andb_prop in Hvalid. destruct Hvalid as [Hvalid' _].
            apply andb_prop in Hvalid'. destruct Hvalid' as [_ H3].
            apply Nat.leb_le in H3. exact H3. }
          replace j with (S (j - 1)) by lia.
          apply in_shifted_implies_succ_in_original_B with (lenA := lenA) (lenB := lenB).
          - exact Hrest_valid.
          - exact Hcontra. }
        apply Hnot_in. exact Hin_orig.
      * apply IH; assumption.
Qed.

(** NoDup preservation for A under shift_trace_B (when has_B1 = false) *)
Lemma shift_trace_B_NoDup_A : forall T,
  NoDup (touched_in_A T) ->
  has_B1 T = false ->
  NoDup (touched_in_A (shift_trace_B T)).
Proof.
  intros T Hnodup Hno_B1.
  rewrite touched_in_A_shift_trace_B by exact Hno_B1.
  exact Hnodup.
Qed.

(** ========== Helper lemmas for shift_trace_11 (substitution case) ========== *)

(** Length of shift_trace_11 when (1,1) is present and NoDup holds *)
Lemma shift_trace_11_length : forall T,
  NoDup (touched_in_A T) ->
  NoDup (touched_in_B T) ->
  has_pair_11 T = true ->
  length (shift_trace_11 T) = length T - 1.
Proof.
  intros T HnodupA HnodupB H11.
  rewrite shift_trace_11_length_general.
  assert (H_count: count_11 T = 1).
  { pose proof (count_11_le_1_aux T HnodupA HnodupB) as Hle.
    (* count_11 T >= 1 because has_pair_11 T = true *)
    assert (Hge: count_11 T >= 1).
    { unfold has_pair_11 in H11. rewrite existsb_exists in H11.
      destruct H11 as [[i' j'] [Hin Hcheck]].
      apply andb_prop in Hcheck. destruct Hcheck as [Hi' Hj'].
      apply Nat.eqb_eq in Hi'. apply Nat.eqb_eq in Hj'. subst.
      clear -Hin.
      induction T as [| [i j] rest IH].
      - destruct Hin.
      - simpl count_11.
        destruct ((i =? 1) && (j =? 1)) eqn:E.
        + lia.
        + destruct Hin as [Heq | Hin'].
          * injection Heq as Hi Hj. subst.
            simpl in E. discriminate.
          * assert (H := IH Hin'). lia. }
    lia. }
  rewrite H_count. reflexivity.
Qed.

(** Helper: given (i', j') in shift_trace_11 L, there exists (i'', j'') in L
    such that i' = i'' - 1 and j' = j'' - 1, and (i'', j'') ≠ (1, 1) *)
Lemma shift_trace_11_in_original : forall L i' j',
  (forall p, In p L -> fst p = 1 -> snd p = 1 -> False) ->
  In (i', j') (shift_trace_11 L) ->
  exists i'' j'', In (i'', j'') L /\
                  (i'' =? 1) && (j'' =? 1) = false /\
                  i' = i'' - 1 /\ j' = j'' - 1.
Proof.
  induction L as [| [i'' j''] L' IH']; intros i' j' Hno11 Hin.
  - simpl in Hin. destruct Hin.
  - simpl shift_trace_11 in Hin.
    destruct ((i'' =? 1) && (j'' =? 1)) eqn:E'.
    + (* (i'', j'') = (1,1), but this contradicts Hno11 *)
      apply andb_prop in E'. destruct E' as [Ei'' Ej''].
      apply Nat.eqb_eq in Ei''. apply Nat.eqb_eq in Ej''. subst.
      exfalso. apply (Hno11 (1, 1)).
      * left. reflexivity.
      * reflexivity.
      * reflexivity.
    + simpl in Hin.
      destruct Hin as [Heq | Hin'].
      * injection Heq as Hi' Hj'.
        exists i'', j''. split; [left; reflexivity | split; [exact E' | split; [symmetry; exact Hi' | symmetry; exact Hj']]].
      * assert (Hno11': forall p, In p L' -> fst p = 1 -> snd p = 1 -> False).
        { intros p Hp Hfst Hsnd. apply Hno11 with p; auto. right. exact Hp. }
        destruct (IH' i' j' Hno11' Hin') as [i''' [j''' [Hin''' [Hneq [Hi''' Hj''']]]]].
        exists i''', j'''. split; [right; exact Hin''' | split; [exact Hneq | split; [exact Hi''' | exact Hj''']]].
Qed.

(** Helper: if k not in touched_in_A L, then no pair in L has first component k *)
Lemma not_in_touched_A : forall L k,
  ~ In k (touched_in_A L) ->
  forall i j, In (i, j) L -> i <> k.
Proof.
  induction L as [| [a b] L' IH']; intros k Hnot_in i j Hin.
  - destruct Hin.
  - simpl touched_in_A in Hnot_in.
    destruct Hin as [Heq | Hin'].
    + injection Heq as Ha Hb. subst.
      intro Hsub. subst. apply Hnot_in. left. reflexivity.
    + apply IH' with j; auto.
      intro H. apply Hnot_in. right. exact H.
Qed.

(** Helper: if k not in touched_in_B L, then no pair in L has second component k *)
Lemma not_in_touched_B : forall L k,
  ~ In k (touched_in_B L) ->
  forall i j, In (i, j) L -> j <> k.
Proof.
  induction L as [| [a b] L' IH']; intros k Hnot_in i j Hin.
  - destruct Hin.
  - simpl touched_in_B in Hnot_in.
    destruct Hin as [Heq | Hin'].
    + injection Heq as Ha Hb. subst.
      intro Hsub. subst. apply Hnot_in. left. reflexivity.
    + apply IH' with i; auto.
      intro H. apply Hnot_in. right. exact H.
Qed.

(** Validity of shift_trace_11 - requires NoDup *)
Lemma shift_trace_11_valid : forall lenA lenB T,
  NoDup (touched_in_A T) ->
  NoDup (touched_in_B T) ->
  has_pair_11 T = true ->
  simple_valid_trace (S lenA) (S lenB) T = true ->
  simple_valid_trace lenA lenB (shift_trace_11 T) = true.
Proof.
  intros lenA lenB T.
  induction T as [| [i j] rest IH].
  - intros _ _ H11 _. simpl in H11. discriminate.
  - intros HnodupA HnodupB H11 Hvalid.
    simpl touched_in_A in HnodupA. simpl touched_in_B in HnodupB.
    inversion HnodupA as [| x xs Hnot_in_A Hnodup_restA Heq1]. subst.
    inversion HnodupB as [| y ys Hnot_in_B Hnodup_restB Heq2]. subst.

    unfold simple_valid_trace in Hvalid. simpl forallb in Hvalid.
    apply andb_prop in Hvalid. destruct Hvalid as [Hhead Hrest_valid].

    simpl shift_trace_11.
    destruct ((i =? 1) && (j =? 1)) eqn:E.
    + (* (i,j) = (1,1), skipped - recurse on rest *)
      apply andb_prop in E. destruct E as [Ei Ej].
      apply Nat.eqb_eq in Ei. apply Nat.eqb_eq in Ej. subst.
      clear IH.
      (* rest has no (1,1) because 1 is not in touched_in_A rest *)
      assert (Hno11_rest: forall p, In p rest -> fst p = 1 -> snd p = 1 -> False).
      { intros [ia ja] Hpin Hfst Hsnd. simpl in Hfst, Hsnd. subst.
        eapply not_in_touched_A; eauto. }

      unfold simple_valid_trace. rewrite forallb_forall.
      intros [i' j'] Hin'.
      destruct (shift_trace_11_in_original rest i' j' Hno11_rest Hin')
        as [i'' [j'' [Hin'' [Hneq [Hi' Hj']]]]].
      subst i' j'.

      unfold simple_valid_trace in Hrest_valid.
      rewrite forallb_forall in Hrest_valid.
      specialize (Hrest_valid (i'', j'') Hin'').
      apply andb_prop in Hrest_valid. destruct Hrest_valid as [Hv1 Hj''_le].
      apply andb_prop in Hv1. destruct Hv1 as [Hv2 Hj''_ge].
      apply andb_prop in Hv2. destruct Hv2 as [Hi''_ge Hi''_le].
      assert (Hi''_ge': i'' >= 1).
      { destruct i''; simpl in Hi''_ge; [discriminate | lia]. }
      apply Nat.leb_le in Hi''_le.
      assert (Hj''_ge': j'' >= 1).
      { destruct j''; simpl in Hj''_ge; [discriminate | lia]. }
      apply Nat.leb_le in Hj''_le.

      assert (Hi''_neq1: i'' <> 1) by (eapply not_in_touched_A; eauto).
      assert (Hj''_neq1: j'' <> 1) by (eapply not_in_touched_B; eauto).

      (* i'' >= 2 and j'' >= 2, so i'' - 1 >= 1 and j'' - 1 >= 1 *)
      assert (Hi''_ge2: i'' >= 2) by lia.
      assert (Hj''_ge2: j'' >= 2) by lia.
      apply andb_true_intro. split.
      apply andb_true_intro. split.
      apply andb_true_intro. split.
      * destruct i'' as [| [| i''']]; [lia | lia | simpl; reflexivity].
      * apply Nat.leb_le. lia.
      * destruct j'' as [| [| j''']]; [lia | lia | simpl; reflexivity].
      * apply Nat.leb_le. lia.
    + (* (i,j) ≠ (1,1), included as (i-1, j-1) *)
      assert (Hrest11: has_pair_11 rest = true).
      { unfold has_pair_11 in H11. simpl existsb in H11.
        rewrite E in H11. unfold has_pair_11. exact H11. }

      unfold simple_valid_trace. simpl forallb.
      apply andb_true_intro. split.
      * (* Show (i-1, j-1) is valid *)
        apply andb_prop in Hhead. destruct Hhead as [Hv1 Hj_le].
        apply andb_prop in Hv1. destruct Hv1 as [Hv2 Hj_ge].
        apply andb_prop in Hv2. destruct Hv2 as [Hi_ge Hi_le].
        assert (Hi_ge': i >= 1).
        { destruct i; simpl in Hi_ge; [discriminate | lia]. }
        apply Nat.leb_le in Hi_le.
        assert (Hj_ge': j >= 1).
        { destruct j; simpl in Hj_ge; [discriminate | lia]. }
        apply Nat.leb_le in Hj_le.

        (* Since (1,1) is in rest, i ≠ 1 and j ≠ 1 by NoDup *)
        assert (Hi_neq1: i <> 1).
        { intro Hsub. subst i.
          assert (H: exists p, In p rest /\ fst p = 1 /\ snd p = 1).
          { clear -Hrest11.
            unfold has_pair_11 in Hrest11.
            rewrite existsb_exists in Hrest11.
            destruct Hrest11 as [[i' j'] [Hin Hcheck]].
            apply andb_prop in Hcheck. destruct Hcheck as [Hi' Hj'].
            apply Nat.eqb_eq in Hi'. apply Nat.eqb_eq in Hj'. subst.
            exists (1, 1). split; [exact Hin | split; reflexivity]. }
          destruct H as [[i' j'] [Hin [Hi' Hj']]]. simpl in Hi', Hj'. subst.
          apply Hnot_in_A.
          clear -Hin.
          induction rest as [| [a b] rest' IH'].
          - destruct Hin.
          - destruct Hin as [Heq | Hin'].
            + injection Heq as Ha Hb. subst.
              simpl. left. reflexivity.
            + simpl. right. apply IH'. exact Hin'. }
        assert (Hj_neq1: j <> 1).
        { intro Hsub. subst j.
          assert (H: exists p, In p rest /\ fst p = 1 /\ snd p = 1).
          { clear -Hrest11.
            unfold has_pair_11 in Hrest11.
            rewrite existsb_exists in Hrest11.
            destruct Hrest11 as [[i' j'] [Hin Hcheck]].
            apply andb_prop in Hcheck. destruct Hcheck as [Hi' Hj'].
            apply Nat.eqb_eq in Hi'. apply Nat.eqb_eq in Hj'. subst.
            exists (1, 1). split; [exact Hin | split; reflexivity]. }
          destruct H as [[i' j'] [Hin [Hi' Hj']]]. simpl in Hi', Hj'. subst.
          apply Hnot_in_B.
          clear -Hin.
          induction rest as [| [a b] rest' IH'].
          - destruct Hin.
          - destruct Hin as [Heq | Hin'].
            + injection Heq as Ha Hb. subst.
              simpl. left. reflexivity.
            + simpl. right. apply IH'. exact Hin'. }

        assert (Hi_ge2: i >= 2) by lia.
        assert (Hj_ge2: j >= 2) by lia.
        apply andb_true_intro. split.
        apply andb_true_intro. split.
        apply andb_true_intro. split.
        -- destruct i as [| [| i']]; [lia | lia | simpl; reflexivity].
        -- apply Nat.leb_le. lia.
        -- destruct j as [| [| j']]; [lia | lia | simpl; reflexivity].
        -- apply Nat.leb_le. lia.
      * (* Show shift_trace_11 rest is valid *)
        apply IH.
        -- exact Hnodup_restA.
        -- exact Hnodup_restB.
        -- exact Hrest11.
        -- unfold simple_valid_trace. exact Hrest_valid.
Qed.

(** NoDup preservation for shift_trace_11 *)
Lemma shift_trace_11_NoDup_A : forall lenA lenB T,
  simple_valid_trace (S lenA) (S lenB) T = true ->
  NoDup (touched_in_A T) ->
  NoDup (touched_in_A (shift_trace_11 T)).
Proof.
  intros lenA lenB T Hvalid Hnodup.
  induction T as [| [i j] rest IH].
  - simpl. constructor.
  - simpl touched_in_A in Hnodup.
    inversion Hnodup as [| x xs Hnot_in Hnodup_rest Heq]. subst.
    unfold simple_valid_trace in Hvalid. simpl forallb in Hvalid.
    apply andb_prop in Hvalid. destruct Hvalid as [Hhead Hrest_valid].
    simpl shift_trace_11.
    destruct ((i =? 1) && (j =? 1)) eqn:E.
    + (* (i, j) = (1, 1): skip it *)
      apply IH.
      * unfold simple_valid_trace. exact Hrest_valid.
      * exact Hnodup_rest.
    + (* (i, j) ≠ (1, 1): include shifted *)
      simpl touched_in_A.
      constructor.
      * (* Show i - 1 not in touched_in_A (shift_trace_11 rest) *)
        intro Hcontra.
        (* If i-1 is in shifted rest, then S (i-1) = i is in touched_in_A rest *)
        assert (Hin_orig: In i (touched_in_A rest)).
        { assert (Hi_ge_1: 1 <= i).
          { apply andb_prop in Hhead. destruct Hhead as [Hv1 _].
            apply andb_prop in Hv1. destruct Hv1 as [Hv2 _].
            apply andb_prop in Hv2. destruct Hv2 as [Hi_ge _].
            destruct i; simpl in Hi_ge; [discriminate | lia]. }
          replace i with (S (i - 1)) by lia.
          (* Need helper lemma about shifted indices *)
          clear -Hcontra Hrest_valid.
          induction rest as [| [i' j'] rest' IH'].
          - simpl in Hcontra. destruct Hcontra.
          - unfold simple_valid_trace in Hrest_valid. simpl forallb in Hrest_valid.
            apply andb_prop in Hrest_valid. destruct Hrest_valid as [Hhead' Hrest'].
            simpl shift_trace_11 in Hcontra.
            destruct ((i' =? 1) && (j' =? 1)) eqn:E'.
            + simpl touched_in_A. right.
              apply IH'.
              * unfold simple_valid_trace. exact Hrest'.
              * exact Hcontra.
            + simpl touched_in_A in Hcontra.
              destruct Hcontra as [Heq | Hcontra'].
              * simpl touched_in_A. left.
                apply andb_prop in Hhead'. destruct Hhead' as [Hv1' _].
                apply andb_prop in Hv1'. destruct Hv1' as [Hv2' _].
                apply andb_prop in Hv2'. destruct Hv2' as [Hi'_ge _].
                assert (Hi'_ge': i' >= 1).
                { destruct i'; simpl in Hi'_ge; [discriminate | lia]. }
                lia.
              * simpl touched_in_A. right.
                apply IH'.
                -- unfold simple_valid_trace. exact Hrest'.
                -- exact Hcontra'. }
        apply Hnot_in. exact Hin_orig.
      * apply IH.
        -- unfold simple_valid_trace. exact Hrest_valid.
        -- exact Hnodup_rest.
Qed.

Lemma shift_trace_11_NoDup_B : forall lenA lenB T,
  simple_valid_trace (S lenA) (S lenB) T = true ->
  NoDup (touched_in_B T) ->
  NoDup (touched_in_B (shift_trace_11 T)).
Proof.
  intros lenA lenB T Hvalid Hnodup.
  induction T as [| [i j] rest IH].
  - simpl. constructor.
  - simpl touched_in_B in Hnodup.
    inversion Hnodup as [| x xs Hnot_in Hnodup_rest Heq]. subst.
    unfold simple_valid_trace in Hvalid. simpl forallb in Hvalid.
    apply andb_prop in Hvalid. destruct Hvalid as [Hhead Hrest_valid].
    simpl shift_trace_11.
    destruct ((i =? 1) && (j =? 1)) eqn:E.
    + (* (i, j) = (1, 1): skip it *)
      apply IH.
      * unfold simple_valid_trace. exact Hrest_valid.
      * exact Hnodup_rest.
    + (* (i, j) ≠ (1, 1): include shifted *)
      simpl touched_in_B.
      constructor.
      * (* Show j - 1 not in touched_in_B (shift_trace_11 rest) *)
        intro Hcontra.
        assert (Hin_orig: In j (touched_in_B rest)).
        { apply andb_prop in Hhead. destruct Hhead as [Hv1 _].
          apply andb_prop in Hv1. destruct Hv1 as [_ Hj_ge].
          assert (Hj_ge': j >= 1).
          { destruct j; simpl in Hj_ge; [discriminate | lia]. }
          replace j with (S (j - 1)) by lia.
          clear -Hcontra Hrest_valid.
          induction rest as [| [i' j'] rest' IH'].
          - simpl in Hcontra. destruct Hcontra.
          - unfold simple_valid_trace in Hrest_valid. simpl forallb in Hrest_valid.
            apply andb_prop in Hrest_valid. destruct Hrest_valid as [Hhead' Hrest'].
            simpl shift_trace_11 in Hcontra.
            destruct ((i' =? 1) && (j' =? 1)) eqn:E'.
            + simpl touched_in_B. right.
              apply IH'.
              * unfold simple_valid_trace. exact Hrest'.
              * exact Hcontra.
            + simpl touched_in_B in Hcontra.
              destruct Hcontra as [Heq | Hcontra'].
              * simpl touched_in_B. left.
                apply andb_prop in Hhead'. destruct Hhead' as [Hv1' _].
                apply andb_prop in Hv1'. destruct Hv1' as [_ Hj'_ge].
                assert (Hj'_ge': j' >= 1).
                { destruct j'; simpl in Hj'_ge; [discriminate | lia]. }
                lia.
              * simpl touched_in_B. right.
                apply IH'.
                -- unfold simple_valid_trace. exact Hrest'.
                -- exact Hcontra'. }
        apply Hnot_in. exact Hin_orig.
      * apply IH.
        -- unfold simple_valid_trace. exact Hrest_valid.
        -- exact Hnodup_rest.
Qed.

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

(** Helper for natural subtraction *)
Lemma nat_sub_lt_implies_lt : forall a1 a2, a1 - 1 < a2 - 1 -> a1 < a2.
Proof.
  intros a1 a2. destruct a1, a2; simpl; intros H; try lia.
Qed.

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

(** Helper: bounds when there's no (1,1) in trace *)
Lemma shift_trace_11_bounds_no_11 : forall lenA lenB T,
  simple_valid_trace (S lenA) (S lenB) T = true ->
  ~ In 1 (touched_in_A T) ->
  ~ In 1 (touched_in_B T) ->
  Forall (fun '(i, j) => i >= 1 /\ j >= 1) (shift_trace_11 T).
Proof.
  intros lenA lenB T.
  induction T as [| [i j] rest IH]; intros Hvalid HnotA HnotB.
  - constructor.
  - simpl touched_in_A in HnotA. simpl touched_in_B in HnotB.
    assert (Hi_neq1: i <> 1).
    { intro Hsub. subst. apply HnotA. left. reflexivity. }
    assert (Hj_neq1: j <> 1).
    { intro Hsub. subst. apply HnotB. left. reflexivity. }
    assert (HnotA': ~ In 1 (touched_in_A rest)).
    { intro H. apply HnotA. right. exact H. }
    assert (HnotB': ~ In 1 (touched_in_B rest)).
    { intro H. apply HnotB. right. exact H. }
    unfold simple_valid_trace in Hvalid. simpl forallb in Hvalid.
    apply andb_prop in Hvalid. destruct Hvalid as [Hhead Hrest_valid].
    simpl shift_trace_11.
    destruct ((i =? 1) && (j =? 1)) eqn:E.
    + (* (i,j) = (1,1), impossible *)
      apply andb_prop in E. destruct E as [Ei Ej].
      apply Nat.eqb_eq in Ei. apply Nat.eqb_eq in Ej. subst.
      exfalso. apply Hi_neq1. reflexivity.
    + constructor.
      * (* (i-1, j-1) has bounds >= 1 since i >= 2 and j >= 2 *)
        apply andb_prop in Hhead. destruct Hhead as [Hv1 Hj_le].
        apply andb_prop in Hv1. destruct Hv1 as [Hv2 Hj_ge].
        apply andb_prop in Hv2. destruct Hv2 as [Hi_ge Hi_le].
        assert (Hi_ge': i >= 1).
        { destruct i; simpl in Hi_ge; [discriminate | lia]. }
        assert (Hj_ge': j >= 1).
        { destruct j; simpl in Hj_ge; [discriminate | lia]. }
        split; lia.
      * apply IH.
        -- unfold simple_valid_trace. exact Hrest_valid.
        -- exact HnotA'.
        -- exact HnotB'.
Qed.

(** Bounds on indices in shift_trace_11 *)
Lemma shift_trace_11_bounds : forall lenA lenB T,
  simple_valid_trace (S lenA) (S lenB) T = true ->
  has_pair_11 T = true ->
  NoDup (touched_in_A T) ->
  NoDup (touched_in_B T) ->
  Forall (fun '(i, j) => i >= 1 /\ j >= 1) (shift_trace_11 T).
Proof.
  intros lenA lenB T.
  induction T as [| [i j] rest IH]; intros Hvalid H11 HnodupA HnodupB.
  - simpl in H11. discriminate.
  - simpl touched_in_A in HnodupA. simpl touched_in_B in HnodupB.
    inversion HnodupA as [| x xs Hnot_in_A Hnodup_restA Heq1]. subst.
    inversion HnodupB as [| y ys Hnot_in_B Hnodup_restB Heq2]. subst.
    unfold simple_valid_trace in Hvalid. simpl forallb in Hvalid.
    apply andb_prop in Hvalid. destruct Hvalid as [Hhead Hrest_valid].
    simpl shift_trace_11.
    destruct ((i =? 1) && (j =? 1)) eqn:E.
    + (* (i,j) = (1,1), skipped *)
      apply andb_prop in E. destruct E as [Ei Ej].
      apply Nat.eqb_eq in Ei. apply Nat.eqb_eq in Ej. subst.
      (* Use helper lemma *)
      apply shift_trace_11_bounds_no_11 with (lenA := lenA) (lenB := lenB).
      * unfold simple_valid_trace. exact Hrest_valid.
      * exact Hnot_in_A.
      * exact Hnot_in_B.
    + (* (i,j) ≠ (1,1) *)
      constructor.
      * (* (i-1, j-1) bounds >= 1 *)
        unfold has_pair_11 in H11. simpl existsb in H11. rewrite E in H11.
        assert (Hrest11: has_pair_11 rest = true).
        { unfold has_pair_11. exact H11. }
        assert (Hi_neq1: i <> 1).
        { intro Hsub. subst.
          unfold has_pair_11 in Hrest11. rewrite existsb_exists in Hrest11.
          destruct Hrest11 as [[i'' j''] [Hin Hcheck]].
          apply andb_prop in Hcheck. destruct Hcheck as [Hi'' Hj''].
          apply Nat.eqb_eq in Hi''. apply Nat.eqb_eq in Hj''. subst.
          apply Hnot_in_A.
          clear -Hin.
          induction rest as [| [a b] rest' IH'].
          - destruct Hin.
          - destruct Hin as [Heq | Hin'].
            + injection Heq as Ha Hb. subst. simpl. left. reflexivity.
            + simpl. right. apply IH'. exact Hin'. }
        assert (Hj_neq1: j <> 1).
        { intro Hsub. subst.
          unfold has_pair_11 in Hrest11. rewrite existsb_exists in Hrest11.
          destruct Hrest11 as [[i'' j''] [Hin Hcheck]].
          apply andb_prop in Hcheck. destruct Hcheck as [Hi'' Hj''].
          apply Nat.eqb_eq in Hi''. apply Nat.eqb_eq in Hj''. subst.
          apply Hnot_in_B.
          clear -Hin.
          induction rest as [| [a b] rest' IH'].
          - destruct Hin.
          - destruct Hin as [Heq | Hin'].
            + injection Heq as Ha Hb. subst. simpl. left. reflexivity.
            + simpl. right. apply IH'. exact Hin'. }
        apply andb_prop in Hhead. destruct Hhead as [Hv1 Hj_le].
        apply andb_prop in Hv1. destruct Hv1 as [Hv2 Hj_ge].
        apply andb_prop in Hv2. destruct Hv2 as [Hi_ge Hi_le].
        assert (Hi_ge': i >= 1).
        { destruct i; simpl in Hi_ge; [discriminate | lia]. }
        apply Nat.leb_le in Hi_le.
        assert (Hj_ge': j >= 1).
        { destruct j; simpl in Hj_ge; [discriminate | lia]. }
        apply Nat.leb_le in Hj_le.
        split; lia.
      * (* Recurse *)
        apply IH.
        -- unfold simple_valid_trace. exact Hrest_valid.
        -- unfold has_pair_11 in H11. simpl existsb in H11. rewrite E in H11.
           unfold has_pair_11. exact H11.
        -- exact Hnodup_restA.
        -- exact Hnodup_restB.
Qed.

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

(** Cost function for a trace (wrapper for fold_left) *)
Definition trace_cost_fold (A B : list Char) (T : Trace) : nat :=
  fold_left (fun acc '(i, j) => acc + subst_cost (nth (i-1) A default_char) (nth (j-1) B default_char)) T 0.

(** Accumulator property *)
Lemma trace_cost_fold_cons : forall A B i j rest,
  trace_cost_fold A B ((i, j) :: rest) =
  subst_cost (nth (i-1) A default_char) (nth (j-1) B default_char) + trace_cost_fold A B rest.
Proof.
  intros A B i j rest.
  unfold trace_cost_fold. simpl fold_left.
  set (cost := subst_cost (nth (i-1) A default_char) (nth (j-1) B default_char)).
  clearbody cost.
  revert cost.
  induction rest as [| [a b] rest' IH]; intros cost.
  - simpl. lia.
  - simpl fold_left.
    rewrite IH.
    set (cost2 := subst_cost (nth (a-1) A default_char) (nth (b-1) B default_char)).
    rewrite IH with (cost := cost2).
    unfold cost2. lia.
Qed.

(** Helper: when all indices >= 2, trace_cost on (c1::A, c2::B) equals trace_cost on (A, B) after shift *)
Lemma trace_cost_fold_shift_all_ge2 : forall T (A B : list Char) c1 c2,
  Forall (fun '(i, j) => i >= 2 /\ j >= 2) T ->
  trace_cost_fold (c1::A) (c2::B) T = trace_cost_fold A B (shift_trace_11 T).
Proof.
  induction T as [| [i j] rest IH]; intros A B c1 c2 Hge2.
  - reflexivity.
  - rewrite Forall_cons_iff in Hge2. destruct Hge2 as [[Hi Hj] Hrest].
    assert (Enot11: (i =? 1) && (j =? 1) = false).
    { destruct (i =? 1) eqn:Ei; [apply Nat.eqb_eq in Ei; lia | reflexivity]. }
    simpl shift_trace_11. rewrite Enot11.

    rewrite trace_cost_fold_cons.
    rewrite trace_cost_fold_cons.

    (* The key: nth (i-1) (c1::A) = nth (i-2) A when i >= 2 *)
    destruct i as [| [| i']]; [lia | lia |].
    destruct j as [| [| j']]; [lia | lia |].
    (* Now i = S (S i'), j = S (S j') *)
    simpl Nat.sub. simpl nth.
    replace (i' - 0) with i' by lia.
    replace (j' - 0) with j' by lia.

    f_equal.
    apply IH. exact Hrest.
Qed.

(** Change cost decomposition for shift_trace_11 - requires NoDup *)
Lemma change_cost_shift_11 : forall T A B c1 c2,
  has_pair_11 T = true ->
  NoDup (touched_in_A T) ->
  NoDup (touched_in_B T) ->
  Forall (fun '(i, j) => i >= 1 /\ j >= 1) T ->
  trace_cost_fold (c1::A) (c2::B) T =
  subst_cost c1 c2 + trace_cost_fold A B (shift_trace_11 T).
Proof.
  induction T as [| [i j] rest IH]; intros A B c1 c2 H11 HnodupA HnodupB Hvalid.
  - simpl in H11. discriminate.

  - rewrite Forall_cons_iff in Hvalid. destruct Hvalid as [[Hi Hj] Hrest].
    simpl touched_in_A in HnodupA. simpl touched_in_B in HnodupB.
    inversion HnodupA as [| x xs Hnot_in_A Hnodup_restA Heq1]. subst.
    inversion HnodupB as [| y ys Hnot_in_B Hnodup_restB Heq2]. subst.

    destruct ((i =? 1) && (j =? 1)) eqn:E11.
    + (* (i, j) = (1, 1) *)
      apply andb_prop in E11. destruct E11 as [Ei Ej].
      apply Nat.eqb_eq in Ei. apply Nat.eqb_eq in Ej. subst i j.
      simpl shift_trace_11.

      (* All pairs in rest have i >= 2 and j >= 2 because NoDup excludes 1 *)
      assert (H_rest_ge2: Forall (fun '(i', j') => i' >= 2 /\ j' >= 2) rest).
      { rewrite Forall_forall. intros [i' j'] Hin.
        assert (Hne1_A: i' <> 1).
        { intro Heq. subst i'. apply Hnot_in_A.
          apply in_pair_in_A with j'. exact Hin. }
        assert (Hne1_B: j' <> 1).
        { intro Heq. subst j'. apply Hnot_in_B.
          apply in_pair_in_B with i'. exact Hin. }
        rewrite Forall_forall in Hrest. specialize (Hrest (i', j') Hin).
        destruct Hrest as [Hi_ge1 Hj_ge1].
        lia. }

      rewrite trace_cost_fold_cons.
      simpl Nat.sub. simpl nth.

      (* Use the helper lemma for the rest *)
      rewrite trace_cost_fold_shift_all_ge2 by exact H_rest_ge2.
      lia.

    + (* (i, j) ≠ (1, 1), so (1,1) must be in rest *)
      assert (H11_rest: has_pair_11 rest = true).
      { unfold has_pair_11 in H11. simpl existsb in H11.
        unfold has_pair_11. rewrite E11 in H11. simpl in H11. exact H11. }

      assert (Hi_neq1: i <> 1).
      { intro Heq. subst i.
        apply Hnot_in_A. apply has_pair_11_in_A. exact H11_rest. }

      assert (Hj_neq1: j <> 1).
      { intro Heq. subst j.
        apply Hnot_in_B. apply has_pair_11_in_B. exact H11_rest. }

      assert (Hige2: i >= 2) by lia.
      assert (Hjge2: j >= 2) by lia.

      simpl shift_trace_11. rewrite E11.

      rewrite trace_cost_fold_cons.
      rewrite trace_cost_fold_cons.

      (* The key: nth (i-1) (c1::A) = nth (i-2) A when i >= 2 *)
      destruct i as [| [| i']]; [lia | lia |].
      destruct j as [| [| j']]; [lia | lia |].
      simpl Nat.sub. simpl nth.
      replace (i' - 0) with i' by lia.
      replace (j' - 0) with j' by lia.

      specialize (IH A B c1 c2 H11_rest Hnodup_restA Hnodup_restB Hrest).
      rewrite IH.
      lia.
Qed.

(** Main lower bound theorem *)
(** NOTE: We need NoDup constraints on both projections.
    Without NoDup, a trace could use the same position multiple times,
    artificially reducing trace_cost below the true edit distance.

    Counterexample without NoDup:
    A = [a; b], B = [b; b], T = [(2,1); (2,2)]
    - simple_valid_trace = true
    - trace_cost = 0 (both pairs match A[1]=b to B positions)
    - But lev_distance = 1 (need to change 'a' to 'b')
    - So 0 >= 1 is FALSE! *)

Theorem trace_cost_lower_bound : forall A B T,
  simple_valid_trace (length A) (length B) T = true ->
  NoDup (touched_in_A T) ->
  NoDup (touched_in_B T) ->
  trace_monotonic T ->
  trace_cost (length A) (length B) A B T >= lev_distance A B.
Proof.
  intros A B T.
  remember (length A + length B) as n eqn:Hn.
  revert A B T Hn.
  induction n as [n IH] using lt_wf_ind.
  intros A B T Hn Hvalid HnodupA HnodupB Hmono.

  destruct A as [| c1 s1'], B as [| c2 s2'].

  - (* A = [], B = [] *)
    pose proof (valid_trace_empty_A 0 T Hvalid) as HT_nil.
    rewrite HT_nil.
    rewrite trace_cost_nil.
    rewrite lev_distance_nil_nil. lia.

  - (* A = [], B = c2::s2' *)
    pose proof (valid_trace_empty_A (length (c2 :: s2')) T Hvalid) as HT_nil.
    rewrite HT_nil.
    rewrite trace_cost_nil.
    rewrite lev_distance_nil_l. simpl. lia.

  - (* A = c1::s1', B = [] *)
    pose proof (valid_trace_empty_B (length (c1 :: s1')) T Hvalid) as HT_nil.
    rewrite HT_nil.
    rewrite trace_cost_nil.
    rewrite lev_distance_nil_r. simpl. lia.

  - (* A = c1::s1', B = c2::s2' *)
    rewrite lev_distance_cons_cons.

    (* Case analysis on whether position 1 is touched *)
    destruct (has_A1 T) eqn:E_A1.
    + (* Position 1 in A is touched *)
      destruct (has_B1 T) eqn:E_B1.
      * (* Position 1 in B is also touched *)
        destruct (has_pair_11 T) eqn:E_11.
        -- (* (1, 1) is in T - substitution case *)
           (* The trace matches position 1 to position 1 *)
           simpl length in Hvalid.
           pose proof (shift_trace_11_length T HnodupA HnodupB E_11) as Hlen_eq.
           pose proof (shift_trace_11_valid (length s1') (length s2') T HnodupA HnodupB E_11 Hvalid) as Hvalid'.
           pose proof (shift_trace_11_NoDup_A (length s1') (length s2') T Hvalid HnodupA) as HnodupA'.
           pose proof (shift_trace_11_NoDup_B (length s1') (length s2') T Hvalid HnodupB) as HnodupB'.

           (* Need bounds for change_cost_shift_11 *)
           assert (Hbounds: Forall (fun '(i, j) => i >= 1 /\ j >= 1) T).
           { unfold simple_valid_trace in Hvalid.
             rewrite forallb_forall in Hvalid.
             apply Forall_forall. intros [i j] Hin.
             specialize (Hvalid (i, j) Hin).
             (* Structure: (1 <=? i) && (i <=? S|s1'|) && (1 <=? j) && (j <=? S|s2'|) = true *)
             apply andb_prop in Hvalid. destruct Hvalid as [Hvalid1 Hj_upper].
             apply andb_prop in Hvalid1. destruct Hvalid1 as [Hvalid2 Hj_lower].
             apply andb_prop in Hvalid2. destruct Hvalid2 as [Hi_lower Hi_upper].
             apply Nat.leb_le in Hi_lower.
             apply Nat.leb_le in Hj_lower.
             split; lia. }
           pose proof (change_cost_shift_11 T s1' s2' c1 c2 E_11 HnodupA HnodupB Hbounds) as Hchange.
           unfold trace_cost_fold in Hchange.

           (* Apply IH *)
           assert (Hn' : length s1' + length s2' < n).
           { subst n. simpl. lia. }
           assert (Hvalid_ge1: forall i j, In (i, j) T -> i >= 1 /\ j >= 1).
           { intros i j Hin. apply (valid_trace_indices_ge1 (S (length s1')) (S (length s2')) T i j Hvalid Hin). }
           pose proof (shift_trace_11_monotonic T Hmono Hvalid_ge1) as Hmono'.
           specialize (IH (length s1' + length s2') Hn' s1' s2' (shift_trace_11 T)
                          eq_refl Hvalid' HnodupA' HnodupB' Hmono').
           simpl length in IH.

           (* Arithmetic conclusion *)
           (* trace_cost = subst_cost c1 c2 + trace_cost(s1', s2', shift_trace_11 T) *)
           (* >= subst_cost c1 c2 + lev_distance s1' s2' *)
           unfold min3.
           unfold trace_cost.
           rewrite touched_in_A_length, touched_in_B_length.
           simpl length.
           rewrite Hchange.

           unfold trace_cost in IH.
           rewrite touched_in_A_length, touched_in_B_length in IH.
           rewrite Hlen_eq in IH.

           (* Need: T nonempty since has_pair_11 = true *)
           assert (HT_nonempty: length T >= 1).
           { destruct T as [| p rest'].
             - simpl in E_11. discriminate.
             - simpl. lia. }

           (* Key: S|s1'| - |T| + 1 = S|s1'| - (|T| - 1) when |T| >= 1 *)
           (* And: subst_cost + (change_cost' + (|s1'| - (|T|-1)) + (|s2'| - (|T|-1))) *)
           (*    = subst_cost + change_cost' + |s1'| - |T| + 1 + |s2'| - |T| + 1 *)
           (*    = (subst_cost + change_cost') + (S|s1'| - |T|) + (S|s2'| - |T|) *)
           assert (Heq1: S (length s1') - length T = length s1' - (length T - 1)).
           { lia. }
           assert (Heq2: S (length s2') - length T = length s2' - (length T - 1)).
           { lia. }
           lia.
        -- (* (1, 1) not in T, but 1 in both touched lists - cross-matching *)
           (* With monotonicity, this case is IMPOSSIBLE!
              Cross-matching requires pairs (1, j) with j >= 2 and (i, 1) with i >= 2.
              This violates monotonicity: 1 < i should imply j < 1, but j >= 2.
              Use monotonic_cross_matching_impossible to derive contradiction. *)
           exfalso.
           apply (monotonic_cross_matching_impossible (S (length s1')) (S (length s2')) T Hvalid Hmono E_A1 E_B1 E_11).
      * (* Position 1 in B not touched - insertion needed *)
        (* Symmetric to deletion case - shift B instead of A *)
        simpl length in Hvalid.
        pose proof (NoDup_B_bound (S (length s1')) (length s2') T Hvalid E_B1 HnodupB) as Hlen_bound.
        pose proof (valid_no_B1_bounds (S (length s1')) (length s2') T Hvalid E_B1) as Hbounds.
        pose proof (change_cost_shift_B T (c1 :: s1') s2' c2 E_B1 Hbounds) as Hchange.
        pose proof (shift_trace_B_length_no_B1 T E_B1) as Hlen_eq.
        pose proof (shift_trace_B_valid (S (length s1')) (length s2') T E_B1 Hvalid) as Hvalid'.
        pose proof (shift_trace_B_NoDup_B (S (length s1')) (S (length s2')) T Hvalid HnodupB) as HnodupB'.
        pose proof (shift_trace_B_NoDup_A T HnodupA E_B1) as HnodupA'.

        (* Apply IH *)
        assert (Hn' : S (length s1') + length s2' < n).
        { subst n. simpl. lia. }
        pose proof (shift_trace_B_monotonic T Hmono) as Hmono'.
        specialize (IH (S (length s1') + length s2') Hn' (c1 :: s1') s2' (shift_trace_B T)
                       eq_refl Hvalid' HnodupA' HnodupB' Hmono').
        simpl length in IH.

        (* Arithmetic conclusion *)
        unfold min3.
        unfold trace_cost.
        rewrite touched_in_A_length, touched_in_B_length.
        simpl length.
        rewrite Hchange.

        unfold trace_cost in IH.
        rewrite touched_in_A_length, touched_in_B_length in IH.
        rewrite Hlen_eq in IH.

        (* Key: S|s2'| - |T| = 1 + (|s2'| - |T|) when |T| <= |s2'| *)
        assert (Heq: S (length s2') - length T = 1 + (length s2' - length T)).
        { lia. }
        lia.
    + (* Position 1 in A not touched - deletion needed *)
      (* Key insight: With NoDup, |T| <= |s1'| is guaranteed by NoDup_A_bound *)
      simpl length in Hvalid.
      pose proof (NoDup_A_bound (length s1') (S (length s2')) T Hvalid E_A1 HnodupA) as Hlen_bound.
      pose proof (valid_no_A1_bounds (length s1') (S (length s2')) T Hvalid E_A1) as Hbounds.
      pose proof (change_cost_shift_A T s1' (c2 :: s2') c1 E_A1 Hbounds) as Hchange.
      pose proof (shift_trace_A_length_no_A1 T E_A1) as Hlen_eq.
      pose proof (shift_trace_A_valid (length s1') (S (length s2')) T E_A1 Hvalid) as Hvalid'.
      pose proof (shift_trace_A_NoDup_A (S (length s1')) (S (length s2')) T Hvalid HnodupA) as HnodupA'.
      pose proof (shift_trace_A_NoDup_B T HnodupB E_A1) as HnodupB'.

      (* Apply IH *)
      assert (Hn' : length s1' + S (length s2') < n).
      { subst n. simpl. lia. }
      pose proof (shift_trace_A_monotonic T Hmono) as Hmono'.
      specialize (IH (length s1' + S (length s2')) Hn' s1' (c2 :: s2') (shift_trace_A T)
                     eq_refl Hvalid' HnodupA' HnodupB' Hmono').
      simpl length in IH.

      (* Arithmetic conclusion *)
      unfold min3.
      unfold trace_cost.
      rewrite touched_in_A_length, touched_in_B_length.
      simpl length.
      rewrite Hchange.

      unfold trace_cost in IH.
      rewrite touched_in_A_length, touched_in_B_length in IH.
      rewrite Hlen_eq in IH.

      (* Key: S|s1'| - |T| = 1 + (|s1'| - |T|) when |T| <= |s1'| *)
      assert (Heq: S (length s1') - length T = 1 + (length s1' - length T)).
      { lia. }
      lia.
Qed.

(** After proving trace_cost_lower_bound, the main theorem follows: *)
(** trace_cost (optimal_trace_rel A B) = lev_distance A B (already proven)
    forall T valid, trace_cost T >= lev_distance A B
    Therefore: trace_cost (optimal_trace_rel A B) <= trace_cost T for all valid T *)

Print Assumptions trace_cost_lower_bound.
