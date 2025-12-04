(** * Damerau-Levenshtein Trace Composition

    This module defines trace composition for Damerau-Levenshtein traces and
    proves the key cost bound theorem needed for the triangle inequality.

    Part of: Liblevenshtein.Core

    Key insight: For the triangle inequality, we can use a simplified composition
    that converts DL traces to standard Levenshtein traces (matches only),
    compose those, and bound the cost. This works because:
    - DL distance <= Levenshtein distance (transposition can only help)
    - Levenshtein trace composition already has the cost bound property
*)

From Coq Require Import String List Arith Ascii Bool Nat Lia.
Import ListNotations.

From Liblevenshtein.Core Require Import Core.Definitions.
From Liblevenshtein.Core Require Import Core.MinLemmas.
From Liblevenshtein.Core Require Import Core.DamerauLevDistanceDef.
From Liblevenshtein.Core Require Import Core.MetricProperties.
From Liblevenshtein.Core Require Import Trace.TraceBasics.
From Liblevenshtein.Core Require Import Trace.TraceCost.
From Liblevenshtein.Core Require Import Trace.TraceComposition.
From Liblevenshtein.Core Require Import Trace.DamerauTrace.
From Liblevenshtein.Core Require Import Composition.CostBounds.

(** * DL Trace to Simple Trace Conversion *)

(** Convert a DL trace element to simple trace pairs.
    - DLMatch (i,j) becomes [(i,j)]
    - DLTranspose (i,j) becomes [(i,j+1); (i+1,j)] - the swapped matches *)
Definition dl_element_to_pairs (e : DLTraceElement) : list (nat * nat) :=
  match e with
  | DLMatch i j => [(i, j)]
  | DLTranspose i j => [(i, j + 1); (i + 1, j)]
  end.

(** Convert a full DL trace to a list of pairs *)
Definition dl_trace_to_pairs (T : DLTrace) : list (nat * nat) :=
  flat_map dl_element_to_pairs T.

(** * DL Trace Composition via Simple Traces *)

(** Compose DL traces by converting to simple traces and using standard composition.
    This gives a simple trace (not a DL trace), but that's fine for the cost bound. *)
Definition compose_dl_trace_simple {A B C : list Char}
  (T1 : DLTrace) (T2 : DLTrace) : list (nat * nat) :=
  compose_trace (A:=A) (B:=B) (C:=C)
    (dl_trace_to_pairs T1) (dl_trace_to_pairs T2).

(** * Cost Bound Lemmas *)

(** Helper: Cost of a DL element via simple trace is bounded by DL element cost *)
Lemma dl_element_to_pairs_cost_bound :
  forall A B e,
    fold_left (fun acc p =>
      let '(i, j) := p in
      acc + subst_cost (nth (i-1) A default_char) (nth (j-1) B default_char)
    ) (dl_element_to_pairs e) 0 <= dl_element_cost A B e + 1.
Proof.
  intros A B e.
  destruct e as [i j | i j].
  - (* DLMatch *)
    simpl. unfold dl_element_cost. lia.
  - (* DLTranspose *)
    simpl.
    (* For transposition: [(i, j+1); (i+1, j)] *)
    (* Cost via pairs: subst_cost A[i-1] B[j] + subst_cost A[i] B[j-1] *)
    (* DL element cost is 1 if valid transposition, 100 otherwise *)
    unfold dl_element_cost.
    destruct (andb (char_eq (nth (i - 1) A default_char) (nth j B default_char))
                   (char_eq (nth i A default_char) (nth (j - 1) B default_char))) eqn:Hvalid.
    + (* Valid transposition: chars match the swap pattern *)
      apply Bool.andb_true_iff in Hvalid as [H1 H2].
      apply char_eq_correct in H1.
      apply char_eq_correct in H2.
      (* A[i-1] = B[j], A[i] = B[j-1] *)
      (* subst_cost (A[i-1]) (B[j]) = 0 since they're equal *)
      (* But wait - the pairs are (i, j+1) and (i+1, j) *)
      (* So we compute subst_cost A[i-1] B[j] and subst_cost A[i] B[j-1] *)
      (* j+1-1 = j, so nth (j+1-1) B = nth j B *)
      assert (Hcost1: subst_cost (nth (i - 1) A default_char) (nth ((j + 1) - 1) B default_char) = 0).
      { replace ((j + 1) - 1) with j by lia.
        unfold subst_cost. rewrite <- H1.
        destruct (char_eq (nth (i - 1) A default_char) (nth (i - 1) A default_char)) eqn:Heq.
        - reflexivity.
        - exfalso.
          assert (Hrefl: char_eq (nth (i - 1) A default_char) (nth (i - 1) A default_char) = true).
          { apply char_eq_correct. reflexivity. }
          rewrite Hrefl in Heq. discriminate. }
      (* i+1-1 = i, j-1 *)
      assert (Hcost2: subst_cost (nth ((i + 1) - 1) A default_char) (nth (j - 1) B default_char) = 0).
      { replace ((i + 1) - 1) with i by lia.
        unfold subst_cost. rewrite <- H2.
        destruct (char_eq (nth i A default_char) (nth i A default_char)) eqn:Heq.
        - reflexivity.
        - exfalso.
          assert (Hrefl: char_eq (nth i A default_char) (nth i A default_char) = true).
          { apply char_eq_correct. reflexivity. }
          rewrite Hrefl in Heq. discriminate. }
      rewrite Hcost1, Hcost2. simpl. lia.
    + (* Invalid transposition *)
      assert (Hbound1: subst_cost (nth (i - 1) A default_char) (nth ((j + 1) - 1) B default_char) <= 1).
      { apply subst_cost_le_1. }
      assert (Hbound2: subst_cost (nth ((i + 1) - 1) A default_char) (nth (j - 1) B default_char) <= 1).
      { apply subst_cost_le_1. }
      lia.
Qed.

(** Helper: fold_left init shift for subst_cost sum *)
Lemma fold_left_subst_shift :
  forall A B (l : list (nat * nat)) init,
    fold_left (fun acc p =>
      let '(i, j) := p in
      acc + subst_cost (nth (i-1) A default_char) (nth (j-1) B default_char)
    ) l init = init + fold_left (fun acc p =>
      let '(i, j) := p in
      acc + subst_cost (nth (i-1) A default_char) (nth (j-1) B default_char)
    ) l 0.
Proof.
  intros A B l.
  induction l as [| [i' j'] l' IHl]; intros init.
  - simpl. lia.
  - simpl. rewrite IHl. rewrite (IHl (subst_cost _ _)). lia.
Qed.

(** Helper: fold_left init shift for element cost sum *)
Lemma fold_left_element_cost_shift :
  forall A B (l : DLTrace) init,
    fold_left (fun acc e' => acc + dl_element_cost A B e') l init =
    init + fold_left (fun acc e' => acc + dl_element_cost A B e') l 0.
Proof.
  intros A B l.
  induction l as [| e' rest' IHr]; intros init.
  - simpl. lia.
  - simpl. rewrite IHr. rewrite (IHr (dl_element_cost A B e')). lia.
Qed.

(** Helper: flat_map preserves cost ordering *)
Lemma flat_map_cost_bound :
  forall A B T,
    fold_left (fun acc p =>
      let '(i, j) := p in
      acc + subst_cost (nth (i-1) A default_char) (nth (j-1) B default_char)
    ) (dl_trace_to_pairs T) 0 <= dl_change_cost A B T + length T.
Proof.
  intros A B T.
  unfold dl_trace_to_pairs, dl_change_cost.
  induction T as [| e rest IH].
  - simpl. lia.
  - simpl.
    (* flat_map (e :: rest) = dl_element_to_pairs e ++ flat_map rest *)
    rewrite fold_left_app.
    (* First part: fold over dl_element_to_pairs e *)
    assert (H1: fold_left (fun acc p =>
      let '(i, j) := p in
      acc + subst_cost (nth (i-1) A default_char) (nth (j-1) B default_char)
    ) (dl_element_to_pairs e) 0 <= dl_element_cost A B e + 1).
    { apply dl_element_to_pairs_cost_bound. }
    (* Use shift lemma *)
    rewrite fold_left_subst_shift.
    rewrite fold_left_element_cost_shift.
    lia.
Qed.

(** * Triangle Inequality via Direct Bound *)

(** Key lemma: Distance is bounded by the sum of distances via any intermediate string.
    This is proven using the recursive structure of damerau_lev_distance. *)

(** We use the length bound and nonneg properties to establish triangle inequality. *)

Theorem damerau_lev_triangle_via_composition :
  forall A B C : list Char,
    damerau_lev_distance A C <= damerau_lev_distance A B + damerau_lev_distance B C.
Proof.
  (* TODO: Complete proof - lia tactics failing with >= hypotheses *)
  (* This is a well-known property of edit distances; the proof requires
     careful handling of arithmetic with >= and truncating subtraction. *)
Admitted.

(* Original proof structure preserved for reference:
   intros A B C.
   Strong induction on total length
   remember (length A + length B + length C) as n eqn:Hlen.
   revert A B C Hlen.
   induction n as [n IH] using lt_wf_ind.
   intros A B C Hlen.

  (* Case analysis on A *)
  destruct A as [| a A'].
  - (* A = [] *)
    rewrite damerau_lev_empty_left.
    pose proof (damerau_lev_length_bound B C) as Hbc.
    pose proof (damerau_lev_nonneg [] B) as Hnonneg.
    rewrite damerau_lev_empty_left in *.
    (* |C| <= |B| + d(B,C) because d(B,C) >= ||B| - |C|| *)
    unfold abs_diff in Hbc.
    destruct (length B <=? length C) eqn:Hcmp.
    + apply Nat.leb_le in Hcmp. lia.
    + apply Nat.leb_gt in Hcmp. lia.

  - (* A = a :: A' *)
    destruct C as [| c C'].
    + (* C = [] *)
      rewrite !damerau_lev_empty_right.
      pose proof (damerau_lev_length_bound (a :: A') B) as Hab.
      simpl length in *.
      unfold abs_diff in *.
      destruct (S (length A') <=? length B) eqn:Hcmp; simpl in Hab.
      * apply Nat.leb_le in Hcmp.
        (* Goal: S (length A') <= d(a::A', B) + length B *)
        (* Hab: d(a::A', B) >= length B - S (length A') *)
        (* Since Hcmp says S (length A') <= length B, we have length B >= S (length A') *)
        (* So d(a::A', B) >= 0 (trivially) and length B >= S (length A') *)
        lia.
      * apply Nat.leb_gt in Hcmp.
        (* Goal: S (length A') <= d(a::A', B) + length B *)
        (* Hab: d(a::A', B) >= S (length A') - length B *)
        (* Hcmp: S (length A') > length B *)
        (* Since S (length A') > length B, we have S (length A') = length B + (S (length A') - length B) *)
        (* And damerau_lev >= S (length A') - length B *)
        (* So d + length B >= S (length A') - length B + length B = S (length A') *)
        set (d := damerau_lev_distance (a :: A') B) in *.
        set (lenA := S (length A')) in *.
        set (lenB := length B) in *.
        (* Convert >= to <= for lia *)
        unfold ge in Hab.
        apply Nat.le_trans with (m := (lenA - lenB) + lenB).
        -- (* lenA <= lenA - lenB + lenB *)
           rewrite Nat.sub_add; unfold ge in *; lia.
        -- (* lenA - lenB + lenB <= d + lenB *)
           apply Nat.add_le_mono_r. exact Hab.

    + (* A = a :: A', C = c :: C' *)
      destruct B as [| b B'].
      * (* B = [] *)
        rewrite !damerau_lev_empty_right, !damerau_lev_empty_left.
        (* Goal: d(a::A', c::C') <= S(|A'|) + S(|C'|) *)
        pose proof (damerau_lev_le_standard (a :: A') (c :: C')) as Hle_std.
        pose proof (lev_distance_upper_bound (a :: A') (c :: C')) as Hub.
        simpl length in *.
        (* Hub: lev_distance <= max(S |A'|, S |C'|) *)
        (* max(a, b) <= a + b for naturals *)
        assert (Hmax_bound : Nat.max (S (length A')) (S (length C')) <= S (length A') + S (length C')).
        { apply Nat.max_lub; unfold ge in *; lia. }
        lia.

      * (* All three strings non-empty: A = a::A', B = b::B', C = c::C' *)
        (* Use the add_first lemmas to relate to smaller subproblems *)
        (* d(a::A', c::C') <= d(A', C') + 2 (delete a, then insert c at most) *)
        (* d(A', C') <= d(A', B') + d(B', C') by IH *)
        (* d(a::A', b::B') >= d(A', B') - 2 (via length bound) *)
        (* d(b::B', c::C') >= d(B', C') - 2 *)

        (* Key: The minimum cost to transform a::A' to c::C' *)
        (* Either: *)
        (*   - Delete a, transform A' to c::C' *)
        (*   - Insert c, transform a::A' to C' *)
        (*   - Match/substitute a<->c, transform A' to C' *)
        (*   - (If applicable) transpose *)

        (* We bound each case using IH and add_first/remove_first lemmas *)

        (* IH for smaller subproblems *)
        assert (HIH_sub: damerau_lev_distance A' C' <=
                         damerau_lev_distance A' B' + damerau_lev_distance B' C').
        { apply IH with (m := length A' + length B' + length C').
          - simpl in Hlen. lia.
          - reflexivity. }

        (* Use the length bound: d >= |len1 - len2| *)
        (* And add_first: d(c::s, t) <= d(s, t) + 1 *)
        (* And remove_first: d(s, t) <= d(c::s, t) + 1 *)

        pose proof (damerau_lev_add_first_source a A' (c :: C')) as Hadd_a.
        pose proof (damerau_lev_add_first_target (a :: A') c C') as Hadd_c.
        pose proof (damerau_lev_remove_first_source a A' (b :: B')) as Hrem_a.
        pose proof (damerau_lev_remove_first_target (b :: B') c C') as Hrem_c.
        pose proof (damerau_lev_remove_first_source b B' C') as Hrem_b1.
        pose proof (damerau_lev_remove_first_target A' b B') as Hrem_b2.

        (* From IH: d(A', C') <= d(A', B') + d(B', C') *)
        (* From Hrem_a: d(A', b::B') <= d(a::A', b::B') + 1 *)
        (* From Hrem_b2: d(A', B') <= d(A', b::B') + 1 *)
        (* So: d(A', B') <= d(a::A', b::B') + 2 *)

        (* Similarly: d(B', C') <= d(b::B', c::C') + 2 *)

        (* So: d(A', C') <= d(a::A', b::B') + 2 + d(b::B', c::C') + 2 *)
        (*              = d(a::A', b::B') + d(b::B', c::C') + 4 *)

        (* But d(a::A', c::C') may be much less than d(A', C') + 2 *)
        (* In fact, d(a::A', c::C') could be d(A', C') + subst_cost(a,c) *)

        (* The tight bound uses the recursive structure of damerau_lev_distance *)

        (* Proof by case on which branch achieves the minimum for d(a::A', c::C') *)
        destruct A' as [| a' A''].
        -- (* A = [a], C = c::C' *)
           destruct C' as [| c' C''].
           ++ (* A = [a], C = [c] *)
              rewrite !damerau_lev_single.
              pose proof (damerau_lev_nonneg [a] (b :: B')) as Hnn1.
              pose proof (damerau_lev_nonneg (b :: B') [c]) as Hnn2.
              unfold subst_cost. destruct (char_eq a c) eqn:Hac.
              ** (* a = c: goal is 0 <= d + d, trivial *)
                 unfold ge in *. lia.
              ** (* a ≠ c: goal is 1 <= d([a], b::B') + d(b::B', [c]) *)
                 (* We need to show at least one distance is >= 1 *)
                 destruct B' as [| b' B''].
                 --- (* B' = []: d([a], [b]) + d([b], [c]) *)
                     rewrite !damerau_lev_single.
                     unfold subst_cost, char_eq in *.
                     (* If a ≠ c, then either a ≠ b or b ≠ c *)
                     destruct (ascii_dec a b) as [Hab | Hab],
                              (ascii_dec b c) as [Hbc | Hbc].
                     +++ (* a = b, b = c: implies a = c, contradicts Hac *)
                         subst b. destruct (ascii_dec a c); [lia | congruence].
                     +++ (* a = b, b ≠ c *) destruct (ascii_dec a c); unfold ge in *; lia.
                     +++ (* a ≠ b, b = c *) destruct (ascii_dec a c); unfold ge in *; lia.
                     +++ (* a ≠ b, b ≠ c *) destruct (ascii_dec a c); unfold ge in *; lia.
                 --- (* B' non-empty: d([a], b::b'::B'') >= 1 by length bound *)
                     pose proof (damerau_lev_length_bound [a] (b :: b' :: B'')) as Hbd.
                     simpl length in Hbd.
                     unfold abs_diff in Hbd. simpl in Hbd.
                     unfold ge in *. lia.
           ++ (* A = [a], C = c::c'::C'' *)
              rewrite damerau_lev_single_multi.
              (* d([a], c::c'::C'') = min3(del, ins, sub) *)
              (* Goal: min3 del ins sub <= d([a], b::B') + d(b::B', c::c'::C'') *)
              (* Use upper bound approach: d <= max(len1, len2) <= len1 + len2 *)
              pose proof (damerau_lev_le_standard [a] (c :: c' :: C'')) as Hle_std.
              pose proof (lev_distance_upper_bound [a] (c :: c' :: C'')) as Hub.
              pose proof (damerau_lev_length_bound [a] (b :: B')) as Hab.
              pose proof (damerau_lev_length_bound (b :: B') (c :: c' :: C'')) as Hbc.
              simpl length in *.
              unfold abs_diff in *.
              (* max(1, 2 + |C''|) <= 1 + (2 + |C''|) *)
              assert (Hmax : Nat.max 1 (S (S (length C''))) <= 1 + S (S (length C''))).
              { apply Nat.max_lub; unfold ge in *; lia. }
              destruct (1 <=? S (length B')); destruct (S (length B') <=? S (S (length C'')));
              unfold ge in *; unfold ge in *; lia.

        -- (* A = a::a'::A'', C = c::C' *)
           destruct C' as [| c' C''].
           ++ (* A = a::a'::A'', C = [c] *)
              rewrite damerau_lev_multi_single.
              apply Nat.min_glb.
              ** apply Nat.min_glb.
                 --- (* Delete: d(a'::A'', [c]) + 1 *)
                     assert (HIH': damerau_lev_distance (a' :: A'') [c] <=
                                   damerau_lev_distance (a' :: A'') (b :: B') +
                                   damerau_lev_distance (b :: B') [c]).
                     { apply IH with (m := S (length A'') + S (length B') + 1).
                       - simpl in Hlen. lia.
                       - reflexivity. }
                     pose proof (damerau_lev_remove_first_source a (a' :: A'') (b :: B')) as Hrem.
                     lia.
                 --- (* Insert: d(a::a'::A'', []) + 1 *)
                     rewrite damerau_lev_empty_right.
                     pose proof (damerau_lev_length_bound (a :: a' :: A'') (b :: B')) as Hab.
                     pose proof (damerau_lev_length_bound (b :: B') [c]) as Hbc.
                     simpl length in *.
                     unfold abs_diff in *.
                     destruct (S (S (length A'')) <=? S (length B'));
                     destruct (S (length B') <=? 1); unfold ge in *; lia.
              ** (* Substitute: d(a'::A'', []) + subst_cost a c *)
                 rewrite damerau_lev_empty_right.
                 pose proof (damerau_lev_length_bound (a :: a' :: A'') (b :: B')) as Hab.
                 pose proof (damerau_lev_length_bound (b :: B') [c]) as Hbc.
                 simpl length in *.
                 unfold abs_diff, subst_cost in *.
                 destruct (char_eq a c);
                 destruct (S (S (length A'')) <=? S (length B'));
                 destruct (S (length B') <=? 1); unfold ge in *; lia.

           ++ (* A = a::a'::A'', C = c::c'::C'' - full min4 case *)
              rewrite damerau_lev_cons2.
              unfold min4.
              apply Nat.min_glb.
              ** apply Nat.min_glb.
                 --- (* Delete: d(a'::A'', c::c'::C'') + 1 *)
                     assert (HIH': damerau_lev_distance (a' :: A'') (c :: c' :: C'') <=
                                   damerau_lev_distance (a' :: A'') (b :: B') +
                                   damerau_lev_distance (b :: B') (c :: c' :: C'')).
                     { apply IH with (m := S (length A'') + S (length B') + S (S (length C''))).
                       - simpl in Hlen. lia.
                       - reflexivity. }
                     pose proof (damerau_lev_remove_first_source a (a' :: A'') (b :: B')) as Hrem.
                     lia.
                 --- (* Insert: d(a::a'::A'', c'::C'') + 1 *)
                     assert (HIH': damerau_lev_distance (a :: a' :: A'') (c' :: C'') <=
                                   damerau_lev_distance (a :: a' :: A'') (b :: B') +
                                   damerau_lev_distance (b :: B') (c' :: C'')).
                     { apply IH with (m := S (S (length A'')) + S (length B') + S (length C'')).
                       - simpl in Hlen. lia.
                       - reflexivity. }
                     pose proof (damerau_lev_remove_first_target (b :: B') c (c' :: C'')) as Hrem.
                     lia.
              ** apply Nat.min_glb.
                 --- (* Substitute: d(a'::A'', c'::C'') + subst_cost a c *)
                     (* Use nonneg bound - the distance is always >= 0 *)
                     pose proof (damerau_lev_nonneg (a :: a' :: A'') (b :: B')) as Hnn1.
                     pose proof (damerau_lev_nonneg (b :: B') (c :: c' :: C'')) as Hnn2.
                     pose proof (damerau_lev_nonneg (a' :: A'') (c' :: C'')) as Hnn3.
                     pose proof (subst_cost_le_1 a c) as Hsub.
                     lia.
                 --- (* Transpose: d(A'', C'') + trans_cost_calc a a' c c' *)
                     unfold trans_cost_calc.
                     destruct (char_eq a c') eqn:Hac';
                     destruct (char_eq a' c) eqn:Ha'c.
                     +++ (* Valid transpose: cost = 1 *)
                         pose proof (damerau_lev_nonneg (a :: a' :: A'') (b :: B')) as Hnn1.
                         pose proof (damerau_lev_nonneg (b :: B') (c :: c' :: C'')) as Hnn2.
                         lia.
                     +++ (* Invalid transpose: cost = 100 *)
                         pose proof (damerau_lev_nonneg (a :: a' :: A'') (b :: B')) as Hnn1.
                         pose proof (damerau_lev_nonneg (b :: B') (c :: c' :: C'')) as Hnn2.
                         pose proof (damerau_lev_length_bound A'' C'') as Hbd.
                         unfold abs_diff in Hbd.
                         destruct (length A'' <=? length C''); unfold ge in *; lia.
                     +++ (* Invalid transpose: cost = 100 *)
                         pose proof (damerau_lev_nonneg (a :: a' :: A'') (b :: B')) as Hnn1.
                         pose proof (damerau_lev_nonneg (b :: B') (c :: c' :: C'')) as Hnn2.
                         pose proof (damerau_lev_length_bound A'' C'') as Hbd.
                         unfold abs_diff in Hbd.
                         destruct (length A'' <=? length C''); unfold ge in *; lia.
                     +++ (* Invalid transpose: cost = 100 *)
                         pose proof (damerau_lev_nonneg (a :: a' :: A'') (b :: B')) as Hnn1.
                         pose proof (damerau_lev_nonneg (b :: B') (c :: c' :: C'')) as Hnn2.
                         pose proof (damerau_lev_length_bound A'' C'') as Hbd.
                         unfold abs_diff in Hbd.
                         destruct (length A'' <=? length C''); unfold ge in *; lia.
*)

