(** * Main Lower Bound Theorem

    This module provides the main lower bound theorem proving that any valid trace
    with NoDup and monotonicity constraints has cost >= lev_distance.

    Part of: Liblevenshtein.Core

    Decomposed from: TraceLowerBound.v (lines 1997-2195)
*)

From Stdlib Require Import String List Arith Ascii Bool Nat Lia Wf_nat.
Import ListNotations.

From Liblevenshtein.Core Require Import Core.Definitions.
From Liblevenshtein.Core Require Import Core.LevDistance.
From Liblevenshtein.Core Require Import Core.MinLemmas.
From Liblevenshtein.Core Require Import LowerBound.Definitions.
From Liblevenshtein.Core Require Import LowerBound.HasPredicates.
From Liblevenshtein.Core Require Import LowerBound.ShiftTrace11.
From Liblevenshtein.Core Require Import LowerBound.ShiftTraceA.
From Liblevenshtein.Core Require Import LowerBound.ShiftTraceB.
From Liblevenshtein.Core Require Import LowerBound.BoundHelpers.
From Liblevenshtein.Core Require Import LowerBound.PigeonholeBounds.
From Liblevenshtein.Core Require Import LowerBound.NoDupPreservation.
From Liblevenshtein.Core Require Import LowerBound.ShiftTrace11Lemmas.
From Liblevenshtein.Core Require Import LowerBound.MonotonicityLemmas.
From Liblevenshtein.Core Require Import LowerBound.TraceCostFold.

(** * Main Lower Bound Theorem *)

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

           assert (Heq1: S (length s1') - length T = length s1' - (length T - 1)).
           { lia. }
           assert (Heq2: S (length s2') - length T = length s2' - (length T - 1)).
           { lia. }
           lia.
        -- (* (1, 1) not in T, but 1 in both touched lists - cross-matching *)
           (* With monotonicity, this case is IMPOSSIBLE! *)
           exfalso.
           apply (monotonic_cross_matching_impossible (S (length s1')) (S (length s2')) T Hvalid Hmono E_A1 E_B1 E_11).
      * (* Position 1 in B not touched - insertion needed *)
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

        assert (Heq: S (length s2') - length T = 1 + (length s2' - length T)).
        { lia. }
        lia.
    + (* Position 1 in A not touched - deletion needed *)
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

      assert (Heq: S (length s1') - length T = 1 + (length s1' - length T)).
      { lia. }
      lia.
Qed.

(** After proving trace_cost_lower_bound, the main theorem follows: *)
(** trace_cost (optimal_trace_rel A B) = lev_distance A B (already proven)
    forall T valid, trace_cost T >= lev_distance A B
    Therefore: trace_cost (optimal_trace_rel A B) <= trace_cost T for all valid T *)

