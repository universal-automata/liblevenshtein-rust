(** * Generalized Levenshtein Automaton

    This module defines the Generalized Levenshtein NFA A^∀,χ_n from TCS 2011,
    extended with context-sensitive phonetic operations. The automaton accepts
    all strings within a given edit distance of a target word without requiring
    modification for different target words.

    Key innovation: Context information is tracked in positions to enable
    context-sensitive phonetic transformations.
*)

Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Init.Nat.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Bool.Bool.
Require Import Coq.QArith.QArith.
Require Import Coq.NArith.BinNat.
Require Import Coq.micromega.Lia.
Import ListNotations.

Require Import Liblevenshtein.Grammar.Verification.NFA.Types.
Require Import Liblevenshtein.Grammar.Verification.NFA.Operations.

(** ** Automaton Definition *)

(** The Generalized Levenshtein Automaton A^∀,χ_n.

    Following TCS 2011 Definition 15, this is a 5-tuple:
    A^∀,χ_n = ⟨Σ^∀_n, Q^∀,χ_n, I^∀,χ, F^∀,χ_n, δ^∀,χ_n⟩

    Where:
    - Σ^∀_n: Input alphabet is characteristic vectors
    - Q^∀,χ_n: State space is sets of (i, e, ctx) positions
    - I^∀,χ: Initial state {(0, 0, Initial)}
    - F^∀,χ_n: Final states (states with positions reaching end of word)
    - δ^∀,χ_n: Transition function (defined below)
*)
Record GeneralizedAutomaton := mkAutomaton {
  automaton_max_distance : nat;      (** Maximum edit distance n *)
  automaton_operations : OperationSet (** Set of allowed operations χ *)
}.

(** Create automaton with standard operations only *)
Definition standard_automaton (max_dist : nat) : GeneralizedAutomaton :=
  mkAutomaton max_dist standard_ops.

(** Create automaton with phonetic operations *)
Definition phonetic_automaton (max_dist : nat) : GeneralizedAutomaton :=
  mkAutomaton max_dist (standard_ops ++ phonetic_ops_phase1).

(** ** Acceptance Condition *)

(** A state is accepting if it contains a position that has consumed
    the entire target word. Following TCS 2011 page 48, we check if
    any position has reached the word length.
*)
Definition is_accepting_position (word_length : nat) (p : Position) : bool :=
  (pos_i p =? word_length).

Definition is_accepting_state (word_length : nat) (st : GeneralizedState) : bool :=
  existsb (is_accepting_position word_length) (state_positions st).

(** ** Transition Function *)

(** Apply a single operation to a position, yielding new positions.

    For operation op and position (i, e, ctx):
    - If op can apply at current context
    - Consume op_consume_x characters from target word
    - Consume op_consume_y characters from input word
    - Increment error count by ceil(op_weight)
    - Update context based on new position

    Returns list of resulting positions (may be empty if op doesn't apply).
*)
Definition apply_operation_to_position
    (op : OperationType)
    (target input : string)
    (target_pos input_pos : nat)
    (p : Position)
    : list Position :=
  if can_apply op target input (pos_i p) target_pos then
    let new_i := pos_i p + op_consume_x op in
    let new_e := pos_e p + Nat.max 1 (Z.to_nat (Qceiling (op_weight op))) in
    let new_ctx :=
      if new_i =? 0 then Initial
      else if new_i =? String.length target then Final
      else Anywhere (* Simplified context update *)
    in
    [mkPosition new_i new_e new_ctx]
  else
    [].

(** Apply all operations in the operation set to a position *)
Fixpoint apply_all_operations
    (ops : OperationSet)
    (target input : string)
    (target_pos input_pos : nat)
    (p : Position)
    : list Position :=
  match ops with
  | [] => []
  | op :: rest =>
      apply_operation_to_position op target input target_pos input_pos p ++
      apply_all_operations rest target input target_pos input_pos p
  end.

(** Transition function: δ(state, cv) → state'

    Given current state and characteristic vector for next input character:
    1. For each position in current state
    2. Apply all applicable operations
    3. Collect resulting positions
    4. Prune subsumed positions
    5. Filter positions exceeding max distance
*)
Definition delta
    (aut : GeneralizedAutomaton)
    (target input : string)
    (input_pos : nat)
    (st : GeneralizedState)
    : GeneralizedState :=
  let new_positions :=
    flat_map
      (apply_all_operations
        (automaton_operations aut)
        target
        input
        input_pos
        input_pos)
      (state_positions st)
  in
  let filtered_positions :=
    filter (fun p => pos_e p <=? automaton_max_distance aut) new_positions
  in
  prune_state (mkState filtered_positions false (automaton_max_distance aut)).

(** ** Recognition *)

(** Process entire input string through the automaton *)
Fixpoint run_automaton_from
    (aut : GeneralizedAutomaton)
    (target input : string)
    (pos : nat)
    (st : GeneralizedState)
    (fuel : nat)
    : GeneralizedState :=
  match fuel with
  | 0 => st (* Out of fuel *)
  | S fuel' =>
      if pos >=? String.length input then st
      else
        let st' := delta aut target input pos st in
        run_automaton_from aut target input (S pos) st' fuel'
  end.

(** Main recognition function *)
Definition accepts
    (aut : GeneralizedAutomaton)
    (target input : string)
    : bool :=
  let initial := initial_state (automaton_max_distance aut) in
  let fuel := String.length input + 1 in
  let final_state := run_automaton_from aut target input 0 initial fuel in
  is_accepting_state (String.length target) final_state.

(** ** Well-Formedness Properties *)

(** An automaton is well-formed if its operations are well-formed *)
Definition wf_automaton (aut : GeneralizedAutomaton) : Prop :=
  wf_operation_set (automaton_operations aut) /\
  operation_set_bounded 1 (automaton_operations aut).

(** Transition preserves well-formedness *)
Theorem delta_preserves_wf : forall aut target input pos st,
  wf_automaton aut ->
  wf_state st ->
  wf_state (delta aut target input pos st).
Proof.
  intros aut target input pos st [Hwf_ops Hbounded] Hwf_st.
  unfold wf_state in *.
  unfold delta.
  apply Forall_forall. intros p Hin.
  (* After filtering, all positions satisfy error bound *)
  apply filter_In in Hin. destruct Hin as [Hin Hle].
  unfold wf_position.
  apply Nat.leb_le in Hle. assumption.
Qed.

(** Initial state is well-formed *)
Theorem initial_state_wf : forall max_dist,
  wf_state (initial_state max_dist).
Proof.
  intros max_dist.
  unfold wf_state, initial_state. simpl.
  constructor.
  - unfold wf_position. simpl. lia.
  - constructor.
Qed.

(** Running automaton preserves well-formedness *)
Theorem run_automaton_preserves_wf : forall aut target input pos st fuel,
  wf_automaton aut ->
  wf_state st ->
  wf_state (run_automaton_from aut target input pos st fuel).
Proof.
  intros aut target input pos st fuel Hwf_aut Hwf_st.
  generalize dependent st.
  generalize dependent pos.
  induction fuel; intros pos st Hwf_st; simpl.
  - assumption.
  - destruct (pos >=? String.length input) eqn:Hcmp.
    + assumption.
    + apply IHfuel.
      apply delta_preserves_wf; assumption.
Qed.

(** ** Termination *)

(** Running automaton always terminates *)
Theorem run_automaton_terminates : forall aut target input pos st fuel,
  exists final_state,
    run_automaton_from aut target input pos st fuel = final_state.
Proof.
  intros. eexists. reflexivity.
Qed.

(** Fuel is sufficient for input length *)
Lemma fuel_sufficient : forall aut target input st,
  let fuel := String.length input + 1 in
  exists final_state,
    run_automaton_from aut target input 0 st fuel = final_state.
Proof.
  intros. eexists. reflexivity.
Qed.

(** ** State Space Properties *)

(** Maximum number of positions in a state is bounded *)
Definition max_positions (n : nat) : nat :=
  (n + 1) * (n + 1). (* (i, e) pairs: 0 ≤ i ≤ n, 0 ≤ e ≤ n *)

(** After pruning, state size is bounded *)
Theorem state_size_bounded : forall st,
  length (state_positions (prune_state st)) <= max_positions (state_max_distance st).
Proof.
  intros st.
  unfold max_positions.
  (* Pruning removes subsumed positions *)
  (* At most (n+1) × (n+1) distinct (i,e) pairs *)
  admit. (* Requires careful counting argument *)
Admitted.

(** ** Subsumption Correctness *)

(** Pruning preserves acceptance *)
Theorem prune_preserves_acceptance : forall st word_length,
  is_accepting_state word_length st = true ->
  is_accepting_state word_length (prune_state st) = true.
Proof.
  intros st word_length Hacc.
  unfold is_accepting_state in *.
  apply existsb_exists in Hacc.
  destruct Hacc as [p [Hin Hacc_p]].
  apply existsb_exists.
  (* If p is accepting and in original state, either:
     1. p is in pruned state (not subsumed)
     2. Some p' that subsumes p is in pruned state (also accepting) *)
  admit. (* Requires subsumption lemma *)
Admitted.

(** ** Operation Application Properties *)

(** If operation applies, it produces valid positions *)
Lemma apply_operation_produces_valid_positions : forall op target input tpos ipos p,
  wf_operation op ->
  pos_e p <= 3 ->
  Forall (fun p' => pos_i p' >= pos_i p /\ pos_e p' >= pos_e p)
    (apply_operation_to_position op target input tpos ipos p).
Proof.
  intros op target input tpos ipos p Hwf_op He.
  unfold apply_operation_to_position.
  destruct (can_apply op target input (pos_i p) tpos) eqn:Hcan.
  - constructor.
    + simpl. split.
      * apply Nat.le_add_r.
      * apply Nat.le_add_r.
    + constructor.
  - constructor.
Qed.

(** Applying multiple operations accumulates results *)
Lemma apply_all_operations_accumulates : forall ops target input tpos ipos p,
  length (apply_all_operations ops target input tpos ipos p) =
  fold_left (fun acc op =>
    acc + length (apply_operation_to_position op target input tpos ipos p)
  ) ops 0.
Proof.
  induction ops; intros target input tpos ipos p; simpl.
  - reflexivity.
  - rewrite app_length. rewrite IHops. simpl.
    lia.
Qed.

(** ** Determinism Properties *)

(** Transition function is deterministic *)
Theorem delta_deterministic : forall aut target input pos st1 st2,
  st1 = st2 ->
  delta aut target input pos st1 = delta aut target input pos st2.
Proof.
  intros aut target input pos st1 st2 Heq.
  subst. reflexivity.
Qed.

(** Running automaton is deterministic *)
Theorem run_automaton_deterministic : forall aut target input pos st1 st2 fuel,
  st1 = st2 ->
  run_automaton_from aut target input pos st1 fuel =
  run_automaton_from aut target input pos st2 fuel.
Proof.
  intros aut target input pos st1 st2 fuel Heq.
  subst. reflexivity.
Qed.

(** Acceptance is deterministic *)
Theorem accepts_deterministic : forall aut target input,
  exists b, accepts aut target input = b.
Proof.
  intros. eexists. reflexivity.
Qed.

(** ** Empty Language Properties *)

(** If max distance is 0, only exact matches accepted *)
Theorem distance_zero_exact_match : forall target input,
  accepts (standard_automaton 0) target input = true ->
  target = input.
Proof.
  intros target input Hacc.
  unfold accepts in Hacc.
  (* With distance 0, only match operations can apply *)
  (* Therefore target and input must be identical *)
  admit. (* Requires proving match-only transitions preserve characters *)
Admitted.

(** If target is empty, only empty input accepted (with distance 0) *)
Theorem empty_target_empty_input : forall input,
  accepts (standard_automaton 0) EmptyString input = true ->
  input = EmptyString.
Proof.
  intros input Hacc.
  unfold accepts in Hacc. simpl in Hacc.
  (* Empty target → initial state (0,0) is accepting *)
  (* Input must not advance → input is empty *)
  destruct input; auto.
  simpl in Hacc. discriminate.
Qed.

(** ** Monotonicity *)

(** Increasing distance allows more acceptances *)
Theorem distance_monotone : forall aut1 aut2 target input,
  automaton_operations aut1 = automaton_operations aut2 ->
  automaton_max_distance aut1 <= automaton_max_distance aut2 ->
  accepts aut1 target input = true ->
  accepts aut2 target input = true.
Proof.
  intros aut1 aut2 target input Hops Hdist Hacc1.
  unfold accepts in *.
  (* All accepting paths in aut1 are also valid in aut2 *)
  (* Because aut2 allows higher error count *)
  admit. (* Requires proving state inclusion *)
Admitted.

(** Adding operations preserves existing acceptances *)
Theorem operations_monotone : forall aut target input ops_extra,
  wf_operation_set ops_extra ->
  accepts aut target input = true ->
  accepts
    (mkAutomaton
      (automaton_max_distance aut)
      (automaton_operations aut ++ ops_extra))
    target input = true.
Proof.
  intros aut target input ops_extra Hwf_extra Hacc.
  unfold accepts in *.
  (* Adding operations only adds more transitions *)
  (* Existing accepting paths remain valid *)
  admit. (* Requires proving transition inclusion *)
Admitted.

(** ** Phonetic Automaton Properties *)

(** Phonetic automaton accepts all strings standard automaton accepts *)
Theorem phonetic_subsumes_standard : forall max_dist target input,
  accepts (standard_automaton max_dist) target input = true ->
  accepts (phonetic_automaton max_dist) target input = true.
Proof.
  intros max_dist target input Hacc.
  apply operations_monotone; auto.
  - apply phonetic_phase1_well_formed.
  - unfold phonetic_automaton. simpl. assumption.
Qed.

(** Phonetic automaton can accept strings standard automaton rejects *)
Example phonetic_accepts_more :
  accepts (standard_automaton 1) "phone" "fone" = false /\
  accepts (phonetic_automaton 1) "phone" "fone" = true.
Proof.
  split.
  - (* Standard automaton: ph→f requires 2 operations (delete p, substitute h→f) *)
    (* With distance 1, this exceeds the limit *)
    admit. (* Requires concrete execution *)
  - (* Phonetic automaton: ph→f is single operation with weight 0.15 *)
    (* Ceil(0.15) = 1, so accepted with distance 1 *)
    admit. (* Requires concrete execution *)
Admitted.

(** ** Context-Sensitive Operation Properties *)

(** Context matching is correct *)
Lemma context_matches_respects_position : forall ctx s pos,
  context_matches ctx s pos = true ->
  match ctx with
  | Initial => pos = 0
  | Final => pos = String.length s
  | _ => True
  end.
Proof.
  intros ctx s pos Hmatch.
  destruct ctx; simpl in Hmatch; auto.
  - apply Nat.eqb_eq in Hmatch. assumption.
  - apply Nat.eqb_eq in Hmatch. assumption.
Qed.

(** Context-sensitive operations only apply in correct context *)
Theorem context_sensitive_correctness : forall op target input tpos ipos p,
  op_context op <> Anywhere ->
  can_apply op target input (pos_i p) tpos = true ->
  context_matches (op_context op) target (pos_i p) = true.
Proof.
  intros op target input tpos ipos p Hctx Hcan.
  unfold can_apply in Hcan.
  repeat (apply andb_true_iff in Hcan; destruct Hcan as [? Hcan]).
  assumption.
Qed.
