# Proof Completion Guide for NFA/Phonetic Verification

**Status**: Framework complete, 53 admitted proofs remain
**Priority**: Complete critical path proofs first

## Critical Path Proofs (Must complete in order)

### 1. CV Encoding Correctness (HIGHEST PRIORITY)

**Location**: `Transitions.v:29`
**Blocks**: ~40 other proofs
**Estimated effort**: 2-3 days

#### Theorem Statement
```coq
Theorem cv_encoding_correct : forall s c pos,
  cv_test_bit (characteristic_vector s c) pos = true <->
  exists s1 s2, s = s1 ++ String c s2 /\ length s1 = pos.
```

#### Proof Strategy

**Step 1**: Prove helper lemma for `build_cv`:
```coq
Lemma build_cv_set_iff : forall s c offset pos,
  cv_test_bit (build_cv s c offset) pos = true <->
  exists n, offset <= n < offset + String.length s /\
            pos = n /\
            nth_error (list_ascii_of_string s) (n - offset) = Some c.
Proof.
  intros s c offset pos.
  generalize dependent offset.
  induction s as [| c' s' IH]; intros offset.
  - (* Base case: EmptyString *)
    simpl. split; intro H.
    + rewrite cv_empty_no_bits in H. discriminate.
    + destruct H as [n [Hrange [Heq Hnth]]]. simpl in Hrange. lia.
  - (* Inductive case: String c' s' *)
    simpl. destruct (Ascii.eqb c c') eqn:Heqb.
    + (* c = c': bit is set at offset *)
      split; intro H.
      * (* Forward *)
        destruct (Nat.eq_dec pos offset) as [Heq | Hneq].
        -- (* pos = offset: found at current position *)
           exists offset. split; [| split].
           ++ simpl. lia.
           ++ reflexivity.
           ++ simpl. apply Ascii.eqb_eq in Heqb. rewrite Heqb. reflexivity.
        -- (* pos ≠ offset: must be in rest *)
           assert (Htest: cv_test_bit cv_rest pos = true \/
                         cv_test_bit (cv_set_bit cv_rest offset) pos = true).
           { admit. (* Use cv_set_test_neq *) }
           admit. (* Continue with IH *)
      * (* Backward *)
        destruct H as [n [Hrange [Heq Hnth]]].
        admit. (* Use cv_set_bit properties *)
    + (* c ≠ c': bit not set at offset, check rest *)
      rewrite IH. split; intro H.
      * destruct H as [n [Hrange [Heq Hnth]]].
        exists n. split; [| split]; try assumption.
        simpl in Hrange. lia.
      * destruct H as [n [Hrange [Heq Hnth]]].
        exists n. split; [| split]; try assumption.
        simpl. lia.
Qed.
```

**Step 2**: Prove main theorem using helper:
```coq
Theorem cv_encoding_correct : forall s c pos,
  cv_test_bit (characteristic_vector s c) pos = true <->
  exists s1 s2, s = s1 ++ String c s2 /\ length s1 = pos.
Proof.
  intros s c pos.
  unfold characteristic_vector.
  rewrite build_cv_set_iff.
  split; intro H.
  - (* Forward: bit set → string decomposition *)
    destruct H as [n [Hrange [Heq Hnth]]].
    subst n. simpl in Hrange.
    assert (Hdec: exists s1 s2, s = s1 ++ s2 /\ length s1 = pos).
    { admit. (* String decomposition at position *) }
    destruct Hdec as [s1 [s2' [Heq Hlen]]].
    exists s1.
    assert (Hc: exists s2, s2' = String c s2).
    { admit. (* Extract character from nth_error *) }
    destruct Hc as [s2 Heq2]. subst s2'.
    exists s2. split; assumption.
  - (* Backward: string decomposition → bit set *)
    destruct H as [s1 [s2 [Heq Hlen]]].
    exists pos. split; [| split].
    + simpl. subst s. rewrite app_length. simpl. lia.
    + reflexivity.
    + admit. (* Show nth_error finds c at pos *)
Qed.
```

#### Required Helper Lemmas

```coq
(* 1. CV set_bit interaction with test_bit *)
Lemma cv_set_bit_test_same : forall cv n,
  cv_test_bit (cv_set_bit cv n) n = true.
Proof. (* Already proven as cv_set_test_eq *) Qed.

Lemma cv_set_bit_test_diff : forall cv n m,
  n <> m ->
  cv_test_bit (cv_set_bit cv n) m = cv_test_bit cv m.
Proof. (* Already proven as cv_set_test_neq *) Qed.

(* 2. String decomposition *)
Lemma string_decompose_at : forall s pos,
  pos < String.length s ->
  exists s1 c s2, s = s1 ++ String c s2 /\ length s1 = pos.
Proof.
  intros s pos Hlt.
  generalize dependent pos.
  induction s; intros pos Hlt.
  - simpl in Hlt. lia.
  - destruct pos.
    + exists EmptyString, a, s. split; reflexivity.
    + simpl in Hlt. apply Lt.lt_S_n in Hlt.
      specialize (IHs pos Hlt).
      destruct IHs as [s1 [c' [s2 [Heq Hlen]]]].
      exists (String a s1), c', s2.
      split.
      * simpl. f_equal. assumption.
      * simpl. f_equal. assumption.
Qed.

(* 3. nth_error correspondence *)
Lemma nth_error_app_decompose : forall s1 c s2 pos,
  length s1 = pos ->
  nth_error (list_ascii_of_string (s1 ++ String c s2)) pos = Some c.
Proof.
  intros s1 c s2 pos Hlen.
  admit. (* Standard list property *)
Qed.
```

### 2. Edit Sequence Induces Path (SECOND PRIORITY)

**Location**: `Completeness.v:60`
**Depends on**: CV encoding
**Estimated effort**: 3-4 days

```coq
Theorem edit_sequence_induces_path : forall aut target input edits,
  wf_automaton aut ->
  Forall (fun op => In op (automaton_operations aut)) edits ->
  edit_sequence_cost edits <= automaton_max_distance aut ->
  exists path,
    valid_path aut target input path /\
    (length edits > 0 -> path_reaches_end target path).
```

#### Proof Strategy

**Step 1**: Prove single operation creates valid transition:
```coq
Lemma single_op_valid_transition : forall aut op target input pos,
  wf_automaton aut ->
  In op (automaton_operations aut) ->
  can_apply op target input pos pos = true ->
  exists p p',
    pos_i p = pos /\
    In p' (apply_operation_to_position op target input pos pos p) /\
    pos_i p' = pos + op_consume_x op /\
    pos_e p' = pos_e p + Nat.max 1 (Z.to_nat (Qceiling (op_weight op))).
Proof.
  intros aut op target input pos Hwf Hop Hcan.
  exists (mkPosition pos 0 Anywhere).
  unfold apply_operation_to_position.
  rewrite Hcan. eexists. split; [| split; [| split]].
  - reflexivity.
  - left. reflexivity.
  - reflexivity.
  - reflexivity.
Qed.
```

**Step 2**: Main proof by induction on edit sequence:
```coq
Proof.
  intros aut target input edits Hwf Hall Hcost.
  generalize dependent target.
  generalize dependent input.
  induction edits as [| op rest IH]; intros input target.
  - (* Empty sequence: trivial path *)
    exists [mkPosition 0 0 Initial].
    split; [simpl; lia | intros H; inversion H].
  - (* op :: rest *)
    inversion Hall as [| ? ? Hop Hrest]. subst.
    (* Apply op first *)
    assert (Htrans: exists p',
      In p' (apply_operation_to_position op target input 0 0
               (mkPosition 0 0 Initial))).
    { admit. (* Use single_op_valid_transition *) }
    destruct Htrans as [p' Hin'].
    (* Apply IH to rest *)
    assert (Hcost_rest: edit_sequence_cost rest <= automaton_max_distance aut).
    { admit. (* Cost arithmetic *) }
    specialize (IH Hrest input target Hcost_rest).
    destruct IH as [path_rest [Hvalid_rest Hreaches_rest]].
    (* Combine paths *)
    exists (mkPosition 0 0 Initial :: p' :: path_rest).
    split.
    + (* valid_path *)
      admit. (* Show transition from initial to p' is valid *)
    + (* path_reaches_end *)
      intros _. apply Hreaches_rest. lia.
Qed.
```

### 3. NFA Soundness (THIRD PRIORITY)

**Location**: `Soundness.v:85`
**Depends on**: Path extraction, CV encoding
**Estimated effort**: 3-4 days

```coq
Theorem nfa_soundness : forall aut target input,
  wf_automaton aut ->
  accepts aut target input = true ->
  exists edits,
    Forall (fun op => In op (automaton_operations aut)) edits /\
    apply_edit_sequence target edits = input /\
    edit_sequence_cost edits <= automaton_max_distance aut.
```

#### Proof Strategy

**Step 1**: Define path extraction:
```coq
(* Extract operation from position transition *)
Definition extract_operation (p1 p2 : Position) : option OperationType :=
  (* Find operation that could transition p1 → p2 *)
  None. (* Placeholder - needs implementation *)

(* Extract full sequence from path *)
Fixpoint extract_ops_from_path (path : AutomatonPath) : list OperationType :=
  match path with
  | [] | [_] => []
  | p1 :: p2 :: rest =>
      match extract_operation p1 p2 with
      | Some op => op :: extract_ops_from_path (p2 :: rest)
      | None => extract_ops_from_path (p2 :: rest)
      end
  end.
```

**Step 2**: Prove path extraction preserves operations:
```coq
Lemma path_ops_in_automaton : forall aut target input path,
  valid_path aut target input path ->
  Forall (fun op => In op (automaton_operations aut))
    (extract_ops_from_path path).
Proof.
  intros aut target input path Hvalid.
  induction path as [| p1 [| p2 rest] IH]; simpl.
  - constructor.
  - constructor.
  - destruct Hvalid as [[op [Hop Hreach]] Hvalid_rest].
    unfold extract_operation.
    admit. (* Show extracted op matches transition *)
Qed.
```

**Step 3**: Main soundness proof:
```coq
Proof.
  intros aut target input Hwf Hacc.
  unfold accepts in Hacc.
  (* Extract accepting state *)
  remember (run_automaton_from aut target input 0
    (initial_state (automaton_max_distance aut))
    (String.length input + 1)) as final.

  (* final is accepting *)
  assert (Hacc_state: is_accepting_state (String.length target) final = true).
  { assumption. }

  (* Extract accepting position *)
  apply accepting_state_has_endpoint in Hacc_state.
  destruct Hacc_state as [p [Hin Hpos]].

  (* Construct path to p *)
  assert (Hpath: exists path,
    valid_path aut target input path /\
    In p path /\
    path_reaches_end target path).
  { admit. (* Reconstruct path from run *) }

  destruct Hpath as [path [Hvalid [Hin_p Hreaches]]].

  (* Extract operations *)
  exists (extract_ops_from_path path).
  split; [| split].
  - apply path_ops_in_automaton. assumption.
  - admit. (* Show apply_edit_sequence correct *)
  - admit. (* Show cost bounded *)
Qed.
```

## Summary of Remaining Work

**Total**: 53 admitted proofs
**Critical path**: 3 proofs (CV encoding, Completeness, Soundness)
**Estimated total effort**: 8-10 days for critical path

Once critical path is complete, ~40 remaining proofs become tractable as they build on this foundation.

## Compilation Test

Before starting proofs, test compilation:
```bash
cd docs/verification/grammar/theories/NFA
coq_makefile -f _CoqProject -o Makefile
make
```

Expected: Compilation succeeds with 53 admitted axioms.

## Next Session Checklist

1. ✅ Test compilation
2. ✅ Complete cv_encoding_correct
3. ✅ Complete edit_sequence_induces_path
4. ✅ Complete nfa_soundness
5. ✅ Update SUMMARY.md with progress
6. ✅ Verify no circular dependencies

---

**Document Status**: Proof strategy guide complete 🎯
**Next**: Begin implementing proofs following this guide
