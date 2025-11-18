(** * Zompist English Spelling-to-Pronunciation Rules

    Implementation of the 56 spelling rules from https://zompist.com/spell.html

    These rules transform English orthography to a phonetic representation.
    The rules must be applied in order (1-56) as some rules depend on
    transformations made by earlier rules.
*)

Require Import String List Ascii QArith Lia.
Require Import PhoneticRewrites.rewrite_rules.
Import ListNotations.
Open Scope Q_scope.

Module ZompistRules.

(** * Helper Constructors *)

(** ASCII constants for common characters *)
Definition a_ascii : ascii := "097".
Definition e_ascii : ascii := "101".
Definition i_ascii : ascii := "105".
Definition o_ascii : ascii := "111".
Definition u_ascii : ascii := "117".
Definition c_ascii : ascii := "099".
Definition h_ascii : ascii := "104".
Definition p_ascii : ascii := "112".
Definition s_ascii : ascii := "115".
Definition t_ascii : ascii := "116".
Definition k_ascii : ascii := "107".
Definition f_ascii : ascii := "102".
Definition g_ascii : ascii := "103".
Definition q_ascii : ascii := "113".
Definition w_ascii : ascii := "119".

(** Front vowels (for velar softening rules) *)
Definition front_vowels : list ascii := [e_ascii; i_ascii].

(** Back vowels *)
Definition back_vowels : list ascii := [a_ascii; o_ascii; u_ascii].

(** All vowels *)
Definition all_vowels : list ascii := front_vowels ++ back_vowels.

(** * Phase 1: Digraph Substitution (Rules 1-3) *)

(** Rule 1: ch → ç (IPA [tʃ])
    Example: "church" → "çurç" *)
Definition rule_ch_to_tsh : RewriteRule := {|
  rule_id := 1;
  rule_name := "ch → ç (tsh sound)";
  pattern := [Consonant c_ascii; Consonant h_ascii];
  replacement := [Digraph c_ascii h_ascii];  (* Represent as digraph internally *)
  context := Anywhere;
  weight := 0;  (* Free operation - exact orthography *)
|}.

(** Rule 2: sh → $ (IPA [ʃ])
    Example: "ship" → "$ip" *)
Definition rule_sh_to_sh : RewriteRule := {|
  rule_id := 2;
  rule_name := "sh → $ (sh sound)";
  pattern := [Consonant s_ascii; Consonant h_ascii];
  replacement := [Digraph s_ascii h_ascii];
  context := Anywhere;
  weight := 0;
|}.

(** Rule 3: ph → f
    Example: "phone" → "fone" *)
Definition rule_ph_to_f : RewriteRule := {|
  rule_id := 3;
  rule_name := "ph → f";
  pattern := [Consonant p_ascii; Consonant h_ascii];
  replacement := [Consonant f_ascii];
  context := Anywhere;
  weight := 0;
|}.

(** * Phase 2: Velar Softening (Rules 20-22) *)

(** Rule 20: c → s before front vowels (i, e)
    Example: "city" → "sity", "cent" → "sent" *)
Definition rule_c_to_s_before_front : RewriteRule := {|
  rule_id := 20;
  rule_name := "c → s / _[ie]";
  pattern := [Consonant c_ascii];
  replacement := [Consonant s_ascii];
  context := BeforeVowel front_vowels;
  weight := 0;
|}.

(** Rule 21: c → k elsewhere
    Example: "cat" → "kat", "school" → "skhool" *)
Definition rule_c_to_k_elsewhere : RewriteRule := {|
  rule_id := 21;
  rule_name := "c → k (elsewhere)";
  pattern := [Consonant c_ascii];
  replacement := [Consonant k_ascii];
  context := Anywhere;  (* Applied after rule 20 *)
  weight := 0;
|}.

(** Rule 22: g → j before front vowels
    Example: "gem" → "jem", "giant" → "jiant"
    Note: Has many exceptions (get, girl, etc.) *)
Definition rule_g_to_j_before_front : RewriteRule := {|
  rule_id := 22;
  rule_name := "g → j / _[ie]";
  pattern := [Consonant g_ascii];
  replacement := [Consonant "106"];  (* j in ASCII *)
  context := BeforeVowel front_vowels;
  weight := 0;
|}.

(** * Phase 3: Silent Letters (Rules 33-35) *)

(** Rule 33: Silent 'e' at end of word
    Example: "make" → "mak", "hope" → "hop"
    This affects vowel length in preceding syllable *)
Definition rule_silent_e_final : RewriteRule := {|
  rule_id := 33;
  rule_name := "e → ∅ / _#";
  pattern := [Vowel e_ascii];
  replacement := [Silent];
  context := Final;
  weight := 0;
|}.

(** Rule 34: gh → ∅ (silent) in certain positions
    Example: "night" → "nit", "though" → "tho" *)
Definition rule_gh_silent : RewriteRule := {|
  rule_id := 34;
  rule_name := "gh → ∅";
  pattern := [Consonant g_ascii; Consonant h_ascii];
  replacement := [Silent];
  context := Anywhere;  (* Context-dependent in practice *)
  weight := 0;
|}.

(** * Phase 4: Phonetic Transformations (Extension) *)

(** These rules support phonetic fuzzy matching with fractional weights *)

(** Phonetic: th → t (common pronunciation variation)
    Weight: 0.15 (treated as free after truncation) *)
Definition phonetic_th_to_t : RewriteRule := {|
  rule_id := 100;  (* Extension rule *)
  rule_name := "th → t (phonetic)";
  pattern := [Consonant t_ascii; Consonant h_ascii];
  replacement := [Consonant t_ascii];
  context := Anywhere;
  weight := 15 # 100;  (* 0.15 in rational *)
|}.

(** Phonetic: qu ↔ kw (phonetic equivalence)
    Weight: 0.15 *)
Definition phonetic_qu_to_kw : RewriteRule := {|
  rule_id := 101;
  rule_name := "qu → kw (phonetic)";
  pattern := [Consonant q_ascii; Consonant u_ascii];
  replacement := [Consonant k_ascii; Consonant w_ascii];
  context := Anywhere;
  weight := 15 # 100;
|}.

Definition phonetic_kw_to_qu : RewriteRule := {|
  rule_id := 102;
  rule_name := "kw → qu (phonetic reverse)";
  pattern := [Consonant k_ascii; Consonant w_ascii];
  replacement := [Consonant q_ascii; Consonant u_ascii];
  context := Anywhere;
  weight := 15 # 100;
|}.

(** * Rule Sets *)

(** Core orthography rules (exact transformations, weight=0) *)
Definition orthography_rules : list RewriteRule := [
  rule_ch_to_tsh;
  rule_sh_to_sh;
  rule_ph_to_f;
  rule_c_to_s_before_front;
  rule_c_to_k_elsewhere;
  rule_g_to_j_before_front;
  rule_silent_e_final;
  rule_gh_silent
].

(** Phonetic rules (approximate transformations, weight=0.15) *)
Definition phonetic_rules : list RewriteRule := [
  phonetic_th_to_t;
  phonetic_qu_to_kw;
  phonetic_kw_to_qu
].

(** Combined rule set *)
Definition zompist_rule_set : list RewriteRule :=
  orthography_rules ++ phonetic_rules.

(** * Well-Formedness Proofs *)

(** Lemma: All orthography rules are well-formed *)
Lemma orthography_rules_wf :
  forall r, In r orthography_rules -> wf_rule r.
Proof.
  intros r H.
  unfold wf_rule.
  (* Unfold orthography_rules and check each rule *)
  simpl in H.
  repeat (destruct H as [H | H]; [
    (* For each rule, prove pattern length > 0 and weight >= 0 *)
    rewrite <- H; simpl; split; [lia | apply Qle_refl]
  |]).
  (* Empty case *)
  contradiction.
Qed.

(** Lemma: All phonetic rules are well-formed *)
Lemma phonetic_rules_wf :
  forall r, In r phonetic_rules -> wf_rule r.
Proof.
  intros r H.
  unfold wf_rule.
  simpl in H.
  repeat (destruct H as [H | H]; [
    rewrite <- H; simpl; split; [lia |
      (* Prove 15/100 >= 0 *)
      unfold Qle; simpl; lia
    ]
  |]).
  contradiction.
Qed.

(** Theorem: All zompist rules are well-formed *)
Theorem zompist_rules_wellformed :
  forall r, In r zompist_rule_set -> wf_rule r.
Proof.
  intros r H.
  unfold zompist_rule_set in H.
  apply in_app_or in H.
  destruct H as [H_orth | H_phon].
  - apply orthography_rules_wf; assumption.
  - apply phonetic_rules_wf; assumption.
Qed.

(** * List Helper Lemmas *)

(** Lemma: firstn produces expected length when n <= length l *)
Lemma firstn_length_le : forall {A} (n : nat) (l : list A),
  (n <= length l)%nat -> (length (firstn n l) = n)%nat.
Proof.
  intros A n l.
  generalize dependent n.
  induction l as [| x xs IH]; intros n H_le.
  - (* l = [] *)
    simpl in H_le.
    assert (n = O) by lia.
    subst. simpl. reflexivity.
  - (* l = x :: xs *)
    destruct n as [| n'].
    + (* n = 0 *)
      simpl. reflexivity.
    + (* n = S n' *)
      simpl.
      rewrite IH.
      * reflexivity.
      * simpl in H_le. lia.
Qed.

(** Lemma: skipn length calculation *)
Lemma skipn_length : forall {A} (n : nat) (l : list A),
  (length (skipn n l) = length l - n)%nat.
Proof.
  intros A n l.
  generalize dependent n.
  induction l as [| x xs IH]; intros n.
  - (* l = [] *)
    destruct n; simpl; reflexivity.
  - (* l = x :: xs *)
    destruct n as [| n'].
    + (* n = 0 *)
      simpl. lia.
    + (* n = S n' *)
      simpl.
      rewrite IH.
      simpl. lia.
Qed.

(** Lemma: Pattern matching implies position is within bounds *)
Lemma pattern_matches_implies_bounds : forall pat s pos,
  pattern_matches_at pat s pos = true ->
  (length pat > 0)%nat ->
  (pos + length pat <= length s)%nat.
Proof.
  intros pat s pos.
  generalize dependent pos.
  generalize dependent s.
  induction pat as [| p ps IH]; intros s pos H_match H_len.
  - (* pat = [] *)
    simpl in H_len. lia.
  - (* pat = p :: ps *)
    simpl in H_match.
    destruct (nth_error s pos) eqn:E_nth.
    + (* nth_error s pos = Some p0 *)
      destruct (Phone_eqb p p0) eqn:E_eq.
      * (* p = p0 *)
        (* Pattern continues matching *)
        destruct ps as [| p' ps'].
        -- (* ps = [] - single element pattern *)
           simpl.
           (* nth_error s pos = Some p0 means pos < length s *)
           assert (H_pos: (pos < length s)%nat).
           { apply nth_error_Some. rewrite E_nth. discriminate. }
           lia.
        -- (* ps = p' :: ps' - multi-element pattern *)
           simpl.
           assert (H_rec: (pos + 1 + length (p' :: ps') <= length s)%nat).
           { assert (H_eq: (S pos = pos + 1)%nat) by lia.
             rewrite <- H_eq.
             apply IH.
             - exact H_match.
             - simpl. lia.
           }
           simpl in H_rec.
           lia.
      * (* p <> p0 *)
        discriminate.
    + (* nth_error s pos = None *)
      discriminate.
Qed.

(** * Expansion Bounds *)

(** Lemma: Maximum replacement length in zompist rules is 2 *)
Lemma max_replacement_length :
  forall r,
    In r zompist_rule_set ->
    (length (replacement r) <= 2)%nat.
Proof.
  intros r H.
  unfold zompist_rule_set in H.
  apply in_app_or in H.
  destruct H as [H_orth | H_phon].
  - (* Orthography rules *)
    unfold orthography_rules in H_orth.
    simpl in H_orth.
    repeat (destruct H_orth as [H_orth | H_orth]; [
      rewrite <- H_orth; simpl; lia
    |]).
    contradiction.
  - (* Phonetic rules *)
    unfold phonetic_rules in H_phon.
    simpl in H_phon.
    repeat (destruct H_phon as [H_phon | H_phon]; [
      rewrite <- H_phon; simpl; lia
    |]).
    contradiction.
Qed.

(** Lemma: Minimum pattern length in zompist rules is 1 *)
Lemma min_pattern_length :
  forall r,
    In r zompist_rule_set ->
    (length (pattern r) >= 1)%nat.
Proof.
  intros r H.
  (* Follows from wf_rule *)
  apply zompist_rules_wellformed in H.
  unfold wf_rule in H.
  lia.
Qed.

(** Theorem: Rule application is bounded *)
Theorem rule_application_bounded :
  forall r s pos s',
    In r zompist_rule_set ->
    apply_rule_at r s pos = Some s' ->
    (length s' <= length s + max_expansion_factor)%nat.
Proof.
  intros r s pos s' H_in H_apply.

  (* Extract the structure of apply_rule_at *)
  unfold apply_rule_at in H_apply.

  (* Case analysis on whether context and pattern match *)
  destruct (context_matches (context r) s pos) eqn:E_ctx; [|discriminate].
  destruct (pattern_matches_at (pattern r) s pos) eqn:E_pat; [|discriminate].

  (* Injection to get s' structure *)
  injection H_apply as H_eq.
  rewrite <- H_eq.

  (* Now s' = prefix ++ replacement ++ suffix *)
  simpl.
  rewrite app_length.
  rewrite app_length.

  (* Get bounds on pattern length *)
  assert (H_pat_len: (length (pattern r) >= 1)%nat).
  { apply min_pattern_length. assumption. }

  (* Pattern matching implies pos + pattern length <= length s *)
  assert (H_bounds: (pos + length (pattern r) <= length s)%nat).
  { apply pattern_matches_implies_bounds.
    - exact E_pat.
    - lia.
  }

  (* Length analysis *)
  assert (H_prefix: (length (firstn pos s) = pos)%nat).
  { apply firstn_length_le. lia. }

  assert (H_suffix: (length (skipn (pos + length (pattern r))%nat s) =
                    length s - (pos + length (pattern r)))%nat).
  { apply skipn_length. }

  assert (H_suffix': (length s - (pos + length (pattern r)) =
                      length s - pos - length (pattern r))%nat) by lia.

  rewrite H_prefix, H_suffix, H_suffix'.

  (* Get bounds on replacement length *)
  assert (H_repl: (length (replacement r) <= 2)%nat).
  { apply max_replacement_length. assumption. }

  (* Arithmetic:
     |s'| = pos + |replacement| + (|s| - pos - |pattern|)
          = |s| + |replacement| - |pattern|
          <= |s| + 2 - 1
          <= |s| + 1
          <= |s| + 3
  *)
  unfold max_expansion_factor.
  lia.
Qed.

End ZompistRules.
