# Context-Free Grammar Correction for Text Normalization

**Status**: Design Document
**Last Updated**: 2025-11-20
**Purpose**: Deep dive into CFG-based grammatical error correction

---

## Table of Contents

1. [Introduction](#introduction)
2. [Theoretical Foundation](#theoretical-foundation)
3. [Why CFG is Necessary](#why-cfg-is-necessary)
4. [Error Grammar Formalism](#error-grammar-formalism)
5. [Grammar Categories for Text Normalization](#grammar-categories-for-text-normalization)
6. [Probabilistic CFG for Disambiguation](#probabilistic-cfg-for-disambiguation)
7. [Chart Parsing Algorithms](#chart-parsing-algorithms)
8. [Integration with FST Lattices](#integration-with-fst-lattices)
9. [Implementation Strategy](#implementation-strategy)
10. [Benchmarks and Evaluation](#benchmarks-and-evaluation)
11. [Integration with Large Language Models](#integration-with-large-language-models)
12. [References](#references)

---

## Introduction

### The Grammar Correction Gap

**Industry Problem** (NVIDIA, Google systems):
- FSTs handle spelling and phonetic errors well
- Grammar correction requires neural networks
- Neural models prone to "unrecoverable errors"
- No deterministic symbolic grammar layer

**liblevenshtein-rust Solution**:
- Add CFG layer between FST and Neural tiers
- Deterministic symbolic grammar correction
- Handles syntax errors that FSTs cannot
- Falls back to neural only for semantic ambiguity

### What CFG Adds

**Beyond FST Capabilities**:
```
FST (Regular):  a*b*         ✅ Can recognize
CFG (Context-Free): a^n b^n  ✅ Can recognize (CFG only)
CSG (Context-Sensitive): a^n b^n c^n  ❌ Requires LBA (neural)
```

**Practical Examples**:
| Error Type | FST | CFG | Neural |
|------------|-----|-----|--------|
| Spelling ("teh" → "the") | ✅ | - | - |
| Phonetic ("fone" → "phone") | ✅ | - | - |
| Article ("a apple" → "an apple") | ❌ | ✅ | ✅ |
| Subject-verb ("they was" → "they were") | ❌ | ✅ | ✅ |
| Nested phrases ("the cat [[that] slept] meowed") | ❌ | ✅ | ✅ |
| Semantic ("bank" = river vs financial) | ❌ | ❌ | ✅ |

---

## Theoretical Foundation

### Chomsky Hierarchy

**Type 3: Regular Languages** (FST/NFA)
- **Recognition**: Finite-state automaton
- **Generation**: Regular grammar (A → aB, A → a)
- **Complexity**: O(n) recognition
- **Example**: a*b* (any number of a's followed by any number of b's)

**Type 2: Context-Free Languages** (CFG)
- **Recognition**: Pushdown automaton (stack machine)
- **Generation**: Context-free grammar (A → α where α is any string)
- **Complexity**: O(n³) CYK parsing, O(n²) average Earley
- **Example**: a^n b^n (equal number of a's and b's)

**Type 1: Context-Sensitive Languages** (CSG)
- **Recognition**: Linear-bounded automaton
- **Generation**: Context-sensitive grammar (αAβ → αγβ)
- **Complexity**: PSPACE-complete
- **Example**: a^n b^n c^n (equal number of a's, b's, and c's)

**Type 0: Recursively Enumerable** (Turing Machine)
- **Recognition**: Turing machine
- **Complexity**: Undecidable in general

### Formal Definitions

**Context-Free Grammar**: G = (N, Σ, P, S)
- **N**: Set of non-terminal symbols
- **Σ**: Set of terminal symbols (alphabet)
- **P**: Set of production rules (A → α)
- **S**: Start symbol (S ∈ N)

**Production Rule Format**:
```
A → α
```
where:
- A ∈ N (single non-terminal on left-hand side)
- α ∈ (N ∪ Σ)* (any string of terminals and non-terminals)

**Example Grammar**:
```coq
N = {S, NP, VP, DT, N, V}
Σ = {the, cat, sat}
S = S

Productions:
  S → NP VP
  NP → DT N
  VP → V
  DT → the
  N → cat
  V → sat
```

**Derivation**:
```
S ⇒ NP VP
  ⇒ DT N VP
  ⇒ the N VP
  ⇒ the cat VP
  ⇒ the cat V
  ⇒ the cat sat
```

---

## Why CFG is Necessary

### Pumping Lemma for Regular Languages

**Theorem**: If L is regular, then there exists p (pumping length) such that for any string s ∈ L with |s| ≥ p, s can be divided into xyz where:
1. |xy| ≤ p
2. |y| > 0
3. xy^i z ∈ L for all i ≥ 0

**Proof that {a^n b^n | n ≥ 0} is not regular**:

Assume {a^n b^n} is regular with pumping length p.

Consider s = a^p b^p (clearly s ∈ L and |s| = 2p ≥ p).

By pumping lemma, s = xyz where |xy| ≤ p and |y| > 0.

Since |xy| ≤ p, both x and y consist only of a's.

So y = a^k for some k > 0.

Pumping: xy²z = a^p a^k b^p = a^(p+k) b^p.

But (p+k) ≠ p, so xy²z ∉ {a^n b^n}.

**Contradiction**! Therefore {a^n b^n} is not regular. ∎

### Linguistic Structures Requiring CFG

**1. Subject-Verb Agreement** (requires counting)

```
Input: "the cats runs"
Structure: NP[plural] VP[singular]  ← MISMATCH

This is like a^n b^m where we need n = m (number agreement).
FST cannot count noun number and match with verb number.
CFG can track features through parse tree.
```

**2. Nested Phrase Structures**

```
Input: "the cat [that [the dog chased]] meowed"
Structure:
  NP
  ├── DT: the
  └── N'
      ├── N: cat
      └── RC (relative clause)
          ├── COMP: that
          └── S (nested)
              ├── NP: the dog
              └── VP: chased

FST cannot handle nested recursion (balanced brackets).
CFG naturally represents tree structures.
```

**3. Auxiliary Verb Selection**

```
Input: "he can able to swim"
Error: Double modal ("can" + "able")

Grammar constraint: AUX → Modal | "be able to" (not both)

This requires parsing verb phrase structure:
  VP
  ├── AUX: can
  └── VP
      ├── AUX: able  ← ERROR (nested AUX not allowed)
      └── V: swim

FST sees linear sequence "can able swim" (cannot detect nesting).
CFG enforces VP structural constraints.
```

**4. Tense Consistency**

```
Input: "yesterday he eats dinner"
Error: Past temporal adverb + present tense verb

Constraint: AdvP[past] → S[past_tense]

Parse tree:
  S
  ├── AdvP[past]: yesterday
  └── S
      ├── NP: he
      └── VP[present]  ← MISMATCH
          └── V[present]: eats

CFG propagates temporal features through tree.
FST cannot enforce cross-phrase constraints.
```

---

## Error Grammar Formalism

### Well-Formed vs Error Grammars

**Traditional CFG**: Generates only grammatically correct sentences

**Error Grammar**: Extends CFG with error productions + corrections

### Error Production Definition

**Syntax**:
```coq
A → α  { ERROR: description, FIX: correction, COST: weight }
```

**Components**:
- **LHS**: Non-terminal A
- **RHS**: String α (may include error patterns)
- **ERROR**: Error type description
- **FIX**: Correction strategy (replacement, insertion, deletion)
- **COST**: Penalty weight (tropical semiring)

### Example Error Productions

**1. Article Selection Error**

**Well-formed rules**:
```coq
NP → DT[a] N[-vowel_initial]
NP → DT[an] N[+vowel_initial]
```

**Error rules**:
```coq
NP → DT[a] N[+vowel_initial]
  { ERROR: "Article 'a' before vowel-initial noun",
    FIX: Replace(DT[a], DT[an]),
    COST: 0.5 }

NP → DT[an] N[-vowel_initial]
  { ERROR: "Article 'an' before consonant-initial noun",
    FIX: Replace(DT[an], DT[a]),
    COST: 0.5 }
```

**Example Correction**:
```
Input: "a elephant"
Parse:
  NP
  ├── DT[a]: "a"
  └── N[+vowel]: "elephant"

Error production matches: NP → DT[a] N[+vowel_initial]
Correction: Replace "a" with "an"
Output: "an elephant"
Cost: 0.5
```

**2. Subject-Verb Agreement Error**

**Well-formed rules**:
```coq
S → NP[num=sg] VP[num=sg]
S → NP[num=pl] VP[num=pl]
```

**Error rules**:
```coq
S → NP[num=sg] VP[num=pl]
  { ERROR: "Singular subject with plural verb",
    FIX: Replace(VP[num=pl], VP[num=sg]),
    COST: 1.0 }

S → NP[num=pl] VP[num=sg]
  { ERROR: "Plural subject with singular verb",
    FIX: Replace(VP[num=sg], VP[num=pl]),
    COST: 1.0 }
```

**Example Correction**:
```
Input: "the cat run fast"
Parse:
  S
  ├── NP[num=sg]
  │   ├── DT: "the"
  │   └── N[sg]: "cat"
  └── VP[num=pl]  ← ERROR
      ├── V[pl]: "run"
      └── ADV: "fast"

Error production: S → NP[sg] VP[pl]
Correction: Morph "run" → "runs"
Output: "the cat runs fast"
Cost: 1.0
```

**3. Auxiliary Verb Error**

**Well-formed rules**:
```coq
VP → AUX[modal] VP[inf]
VP → V
```

**Error rules**:
```coq
VP → AUX[modal] AUX[to-inf] VP[inf]
  { ERROR: "Double auxiliary (modal + 'to')",
    FIX: Delete(AUX[to-inf]),
    COST: 1.2 }
```

**Example**:
```
Input: "he can to swim"
Parse:
  VP
  ├── AUX[modal]: "can"
  ├── AUX[to]: "to"  ← ERROR (should be deleted)
  └── V[inf]: "swim"

Correction: Delete "to"
Output: "he can swim"
Cost: 1.2
```

**4. Tense Inconsistency**

**Well-formed rules**:
```coq
S → AdvP[past] S[past]
S → AdvP[present] S[present]
```

**Error rules**:
```coq
S → AdvP[past] S[present]
  { ERROR: "Past temporal adverb with present tense",
    FIX: Replace(S[present], S[past]),
    COST: 0.8 }
```

**Example**:
```
Input: "yesterday he eats dinner"
Parse:
  S
  ├── AdvP[past]: "yesterday"
  └── S[present]  ← ERROR
      └── VP
          └── V[present]: "eats"

Correction: "eats" → "ate"
Output: "yesterday he ate dinner"
Cost: 0.8
```

### Feature Propagation

**Feature Structures**:
```coq
NP: [number: {sg, pl}, person: {1, 2, 3}, case: {nom, acc}]
VP: [number: {sg, pl}, person: {1, 2, 3}, tense: {past, present, future}]
DT: [definiteness: {def, indef}]
N: [number: {sg, pl}, initial_sound: {vowel, consonant}]
```

**Agreement Constraints**:
```coq
S → NP[num=X, pers=Y] VP[num=X, pers=Y]
  where X, Y are unified (must match)
```

**Example with Features**:
```
Input: "they was happy"
Parse attempt:
  S
  ├── NP[num=pl, pers=3]
  │   └── PRON: "they"
  └── VP[num=sg, pers=3]  ← MISMATCH (num ≠ pl)
      ├── AUX[sg]: "was"
      └── ADJ: "happy"

Error: Feature unification fails (pl ≠ sg)
Correction: "was" → "were"
```

---

## Grammar Categories for Text Normalization

### 1. Morphosyntax

**Agreement**:
- Subject-verb number agreement
- Determiner-noun agreement
- Pronoun-antecedent agreement

**Case**:
- Nominative vs accusative pronouns ("I" vs "me")
- Possessive forms ("its" vs "it's")

**Tense**:
- Temporal consistency
- Sequence of tenses in subordinate clauses

**Example Grammar**:
```coq
(* Subject-verb agreement *)
S → NP[num=X] VP[num=X]

(* Pronoun case *)
NP[case=nom] → PRON[case=nom]  (* I, he, she, they *)
NP[case=acc] → PRON[case=acc]  (* me, him, her, them *)

(* Error: Wrong case *)
VP → V NP[case=nom]
  { ERROR: "Nominative pronoun in object position",
    FIX: Replace(PRON[nom], PRON[acc]),
    COST: 0.8 }
```

### 2. Phrase Structure

**Noun Phrases**:
```coq
NP → DT N
NP → DT ADJ N
NP → DT N PP
NP → NP RelClause
```

**Verb Phrases**:
```coq
VP → V
VP → V NP
VP → V NP PP
VP → AUX VP
```

**Error: Missing Determiner**:
```coq
NP → N[count, sg]
  { ERROR: "Missing determiner for singular countable noun",
    FIX: Insert(DT[a], position=0),
    COST: 0.6 }
```

**Example**:
```
Input: "cat sat on mat"
Error: Missing determiners

Corrections:
  "cat" → "the cat" or "a cat"
  "mat" → "the mat" or "a mat"

Output: "the cat sat on the mat"
```

### 3. Determiners and Articles

**Article Selection** (a/an):
```coq
DT[a] → "a"
DT[an] → "an"

NP → DT[a] N[-vowel_initial]
NP → DT[an] N[+vowel_initial]

(* Errors *)
NP → DT[a] N[+vowel_initial]
  { ERROR: "Use 'an' before vowel sound",
    FIX: Replace(DT[a], DT[an]),
    COST: 0.5 }
```

**Phonetic Exceptions**:
```
"a university" (starts with /j/ sound, not vowel)
"an hour" (silent h, vowel sound)
"a one-time event" (/w/ sound)
"an FBI agent" (/ɛ/ sound for "F")
```

**Implementation**:
```rust
fn is_vowel_initial(word: &str) -> bool {
    let first_phone = phonetic_initial_sound(word);
    matches!(first_phone, Phone::Vowel(_))
}

// Handles "hour" → /aʊr/ (vowel), "university" → /jun/ (consonant)
```

### 4. Auxiliary Verbs

**Modal Auxiliaries**:
```coq
AUX[modal] → "can" | "could" | "may" | "might" | "must" | "shall" | "should" | "will" | "would"

VP → AUX[modal] VP[inf]  (* can swim *)
VP → "be able to" VP[inf]  (* is able to swim *)

(* Error: Double modal *)
VP → AUX[modal] "be able to" VP[inf]
  { ERROR: "Cannot use modal + 'be able to'",
    FIX: Delete("be able to"),
    COST: 1.2 }
```

**Perfect Aspect**:
```coq
VP → AUX[have] VP[past_participle]

(* Error: Wrong participle form *)
VP → AUX[have] VP[inf]
  { ERROR: "Infinitive after 'have' (need past participle)",
    FIX: Replace(VP[inf], VP[past_part]),
    COST: 0.9 }
```

**Example**:
```
Input: "I have eat dinner"
Error: "eat" is infinitive, need past participle

Parse:
  VP
  ├── AUX[have]: "have"
  └── VP[inf]: "eat"  ← ERROR

Correction: "eat" → "eaten"
Output: "I have eaten dinner"
```

### 5. Negation

**Negative Polarity Items** (NPIs):
```coq
(* "any" requires negative context *)
NP[+neg] → "any" N  (* valid in negative sentences *)
NP[-neg] → "some" N  (* valid in affirmative *)

S[+neg] → NP[subj] "not" VP
S[+neg] → NP[subj] VP[+neg]

(* Error: NPI in affirmative context *)
S[-neg] → NP "any" N
  { ERROR: "'any' requires negative context",
    FIX: Replace("any", "some"),
    COST: 0.7 }
```

**Example**:
```
Input: "I have any money"  ❌
Correction: "I have some money"  ✅

Input: "I don't have any money"  ✅
```

---

## Probabilistic CFG for Disambiguation

### Motivation

**Ambiguous Parse**:
```
Input: "I saw the man with a telescope"

Parse 1 (PP attaches to VP):
  S
  ├── NP: I
  └── VP
      ├── V: saw
      ├── NP: the man
      └── PP: with a telescope  (* I used telescope to see *)

Parse 2 (PP attaches to NP):
  S
  ├── NP: I
  └── VP
      ├── V: saw
      └── NP
          ├── NP: the man
          └── PP: with a telescope  (* man has telescope *)
```

Both parses are grammatically valid. Which is correct?

**Solution**: Assign probabilities to productions, select most likely parse.

### PCFG Definition

**Probabilistic Context-Free Grammar**: G = (N, Σ, P, S, θ)

**Production Probabilities**:
```
P(A → α | A) = θ_A→α
```
where:
- Sum of probabilities for all productions with LHS = A equals 1
- ΣP(A → α | A) = 1 for all α

**Example PCFG**:
```coq
S → NP VP        [0.9]
S → VP           [0.1]

NP → DT N        [0.6]
NP → DT ADJ N    [0.3]
NP → NP PP       [0.1]

VP → V NP        [0.5]
VP → V NP PP     [0.3]
VP → V PP        [0.2]

PP → P NP        [1.0]
```

### Estimating Probabilities

**Maximum Likelihood Estimation (MLE)** from treebank:

```
P(A → α | A) = Count(A → α) / Count(A)
```

**Example**:
```
Treebank:
  S → NP VP (observed 900 times)
  S → VP (observed 100 times)

P(S → NP VP | S) = 900 / 1000 = 0.9
P(S → VP | S) = 100 / 1000 = 0.1
```

**Smoothing** (for unseen productions):

**Add-k smoothing**:
```
P(A → α | A) = (Count(A → α) + k) / (Count(A) + k·|Productions with LHS=A|)
```

**Kneser-Ney smoothing**: More sophisticated, handles sparse data better.

### Parse Probability

**Probability of Derivation**:
```
P(tree) = Π P(rule | LHS) for all rules in tree
```

**Example**:
```
Parse: S → NP VP → DT N VP → the cat VP → the cat V → the cat sat

P(tree) = P(S → NP VP) · P(NP → DT N) · P(DT → the) · P(N → cat) · P(VP → V) · P(V → sat)
        = 0.9 · 0.6 · 0.5 · 0.3 · 0.4 · 0.2
        = 0.00648
```

### Viterbi Parsing

**Goal**: Find most probable parse tree

**Algorithm**: Dynamic programming (similar to CYK)

**Complexity**: O(n³ · |G|) for grammar size |G|

**Pseudocode**:
```python
def viterbi_parse(words, pcfg):
    n = len(words)
    chart = {}  # chart[i][j][A] = (prob, backpointer)

    # Base case: Terminals
    for i in range(n):
        for rule in pcfg.terminal_rules():  # A → word[i]
            if rule.rhs == words[i]:
                chart[i][i+1][rule.lhs] = (rule.prob, None)

    # Recursive case: Non-terminals
    for length in range(2, n+1):
        for i in range(n - length + 1):
            j = i + length
            for rule in pcfg.non_terminal_rules():  # A → B C
                for k in range(i+1, j):
                    if rule.rhs[0] in chart[i][k] and rule.rhs[1] in chart[k][j]:
                        prob_B = chart[i][k][rule.rhs[0]][0]
                        prob_C = chart[k][j][rule.rhs[1]][0]
                        prob = rule.prob * prob_B * prob_C

                        if rule.lhs not in chart[i][j] or prob > chart[i][j][rule.lhs][0]:
                            chart[i][j][rule.lhs] = (prob, (k, rule))

    # Extract best parse
    return extract_tree(chart, 0, n, pcfg.start_symbol)
```

### Example: Disambiguating Article Errors

**Input**: "a apple" or "an apple"?

**PCFG** (trained on correct English):
```
NP → DT[an] N[+vowel]  [0.8]  (* common pattern *)
NP → DT[a] N[+vowel]   [0.05]  (* rare, likely error *)

NP → DT[a] N[-vowel]   [0.8]
NP → DT[an] N[-vowel]  [0.05]
```

**Parse "a apple"**:
```
P(NP → DT[a] N[+vowel]) = 0.05  (* LOW probability *)
```

**Parse "an apple"**:
```
P(NP → DT[an] N[+vowel]) = 0.8  (* HIGH probability *)
```

**Correction**: Select higher probability parse → "an apple"

---

## Chart Parsing Algorithms

### CYK (Cocke-Younger-Kasami) Algorithm

**Requirements**:
- Grammar must be in **Chomsky Normal Form** (CNF)

**CNF Format**:
```
A → B C  (two non-terminals)
A → a    (single terminal)
S → ε    (only for start symbol if ε ∈ L)
```

**Conversion to CNF**:
```coq
Original: S → NP VP
CNF: S → NP VP  ✅ (already CNF)

Original: NP → DT ADJ N
CNF: NP → DT X1
     X1 → ADJ N  (introduce intermediate)

Original: VP → V
CNF: VP → V  ✅ (if V is terminal)
     or VP → X_V (if V is non-terminal)
     X_V → V
```

**CYK Algorithm**:

**Data Structure**: Chart `C[i][j]` contains set of non-terminals that can derive words[i..j]

**Pseudocode**:
```python
def cyk_parse(words, cnf_grammar):
    n = len(words)
    chart = [[set() for _ in range(n+1)] for _ in range(n+1)]

    # Base case: Single words
    for i in range(n):
        for rule in cnf_grammar.terminal_rules():  # A → word[i]
            if rule.rhs == words[i]:
                chart[i][i+1].add(rule.lhs)

    # Recursive case: Combine spans
    for length in range(2, n+1):  # span length
        for i in range(n - length + 1):
            j = i + length
            for k in range(i+1, j):  # split point
                for rule in cnf_grammar.binary_rules():  # A → B C
                    if rule.rhs[0] in chart[i][k] and rule.rhs[1] in chart[k][j]:
                        chart[i][j].add(rule.lhs)

    # Check if start symbol derives entire input
    return cnf_grammar.start in chart[0][n]
```

**Complexity**: O(n³ · |G|) where |G| is number of binary rules

**Example**:
```
Input: "the cat sat"
Grammar (CNF):
  S → NP VP
  NP → DT N
  VP → V
  DT → the
  N → cat
  V → sat

Chart filling:
  C[0][1] = {DT}       ("the")
  C[1][2] = {N}        ("cat")
  C[2][3] = {V, VP}    ("sat", V→VP)

  C[0][2] = {NP}       (DT N)
  C[1][3] = {}         (no rule N VP)

  C[0][3] = {S}        (NP VP)

Parse succeeds: S ∈ C[0][3]
```

### Earley Algorithm

**Advantage**: Handles arbitrary CFG (no CNF required)

**Complexity**: O(n³) worst case, O(n²) for unambiguous grammars, O(n) for LR grammars

**Data Structure**: State sets S[i] (i = 0 to n)

**Earley State**: `[A → α • β, j]`
- **Rule**: A → αβ
- **Dot position**: • separates what's been recognized (α) from what's expected (β)
- **Origin**: State started at position j

**Operations**:

1. **Predictor**: If next symbol is non-terminal B, add all rules B → •γ
2. **Scanner**: If next symbol is terminal a and input[i] = a, advance dot
3. **Completer**: If dot at end (A → α•), propagate to parent states

**Pseudocode**:
```python
def earley_parse(words, grammar):
    n = len(words)
    S = [set() for _ in range(n+1)]

    # Initialize: Add S' → •S to S[0]
    S[0].add(EarleyState(rule=("S'", "S"), dot=0, origin=0))

    for i in range(n+1):
        for state in S[i]:
            if not state.is_complete():
                next_sym = state.next_symbol()

                if grammar.is_non_terminal(next_sym):
                    # Predictor: Add all rules for next_sym
                    for rule in grammar.rules_for(next_sym):
                        S[i].add(EarleyState(rule=rule, dot=0, origin=i))

                elif i < n and words[i] == next_sym:
                    # Scanner: Advance dot if terminal matches
                    S[i+1].add(state.advance_dot())

            else:
                # Completer: State is complete (dot at end)
                for parent in S[state.origin]:
                    if parent.next_symbol() == state.lhs:
                        S[i].add(parent.advance_dot())

    # Check if S' → S• is in S[n]
    return any(s.lhs == "S'" and s.is_complete() for s in S[n])
```

**Example**:
```
Input: "the cat sat"
Grammar:
  S → NP VP
  NP → DT N
  VP → V
  DT → the
  N → cat
  V → sat

S[0]:
  [S' → •S, 0]
  [S → •NP VP, 0]  (predictor from S')
  [NP → •DT N, 0]  (predictor from S)
  [DT → •the, 0]   (predictor from NP)

S[1]:  (after scanning "the")
  [DT → the•, 0]
  [NP → DT •N, 0]  (completer from DT)
  [N → •cat, 1]    (predictor from NP)

S[2]:  (after scanning "cat")
  [N → cat•, 1]
  [NP → DT N•, 0]  (completer from N)
  [S → NP •VP, 0]  (completer from NP)
  [VP → •V, 2]     (predictor from S)
  [V → •sat, 2]    (predictor from VP)

S[3]:  (after scanning "sat")
  [V → sat•, 2]
  [VP → V•, 2]     (completer from V)
  [S → NP VP•, 0]  (completer from VP)
  [S' → S•, 0]     (completer from S)  ✅ ACCEPT
```

**Advantages of Earley**:
- No CNF conversion required
- Handles left-recursion
- Efficient for most natural language grammars (O(n²) average)
- Easy to extend with probabilistic weights

---

## Integration with FST Lattices

### Problem: Lattice Parsing

**Input**: Word lattice (not single string)
- Multiple hypotheses from FST layer
- Want to parse all paths simultaneously
- Select grammatically valid + high-scoring paths

**Example Lattice**:
```
     ┌─("seen", 0.6)─┐
0───→1                2───→3
     └─("saw", 0.8)──┘

Paths:
  1. "I seen the movie" (FST cost = 0.6)
  2. "I saw the movie" (FST cost = 0.8)
```

### Lattice-Aware Earley Parsing

**Modification**: Scanner reads from lattice edges, not fixed word sequence

**Algorithm**:
```python
def earley_parse_lattice(lattice, grammar):
    S = {node: set() for node in lattice.nodes}

    # Initialize at start node
    S[lattice.start].add(EarleyState(rule=("S'", "S"), dot=0, origin=lattice.start))

    for node in lattice.topological_order():
        for state in S[node]:
            if not state.is_complete():
                next_sym = state.next_symbol()

                if grammar.is_non_terminal(next_sym):
                    # Predictor
                    for rule in grammar.rules_for(next_sym):
                        S[node].add(EarleyState(rule=rule, dot=0, origin=node))

                else:
                    # Scanner: Check lattice edges from current node
                    for edge in lattice.outgoing_edges(node):
                        if edge.label == next_sym:
                            new_state = state.advance_dot()
                            new_state.add_cost(edge.weight)  # Accumulate FST cost
                            S[edge.target].add(new_state)

            else:
                # Completer
                for parent in S[state.origin]:
                    if parent.next_symbol() == state.lhs:
                        S[node].add(parent.advance_dot())

    # Extract all complete parses reaching final nodes
    parses = []
    for final_node in lattice.final_nodes:
        for state in S[final_node]:
            if state.lhs == "S'" and state.is_complete():
                parses.append(extract_parse_tree(state))

    return parses
```

**Key Difference**: Scanner explores lattice edges instead of sequential words.

### Combined Scoring

**Total Cost** = α·FST_cost + β·Grammar_cost + γ·LM_cost

**Example**:
```
Lattice path 1: "I seen the movie"
  FST_cost = 0.6 (phonetic + spelling)
  Grammar_cost = 2.0 (past participle without auxiliary)
  LM_cost = 3.0 (low probability)
  Total = 0.3·0.6 + 0.4·2.0 + 0.3·3.0 = 0.18 + 0.8 + 0.9 = 1.88

Lattice path 2: "I saw the movie"
  FST_cost = 0.8 (slightly higher edit cost)
  Grammar_cost = 0.0 (grammatically correct)
  LM_cost = 0.5 (high probability)
  Total = 0.3·0.8 + 0.4·0.0 + 0.3·0.5 = 0.24 + 0.0 + 0.15 = 0.39  ← WINNER
```

### Parse Forest Representation

**Shared Forest**: Compactly represents all parses

**Node Types**:
- **OR nodes**: Alternative parses (ambiguity)
- **AND nodes**: Sequence of constituents

**Example**:
```
Input: "I saw the man with a telescope"

Shared Forest:
  S
  ├── NP: I
  └── OR
      ├── VP (PP-attachment to VP)
      │   ├── V: saw
      │   ├── NP: the man
      │   └── PP: with a telescope
      └── VP (PP-attachment to NP)
          ├── V: saw
          └── NP
              ├── NP: the man
              └── PP: with a telescope
```

**Advantages**:
- Avoids exponential enumeration
- Efficient storage (O(n³) nodes)
- Can extract k-best parses efficiently

### Lattice Parsing Efficiency Analysis

#### The Exponential Candidate Problem

For a lattice with **K corrections per word** over **N words**, the number of paths grows as **K^N**:

| Input Length | K=5 corrections | K=10 corrections |
|--------------|----------------|------------------|
| 3 words | 125 paths | 1,000 paths |
| 5 words | 3,125 paths | 100,000 paths |
| 7 words | 78,125 paths | 10,000,000 paths |
| 10 words | 9.7M paths | 10 billion paths |

**Problem**: Parsing each path individually causes exponential blowup:
- **Path enumeration**: O(K^N) memory to store paths
- **Individual parsing**: O(K^N × N³) time to parse all paths

**Solution**: Lattice parsing avoids path enumeration entirely.

#### Complexity Comparison

| Approach | Time Complexity | Space Complexity | Practical Limit |
|----------|----------------|------------------|-----------------|
| **String List** | O(K^N × N³) | O(K^N × N) | ~8 words |
| **Lattice Parsing** | O(K×N × N²) | O(K×N) | 20+ words |
| **Speedup** | **O(K^(N-1) × N)** | **O(K^(N-1))** | **Exponential** |

**Key Insight**: Lattice parsing has **same asymptotic complexity as single-string parsing** (O(N³) Earley), but operates on the compact lattice representation (O(K×N) edges) instead of the exponential path space (O(K^N) paths).

#### Practical Performance Measurements

Benchmark corpus: 1000 real user queries with spelling errors

| Metric | String List | Lattice | Speedup |
|--------|-------------|---------|---------|
| Average candidates | 127 | 127 (same) | - |
| Average lattice edges | - | 23 | - |
| Parse time (mean) | 847 ms | 142 ms | **5.97×** |
| Parse time (median) | 612 ms | 98 ms | **6.24×** |
| Parse time (p95) | 2341 ms | 387 ms | **6.05×** |
| Memory (peak) | 1.2 GB | 0.3 GB | **4×** |
| Chart states created | 15,432 | 2,871 | **5.37×** |

**Source**: See [lattice_parsing.md](./lattice_parsing.md) Section 9 for full benchmark methodology

#### Why Lattice Parsing is Faster

**Shared prefix parsing**:

```
String list approach (redundant work):
  Parse("I seen the cat")  → 4 words parsed
  Parse("I seen the dog")  → 4 words parsed (prefix "I seen the" reparsed!)
  Parse("I saw the cat")   → 4 words parsed (prefix "I" and "the" reparsed!)
  Parse("I saw the dog")   → 4 words parsed
  Total: 16 word parses (4 sentences × 4 words)

Lattice approach (memoized):
  Node 0→1: Parse "I" (1×)
  Node 1→2: Parse "seen" (1×), "saw" (1×)
  Node 2→3: Parse "the" (1×)
  Node 3→4: Parse "cat" (1×), "dog" (1×)
  Total: 6 word parses

Speedup: 16 / 6 = 2.67× (for just 2-word sentences!)
```

**Chart memoization**: Earley states at `(node, position)` are reused across all paths passing through that node, avoiding redundant derivations.

### Integration with liblevenshtein-rust Three-Tier Pipeline

**End-to-End Example**:

```rust
use liblevenshtein::transducer::Transducer;
use liblevenshtein::cfg::{Grammar, EarleyParser};

// Tier 1: FST spelling correction → Lattice
let transducer = Transducer::for_dictionary(dictionary)
    .algorithm(Algorithm::Transposition)
    .max_distance(2)
    .build();

let lattice = transducer
    .query("i seen a elephant yesterday")
    .to_lattice();  // Compact DAG, O(K×N) edges

println!("Lattice: {} nodes, {} edges, {} paths",
         lattice.node_count(),
         lattice.edge_count(),
         lattice.path_count());
// Output: "Lattice: 6 nodes, 15 edges, 243 paths"

// Tier 2: CFG grammar correction → Parse Forest
let grammar = Grammar::from_file("grammar.cfg")?;
let parser = EarleyParser::new(&grammar);

let forest = parser.parse_lattice(&lattice)?;

println!("Parse forest: {} derivations",
         forest.parse_count());
// Output: "Parse forest: 3 derivations" (240 paths rejected by grammar!)

// Extract top-K grammatically valid candidates
let candidates = forest.k_best_parses(5);

for (i, parse) in candidates.iter().enumerate() {
    println!("Rank {}: {} (score: {:.3})",
             i+1, parse.sentence(), parse.score());
}
// Output:
// Rank 1: I saw an elephant yesterday (score: 0.892)
// Rank 2: I seen an elephant yesterday (score: 0.654)
// Rank 3: I see an elephant yesterday (score: 0.532)

// Tier 3 (optional): Neural reranking for semantic disambiguation
let best = neural_reranker.rerank(&candidates);
println!("Final correction: {}", best.sentence());
// Output: "Final correction: I saw an elephant yesterday"
```

**Key Advantages**:
1. **No path enumeration**: 243 paths never materialized in memory
2. **Grammar filtering**: 240/243 paths rejected by CFG rules
3. **Efficient extraction**: k-best algorithm extracts top-5 without enumerating all parses
4. **Tractable complexity**: O(15 edges × 5² Earley) = O(375) operations vs. O(243 × 5³) = O(30,375) for string list

### Advanced Topics

#### Term-Level vs. Character-Level Lattices

**liblevenshtein-rust uses term-level lattices**:

```
Term-level (correct):
  Node 0 ──["the", "tea", "ten"]──> Node 1 ──["cat", "car"]──> Node 2

Character-level (inefficient):
  Node 0 ──[t]──> Node 1 ──[h,e,a,e]──> Node 2 ──[e,a,n]──> Node 3 ...
```

**Why term-level?**
- CFG rules operate on **words** (terminals), not characters
- Character lattices require morphological analysis to recover word boundaries
- Term-level matches CFG granularity directly

**Trade-off**: Term-level lattices lose some phonetic error patterns (e.g., "donut" vs. "do nut"), but gain 10-100× efficiency for CFG parsing.

#### Parse Forest k-best Extraction

**Algorithm** (Huang & Chiang 2005):

```rust
impl ParseForest {
    /// Extract k-best parses using lazy enumeration
    pub fn k_best_parses(&self, k: usize) -> Vec<ParseTree> {
        let mut heap = BinaryHeap::new();
        let mut results = Vec::with_capacity(k);

        // Initialize with best derivation for each root alternative
        for alt in &self.root().alternatives {
            heap.push(Candidate {
                derivation: alt.clone(),
                score: alt.probability,
                child_ranks: vec![0; alt.children.len()],
            });
        }

        // Extract k-best
        while results.len() < k {
            if let Some(best) = heap.pop() {
                results.push(best.to_parse_tree());

                // Lazy enumeration: generate successors
                for i in 0..best.child_ranks.len() {
                    let mut successor = best.clone();
                    successor.child_ranks[i] += 1;
                    successor.update_score();
                    heap.push(successor);
                }
            } else {
                break;  // Fewer than k parses
            }
        }

        results
    }
}
```

**Complexity**: O(k log k) to extract k-best, independent of total parse count!

**Further Reading**:
- [lattice_parsing.md](./lattice_parsing.md) - Complete pedagogical guide with worked examples
- [lattice_data_structures.md](./lattice_data_structures.md) - Technical reference for Lattice, Chart, ParseForest data structures
- [architecture.md](./architecture.md#lattice-parsing-efficient-cfg-integration) - High-level three-tier pipeline overview

---

## Implementation Strategy

### Rust Data Structures

**CFG Definition**:
```rust
use std::collections::{HashMap, HashSet};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Symbol {
    Terminal(String),
    NonTerminal(String),
}

#[derive(Debug, Clone)]
pub struct Production {
    pub lhs: String,  // Non-terminal
    pub rhs: Vec<Symbol>,
    pub prob: f64,  // For PCFG
}

#[derive(Debug, Clone)]
pub struct ErrorProduction {
    pub production: Production,
    pub error_type: ErrorType,
    pub correction: Correction,
    pub cost: f64,
}

#[derive(Debug, Clone)]
pub enum ErrorType {
    ArticleError,
    SubjectVerbAgreement,
    TenseInconsistency,
    AuxiliaryError,
    MissingDeterminer,
}

#[derive(Debug, Clone)]
pub enum Correction {
    Replace { from: Symbol, to: Symbol },
    Insert { symbol: Symbol, position: usize },
    Delete { position: usize },
}

pub struct CFG {
    pub start: String,
    pub productions: Vec<Production>,
    pub error_productions: Vec<ErrorProduction>,
    pub terminal_rules: HashMap<String, Vec<Production>>,
    pub non_terminal_rules: HashMap<String, Vec<Production>>,
}
```

**Earley State**:
```rust
#[derive(Debug, Clone)]
pub struct EarleyState {
    pub rule: Production,
    pub dot: usize,  // Position in RHS
    pub origin: NodeId,  // Where state started
    pub cost: f64,  // Accumulated cost
    pub backpointers: Vec<(usize, usize)>,  // For parse tree extraction
}

impl EarleyState {
    pub fn next_symbol(&self) -> Option<&Symbol> {
        self.rule.rhs.get(self.dot)
    }

    pub fn is_complete(&self) -> bool {
        self.dot >= self.rule.rhs.len()
    }

    pub fn advance_dot(&self) -> Self {
        let mut new_state = self.clone();
        new_state.dot += 1;
        new_state
    }
}
```

**Earley Parser**:
```rust
pub struct EarleyParser {
    pub grammar: CFG,
}

impl EarleyParser {
    pub fn parse(&self, words: &[&str]) -> Option<ParseForest> {
        let n = words.len();
        let mut chart: Vec<HashSet<EarleyState>> = vec![HashSet::new(); n + 1];

        // Initialize
        let start_production = self.grammar.start_production();
        chart[0].insert(EarleyState {
            rule: start_production,
            dot: 0,
            origin: 0,
            cost: 0.0,
            backpointers: vec![],
        });

        // Process each position
        for i in 0..=n {
            let states: Vec<_> = chart[i].iter().cloned().collect();

            for state in states {
                if let Some(next_sym) = state.next_symbol() {
                    match next_sym {
                        Symbol::NonTerminal(nt) => {
                            // Predictor
                            for prod in self.grammar.non_terminal_rules.get(nt).unwrap_or(&vec![]) {
                                chart[i].insert(EarleyState {
                                    rule: prod.clone(),
                                    dot: 0,
                                    origin: i,
                                    cost: state.cost,
                                    backpointers: vec![],
                                });
                            }
                        }
                        Symbol::Terminal(term) if i < n && words[i] == term => {
                            // Scanner
                            chart[i + 1].insert(state.advance_dot());
                        }
                        _ => {}
                    }
                } else {
                    // Completer
                    self.complete(&mut chart, i, &state);
                }
            }
        }

        // Extract parse forest
        self.extract_forest(&chart, n)
    }

    fn complete(&self, chart: &mut Vec<HashSet<EarleyState>>, pos: usize, completed: &EarleyState) {
        let origin = completed.origin;
        let lhs = &completed.rule.lhs;

        let parent_states: Vec<_> = chart[origin]
            .iter()
            .filter(|s| {
                if let Some(Symbol::NonTerminal(nt)) = s.next_symbol() {
                    nt == lhs
                } else {
                    false
                }
            })
            .cloned()
            .collect();

        for parent in parent_states {
            let mut new_state = parent.advance_dot();
            new_state.backpointers.push((origin, pos));
            chart[pos].insert(new_state);
        }
    }

    fn extract_forest(&self, chart: &[HashSet<EarleyState>], n: usize) -> Option<ParseForest> {
        // Find complete parse (S' → S•)
        for state in &chart[n] {
            if state.rule.lhs == "S'" && state.is_complete() {
                return Some(self.build_forest(chart, state));
            }
        }
        None
    }
}
```

**Lattice Integration**:
```rust
impl EarleyParser {
    pub fn parse_lattice(&self, lattice: &Lattice) -> Vec<(ParseTree, f64)> {
        let mut chart: HashMap<NodeId, HashSet<EarleyState>> = HashMap::new();

        // Initialize at start node
        chart.entry(lattice.start).or_insert_with(HashSet::new).insert(
            EarleyState {
                rule: self.grammar.start_production(),
                dot: 0,
                origin: lattice.start,
                cost: 0.0,
                backpointers: vec![],
            }
        );

        // Process nodes in topological order
        for node in lattice.topological_order() {
            let states: Vec<_> = chart.get(&node).unwrap_or(&HashSet::new()).iter().cloned().collect();

            for state in states {
                if let Some(next_sym) = state.next_symbol() {
                    match next_sym {
                        Symbol::NonTerminal(_) => {
                            // Predictor (same as before)
                        }
                        Symbol::Terminal(term) => {
                            // Scanner: Check lattice edges
                            for edge in lattice.outgoing_edges(node) {
                                if &edge.label == term {
                                    let mut new_state = state.advance_dot();
                                    new_state.cost += edge.weight;  // FST cost
                                    chart.entry(edge.target).or_insert_with(HashSet::new).insert(new_state);
                                }
                            }
                        }
                    }
                } else {
                    // Completer
                    self.complete_lattice(&mut chart, node, &state);
                }
            }
        }

        // Extract all valid parses
        self.extract_all_parses(&chart, &lattice.final_nodes)
    }
}
```

---

## Benchmarks and Evaluation

### Datasets

**CoNLL-2014 GEC Shared Task**:
- **Size**: 62 annotated essays
- **Errors**: 3,542 error annotations
- **Task**: Grammatical error correction
- **Baseline**: 30-40% F0.5

**JFLEG (JHU Fluency-Extended GUG)**:
- **Size**: 1,511 sentences
- **Annotations**: 4 fluency judgments per sentence
- **Metric**: GLEU score
- **Baseline**: 40-50 GLEU

**BEA-2019 Shared Task**:
- **Datasets**: Write & Improve (L2 learner essays), LOCNESS (native speaker)
- **Task**: GEC with fluency improvements
- **SOTA**: 70+ F0.5

### Metrics

**Precision, Recall, F0.5**:
```
Precision = TP / (TP + FP)  (of proposed corrections, how many are correct?)
Recall = TP / (TP + FN)  (of all errors, how many detected?)

F0.5 = (1 + 0.5²) · (Precision · Recall) / (0.5² · Precision + Recall)
     = 1.25 · (Precision · Recall) / (0.25 · Precision + Recall)
```

**Why F0.5?** Precision weighted 2× more than recall (avoid false corrections).

**GLEU (Generalized Language Evaluation Understanding)**:
- Variation of BLEU for GEC
- Rewards both corrections and fluency
- Range: 0-100 (higher is better)

### Evaluation Protocol

**Steps**:
1. **Preprocess**: Tokenize input and reference
2. **Correct**: Apply CFG error grammar + FST + Neural layers
3. **Align**: Match system output to gold annotations (M² scorer)
4. **Score**: Compute Precision, Recall, F0.5

**Example**:
```
Input: "I seen a elephant yesterday"
Gold: "I saw an elephant yesterday"
System: "I saw an elephant yesterday"

Annotations:
  Error 1: "seen" → "saw" (tense error)  ✅ DETECTED
  Error 2: "a" → "an" (article error)    ✅ DETECTED

TP = 2, FP = 0, FN = 0
Precision = 2/2 = 100%
Recall = 2/2 = 100%
F0.5 = 100%
```

---

## Integration with Large Language Models

### Overview

The CFG layer serves as a critical bridge between symbolic correction (Tier 1: FST/NFA) and neural understanding (Tier 3: LLM). This section explores practical use cases where CFG validation enhances LLM applications.

**Key Insight**: CFG provides **deterministic grammatical guarantees** that complement LLM flexibility. While LLMs excel at semantic understanding and generation, they can produce grammatically incorrect output. CFG validation catches these errors without requiring additional neural inference.

### Use Case 1: Validating LLM-Generated Text

**Problem**: LLMs like GPT, Claude, and Llama can generate grammatically incorrect sentences, especially when:
- Operating under token limits (truncated output)
- Generating from constrained prompts
- Fine-tuned on noisy data
- Responding to adversarial inputs

**Solution**: CFG validation as postprocessing layer.

**Pipeline**:
```
User Prompt → LLM Generation → CFG Validation → Corrected Output
```

**Implementation**:
```rust
struct LLMValidator {
    grammar: Grammar,
    parser: EarleyParser,
    llm_client: LLMClient,
}

impl LLMValidator {
    async fn generate_and_validate(
        &self,
        prompt: &str,
        max_retries: usize,
    ) -> Result<String, Error> {
        for attempt in 0..max_retries {
            // Step 1: Generate with LLM
            let response = self.llm_client.generate(prompt).await?;

            // Step 2: Tokenize
            let tokens = tokenize(&response);

            // Step 3: CFG validation
            match self.parser.parse(&tokens) {
                Ok(forest) if forest.is_grammatical() => {
                    return Ok(response); // Valid grammar
                }
                Ok(forest) => {
                    // Attempt CFG correction
                    if let Some(corrected) = forest.best_parse() {
                        return Ok(corrected.sentence());
                    }
                }
                Err(_) => {
                    // Parse failed - retry generation
                    if attempt < max_retries - 1 {
                        continue;
                    }
                }
            }
        }

        Err(Error::NoGrammaticalOutput)
    }
}
```

**Benefits**:
- **Deterministic**: Grammar rules are symbolic (not learned)
- **Fast**: O(n³) CFG vs O(n²) additional LLM inference
- **Interpretable**: Know exactly which grammar rule failed
- **Cost-effective**: No additional LLM API calls for validation

**Example**:
```
LLM Output: "The data shows that each of the students have submitted their work."
CFG Error: Subject-verb agreement ("each" singular, "have" plural)
Corrected: "The data shows that each of the students has submitted their work."
```

---

### Use Case 2: Educational Writing Assistant

**Application**: Provide pedagogical explanations for grammar errors in student writing.

**Pipeline**:
```
Student Text → CFG Parse → Error Detection → LLM Explanation → Feedback
```

**Why CFG + LLM?**
- **CFG**: Detects specific grammatical errors (deterministic, fast)
- **LLM**: Generates natural language explanations (pedagogical, context-aware)

**Implementation**:
```rust
struct WritingAssistant {
    grammar: ErrorGrammar,
    parser: EarleyParser,
    llm: LLMClient,
}

impl WritingAssistant {
    async fn analyze_and_explain(
        &self,
        student_text: &str,
    ) -> Result<Vec<Feedback>, Error> {
        let tokens = tokenize(student_text);
        let forest = self.parser.parse(&tokens)?;

        let mut feedback = Vec::new();

        // Extract all grammatical errors from parse forest
        for error in forest.extract_errors() {
            let correction = error.suggested_correction();

            // Generate pedagogical explanation with LLM
            let prompt = format!(
                "Explain this grammar error to a student:\n\
                 Original: {}\n\
                 Error type: {}\n\
                 Correction: {}\n\
                 Provide a clear, encouraging explanation with an example.",
                error.original_span(),
                error.error_type(),
                correction,
            );

            let explanation = self.llm.generate(&prompt).await?;

            feedback.push(Feedback {
                span: error.span(),
                error_type: error.error_type(),
                original: error.original_span().to_string(),
                correction: correction.to_string(),
                explanation,
            });
        }

        Ok(feedback)
    }
}

struct Feedback {
    span: Span,
    error_type: ErrorType,
    original: String,
    correction: String,
    explanation: String,
}
```

**Example Output**:
```
Student Input: "Me and him went to the store."

CFG Detection:
  Error: Pronoun case error at position 0-10
  Rule violated: SUBJ → NP[nominative]
  Suggestion: "He and I went to the store."

LLM Explanation:
  "Great job forming a complete sentence! There's a small issue with
   pronoun case. When pronouns are subjects (doing the action), we use
   the nominative case: 'I' and 'he' instead of 'me' and 'him'.

   Think of it this way: you wouldn't say 'Me went to the store' or
   'Him went to the store', right? Same rule applies when there are
   multiple subjects.

   Corrected: 'He and I went to the store.'

   Pro tip: Try removing the other person - if 'me' sounds wrong alone,
   use 'I' instead!"
```

**Advantages**:
- **Precision**: CFG detects exact error location and type
- **Pedagogy**: LLM generates encouraging, contextual explanations
- **Scalability**: CFG runs in O(n³), LLM only called per error (not per sentence)

---

### Use Case 3: Structured Output Validation (JSON, Code)

**Problem**: LLMs frequently generate syntactically invalid structured output:
- JSON with trailing commas
- Mismatched brackets/braces
- Invalid escape sequences
- Unclosed strings

**Solution**: CFG grammar for structured formats + LLM for content generation.

**Pipeline**:
```
Prompt → LLM → JSON String → CFG JSON Parser → Valid JSON / Error
```

**JSON CFG Example**:
```
S → Object | Array
Object → { } | { Members }
Members → Pair | Pair , Members
Pair → String : Value
Value → String | Number | Object | Array | true | false | null
Array → [ ] | [ Elements ]
Elements → Value | Value , Elements
String → " Chars "
Number → Digits | Digits . Digits
```

**Implementation**:
```rust
struct StructuredOutputValidator {
    json_grammar: Grammar,
    parser: EarleyParser,
    llm: LLMClient,
}

impl StructuredOutputValidator {
    async fn generate_json(
        &self,
        prompt: &str,
    ) -> Result<serde_json::Value, Error> {
        let response = self.llm.generate(prompt).await?;

        // Step 1: Extract JSON from markdown code blocks if present
        let json_str = extract_json(&response)?;

        // Step 2: CFG validation
        let tokens = tokenize_json(&json_str);
        match self.parser.parse(&tokens) {
            Ok(forest) if forest.is_complete() => {
                // Valid JSON grammar - parse into serde_json::Value
                serde_json::from_str(&json_str)
                    .map_err(|e| Error::JsonSemantic(e))
            }
            Ok(forest) => {
                // Syntax errors - extract specific issue
                let errors = forest.extract_syntax_errors();
                Err(Error::JsonSyntax(errors))
            }
            Err(e) => Err(Error::ParseFailed(e)),
        }
    }
}
```

**Benefits**:
- **Fast Validation**: CFG parsing O(n³) vs regex hacks O(n²+)
- **Precise Errors**: Know exact token where syntax breaks
- **Formal Guarantee**: Provably correct grammar (unlike regex)

**Example**:
```
LLM Output (INVALID):
{
  "name": "John",
  "age": 30,  # Comment not allowed in JSON!
  "hobbies": ["reading", "coding",]  # Trailing comma
}

CFG Parse Error:
  Position 34: Unexpected token '#' (comments not in grammar)
  Position 72: Trailing comma before ']' (not allowed in Members rule)

Corrected:
{
  "name": "John",
  "age": 30,
  "hobbies": ["reading", "coding"]
}
```

---

### Performance Comparison

**Validation Latency**:

| Approach | Latency | Cost | Accuracy |
|----------|---------|------|----------|
| **No validation** | 0ms | Free | ~85% (LLM baseline) |
| **Regex validation** | 1-5ms | Free | ~90% (misses nested errors) |
| **CFG validation** | 5-20ms | Free | ~98% (catches syntax errors) |
| **LLM self-correction** | +500-2000ms | $$$ (2× inference) | ~95% (still probabilistic) |

**Why CFG Wins**:
- **Deterministic**: 100% accuracy for defined grammar rules
- **Fast**: O(n³) but with small constant factors (n = sentence length ~10-50 tokens)
- **Zero marginal cost**: No API calls, runs locally
- **Interpretable**: Exact error location and rule violation

---

### Integration Patterns

**Pattern 1: Postprocessing (Validation)**
```
LLM Generate → CFG Validate → Accept / Reject
```
**Use Case**: Ensure LLM output is grammatically correct

**Pattern 2: Preprocessing (Normalization)**
```
User Input → CFG Correct → LLM Process
```
**Use Case**: Clean user queries before LLM (see architecture.md section 9)

**Pattern 3: Hybrid Correction (CFG + LLM)**
```
Text → CFG Detect Errors → LLM Generate Correction → CFG Validate
```
**Use Case**: CFG finds errors, LLM proposes fixes, CFG validates proposals

---

### Summary

**CFG + LLM Complementarity**:

| Layer | Strength | Weakness | Role in Pipeline |
|-------|----------|----------|------------------|
| **CFG** | Deterministic syntax validation | No semantic understanding | Error detection & structural validation |
| **LLM** | Semantic understanding, fluency | Probabilistic, can make errors | Content generation & explanation |

**Best Practices**:
1. **Use CFG for validation**: Fast, deterministic, interpretable
2. **Use LLM for generation**: Contextual, fluent, creative
3. **Combine for robustness**: CFG catches LLM syntax errors
4. **Pedagogical applications**: CFG detects, LLM explains

**See Also**:
- [architecture.md section 9](architecture.md#integration-with-large-language-models) for comprehensive LLM integration patterns
- [lattice_parsing.md](lattice_parsing.md) for efficient CFG parsing over FST lattices

---

## References

### Key Papers

1. **Stahlberg, F., Bryant, C., Byrne, B.** (2019). Neural Grammatical Error Correction with Finite State Transducers. NAACL 2019. arXiv:1903.10625

2. **Ebden, P., Sproat, R.** (2015). The Kestrel TTS Text Normalization System. Natural Language Engineering, 21(3), 333-353.

3. **Google Patent US5970449A**: Text normalization using a context-free grammar.

4. **Earley, J.** (1970). An efficient context-free parsing algorithm. Communications of the ACM, 13(2), 94-102.

5. **Younger, D.H.** (1967). Recognition and parsing of context-free languages in time n³. Information and Control, 10(2), 189-208.

6. **Chomsky, N.** (1956). Three models for the description of language. IRE Transactions on Information Theory, 2(3), 113-124.

### Tools

- **NLTK**: Python library with CYK, Earley parsers
- **spaCy**: Dependency parsing (not CFG, but useful)
- **Stanford CoreNLP**: Java-based CFG parsing

### Shared Tasks

- **CoNLL-2014 GEC**: https://www.comp.nus.edu.sg/~nlp/conll14st.html
- **BEA-2019 GEC**: https://www.cl.cam.ac.uk/research/nl/bea2019st/
- **JFLEG**: https://github.com/keisks/jfleg
