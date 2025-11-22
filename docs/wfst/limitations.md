# WFST Text Normalization: Limitations and Trade-offs

**Status**: Design Document
**Last Updated**: 2025-11-20
**Purpose**: Understanding capabilities and boundaries of each layer

---

## Table of Contents

1. [Introduction](#introduction)
2. [Chomsky Hierarchy Positioning](#chomsky-hierarchy-positioning)
3. [FST/NFA Capabilities (Type 3)](#fstnfa-capabilities-type-3)
4. [CFG Capabilities (Type 2)](#cfg-capabilities-type-2)
5. [Neural Capabilities (Beyond Type 2)](#neural-capabilities-beyond-type-2)
6. [Parsing Complexity Trade-offs](#parsing-complexity-trade-offs)
7. [When to Use Each Layer](#when-to-use-each-layer)
8. [Common Pitfalls](#common-pitfalls)
9. [Design Recommendations](#design-recommendations)

---

## Introduction

### Why Limitations Matter

**Problem**: Choosing the wrong formalism leads to:
- **Under-powered**: Cannot handle the error type (FST for grammar)
- **Over-powered**: Unnecessary complexity and latency (neural for spelling)
- **Combinatorial explosion**: Wrong algorithm for problem size

**Solution**: Understand the **formal language hierarchy** and select the minimal sufficient formalism.

### Three-Tier Philosophy

```
┌─────────────────────────────────────────────────────────┐
│ Tier 3: Neural (Unrestricted)                           │
│ - Semantic disambiguation                               │
│ - Discourse coherence                                   │
│ - Cost: High latency, non-deterministic                 │
└─────────────────────────────────────────────────────────┘
                          ↑ (only if needed)
┌─────────────────────────────────────────────────────────┐
│ Tier 2: CFG (Context-Free)                              │
│ - Syntax, phrase structure                              │
│ - Cost: O(n³) parsing                                   │
└─────────────────────────────────────────────────────────┘
                          ↑ (only if needed)
┌─────────────────────────────────────────────────────────┐
│ Tier 1: FST/NFA (Regular)                               │
│ - Spelling, phonetic, morphology                        │
│ - Cost: O(n) recognition                                │
└─────────────────────────────────────────────────────────┘
                          ↑ (always start here)
```

**Principle**: Use the **simplest formalism** that can solve the problem.

---

## Chomsky Hierarchy Positioning

### The Hierarchy

**Type 3: Regular Languages** (FST/NFA)
- **Grammar**: A → aB | a (right-linear)
- **Automaton**: Finite-state automaton
- **Memory**: Finite states (no stack)
- **Complexity**: O(n) recognition
- **Example**: a*b*

**Type 2: Context-Free Languages** (CFG)
- **Grammar**: A → α (any string on RHS)
- **Automaton**: Pushdown automaton (FSA + stack)
- **Memory**: Unbounded stack
- **Complexity**: O(n³) CYK, O(n²) average Earley
- **Example**: a^n b^n (balanced parentheses)

**Type 1: Context-Sensitive Languages** (CSG)
- **Grammar**: αAβ → αγβ (context around A)
- **Automaton**: Linear-bounded automaton
- **Memory**: Tape bounded by input length
- **Complexity**: PSPACE-complete
- **Example**: a^n b^n c^n

**Type 0: Recursively Enumerable** (Turing Machine)
- **Grammar**: Unrestricted rewriting
- **Automaton**: Turing machine
- **Memory**: Unbounded tape
- **Complexity**: Undecidable
- **Example**: Halting problem

### Inclusion Relationships

```
Type 3 ⊂ Type 2 ⊂ Type 1 ⊂ Type 0

Regular ⊂ Context-Free ⊂ Context-Sensitive ⊂ Recursively Enumerable
```

**Strict Inclusions** (proven via pumping lemmas):
- {a^n b^n} ∈ Type 2, {a^n b^n} ∉ Type 3
- {a^n b^n c^n} ∈ Type 1, {a^n b^n c^n} ∉ Type 2

### Text Normalization Mapping

| Error Type | Language Class | Formalism | Why |
|------------|----------------|-----------|-----|
| Spelling (typos) | Type 3 | FST | Character edits (no counting) |
| Phonetic ("fone") | Type 3 | NFA | Pattern matching (no nesting) |
| Morphology (plurals) | Type 3 | FST | Suffix rules (finite patterns) |
| Article (a/an) | Type 2 | CFG | Phonological context (requires parsing) |
| Subject-verb agreement | Type 2 | CFG | Counting (NP number ↔ VP number) |
| Nested phrases | Type 2 | CFG | Balanced structures (recursion) |
| Anaphora resolution | Beyond Type 2 | Neural | Cross-sentence dependencies |
| Semantic ("bank") | Beyond Type 2 | Neural | World knowledge |

---

## FST/NFA Capabilities (Type 3)

### What FSTs CAN Do

**1. Character-Level Edit Operations**:
```
Levenshtein distance: insertion, deletion, substitution, transposition
Example: "teh" → "the" (transposition)
Complexity: O(n) with pre-compiled automaton
```

**2. Phonetic Transformations**:
```
Pattern matching: (ph|f), (ough|uff), c→s/_[ei]
Example: "fone" → "phone", "sity" → "city"
Complexity: O(n·|NFA states|)
```

**3. Morphological Variants** (if context-free):
```
Plurals: cat → cats (suffix -s)
Past tense: walk → walked (suffix -ed)
Limitation: Only if rules don't depend on word structure
```

**4. Lexical Normalization**:
```
Abbreviations: "u" → "you", "4" → "for"
Emoticons: ":)" → "happy", ":(" → "sad"
Complexity: O(n) lookup in trie
```

**5. Finite-State Constraints**:
```
Character classes: [aeiou], [^aeiou]
Repetition: a*, a+, a{2,5}
Concatenation, alternation
```

### What FSTs CANNOT Do

**1. Balanced Structures** (requires stack):
```
❌ Balanced parentheses: (a(b)c)
❌ XML tags: <tag>content</tag>
❌ Nested quotes: "He said 'hello' to me"

Why: Requires counting opens vs closes (a^n b^n)
FST has finite memory, cannot count unboundedly
```

**2. Cross-Serial Dependencies**:
```
❌ Swiss German: a^n b^m c^n d^m
❌ English: "The cats that the dogs chased ran"
    (cats_plural ↔ ran_plural, across "that..." clause)

Why: Requires tracking multiple counters
```

**3. Subject-Verb Agreement** (beyond trigram):
```
❌ "The cat [that the dog chased] runs fast"
    (cat_singular ↔ runs_singular, long distance)

✅ "The cat runs" (within FST trigram window)

Why: FST can handle local agreement (3-gram context)
      Cannot handle long-range dependencies
```

**4. Copy Language**:
```
❌ L = {ww | w ∈ Σ*}  (two identical copies)
Example: "abcabc" (first half = second half)

Why: Pumping lemma proof shows not regular
```

**5. Semantic Disambiguation**:
```
❌ "bank" = river bank vs financial bank
❌ "run" = jog vs execute program vs color spreading

Why: Requires world knowledge, not syntactic patterns
```

### Pumping Lemma for Regular Languages

**Theorem**: If L is regular, then ∃p (pumping length) such that ∀s ∈ L with |s| ≥ p,
s can be written as xyz where:
1. |xy| ≤ p
2. |y| > 0
3. xy^i z ∈ L for all i ≥ 0

**Proof that {a^n b^n} is not regular**:

Assume {a^n b^n} is regular with pumping length p.

Let s = a^p b^p ∈ L (clearly |s| ≥ p).

By pumping lemma, s = xyz where |xy| ≤ p and |y| > 0.

Since |xy| ≤ p, both x and y consist only of a's.

So y = a^k for some k > 0.

Pump down (i=0): xz = a^(p-k) b^p.

But (p-k) ≠ p, so xz ∉ {a^n b^n}.

**Contradiction**! Therefore {a^n b^n} is not regular. ∎

---

## CFG Capabilities (Type 2)

### What CFGs CAN Do

**1. Nested Phrase Structures**:
```coq
S → NP VP
NP → DT N | NP PP
PP → P NP

Example: "the cat [on the mat [in the room]]"
         (nested PPs)
```

**2. Subject-Verb Agreement**:
```coq
S → NP[num=X] VP[num=X]

Example: "The cats run" (plural ↔ plural)
         "The cat runs" (singular ↔ singular)

Feature unification ensures agreement
```

**3. Balanced Structures**:
```coq
S → ε
S → ( S )
S → S S

Language: Balanced parentheses
Example: "(()())", "((()))", "()()"
```

**4. Arithmetic Expressions**:
```coq
E → E + E | E * E | (E) | number

Example: "1 + (2 * 3)"
Correctly handles operator precedence with grammar rules
```

**5. Determiners and Articles**:
```coq
NP → DT[a] N[-vowel_initial]
NP → DT[an] N[+vowel_initial]

Example: "an apple", "a banana"
Phonological context handled via features
```

**6. Auxiliary Verb Selection**:
```coq
VP → AUX[modal] VP[inf]
VP → AUX[have] VP[past_part]

Example: "can swim" (modal + infinitive)
         "have eaten" (perfect aspect)
```

### What CFGs CANNOT Do

**1. Cross-Serial Dependencies** (a^n b^m c^n d^m):
```
❌ Swiss German: "mer em Hans es huus hälfe aastriiche"
   (we Hans_DAT the house_ACC help paint)
   Datives and accusatives cross-serialize

Why: CFG stack processes in LIFO order
     Cannot interleave two dependency chains
```

**2. Copy Language** (ww):
```
❌ L = {ww | w ∈ Σ*}
Example: "abcabc"

Why: Pumping lemma for CFLs
     Cannot verify first half = second half
```

**3. MIX Language** ({a,b,c}* with equal counts):
```
❌ L = {w ∈ {a,b,c}* | #_a(w) = #_b(w) = #_c(w)}
Example: "aabbcc", "abcabc", "cabacb"

Why: Requires three independent counters
     CFG stack can only count one dependency
```

**4. Semantic Constraints**:
```
❌ "Colorless green ideas sleep furiously" (syntactically valid, semantically nonsense)
❌ "The table ate the chair" (syntax OK, semantics wrong)

Why: CFG models syntax, not meaning
```

**5. Long-Range Anaphora**:
```
❌ "John said Mary thought Bill believed [he]_? was right"
   (who does "he" refer to? John, Bill, or someone else?)

Why: Requires discourse model, world knowledge
```

### Pumping Lemma for Context-Free Languages

**Theorem**: If L is context-free, then ∃p (pumping length) such that ∀s ∈ L with |s| ≥ p,
s can be written as uvxyz where:
1. |vxy| ≤ p
2. |vy| > 0
3. uv^i xy^i z ∈ L for all i ≥ 0

**Proof that {a^n b^n c^n} is not context-free**:

Assume {a^n b^n c^n} is context-free with pumping length p.

Let s = a^p b^p c^p ∈ L.

By pumping lemma, s = uvxyz where |vxy| ≤ p and |vy| > 0.

**Case 1**: vxy contains only a's.
Pump up (i=2): uv²xy²z = a^(p+k) b^p c^p for some k > 0.
Not in L (unequal counts).

**Case 2**: vxy contains only b's.
Similar argument.

**Case 3**: vxy contains only c's.
Similar argument.

**Case 4**: vxy spans a's and b's (but not c's, since |vxy| ≤ p).
Pump up: increases a's and/or b's, but not c's.
Not in L.

**Case 5**: vxy spans b's and c's (but not a's).
Similar argument.

All cases lead to contradiction! Therefore {a^n b^n c^n} is not context-free. ∎

---

## Neural Capabilities (Beyond Type 2)

### What Neural Models CAN Do

**1. Semantic Disambiguation**:
```
Input: "I went to the bank"
Context: "to deposit money" → financial bank
Context: "by the river" → river bank

Method: Contextual embeddings (BERT, GPT)
```

**2. Discourse Coherence**:
```
Input: "Mary loves ice cream. She ate it yesterday."
Resolve: "She" → Mary, "it" → ice cream

Method: Coreference resolution, transformer attention
```

**3. Pragmatic Inference**:
```
Input: "Can you pass the salt?"
Interpretation: Request (not yes/no question)

Method: Learned pragmatic conventions
```

**4. Style Transfer**:
```
Input: "hey whats up lol"
Output: "Hello, how are you?"

Method: Seq2seq with style embeddings
```

**5. Cross-Lingual Transfer**:
```
Input: "Je suis un étudiant"
Output: "I am a student"

Method: Multilingual transformers (mBERT, XLM)
```

**6. Creative Generation**:
```
Input: "Once upon a time"
Output: "there was a dragon who loved to read books..."

Method: Autoregressive LM (GPT-3, Claude)
```

### What Neural Models CANNOT Guarantee

**1. Determinism**:
```
❌ Same input may yield different outputs (temperature, sampling)
✅ CFG/FST: Same input → same output (reproducible)
```

**2. Unrecoverable Errors**:
```
❌ "I have 5 apples" → "I have 7 bananas" (hallucination)
❌ "Meet at 3pm" → "Meet at 5am" (date/time errors)

Why: No hard constraints, only soft probabilities
```

**3. Formal Correctness**:
```
❌ "2 + 2 = 5" (arithmetic error)
❌ Balanced parentheses (may produce unbalanced)

Why: Learned patterns, not formal rules
```

**4. Explainability**:
```
❌ "Why did you change 'seen' to 'saw'?"
    Neural answer: "High probability in context"
    (black box, no interpretable rule)

✅ CFG/FST: Point to explicit grammar rule
```

**5. Low-Latency Guarantees**:
```
❌ Transformer inference: 50-500ms (variable)
✅ FST: <10ms (constant for given input size)
```

---

## Parsing Complexity Trade-offs

### Time Complexity

| Formalism | Recognition | Parsing | Example |
|-----------|-------------|---------|---------|
| FST | O(n) | O(n) | Levenshtein |
| NFA | O(n·\|Q\|) | O(n·\|Q\|) | Phonetic regex |
| CYK (CNF) | O(n³·\|G\|) | O(n³·\|G\|) | Grammar |
| Earley (general CFG) | O(n³) worst, O(n²) avg | O(n³) | Grammar |
| Transformer | O(n²·d) | O(n²·d) | BERT, GPT |

**Legend**:
- n = input length
- |Q| = NFA state count
- |G| = grammar size (productions)
- d = model dimension (768, 1024, etc.)

### Space Complexity

| Formalism | Memory | Notes |
|-----------|--------|-------|
| FST | O(\|Q\|) | States + transitions (constant per input) |
| NFA | O(\|Q\|) | Active state set |
| DFA | O(2^{\|Q\|}) | Exponential blowup in worst case |
| CYK | O(n²·\|G\|) | Chart size (triangular matrix) |
| Earley | O(n²·\|G\|) | State sets (can be sparse) |
| Transformer | O(n²) | Attention matrix |

### Latency Benchmarks (Estimated)

**Input**: 50-character sentence

| Layer | Formalism | Latency | Throughput |
|-------|-----------|---------|------------|
| Tier 1 (FST) | Levenshtein | <5ms | >10,000 sent/sec |
| Tier 1 (NFA) | Phonetic regex | <10ms | >5,000 sent/sec |
| Tier 2 (CFG) | Earley parser | <100ms | >500 sent/sec |
| Tier 3 (Neural) | BERT-base (CPU) | ~200ms | >25 sent/sec |
| Tier 3 (Neural) | BERT-base (GPU) | ~50ms | >100 sent/sec |
| Tier 3 (Neural) | GPT-3 API | ~500ms | Variable (rate-limited) |

**Recommendation**: Start with Tier 1, add Tier 2 only if needed, Tier 3 as last resort.

---

## When to Use Each Layer

### Decision Tree

```
Start: Is error character-level (spelling, typo)?
  ├─ YES → Use FST (Tier 1)
  │   └─ Levenshtein automaton (O(n), <10ms)
  │
  └─ NO → Is error phonetic (sound-based)?
      ├─ YES → Use NFA (Tier 1)
      │   └─ Phonetic regex (O(n·|NFA|), <20ms)
      │
      └─ NO → Does error require phrase structure (grammar)?
          ├─ YES → Use CFG (Tier 2)
          │   └─ Earley parser (O(n³), <200ms)
          │
          └─ NO → Does error require semantics/discourse?
              ├─ YES → Use Neural (Tier 3)
              │   └─ BERT/GPT (O(n²), 50-500ms)
              │
              └─ NO → Error not handleable (out of scope)
```

### Error Type Examples

**Tier 1 (FST)** - Use for:
- ✅ Spelling: "teh" → "the"
- ✅ Typos: "helo" → "hello"
- ✅ Abbreviations: "u" → "you"
- ✅ Emoticons: ":)" → "happy"
- ✅ Morphology (simple): "cats" → "cat"

**Tier 1 (NFA)** - Use for:
- ✅ Phonetic: "fone" → "phone"
- ✅ Sound patterns: "nite" → "night"
- ✅ Dialect: "wanna" → "want to"

**Tier 2 (CFG)** - Use for:
- ✅ Articles: "a apple" → "an apple"
- ✅ Agreement: "they was" → "they were"
- ✅ Auxiliaries: "can able" → "can" or "is able"
- ✅ Tense: "yesterday he eats" → "yesterday he ate"

**Tier 3 (Neural)** - Use for:
- ✅ Semantic: "bank" → river/financial (context)
- ✅ Anaphora: "She" → who?
- ✅ Pragmatics: politeness, formality
- ✅ Style: informal → formal

### Performance vs Accuracy

**Fast Mode** (<50ms total):
```
[FST + NFA only]
Latency: <20ms
Accuracy: ~85%
Use case: Mobile keyboard, real-time chat
```

**Balanced Mode** (<300ms total):
```
[FST + NFA + CFG]
Latency: ~200ms
Accuracy: ~92%
Use case: Desktop editor, batch processing
```

**Accurate Mode** (<1s total):
```
[FST + NFA + CFG + Neural]
Latency: ~500ms
Accuracy: ~96%
Use case: Document polishing, professional writing
```

---

## Common Pitfalls

### Pitfall 1: Using Neural for Everything

**❌ Mistake**:
```rust
// Bad: Neural LM for simple spelling correction
let corrected = bert_model.correct("teh cat");
// Latency: 200ms, may hallucinate
```

**✅ Correct**:
```rust
// Good: FST for spelling, fast and deterministic
let corrected = levenshtein.query("teh", 1).next().unwrap();
// Latency: 2ms, guaranteed correct if in dictionary
```

**Why**: Over-powered tool adds latency without benefit.

### Pitfall 2: Using FST for Grammar

**❌ Mistake**:
```rust
// Bad: FST cannot handle subject-verb agreement
let fst = compile_regex("the cat run|the cats run|the cat runs|the cats run");
// Doesn't scale, misses patterns
```

**✅ Correct**:
```rust
// Good: CFG with feature unification
let cfg = parse_grammar("S → NP[num=X] VP[num=X]");
// Handles all cases systematically
```

**Why**: Under-powered tool cannot express the constraint.

### Pitfall 3: Exponential DFA Blowup

**❌ Mistake**:
```rust
// Bad: NFA → DFA conversion for complex patterns
let nfa = compile_regex("(a|b)*c(d|e)*f(g|h)*");
let dfa = nfa.to_dfa();  // May create 2^|states| states!
```

**✅ Correct**:
```rust
// Good: Keep as NFA, use lazy DFA
let nfa = compile_regex("(a|b)*c(d|e)*f(g|h)*");
let lazy_dfa = LazyDFA::new(nfa);  // Build states on-demand
```

**Why**: Subset construction can cause exponential blowup.

### Pitfall 4: Ignoring Pumping Lemma

**❌ Mistake**:
```rust
// Bad: Trying to use FST for balanced parentheses
let fst = compile_regex("()*");  // Doesn't work!
```

**✅ Correct**:
```rust
// Good: Use CFG for balanced structures
let cfg = parse_grammar("S → ε | (S) | SS");
```

**Why**: FST fundamentally cannot count (pumping lemma).

### Pitfall 5: Trusting Neural Without Constraints

**❌ Mistake**:
```rust
// Bad: Neural model may hallucinate dates
let corrected = gpt3("I have a meeting on 3pm");
// Possible output: "I have a meeting on 5am" ❌
```

**✅ Correct**:
```rust
// Good: FST constraints + Neural ranking
let candidates = fst.extract_times("3pm");  // ["3pm", "15:00"]
let best = neural_lm.rank(candidates, context);
```

**Why**: Neural models lack hard constraints (unrecoverable errors).

---

## Design Recommendations

### Recommendation 1: Start Simple

**Principle**: Use the simplest formalism that solves the problem.

```
Decision order:
1. Try FST first (O(n), fast)
2. If FST insufficient, try CFG (O(n³), slower but correct)
3. If CFG insufficient, try Neural (O(n²), slowest but flexible)
```

### Recommendation 2: Hybrid Pipelines

**Architecture**: Layer symbolic (FST/CFG) with neural ranking.

```rust
// Symbolic generates candidates (deterministic)
let fst_candidates = levenshtein.query(input, 2);
let cfg_candidates = earley.parse_lattice(fst_candidates);

// Neural ranks candidates (context-aware)
let best = bert.rank(cfg_candidates, context);
```

**Benefits**:
- Deterministic candidate generation (no hallucination)
- Context-aware selection (neural strengths)

### Recommendation 3: Know Your Complexity

**Scaling**:
- FST: Scales to millions of words (O(n))
- CFG: Scales to hundreds of words (O(n³))
- Neural: Scales to hundreds of words (O(n²), but high constant)

**Rule of Thumb**:
- Input <100 chars → All tiers feasible
- Input 100-500 chars → FST + CFG feasible, Neural slow
- Input >500 chars → FST only, or split into chunks

### Recommendation 4: Formal Verification Where Possible

**Priority**:
1. **Critical rules**: Formally verify (Coq, Isabelle)
2. **Non-critical rules**: Extensive testing
3. **Neural**: Constrain with symbolic checks

**Example** (liblevenshtein-rust):
```coq
(* Coq-verified phonetic rules *)
Theorem ph_to_f_preserves_length : ...
Theorem rule_application_terminates : ...

(* Compile to FST, preserving properties *)
let fst = PhoneticFST::from_verified_rules(coq_rules);
```

### Recommendation 5: Measure, Don't Guess

**Benchmark**:
```rust
#[bench]
fn bench_fst_vs_cfg_vs_neural(b: &mut Bencher) {
    let input = "the cat run fast";

    b.iter(|| {
        // Tier 1: FST
        let t1 = Instant::now();
        let fst_result = levenshtein.correct(input);
        let fst_time = t1.elapsed();

        // Tier 2: CFG
        let t2 = Instant::now();
        let cfg_result = earley.correct(input);
        let cfg_time = t2.elapsed();

        // Tier 3: Neural
        let t3 = Instant::now();
        let neural_result = bert.correct(input);
        let neural_time = t3.elapsed();

        println!("FST: {:?}, CFG: {:?}, Neural: {:?}",
                 fst_time, cfg_time, neural_time);
    });
}
```

**Hypothesis**: Test, measure, validate. Don't assume.

---

## Summary Table

| Aspect | FST/NFA (Type 3) | CFG (Type 2) | Neural (Beyond Type 2) |
|--------|------------------|--------------|------------------------|
| **Language Class** | Regular | Context-Free | Unrestricted |
| **Memory** | Finite states | Stack (unbounded) | Learned weights |
| **Complexity** | O(n) | O(n³) CYK, O(n²) avg | O(n²) transformer |
| **Latency** | <10ms | <200ms | 50-500ms |
| **Deterministic** | ✅ Yes | ✅ Yes (with PCFG) | ❌ No |
| **Can Count** | ❌ No | ✅ Yes (one stack) | ✅ Yes (learned) |
| **Can Nest** | ❌ No | ✅ Yes (balanced) | ✅ Yes |
| **Semantics** | ❌ No | ❌ No | ✅ Yes |
| **Formal Verification** | ✅ Possible | ✅ Possible | ❌ Difficult |
| **Training Data** | ❌ Not needed | ❌ Not needed | ✅ Required (large) |
| **Hallucination Risk** | ✅ None | ✅ None | ❌ High |
| **Explainability** | ✅ Full | ✅ Full | ❌ Limited |

**Recommendation**: Use FST → CFG → Neural progression (simplest sufficient formalism).

---

## References

### Formal Language Theory

1. **Hopcroft, J.E., Motwani, R., Ullman, J.D.** (2006). Introduction to Automata Theory, Languages, and Computation (3rd ed.). Pearson.
   - Comprehensive treatment of Chomsky hierarchy

2. **Sipser, M.** (2012). Introduction to the Theory of Computation (3rd ed.). Cengage Learning.
   - Pumping lemmas, decidability

3. **Chomsky, N.** (1956). Three models for the description of language. IRE Transactions on Information Theory, 2(3), 113-124.
   - Original hierarchy definition

### Text Normalization Limitations

4. **Sproat, R., Jaitly, N.** (2016). RNN Approaches to Text Normalization: A Challenge. arXiv:1611.00068.
   - "Unrecoverable errors" in neural approaches

5. **Bakhturina, E., et al.** (2021). NeMo Inverse Text Normalization: From Development To Production. arXiv:2104.05055.
   - "Low tolerance towards unrecoverable errors is the main reason why most ITN systems in production are still largely rule-based"

### Complexity Analysis

6. **Aho, A.V., Ullman, J.D.** (1972). The Theory of Parsing, Translation, and Compiling. Prentice-Hall.
   - Parsing complexity analysis

7. **Earley, J.** (1970). An efficient context-free parsing algorithm. Communications of the ACM, 13(2), 94-102.
   - O(n³) worst case, O(n²) average for unambiguous grammars
