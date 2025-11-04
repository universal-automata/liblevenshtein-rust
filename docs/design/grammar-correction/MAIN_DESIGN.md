# Multi-Layer Grammar and Semantic Error Correction

**Design Document v1.0**
**Date**: 2025-01-04
**Authors**: Design by Claude (Anthropic) based on comprehensive research
**Project**: liblevenshtein-rust

## Table of Contents

1. [Introduction](#1-introduction)
2. [Theoretical Foundations](#2-theoretical-foundations)
3. [String vs Tree Edit Distance](#3-string-vs-tree-edit-distance)
4. [Parsing Algorithms](#4-parsing-algorithms)
5. [Error Correction Theory](#5-error-correction-theory)
6. [Search Strategies for Correction](#6-search-strategies-for-correction)
7. [Tree-sitter Integration](#7-tree-sitter-integration)
8. [BFS Grammar Correction: Detailed Algorithm](#8-bfs-grammar-correction-detailed-algorithm)
9. [Semantic Error Detection](#9-semantic-error-detection)
10. [Semantic Error Correction Approaches](#10-semantic-error-correction-approaches)
11. [Process Calculi and Session Types](#11-process-calculi-and-session-types)
12. [WFST Composition for Multi-Layer Correction](#12-wfst-composition-for-multi-layer-correction)
13. [Implementation Design](#13-implementation-design)
14. [Testing and Evaluation](#14-testing-and-evaluation)
15. [Implementation Roadmap](#15-implementation-roadmap)
16. [Open-Access References](#16-open-access-references)
17. [Open Questions and Future Work](#17-open-questions-and-future-work)

---

## 1. Introduction

### 1.1 Problem Statement

Programming language error correction is fundamentally a multi-level problem. A programmer writes text that may contain errors at different levels of abstraction:

1. **Lexical level**: Typos in identifiers, keywords (`prnt` instead of `print`)
2. **Syntactic level**: Missing punctuation, unbalanced brackets, incorrect grammar
3. **Semantic level**: Type mismatches, undefined variables, scope errors
4. **Behavioral level**: Protocol violations, deadlocks, race conditions (in concurrent systems)

This design document presents a comprehensive architecture for **multi-layer error correction** that addresses errors at all these levels using a unified framework based on **Weighted Finite-State Transducers (WFSTs)** and **breadth-first search (BFS)** over grammar transitions.

Traditional approaches typically handle only one level:
- **Spell checkers** correct lexical errors using edit distance
- **Parser error recovery** fixes syntax errors with heuristics
- **Type checkers** report semantic errors but rarely suggest repairs
- **Static analyzers** detect behavioral issues without correction

Our architecture **composes** these layers, enabling correction that:
- Considers interactions between levels (lexical errors may cause syntax errors)
- Provides globally optimal solutions (minimizes total cost across all layers)
- Leverages feedback (semantic validity informs lexical/syntactic choices)
- Scales efficiently (incremental algorithms, beam search pruning)

### 1.2 Position in Multi-Layer Correction Pipeline

This design integrates with and extends the existing `hierarchical-correction.md` design for liblevenshtein. The complete correction pipeline is:

```
┌─────────────────────────────────────────────────────────────────┐
│                    INPUT: Raw Text with Errors                  │
└──────────────────────┬──────────────────────────────────────────┘
                       │
┌──────────────────────▼──────────────────────────────────────────┐
│  LAYER 1: Lexical Correction (liblevenshtein)                   │
│  ┌──────────────────────────────────────────────────────────┐  │
│  │ • Universal Levenshtein Automata                         │  │
│  │ • Character-level edit distance                          │  │
│  │ • Dictionary lookup with fuzzy matching                  │  │
│  │ • Output: Top-k token corrections                        │  │
│  └──────────────────────────────────────────────────────────┘  │
│  Complexity: O(n × d) per token, d = max distance              │
│  Weight: Tropical semiring (min edit cost)                      │
└──────────────────────┬──────────────────────────────────────────┘
                       │ corrected tokens
┌──────────────────────▼──────────────────────────────────────────┐
│  LAYER 2: Grammar Correction (THIS DOCUMENT)                    │
│  ┌──────────────────────────────────────────────────────────┐  │
│  │ • Tree-sitter GLR parsing                                │  │
│  │ • BFS over parse state transitions                       │  │
│  │ • LookaheadIterator for valid symbols                    │  │
│  │ • Incremental reparsing for efficiency                   │  │
│  │ • Output: Syntactically valid parse trees                │  │
│  └──────────────────────────────────────────────────────────┘  │
│  Complexity: O(beam_width × distance × parse_time)              │
│  Weight: Tropical semiring (min syntax repair cost)             │
└──────────────────────┬──────────────────────────────────────────┘
                       │ valid parse trees
┌──────────────────────▼──────────────────────────────────────────┐
│  LAYER 3: Semantic Validation (THIS DOCUMENT)                   │
│  ┌──────────────────────────────────────────────────────────┐  │
│  │ • Type checking (Hindley-Milner)                         │  │
│  │ • Scope analysis (undefined variables)                   │  │
│  │ • Arity checking (function arguments)                    │  │
│  │ • Output: Semantically valid subset of candidates        │  │
│  └──────────────────────────────────────────────────────────┘  │
│  Complexity: O(n log n) per candidate (type inference)          │
│  Weight: Semantic error count                                   │
└──────────────────────┬──────────────────────────────────────────┘
                       │ type-correct programs
┌──────────────────────▼──────────────────────────────────────────┐
│  LAYER 4: Semantic Repair (THIS DOCUMENT)                       │
│  ┌──────────────────────────────────────────────────────────┐  │
│  │ • Error localization (SHErrLoc-style)                    │  │
│  │ • Constraint solving (SMT-based repair)                  │  │
│  │ • Template-based fixes                                   │  │
│  │ • Output: Repaired programs with suggestions             │  │
│  └──────────────────────────────────────────────────────────┘  │
│  Complexity: O(constraints × paths) for localization            │
│  Weight: Repair cost                                            │
└──────────────────────┬──────────────────────────────────────────┘
                       │ repaired programs
┌──────────────────────▼──────────────────────────────────────────┐
│  LAYER 5: Process Verification (THIS DOCUMENT)                  │
│  ┌──────────────────────────────────────────────────────────┐  │
│  │ • Session type checking (for process calculi)            │  │
│  │ • Behavioral type validation                             │  │
│  │ • Deadlock detection                                     │  │
│  │ • Race condition analysis                                │  │
│  │ • Output: Verified correct concurrent programs           │  │
│  └──────────────────────────────────────────────────────────┘  │
│  Complexity: O(n) for session type checking                     │
│  Weight: Protocol violation count                               │
└──────────────────────┬──────────────────────────────────────────┘
                       │
┌──────────────────────▼──────────────────────────────────────────┐
│  FEEDBACK MECHANISM                                             │
│  ┌──────────────────────────────────────────────────────────┐  │
│  │ • Update Layer 1-2 weights based on semantic results     │  │
│  │ • Prefer lexical/grammar corrections that lead to        │  │
│  │   semantically valid programs                            │  │
│  │ • Learn from correction history                          │  │
│  └──────────────────────────────────────────────────────────┘  │
└─────────────────────────────────────────────────────────────────┘
                       │
┌──────────────────────▼──────────────────────────────────────────┐
│              OUTPUT: Corrected, Verified Program                │
└─────────────────────────────────────────────────────────────────┘
```

**Key Integration Points**:
- Layer 1 uses existing liblevenshtein Levenshtein automata (see `hierarchical-correction.md`)
- Layers 2-5 are the focus of this document
- WFST composition unifies all layers (Section 12)
- Feedback improves Layer 1-2 over time

### 1.3 Key Challenges

**Challenge 1: Why String Techniques Don't Generalize to Trees**

Levenshtein automata work beautifully for spell checking because strings are **linear**:
- State = (position, errors_remaining)
- Size = O(n × k) for string length n, max errors k
- Recognition in O(n) time

Parse trees are **hierarchical**:
- State must track position in tree + error context for all subtrees
- Size explodes exponentially
- Tree edit distance requires O(n²m²) dynamic programming (Zhang-Shasha algorithm)

**We cannot directly build a "parse tree Levenshtein automaton"**. Instead, we use **BFS over parser states**.

**Challenge 2: Computational Complexity**

| Level | Algorithm | Time Complexity | Space |
|-------|-----------|----------------|-------|
| Lexical | Levenshtein automaton | O(n) | O(n) |
| Grammar | BFS + parsing | O(beam × d × parse) | O(beam) |
| Semantic | Type inference | O(n log n) avg | O(n) |
| Process | Session types | O(n) | O(n) |

For a 100-token program with distance d=2, beam width=20:
- Grammar: ~20 × 2 × 5ms = 200ms
- Semantic: 20 × 1ms = 20ms
- Process: 5ms
- **Total: ~225ms** (acceptable for IDE use if optimized)

**Challenge 3: Search Space Explosion**

The space of possible corrections grows exponentially:
- 10 tokens, alphabet size 100, distance 2: ~10^6 candidates
- **Mitigation**: Beam search (keep top-k only)

**Challenge 4: Error Cascades**

A single lexical error may cause multiple syntax errors:
```
Input:  "for i in rang(10):"

Lexical: "rang" → "range" (1 error)
Grammar: Missing block (1 error)
Total:   2 reported errors, but only 1 root cause
```

**Mitigation**: Multi-layer architecture isolates concerns.

### 1.4 Contributions of This Design

This document makes the following contributions:

1. **Unified Framework**: WFST composition for multi-layer correction (first of its kind)
2. **BFS Grammar Correction**: Novel application of BFS to Tree-sitter LookaheadIterator
3. **Semantic Integration**: Combines grammar and type correction in principled way
4. **Process Calculi**: Session type checking for Rholang (process calculus)
5. **Practical Focus**: 30-week implementation roadmap with concrete milestones
6. **Open-Access Resources**: 80+ curated open-access papers for implementation
7. **Rholang Implementation**: Complete working example throughout

### 1.5 Document Roadmap

**Part I: Foundations (Sections 2-3)**
Build theoretical understanding from first principles.

**Part II: Grammar Correction (Sections 4-8)**
Parsing algorithms, error correction theory, Tree-sitter integration, BFS algorithm.

**Part III: Semantic Correction (Sections 9-11)**
Type systems, error localization, repair strategies, process calculi.

**Part IV: Integration (Sections 12-13)**
WFST composition, multi-layer architecture, implementation design.

**Part V: Practice (Sections 14-17)**
Testing, roadmap, references, future work.

**Reader Background**: Assumes familiarity with:
- Basic automata theory (DFA, NFA, regular expressions)
- Algorithms and data structures (graphs, dynamic programming)
- Programming language concepts (parsing, type checking)

**No prior knowledge assumed** of:
- Tree edit distance algorithms
- Process calculi
- WFST composition
- SMT solvers

---

## 2. Theoretical Foundations

This section establishes the formal groundwork for multi-layer error correction. We build from the **Chomsky hierarchy** (relating language classes to automata), through **type theory** (for semantic correctness), to **process calculi** (for concurrent systems).

### 2.1 The Chomsky Hierarchy

The Chomsky hierarchy classifies formal languages by their generative power:

```
Type 0: Recursively Enumerable Languages
    ├─ Recognized by: Turing machines
    ├─ Generated by: Unrestricted grammars
    └─ Power: Can recognize any computable language
        │
        ▼
Type 1: Context-Sensitive Languages
    ├─ Recognized by: Linear-bounded automata
    ├─ Generated by: Context-sensitive grammars
    └─ Power: Production rules can depend on context
        │
        ▼
Type 2: Context-Free Languages ◄── FOCUS (programming languages)
    ├─ Recognized by: Pushdown automata
    ├─ Generated by: Context-free grammars
    └─ Power: Nested structures (balanced parentheses)
        │
        ▼
Type 3: Regular Languages ◄── FOCUS (lexical analysis)
    ├─ Recognized by: Finite automata
    ├─ Generated by: Regular grammars / Regular expressions
    └─ Power: Sequential patterns (no nesting)
```

**Key Theorem**: A language is context-free if and only if it is accepted by some pushdown automaton.

**Relevance to Error Correction**:
- **Lexical errors** (Layer 1) operate at Type 3 (regular languages)
  - Levenshtein automata are finite automata
  - Efficient: O(n) recognition
- **Grammar errors** (Layer 2) operate at Type 2 (context-free languages)
  - Requires pushdown automata or equivalent (GLR parsing)
  - Less efficient: O(n³) worst-case parsing
- **Semantic/Process errors** (Layers 3-5) operate beyond Chomsky hierarchy
  - Require external semantic models (type systems, session types)
  - Can be undecidable in general

**Why CFG for Programming Languages?**

Context-free grammars can express:
- Nested structures: `{ { } }`, `( ( ) )`
- Recursive definitions: `Expr → Expr + Expr`
- Hierarchical syntax: function calls, control flow

But cannot express (require Type 1 or semantic checks):
- Context-sensitivity: `a^n b^n c^n` (three balanced symbols)
- Scope rules: variable must be declared before use
- Type constraints: function arguments must match parameter types

### 2.2 Regular Languages and Finite Automata

**Definition**: A **finite automaton** is a 5-tuple M = (Q, Σ, δ, q₀, F) where:
- Q: Finite set of states
- Σ: Input alphabet
- δ: Q × Σ → Q (transition function, DFA) or δ: Q × Σ → 2^Q (NFA)
- q₀ ∈ Q: Initial state
- F ⊆ Q: Accepting states

**Example**: DFA recognizing strings with even number of 'a's:

```
    ┌─────┐  a   ┌─────┐
    │ q₀  ├─────→│ q₁  │
    │(even)│←─────┤(odd)│
    └──┬──┘  a   └──┬──┘
       │            │
       └──b─────────┘ b (self-loops)

States: Q = {q₀, q₁}
Alphabet: Σ = {a, b}
Transitions:
  δ(q₀, a) = q₁
  δ(q₁, a) = q₀
  δ(q₀, b) = q₀
  δ(q₁, b) = q₁
Initial: q₀
Accepting: F = {q₀}
```

**Closure Properties** (used in error correction):
- **Union**: L₁ ∪ L₂ is regular (combine automata)
- **Concatenation**: L₁ · L₂ is regular
- **Kleene Star**: L* is regular
- **Complement**: Regular languages closed under complement

**Key Property**: Regular languages have **finite memory** (bounded by number of states). This makes Levenshtein automata possible for spell checking.

**Non-Example**: L = {a^n b^n | n ≥ 0} is **not regular**
- Requires unbounded counting
- Pumping lemma proves this

This is why balanced parentheses (CFG, not regular) require more powerful parsing.

### 2.3 Context-Free Grammars

**Definition**: A **context-free grammar** is a 4-tuple G = (V, Σ, R, S) where:
- V: Finite set of non-terminal symbols
- Σ: Finite set of terminal symbols (V ∩ Σ = ∅)
- R: Finite set of production rules (V → (V ∪ Σ)*)
- S ∈ V: Start symbol

**Example**: Arithmetic expression grammar:

```
E → E + T
  | T

T → T * F
  | F

F → ( E )
  | number
  | identifier
```

Non-terminals: V = {E, T, F}
Terminals: Σ = {+, *, (, ), number, identifier}
Start symbol: S = E

**Derivation** (how to produce strings):

```
E ⇒ E + T
  ⇒ T + T
  ⇒ F + T
  ⇒ number + T
  ⇒ number + T * F
  ⇒ number + F * F
  ⇒ number + number * number

Produces: "number + number * number" (e.g., "3 + 4 * 5")
```

**Parse Tree** (hierarchical structure):

```
          E
        / │ \
       E  +  T
       │   / │ \
       T  T  *  F
       │  │     │
       F  F  number
       │  │
   number number

Represents: (3 + 4) * 5  [operator precedence via tree structure]
```

**Ambiguity**: A grammar is **ambiguous** if some string has multiple parse trees.

Example (ambiguous grammar):
```
E → E + E | E * E | number

String "1 + 2 * 3" has TWO parse trees:

     E                    E
   / │ \                / │ \
  E  +  E              E  *  E
 /│\   /│\            /│\   │
E * E  E number      E + E  number
│   │  │            │   │
1   2  3            1   2
                    3

Left tree: (1 + 2) * 3 = 9
Right tree: 1 + (2 * 3) = 7  [WRONG for typical precedence]
```

**Solution**: Use precedence and associativity (see grammar at start of section).

**Left Recursion**: Production A → Aα is **left-recursive**.
- Problem: Naive top-down parsers loop infinitely
- Solution: Left-recursion elimination (transform grammar)

**Relevance to Error Correction**:
- CFG defines what is **syntactically valid**
- Error correction: Find minimal edits to make input derivable from grammar
- Ambiguity complicates correction (multiple valid interpretations)

### 2.4 Pushdown Automata

**Definition**: A **pushdown automaton (PDA)** is a 7-tuple M = (Q, Σ, Γ, δ, q₀, Z₀, F) where:
- Q: Finite set of states
- Σ: Input alphabet
- Γ: Stack alphabet
- δ: Q × (Σ ∪ {ε}) × Γ → P(Q × Γ*) (transition function)
- q₀ ∈ Q: Initial state
- Z₀ ∈ Γ: Initial stack symbol
- F ⊆ Q: Accepting states

**Key Difference from Finite Automata**: Unbounded **stack** for memory.

**Example**: PDA for L = {a^n b^n | n ≥ 0} (balanced strings):

```
States: Q = {q₀, q₁, q₂}
Input: Σ = {a, b}
Stack: Γ = {Z₀, A} (Z₀ = bottom marker, A = symbol)

Transitions:
1. δ(q₀, a, Z₀) = {(q₀, AZ₀)}     // Push A for each 'a', keep Z₀
2. δ(q₀, a, A)  = {(q₀, AA)}      // Push A for each 'a'
3. δ(q₀, b, A)  = {(q₁, ε)}       // Pop A for each 'b'
4. δ(q₁, b, A)  = {(q₁, ε)}       // Continue popping
5. δ(q₁, ε, Z₀) = {(q₂, Z₀)}      // Accept if stack back to Z₀

Accepting: F = {q₂}

Execution on "aabb":
(q₀, aabb, Z₀)  ⊢ (q₀, abb, AZ₀)    [push A]
                ⊢ (q₀, bb, AAZ₀)     [push A]
                ⊢ (q₁, b, AZ₀)       [pop A]
                ⊢ (q₁, ε, Z₀)        [pop A]
                ⊢ (q₂, ε, Z₀)        [accept]  ✓
```

**CFG ↔ PDA Equivalence**:

**Theorem**: For any CFG G, there exists a PDA M such that L(G) = L(M), and vice versa.

**Construction** (CFG → PDA):
- Stack stores grammar symbols
- Simulate leftmost derivation
- Terminals matched with input
- Non-terminals replaced using productions

**Relevance to Error Correction**:
- PDA captures essence of parsing (stack for nested structures)
- Error correction must handle stack operations
- Modern parsers (LR, GLR) use stack explicitly

### 2.5 Parse Trees vs Abstract Syntax Trees

**Parse Tree** (Concrete Syntax Tree):
- Represents exact grammatical structure
- Includes all symbols (keywords, punctuation, etc.)
- Preserves source formatting

**Abstract Syntax Tree** (AST):
- Represents semantic meaning
- Omits syntactic details
- Optimized for compilation/interpretation

**Example** (Python code):

```python
if x > 0:
    print(x)
```

**Parse Tree** (concrete):
```
        if_statement
        /    |    |   \
      IF   expr  :   block
           /|\        /   \
          x > 0    NEWLINE print_statement
                            /      |     \
                        print      (   expr_list   )
                                        |
                                     identifier
                                        |
                                        x
```

**Abstract Syntax Tree** (semantic):
```
    IfStmt
    /    \
Condition  Body
   |        |
 Greater  Call
  / \      /  \
 x   0  print  [x]
```

**Key Differences**:

| Aspect | Parse Tree | AST |
|--------|-----------|-----|
| Size | Larger (all symbols) | Smaller (semantic only) |
| Keywords | Included (`if`, `:`) | Omitted (implicit in IfStmt) |
| Punctuation | Included (`(`, `)`, `,`) | Omitted |
| Whitespace | Sometimes (depends on parser) | Never |
| Use Case | Error recovery, formatting | Compilation, analysis |

**Relevance to Error Correction**:
- **Grammar correction** (Layer 2) produces parse trees
  - Need concrete syntax for source reconstruction
  - Preserve user's formatting preferences
- **Semantic correction** (Layers 3-4) operates on ASTs
  - Type checking doesn't care about parentheses
  - More efficient (smaller trees)

**Conversion**:
```rust
fn parse_tree_to_ast(parse_tree: &ParseTree) -> AST {
    match parse_tree.kind {
        "if_statement" => {
            let condition = parse_tree_to_ast(parse_tree.child_by_field("condition"));
            let body = parse_tree_to_ast(parse_tree.child_by_field("consequence"));
            AST::IfStmt { condition: Box::new(condition), body: Box::new(body) }
        }
        // ... more cases
    }
}
```

### 2.6 Type Theory Basics

**Type theory** provides a formal framework for reasoning about program correctness. We focus on **simply-typed lambda calculus (STLC)** and **Hindley-Milner** type inference.

#### 2.6.1 Simply-Typed Lambda Calculus

**Syntax**:
```
Types:     τ ::= α | τ₁ → τ₂
Terms:     e ::= x | λx:τ. e | e₁ e₂
Contexts:  Γ ::= ∅ | Γ, x:τ
```

Where:
- α: Base types (Int, Bool, etc.)
- τ₁ → τ₂: Function type (τ₁ to τ₂)
- x: Variables
- λx:τ. e: Lambda abstraction (function definition)
- e₁ e₂: Application (function call)

**Typing Rules**:

```
         (Var)
    ────────────── (x:τ ∈ Γ)
     Γ ⊢ x : τ


      Γ, x:τ₁ ⊢ e : τ₂
    ───────────────────────  (Abs)
    Γ ⊢ λx:τ₁. e : τ₁ → τ₂


    Γ ⊢ e₁ : τ₁ → τ₂    Γ ⊢ e₂ : τ₁
    ───────────────────────────────  (App)
           Γ ⊢ e₁ e₂ : τ₂
```

**Example**:

```
Term: λx:Int. λy:Int. x + y
Type: Int → (Int → Int)

Derivation:
  x:Int, y:Int ⊢ x : Int        (Var)
  x:Int, y:Int ⊢ y : Int        (Var)
  x:Int, y:Int ⊢ (+) : Int → Int → Int  (Constant)
  ─────────────────────────────────────
  x:Int, y:Int ⊢ x + y : Int    (App twice)
  ─────────────────────────────────────
  x:Int ⊢ λy:Int. x + y : Int → Int     (Abs)
  ─────────────────────────────────────
  ∅ ⊢ λx:Int. λy:Int. x + y : Int → Int → Int  (Abs)
```

**Type Safety** (fundamental theorems):

**Progress**: If ∅ ⊢ e : τ, then either e is a value or e → e' for some e'.
- *Well-typed terms don't get stuck*

**Preservation**: If Γ ⊢ e : τ and e → e', then Γ ⊢ e' : τ.
- *Types are preserved during evaluation*

**Relevance to Error Correction**:
- Type checking catches semantic errors statically
- Error correction: Find minimal edits to make program well-typed
- Type derivations guide repair (Section 10)

#### 2.6.2 Hindley-Milner Type System

**Extension of STLC**: Adds **parametric polymorphism** (generics).

**Syntax**:
```
Types:       τ ::= α | τ₁ → τ₂ | ∀α. τ
Type schemes: σ ::= τ | ∀α. σ
```

**Example**:

```haskell
-- Identity function (polymorphic)
id :: ∀α. α → α
id x = x

-- Usage:
id 5      :: Int
id True   :: Bool
id "hello" :: String
```

**Algorithm W** (type inference):

```
W(Γ, e) → (S, τ)  where S = substitution, τ = type

W(Γ, x):
  if (x:σ) ∈ Γ:
    return (∅, instantiate(σ))  // Replace ∀α with fresh type vars
  else:
    error "Unbound variable"

W(Γ, λx. e):
  α = fresh()                    // Create fresh type variable
  (S, τ) = W(Γ ∪ {x:α}, e)
  return (S, S(α) → τ)

W(Γ, e₁ e₂):
  (S₁, τ₁) = W(Γ, e₁)
  (S₂, τ₂) = W(S₁(Γ), e₂)
  α = fresh()
  S₃ = unify(S₂(τ₁), τ₂ → α)    // τ₁ must be a function type
  return (S₃ ∘ S₂ ∘ S₁, S₃(α))
```

**Unification** (Robinson's algorithm):

```
unify(τ₁, τ₂) → S

unify(α, τ) where α not in τ:
  return {α ↦ τ}

unify(τ, α):
  return unify(α, τ)

unify(τ₁ → τ₂, τ₃ → τ₄):
  S₁ = unify(τ₁, τ₃)
  S₂ = unify(S₁(τ₂), S₁(τ₄))
  return S₂ ∘ S₁

unify(τ, τ):
  return ∅

unify(τ₁, τ₂):
  error "Cannot unify τ₁ and τ₂"
```

**Example** (type inference):

```rust
// Infer type of: \x -> x + 1

W(∅, λx. x + 1):
  α = fresh()  // Let α be type of x
  W({x:α}, x + 1):
    W({x:α}, x) = (∅, α)
    W({x:α}, 1) = (∅, Int)
    W({x:α}, (+)) = (∅, Int → Int → Int)

    Apply (+) to x:
      unify(Int → Int → Int, α → β) where β = fresh()
      Gives: α = Int, result type = Int → Int

    Apply (x + _) to 1:
      unify(Int → Int, Int → γ) where γ = fresh()
      Gives: γ = Int

  Return: (∅, Int → Int)

Result: λx. x + 1 :: Int → Int
```

**Complexity**:
- Best/Average: O(n log n) where n = term size
- Worst: Exponential (due to occurs check in unification)
- Practice: Near-linear for typical programs

**Relevance to Error Correction**:
- Type inference is fundamental to semantic error detection (Section 9)
- Constraint-based type inference enables error localization (Section 10.1)
- Unification failures indicate type errors → repair opportunities

### 2.7 Process Calculi Foundations

**Process calculi** are formal models for concurrent, communicating systems. We focus on **π-calculus** (basis for most process calculi) and **ρ-calculus** (basis for Rholang).

#### 2.7.1 π-Calculus

**Syntax**:
```
Processes:
P, Q ::= 0                     (nil process - does nothing)
       | a!v.P                (send value v on channel a, then P)
       | a?x.P                (receive on channel a, bind to x, then P)
       | P | Q                (parallel composition - run P and Q concurrently)
       | νa.P                 (name restriction - create fresh channel a)
       | !P                   (replication - infinite copies of P)
       | (if c then P else Q) (conditional)
```

**Structural Congruence** (syntactic equivalence):
```
P | 0 ≡ P                      (nil is identity for parallel composition)
P | Q ≡ Q | P                  (parallel composition is commutative)
(P | Q) | R ≡ P | (Q | R)      (parallel composition is associative)
νa.νb.P ≡ νb.νa.P              (order of restrictions doesn't matter)
νa.0 ≡ 0                       (unused restriction is nil)
```

**Reduction Semantics** (operational behavior):

```
        (Comm)
──────────────────────────
a!v.P | a?x.Q → P | Q[x := v]


     P → P'
──────────────  (Par)
P | Q → P' | Q


    P → P'
─────────────  (Res)
νa.P → νa.P'


P ≡ P'   P' → Q'   Q' ≡ Q
──────────────────────────  (Struct)
        P → Q
```

**Example** (simple communication):

```
Process:
  νchannel. (channel!5.0 | channel?x.print(x))

Execution:
  νchannel. (channel!5.0 | channel?x.print(x))
  → νchannel. (0 | print(5))        [Comm: send 5, receive into x]
  → νchannel. print(5)              [Par: simplify]
  → print(5)                        [Res: remove unused channel]
```

**Key Property**: **Mobility** - Channel names can be communicated:

```
νa. (c!a.0 | c?x. x!v.0)

This sends channel 'a' over channel 'c', then sends 'v' over the received channel.
```

#### 2.7.2 ρ-Calculus

**Extension of π-calculus**: Adds **reflection** (higher-order processes).

**Key Idea**:
- **Quotes**: Turn processes into names: `@P`
- **Unquotes**: Turn names back into processes: `*x`

**Syntax**:
```
Processes:
P ::= 0
    | x!(P).Q          (send process P on channel x)
    | x?(@y).Q         (receive process, reflect to name y)
    | P | Q
    | *x               (dereference name to process)

Names:
x, y ::= @P            (quote process to name)
```

**Reflection Laws**:
```
*@P ≡ P                (unquote of quote is identity)
@*x ≡ x                (quote of unquote is identity, if x = @P)
```

**Example** (higher-order communication):

```
Process:
  @P!(Q).R | @P?(@x).S

Reduction:
  @P!(Q).R | @P?(@x).S
  → R | S[x := @Q]                  [Comm: send process Q, bind to name x]

Now S can use *(@Q) to execute the received process Q.
```

**Relevance to Rholang**:
- Rholang is based on ρ-calculus
- Processes are first-class (can be sent/received)
- Enables meta-programming, protocol composition
- More complex semantics → more semantic errors to correct

**Comparison**:

| Feature | π-Calculus | ρ-Calculus (Rholang) |
|---------|-----------|---------------------|
| Channels | Names (first-order) | Processes (higher-order) |
| Communication | Values | Processes |
| Reflection | No | Yes (@P, *x) |
| Power | Basic concurrency | Meta-programming |
| Complexity | Moderate | Higher |

### 2.8 Computational Complexity Primer

**Big-O Notation**: f(n) ∈ O(g(n)) if ∃c, n₀ such that f(n) ≤ c · g(n) for all n ≥ n₀.

**Common Complexities** (from fastest to slowest):

| Notation | Name | Example |
|----------|------|---------|
| O(1) | Constant | Array indexing |
| O(log n) | Logarithmic | Binary search |
| O(n) | Linear | Array scan |
| O(n log n) | Linearithmic | Merge sort, Hindley-Milner (average) |
| O(n²) | Quadratic | Naive string matching, unification (worst) |
| O(n³) | Cubic | CYK parsing, Earley parsing (worst) |
| O(2^n) | Exponential | Naive constraint solving |
| O(n!) | Factorial | Traveling salesman (brute force) |

**Dynamic Programming**: Technique to avoid recomputation by memoizing subproblem results.

**Example** (Fibonacci):

```python
# Naive (exponential):
def fib(n):
    if n <= 1: return n
    return fib(n-1) + fib(n-2)  # Recomputes subproblems

# DP (linear):
def fib_dp(n):
    memo = [0, 1]
    for i in range(2, n+1):
        memo.append(memo[i-1] + memo[i-2])
    return memo[n]
```

**Relevance to Error Correction**:
- Wagner-Fischer (string edit distance): O(mn) via DP
- Zhang-Shasha (tree edit distance): O(n²m²) via DP
- Earley parsing: O(n³) via chart (DP on substrings × grammar symbols)
- Algorithm W (type inference): O(n log n) average, O(n²) worst

**Amortized Complexity**: Average cost per operation over sequence.

**Example**: Dynamic array (vector) push:
- Individual push may take O(n) (when resizing)
- Amortized cost: O(1) (resize infrequent)

**Relevance**:
- Tree-sitter incremental parsing: O(log n) amortized per edit
- Union-Find (unification): O(α(n)) amortized, where α is inverse Ackermann (effectively constant)

### 2.9 Summary of Theoretical Foundations

We've established:

1. **Chomsky Hierarchy**: Language classes and their automata
   - Regular (Type 3) → Lexical errors
   - Context-Free (Type 2) → Grammar errors
   - Beyond → Semantic/Process errors

2. **Finite Automata**: Basis for Levenshtein automata (lexical correction)

3. **CFG and PDA**: Basis for parsing (grammar correction)

4. **Type Theory**: Basis for semantic correctness (type checking, inference)

5. **Process Calculi**: Basis for concurrent systems (Rholang)

6. **Complexity**: Understanding time/space trade-offs

**Next Section**: We explore why string edit distance techniques (Levenshtein automata) don't generalize to trees, motivating our BFS approach for grammar correction.

---

## 3. String vs Tree Edit Distance

This section explains the fundamental difference between **string edit distance** (1-dimensional sequences) and **tree edit distance** (hierarchical structures), and why Levenshtein automata cannot be extended to parse trees.

### 3.1 Levenshtein Distance (String Edit Distance)

**Definition**: The **Levenshtein distance** d(s, t) between strings s and t is the minimum number of single-character edits (insertions, deletions, substitutions) needed to transform s into t.

**Edit Operations**:
1. **Insert**: a → ab (cost 1)
2. **Delete**: ab → a (cost 1)
3. **Substitute**: a → b (cost 1)

**Mathematical Formulation**:

```
d(s[1..i], t[1..j]) = min {
  d(s[1..i-1], t[1..j]) + 1,           // Delete s[i]
  d(s[1..i], t[1..j-1]) + 1,           // Insert t[j]
  d(s[1..i-1], t[1..j-1]) + cost       // Substitute (cost=0 if s[i]=t[j], else 1)
}

Base cases:
d(s[1..i], "") = i    // Delete all
d("", t[1..j]) = j    // Insert all
```

**Example**:

```
s = "SUNDAY"
t = "SATURDAY"

Compute d("SUNDAY", "SATURDAY"):

      ""  S  A  T  U  R  D  A  Y
 ""    0  1  2  3  4  5  6  7  8
 S     1  0  1  2  3  4  5  6  7
 U     2  1  1  2  2  3  4  5  6
 N     3  2  2  2  3  3  4  5  6
 D     4  3  3  3  3  4  3  4  5
 A     5  4  3  4  4  4  4  3  4
 Y     6  5  4  4  5  5  5  4  3

d("SUNDAY", "SATURDAY") = 3

Edit sequence:
  SUNDAY
  STURDAY   (substitute N → T)
  SATURDAY  (insert A after T)
  SATURDAY  (substitute U → A)
```

### 3.2 Wagner-Fischer Algorithm

**Dynamic Programming Solution**:

```python
def edit_distance(s, t):
    m, n = len(s), len(t)
    # Create DP table
    dp = [[0] * (n + 1) for _ in range(m + 1)]

    # Initialize base cases
    for i in range(m + 1):
        dp[i][0] = i  # Delete all of s
    for j in range(n + 1):
        dp[0][j] = j  # Insert all of t

    # Fill table
    for i in range(1, m + 1):
        for j in range(1, n + 1):
            if s[i-1] == t[j-1]:
                cost = 0  # Characters match
            else:
                cost = 1  # Substitution needed

            dp[i][j] = min(
                dp[i-1][j] + 1,      # Delete
                dp[i][j-1] + 1,      # Insert
                dp[i-1][j-1] + cost  # Substitute/Match
            )

    return dp[m][n]
```

**Complexity**:
- Time: O(m × n) where m = |s|, n = |t|
- Space: O(m × n) (can be optimized to O(min(m, n)) with rolling array)

**Backtracking** (recover edit sequence):

```python
def edit_distance_with_path(s, t):
    # ... compute dp table as above ...

    # Backtrack to find edits
    edits = []
    i, j = m, n
    while i > 0 or j > 0:
        if i == 0:
            edits.append(('insert', t[j-1]))
            j -= 1
        elif j == 0:
            edits.append(('delete', s[i-1]))
            i -= 1
        elif s[i-1] == t[j-1]:
            # Match, no edit
            i -= 1
            j -= 1
        else:
            # Find which operation was used
            delete_cost = dp[i-1][j]
            insert_cost = dp[i][j-1]
            substitute_cost = dp[i-1][j-1]

            if delete_cost <= insert_cost and delete_cost <= substitute_cost:
                edits.append(('delete', s[i-1]))
                i -= 1
            elif insert_cost <= substitute_cost:
                edits.append(('insert', t[j-1]))
                j -= 1
            else:
                edits.append(('substitute', s[i-1], t[j-1]))
                i -= 1
                j -= 1

    return dp[m][n], edits[::-1]
```

**Properties**:
- **Optimal Substructure**: Optimal solution contains optimal solutions to subproblems
- **Overlapping Subproblems**: Same subproblems computed multiple times (DP helps)
- **Symmetry**: d(s, t) = d(t, s)
- **Triangle Inequality**: d(s, u) ≤ d(s, t) + d(t, u)
- **Non-negativity**: d(s, t) ≥ 0, with d(s, t) = 0 ⟺ s = t

### 3.3 Levenshtein Automata

**Key Insight**: For fixed string W and distance bound n, we can construct a finite automaton that recognizes exactly the language {V | d(V, W) ≤ n}.

**State Representation**: (position in W, errors remaining, is_special)

**Example**: Levenshtein automaton for W="CAT", n=1:

```
States encode: (position in "CAT", errors used)

State format: q_{position}^{errors}

          C (match)
(0,0) ─────────────→ (1,0)
  │                    │
  │ a,t,... (subst)    │ C (delete)
  │                    ↓
  ↓                  (2,1)
(0,1) ──────────────→
  │      Any char      │
  │                    │
  ...                  ...

Accepting states: {(3,0), (3,1)} = end of "CAT" with ≤1 error

Language recognized: {CAT, CA, AT, CT, CET, CAR, TAT, ...}
                     All strings within distance 1 of "CAT"
```

**Schulz-Mihov Construction**:

```python
def levenshtein_automaton(word, max_dist):
    """
    Construct Levenshtein automaton for given word and max distance.
    Returns: DFA that accepts strings within max_dist edits of word.
    """
    n = len(word)

    # States: (position, errors_used)
    states = set()
    for pos in range(n + 1):
        for errors in range(max_dist + 1):
            states.add((pos, errors))

    initial = (0, 0)
    accepting = {(n, e) for e in range(max_dist + 1)}

    transitions = {}

    for (pos, errors) in states:
        if pos < n:
            # Match
            char = word[pos]
            transitions[((pos, errors), char)] = (pos + 1, errors)

            if errors < max_dist:
                # Insert (read char without advancing in word)
                for c in alphabet:
                    if c != char:
                        transitions[((pos, errors), c)] = (pos, errors + 1)

                # Delete (advance in word without reading)
                transitions[((pos, errors), None)] = (pos + 1, errors + 1)

                # Substitute
                for c in alphabet:
                    if c != char:
                        transitions[((pos, errors), c)] = (pos + 1, errors + 1)

    return DFA(states, alphabet, transitions, initial, accepting)
```

**Complexity**:
- **Construction**: O(|W| × n) where |W| = word length, n = max distance
- **Recognition**: O(|V|) where |V| = input string length
- **States**: O(|W| × n) (linear in word length!)

**Why This Works**:
1. **Finite state space**: Position ∈ [0, |W|], errors ∈ [0, n]
2. **Markov property**: Future depends only on current state, not history
3. **Sequential nature**: Strings are 1-dimensional

### 3.4 Applications of Levenshtein Automata

**Spell Checking**:
```python
def spell_check(word, dictionary, max_distance=2):
    """Find all dictionary words within max_distance of word."""
    automaton = levenshtein_automaton(word, max_distance)
    matches = []

    for dict_word in dictionary:
        if automaton.accepts(dict_word):
            matches.append((dict_word, edit_distance(word, dict_word)))

    return sorted(matches, key=lambda x: x[1])

# Example:
spell_check("prnt", dictionary, max_distance=1)
# Returns: [("print", 1), ("pint", 1), ("punt", 1)]
```

**Fuzzy Search** (used in liblevenshtein):
```rust
pub struct TransducerBuilder<T> {
    dictionary: Dictionary,
    algorithm: Algorithm,
    max_distance: usize,
}

impl<T> TransducerBuilder<T> {
    pub fn build(self) -> Transducer<T> {
        // Build Levenshtein automaton
        // Compose with dictionary automaton
        // Return combined transducer
    }
}

pub fn query(input: &str, max_distance: usize) -> Vec<(String, usize)> {
    // Returns all dictionary words within max_distance of input
}
```

### 3.5 Tree Edit Distance

**Definition**: The **tree edit distance** TED(T₁, T₂) between trees T₁ and T₂ is the minimum cost sequence of node operations to transform T₁ into T₂.

**Node Operations**:
1. **Insert**: Add new node as child
2. **Delete**: Remove node (children become children of parent)
3. **Relabel**: Change node label

**Constraint**: Must preserve **ancestor relationships** (cannot make ancestor a descendant).

**Example**:

```
T₁:        a               T₂:        a
          / \                        / \
         b   c                      b   d
                                        |
                                        c

TED(T₁, T₂) = 2

Edit sequence:
1. Insert 'd' as child of 'a'
2. Move 'c' to be child of 'd' (equivalently: delete 'c', insert 'c' as child of 'd')

Alternatively:
1. Relabel 'c' → 'd'
2. Insert 'c' as child of new 'd'

Minimum cost: 2
```

**Why More Complex Than Strings**:
- Strings: Linear structure (one next position)
- Trees: Hierarchical (multiple children, arbitrary branching)
- String DP: 2D table (position in s × position in t)
- Tree DP: 4D structure (subtree pairs × forest pairs)

### 3.6 Zhang-Shasha Algorithm

**Key Idea**: Decompose trees into **forests** (ordered sequences of trees), compute edit distance on forests.

**Definitions**:
- **Left-path**: Path from node to leftmost leaf
- **Keyroot**: Rightmost node on each left-path
- **Forest**: Ordered sequence of trees (e.g., children of a node)

**Algorithm Sketch**:

```python
def zhang_shasha(T1, T2):
    """Compute tree edit distance between T1 and T2."""
    # Step 1: Compute keyroots for both trees
    keyrootsClauassistantde,

Based on the comprehensive research and planning, I'll now create the complete design document. However, I realize that creating a 6000-8000 line document in a single Write operation may be too large and could hit limits. Let me create a well-structured, comprehensive document that covers all the essential content in a more focused way.

<function_calls>
<invoke name="TodoWrite">
<parameter name="todos">[{"content": "Create document structure and introduction section", "status": "completed", "activeForm": "Creating document structure and introduction"}, {"content": "Write theoretical foundations (automata, type theory, process calculi)", "status": "in_progress", "activeForm": "Writing theoretical foundations"}, {"content": "Write string vs tree edit distance section", "status": "pending", "activeForm": "Writing edit distance section"}, {"content": "Write parsing algorithms section", "status": "pending", "activeForm": "Writing parsing algorithms"}, {"content": "Write error correction theory section", "status": "pending", "activeForm": "Writing error correction theory"}, {"content": "Write search strategies section", "status": "pending", "activeForm": "Writing search strategies"}, {"content": "Write Tree-sitter integration section", "status": "pending", "activeForm": "Writing Tree-sitter integration"}, {"content": "Write BFS grammar correction algorithm with Rholang subsection", "status": "pending", "activeForm": "Writing BFS algorithm and Rholang implementation"}, {"content": "Write semantic error detection section", "status": "pending", "activeForm": "Writing semantic error detection"}, {"content": "Write semantic error correction approaches section", "status": "pending", "activeForm": "Writing semantic correction approaches"}, {"content": "Write process calculi and session types section", "status": "pending", "activeForm": "Writing process calculi section"}, {"content": "Write WFST multi-layer composition section", "status": "pending", "activeForm": "Writing WFST composition"}, {"content": "Write implementation design section", "status": "pending", "activeForm": "Writing implementation design"}, {"content": "Write testing and evaluation section", "status": "pending", "activeForm": "Writing testing section"}, {"content": "Write implementation roadmap", "status": "pending", "activeForm": "Writing implementation roadmap"}, {"content": "Compile and format all references (80+ papers)", "status": "pending", "activeForm": "Compiling references"}, {"content": "Write open questions and future work section", "status": "pending", "activeForm": "Writing future work section"}]