# MeTTa Operational Semantics

This document presents the operational semantics of MeTTa as defined in the Meta-MeTTa
paper (Meredith et al., 2023). Understanding this foundation is essential before
exploring semantic type checking approaches.

---

## Table of Contents

1. [The State Machine Model](#the-state-machine-model)
2. [Term Syntax](#term-syntax)
3. [Rewrite Rules](#rewrite-rules)
4. [Evaluation Semantics](#evaluation-semantics)
5. [Connection to Type Checking](#connection-to-type-checking)

---

## The State Machine Model

MeTTa computation is modeled as a state machine with four components:

```
State = ⟨i, k, w, o⟩
```

| Component | Name | Description |
|-----------|------|-------------|
| `i` | Input | The input register (term to evaluate) |
| `k` | Knowledge | The knowledge base (database of facts and rules) |
| `w` | Workspace | The working memory (intermediate computation) |
| `o` | Output | The output register (results of computation) |

### State Transitions

Computation proceeds by applying rewrite rules to transform one state into another:

```
⟨i₀, k₀, w₀, o₀⟩ ⟶ ⟨i₁, k₁, w₁, o₁⟩
```

The knowledge base `k` typically remains constant during simple queries but can be
modified by `AddAtom` and `RemAtom` operations.

---

## Term Syntax

MeTTa terms are built from the following constructors:

### Atomic Terms

```
Atom ::= symbol           ; Symbolic atoms (identifiers)
       | number           ; Numeric literals
       | string           ; String literals
       | variable         ; Pattern variables (start with $)
```

### Compound Terms

```
Term ::= Atom                        ; Atomic term
       | (Term₁ Term₂ ... Termₙ)     ; List (ordered sequence)
       | {Term₁ Term₂ ... Termₙ}     ; Multiset (unordered bag)
       | [Pattern | Condition]       ; Comprehension
```

### Lists

Lists are ordered sequences with structural equality:

```
(a b c) ≠ (b a c)     ; Order matters
(a b c) = (a b c)     ; Identical lists are equal
```

### Multisets

Multisets are unordered with multiplicity:

```
{a b c} = {c a b}     ; Order doesn't matter
{a a b} ≠ {a b}       ; Multiplicity matters
```

The multiset equations (commutativity, associativity) are critical for the
Gph-enriched Lawvere theory approach discussed in
[03-gph-enriched-lawvere.md](./03-gph-enriched-lawvere.md).

### Comprehensions

Comprehensions generate terms from patterns:

```
[f($x) | ($x : Nat)]   ; Apply f to all x of type Nat
```

---

## Rewrite Rules

MeTTa uses five core rewrite rules that define its operational behavior.

### Rule 1: Query

Query matches a pattern against the knowledge base:

```
        match(p, k) = {σ₁, σ₂, ..., σₙ}
─────────────────────────────────────────────
⟨p, k, w, o⟩ ⟶ ⟨ε, k, w ∪ {σ₁(p), ...}, o⟩
```

Where:
- `match(p, k)` returns all substitutions σ that unify pattern p with facts in k
- `σᵢ(p)` is the pattern with substitution applied
- Results are added to the workspace w

**Example**:
```
Knowledge base k = {(parent Alice Bob), (parent Bob Carol)}
Pattern p = (parent $x Bob)
Result: σ = {$x ↦ Alice}
Workspace gets: (parent Alice Bob)
```

### Rule 2: Chain

Chain composes patterns to build derivations:

```
        ⟨p₁, k, w, o⟩ ⟶* ⟨ε, k, w₁, o⟩
        ⟨p₂[w₁], k, w₁, o⟩ ⟶* ⟨ε, k, w₂, o⟩
───────────────────────────────────────────────
⟨(chain p₁ p₂), k, w, o⟩ ⟶* ⟨ε, k, w₂, o⟩
```

This enables multi-step reasoning by feeding the results of one query into another.

### Rule 3: Transform

Transform applies a function to workspace contents:

```
            f : Term → Term
────────────────────────────────────
⟨(transform f), k, w, o⟩ ⟶ ⟨ε, k, f(w), o⟩
```

### Rule 4: AddAtom

AddAtom extends the knowledge base:

```
⟨(add-atom t), k, w, o⟩ ⟶ ⟨ε, k ∪ {t}, w, o⟩
```

This makes MeTTa's knowledge base **mutable** during computation.

### Rule 5: RemAtom

RemAtom removes from the knowledge base:

```
⟨(rem-atom t), k, w, o⟩ ⟶ ⟨ε, k \ {t}, w, o⟩
```

### Rule 6: Output

Output moves results to the output register:

```
⟨output, k, w, o⟩ ⟶ ⟨ε, k, ∅, o ∪ w⟩
```

---

## Evaluation Semantics

### Evaluation Order

MeTTa uses a **non-deterministic** evaluation order for multisets, which is essential
for its concurrent semantics. For lists, evaluation proceeds left-to-right.

### Unification

Pattern matching uses **syntactic unification** with the occurs check:

```
unify(t₁, t₂) =
  | t₁ = t₂           → {}           ; Identical terms
  | t₁ = $x           → {$x ↦ t₂}    ; Variable binding (if occurs check passes)
  | t₂ = $x           → {$x ↦ t₁}    ; Variable binding (symmetric)
  | (f a...) = (g b...) → unify(f,g) ∪ unify(a..., b...)  ; Recursive
  | otherwise         → ⊥            ; Failure
```

### Builtin Operations

MeTTa includes builtin operations for:
- Arithmetic: `+`, `-`, `*`, `/`
- Comparison: `<`, `>`, `=`, `≤`, `≥`
- Logic: `and`, `or`, `not`
- Type checking: `get-type`, `has-type`

---

## Connection to Type Checking

The Meta-MeTTa paper explicitly addresses the relationship to types in Section 8:

> "This semantics does not address typed versions of MeTTa. An interesting avenue of
> approach is to apply Meredith and Stay's OSLF to this semantics to derive a type
> system for MeTTa that includes spatial and behavioral types."

### Why OSLF for MeTTa?

MeTTa's operational semantics can be formalized as a **λ-theory with equality**:

| MeTTa Concept | λ-Theory Formalization |
|---------------|------------------------|
| Term sorts | Sorts in the theory signature |
| Constructors | Operations in the signature |
| Multiset equations | Equational axioms |
| Rewrite rules | Internal graph edges (transitions) |
| Pattern variables | Binding structure |

This formalization is the input to the OSLF construction described in
[02-native-type-theory-oslf.md](./02-native-type-theory-oslf.md).

### Effort Objects

The Meta-MeTTa paper mentions "effort objects" for resource accounting:

```
⟨i, k, w, o, e⟩   ; State extended with effort e
```

Where `e` tracks computational resources (steps, memory, time). This connects to the
"gas" mechanism in Gph-enriched Lawvere theories (see
[03-gph-enriched-lawvere.md](./03-gph-enriched-lawvere.md), Section 6).

---

## Formalizing MeTTa as a λ-Theory

To apply OSLF or Gph-theories, we first express MeTTa as a formal theory.

### Signature Σ_MeTTa

```
Sorts:
  Term      ; General terms
  Atom      ; Atomic values
  List      ; Ordered sequences
  MSet      ; Multisets
  State     ; Machine states

Operations:
  nil       : 1 → List
  cons      : Term × List → List
  empty     : 1 → MSet
  insert    : Term × MSet → MSet
  state     : Term × KB × MSet × MSet → State

Equations:
  insert(x, insert(y, m)) = insert(y, insert(x, m))   ; Multiset commutativity
```

### Rewrite Rules as Graph Edges

Each rewrite rule becomes an edge in the internal graph:

```
query   : State → State    ; Query rule transition
chain   : State → State    ; Chain rule transition
transform : State → State  ; Transform rule transition
addAtom : State → State    ; AddAtom transition
remAtom : State → State    ; RemAtom transition
output  : State → State    ; Output transition
```

This graph structure `G = ⟨s, t⟩ : E → State × State` is the foundation for behavioral
types in OSLF.

---

## Summary

MeTTa's operational semantics provides:

1. **State machine model** with four registers (input, knowledge, workspace, output)
2. **Rich term language** including lists, multisets, and comprehensions
3. **Five core rewrite rules** for query, chaining, transformation, and KB modification
4. **Non-deterministic evaluation** for concurrent semantics
5. **Explicit connection to OSLF** for deriving type systems

The next documents explore how to derive semantic types from this operational
foundation:
- [02-native-type-theory-oslf.md](./02-native-type-theory-oslf.md): Full type theory derivation
- [03-gph-enriched-lawvere.md](./03-gph-enriched-lawvere.md): Simpler graph-based approach

---

## References

- Meredith, L. G., et al. "Meta-MeTTa: an operational semantics for MeTTa."
  arXiv:2305.17218, 2023.
- See [bibliography.md](../reference/bibliography.md) for complete references.
