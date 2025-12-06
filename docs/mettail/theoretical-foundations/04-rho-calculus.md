# The RHO Calculus

This document presents the ρ-calculus (reflective higher-order calculus), the
theoretical foundation of Rholang. Understanding RHO calculus is essential for
integrating MeTTaIL with Rholang's execution model.

---

## Table of Contents

1. [Overview](#overview)
2. [Syntax](#syntax)
3. [Structural Congruence](#structural-congruence)
4. [Reduction Semantics](#reduction-semantics)
5. [The Reflection Mechanism](#the-reflection-mechanism)
6. [Bisimulation](#bisimulation)
7. [Connection to Type Checking](#connection-to-type-checking)

---

## Overview

The ρ-calculus (Meredith & Radestock, 2005) is a **reflective higher-order process
calculus** that:

1. Provides a **closed theory of processes** - names arise from processes themselves
2. Eliminates **higher-order features** as syntactic sugar via reflection
3. Supports **namespace-based scoping** instead of traditional binding

### Key Innovation

Unlike π-calculus where names are primitive, in ρ-calculus:

> **Names are quoted processes**: x = ⌈P⌉

This reflection mechanism enables:
- Self-referential processes
- Higher-order communication without process variables
- Simpler semantic treatments (binding eliminated via quote/dequote)

---

## Syntax

### Process Syntax (P, Q)

```
P, Q ::= 0           ; Null process (inaction)
       | x(y).P      ; Input: receive on channel x, bind to y in P
       | x⟨|P|⟩      ; Lift: send quoted P on channel x
       | ⌊x⌋         ; Drop: evaluate (dequote) name x
       | P | Q       ; Parallel composition
```

### Name Syntax (x, y)

```
x, y ::= ⌈P⌉         ; Quote: the code of process P as a name
```

### Explanation of Constructs

| Construct | Read as | Description |
|-----------|---------|-------------|
| `0` | "zero" or "nil" | Does nothing, terminated process |
| `x(y).P` | "input y on x then P" | Waits for a message on channel x |
| `x⟨\|P\|⟩` | "lift P on x" | Sends the code of P on channel x |
| `⌊x⌋` | "drop x" | Runs the process whose code is x |
| `P \| Q` | "P par Q" | Runs P and Q concurrently |
| `⌈P⌉` | "quote P" | The name (code) of process P |

### Binding Structure

The input construct `x(y).P` binds the name `y` in the body `P`. Free names are:

```
FN(0)        = ∅
FN(x(y).P)   = {x} ∪ (FN(P) \ {y})
FN(x⟨|P|⟩)   = {x} ∪ FN(P)
FN(⌊x⌋)      = {x}
FN(P | Q)    = FN(P) ∪ FN(Q)
```

---

## Structural Congruence

Structural congruence (≡) identifies processes that differ only in structure:

### Parallel Composition Axioms

```
P | 0 ≡ P                    ; Null is identity
P | Q ≡ Q | P                ; Commutativity
(P | Q) | R ≡ P | (Q | R)    ; Associativity
```

### Alpha Equivalence

```
x(y).P ≡ x(z).P{z/y}         ; Rename bound variable (z fresh)
```

### Name Equivalence

Names have their own equivalence ≡_N based on quotation:

```
⌈P⌉ ≡_N ⌈Q⌉  iff  P ≡ Q      ; Quoted processes equal if bodies congruent
```

The key identity is **quote-drop**:

```
⌈⌊x⌋⌉ ≡_N x                   ; Quote of drop is identity on names
```

This means `x = ⌈⌊x⌋⌉` - every name is the code of some process (namely, its drop).

---

## Reduction Semantics

### Communication Rule (COMM)

The fundamental reduction rule is communication:

```
        x₀ ≡_N x₁
─────────────────────────────────
x₀⟨|Q|⟩ | x₁(y).P  →  P{⌈Q⌉/y}
```

**Reading**: If a lift on channel x₀ meets an input on channel x₁, and these channels
are name-equivalent, then:
- The input receives the **quoted** sender process ⌈Q⌉
- Substituted into the continuation P

### Important: What Gets Sent

The receiver gets `⌈Q⌉` (the **code** of Q), not Q itself. To run Q, the receiver
must drop it:

```
x(y).⌊y⌋      ; Receive code and execute it
```

### Congruence Rules

Reduction is closed under structural congruence:

```
    P ≡ P'    P' → Q'    Q' ≡ Q
   ────────────────────────────
            P → Q
```

And under parallel contexts:

```
        P → P'
   ─────────────────
     P | Q → P' | Q
```

---

## The Reflection Mechanism

The quote-drop mechanism is the heart of RHO calculus.

### Quote: ⌈P⌉

**Quote** reifies a process as a name (its "code"):

```
⌈0⌉             ; Name representing null process
⌈x(y).P⌉        ; Name representing an input process
⌈P | Q⌉         ; Name representing a parallel composition
```

Quoting is **syntactic** - it captures the structure of P, not its behavior.

### Drop: ⌊x⌋

**Drop** executes a name (runs its code):

```
⌊⌈P⌉⌋ ≡ P       ; Drop of quote recovers the process
```

Drop is the inverse of quote on well-formed names.

### Lift: x⟨|P|⟩

**Lift** is output with implicit quotation, but susceptible to substitution:

```
x⟨|P|⟩          ; Output the code of P on channel x
```

The difference from standard output `x⟨⌈P⌉⟩` is that lift's body can contain free
variables that are substituted:

```
(λx.y⟨|x|⟩)(P) = y⟨|P|⟩     ; Substitution penetrates lift
```

### Why Reflection Matters for Type Checking

The RHO paper states:

> "Reflection provides a powerful technique for treating nominal phenomena as
> syntactic sugar, thus paving the way for simpler semantic treatments."

This validates using Gph-enriched Lawvere theories
([03-gph-enriched-lawvere.md](./03-gph-enriched-lawvere.md)) for the
MeTTaIL/Rholang integration:

- Bound variables can be eliminated via quote/drop
- Higher-order features encoded without process variables
- Simpler operational semantics suffice

---

## Bisimulation

### N-Barbed Bisimulation

The paper parameterizes bisimulation by a set N of **observable names**:

**Definition (N-Barb)**: Process P has an N-barb at name x, written P ↓_N x, if:
- P can input or output on x
- x ∈ N (the name is observable)

**Definition (N-Barbed Bisimulation)**: A relation R is an N-barbed bisimulation if
whenever P R Q:

1. **Reduction closure**: If P → P' then ∃Q'. Q →* Q' and P' R Q'
2. **Barb preservation**: If P ↓_N x then Q ⇓_N x (weak barb)
3. **Symmetry**: The same conditions hold with P and Q swapped

### Why Parameterized Bisimulation?

N-parameterization enables:

1. **Scope reasoning**: Only observe names in scope
2. **Namespace security**: Verify isolation properties
3. **Behavioral types**: Types as predicates on observable names

### Example: Namespace Security

```
; Process that only communicates on namespace α
safe(α) := P where FN(P) ⊆ α ∧ P ↓_N x ⟹ x ∈ α

; Compile-time firewall (from OSLF):
sole.in(α) := νX. (in(α, N → X) | P) ∧ ¬[in(¬[α], N → P) | P]
```

This type says: "Can input on channels in α and cannot input on ¬α."

---

## Derived Constructs

### Private Names (ν)

Unlike π-calculus, RHO doesn't need primitive `ν` (new name). It's derived:

```
(νx)P := P{⌈0⌉/x}     ; Use a fresh quoted process
```

More generally, use any term guaranteed to be fresh.

### Replication (!)

Replication is also derived (using recursion through reflection):

```
!P := ⌊⌈P | ⌊⌈P⌉⌋⌉⌋    ; Self-replicating via quote-drop
```

Or using a standard fixed-point encoding.

### Higher-Order Communication

Sending and receiving processes directly:

```
; Higher-order send (send process P on channel x)
ho-send(x, P) := x⟨|P|⟩

; Higher-order receive (receive and run)
ho-recv(x) := x(y).⌊y⌋

; Communication:
ho-send(x, P) | ho-recv(x) → P
```

---

## Connection to Type Checking

### RHO Calculus in Rholang

Rholang is essentially an implementation of RHO calculus with:
- Concrete syntax for processes
- System processes for I/O, storage, etc.
- Integration with RSpace (tuple space)

### Integration with MeTTaIL

Since MeTTaIL will become the next version of Rholang:

1. **MeTTaIL provides type checking** at compile time
2. **RHO calculus runtime** executes the typed processes
3. **Behavioral types** from OSLF match RHO's bisimulation semantics

### The Bridge: Quote/Drop ↔ MeTTa Quotation

MeTTa also has quotation (terms as data). The correspondence:

| RHO Calculus | MeTTa |
|--------------|-------|
| ⌈P⌉ (quote) | `(quote P)` |
| ⌊x⌋ (drop) | `(eval x)` or unquote |
| P \| Q | Parallel in knowledge base |
| x(y).P | Pattern matching with binding |

### Behavioral Types for RHO/Rholang

Using OSLF on RHO calculus gives behavioral types:

```
; Type of processes that always respond on channel x
Responsive(x) := □(◇(↓_x))

; Type of processes that never deadlock
Deadlock-free := □(0 ∨ ◇(→))

; Type of processes that terminate
Terminating := ◇(≡ 0)
```

These types can be checked at compile time by MeTTaIL and enforced at runtime by
Rholang.

---

## Summary

The RHO calculus provides:

1. **Closed theory of processes** - names arise from quotation
2. **Reflection mechanism** - quote/drop for code as data
3. **Simpler semantics** - binding eliminated via reflection
4. **N-barbed bisimulation** - behavioral equivalence parameterized by observables
5. **Foundation for Rholang** - the theoretical model for execution

The reflection mechanism is key to the MeTTaIL integration: it enables the simpler
Gph-enriched Lawvere approach while maintaining full expressiveness.

---

## References

- Meredith, L. G. & Radestock, M. "A Reflective Higher-order Calculus."
  ENTCS 141(5), pp. 49-67, 2005.
- Sangiorgi, D. "The π-calculus: A Theory of Mobile Processes." Cambridge, 2001.
- See [bibliography.md](../reference/bibliography.md) for complete references.
