# MeTTaIL Scala Prototype

This document describes the MeTTaIL Scala prototype, its current capabilities, and
how it relates to the goal of semantic type checking for MeTTa.

**Location**: `/home/dylon/Workspace/f1r3fly.io/MeTTaIL/`

---

## Table of Contents

1. [Overview](#overview)
2. [Architecture](#architecture)
3. [Theory Definition Syntax](#theory-definition-syntax)
4. [Hypercube Transformation](#hypercube-transformation)
5. [BNFC Generation](#bnfc-generation)
6. [Relation to OSLF](#relation-to-oslf)
7. [Current Status](#current-status)

---

## Overview

The MeTTaIL Scala prototype is a **theory transformer** that:

1. Accepts theory definitions (sorts, constructors, equations)
2. Validates category-theoretic constraints
3. Transforms theories via the "hypercube" construction
4. Generates BNFC grammars for parser generation

### Design Philosophy

MeTTaIL follows the principle of **theories as first-class objects**:

- Theories are data that can be inspected and transformed
- Type checking arises from categorical structure
- Transformations preserve semantic properties

---

## Architecture

### Core Components

```
┌─────────────────────────────────────────────────────────────┐
│                    MeTTaIL Scala                            │
│                                                             │
│  ┌─────────────┐  ┌──────────────┐  ┌─────────────────┐    │
│  │   Parser    │  │   Theory     │  │   Hypercube     │    │
│  │  (Source)   │──│   Model      │──│   Transform     │    │
│  └─────────────┘  └──────────────┘  └─────────────────┘    │
│         │               │                   │               │
│         ▼               ▼                   ▼               │
│  ┌─────────────┐  ┌──────────────┐  ┌─────────────────┐    │
│  │   AST       │  │  Validation  │  │   BNFC          │    │
│  │             │──│  (Category)  │──│   Generator     │    │
│  └─────────────┘  └──────────────┘  └─────────────────┘    │
└─────────────────────────────────────────────────────────────┘
```

### Key Data Structures

```scala
// Theory representation
case class Theory(
  name: String,
  sorts: List[Sort],
  constructors: List[Constructor],
  equations: List[Equation],
  interpretations: List[Interpretation]
)

// Sort (type in the theory)
case class Sort(
  name: String,
  category: Category  // Domain category for semantics
)

// Constructor (operation in the theory)
case class Constructor(
  name: String,
  domain: List[Sort],   // Input types
  codomain: Sort,       // Output type
  modality: Option[Modality]  // Optional modal annotation
)

// Equation (axiom)
case class Equation(
  lhs: Term,
  rhs: Term
)
```

---

## Theory Definition Syntax

### Basic Theory Structure

```
theory MyTheory {
  // Sort declarations
  sort Term
  sort List
  sort Nat

  // Constructor declarations
  constructor nil : List
  constructor cons : Term × List → List
  constructor zero : Nat
  constructor succ : Nat → Nat

  // Equations (optional)
  equation {
    length(nil) = zero
    length(cons(x, xs)) = succ(length(xs))
  }
}
```

### Category Annotations

Sorts can be annotated with their categorical domain:

```
theory TypedTerms {
  sort Term : Set          // Terms form a set
  sort Type : Preorder     // Types form a preorder (subtyping)
  sort Context : Category  // Contexts form a category

  // Typing judgment as morphism
  constructor typeof : Context × Term → Type
}
```

### Modal Annotations

Constructors can have modality markers:

```
theory ModalTheory {
  sort Prop
  sort World

  constructor box : Prop → Prop      // Necessity □
  constructor diamond : Prop → Prop  // Possibility ◇

  // Modal axiom
  equation {
    box(P) → diamond(P)  // Necessity implies possibility
  }
}
```

---

## Hypercube Transformation

The **hypercube** transformation mechanically lifts an untyped theory to a typed
version by introducing type indices.

### The Idea

Given an untyped theory T, the hypercube H(T) has:
- For each sort S in T, a family of sorts S[τ] indexed by types
- For each constructor f : A → B, a family f[τ] : A[τ] → B[τ]
- Preservation of equations at each type level

### Example: Untyped to Typed Lambda Calculus

**Input**: Untyped lambda calculus theory

```
theory UntypedLambda {
  sort Term

  constructor var : Nat → Term
  constructor app : Term × Term → Term
  constructor lam : Term → Term
}
```

**Output**: Typed lambda calculus via hypercube

```
theory TypedLambda {
  sort Type
  sort Term[Type]  // Terms indexed by type

  constructor base : Type
  constructor arrow : Type × Type → Type

  constructor var[τ] : Nat → Term[τ]
  constructor app[σ,τ] : Term[arrow(σ,τ)] × Term[σ] → Term[τ]
  constructor lam[σ,τ] : Term[τ] → Term[arrow(σ,τ)]
}
```

### Relation to OSLF

The hypercube transformation is **related but distinct** from OSLF:

| Hypercube | OSLF |
|-----------|------|
| Lifts constructors to indexed families | Derives predicates via presheaf |
| Syntactic transformation | Semantic construction |
| Types as indices | Types as predicates |
| Mechanical, uniform | More expressive |

Hypercube is a **subset** of what OSLF can express - it captures type indexing but
not general predicates on terms or behavioral types.

---

## BNFC Generation

MeTTaIL generates BNFC (BNF Converter) grammars from theory definitions.

### What is BNFC?

BNFC is a tool that generates:
- Lexer
- Parser
- Abstract syntax tree types
- Pretty printer

From a grammar specification.

### Generation Process

```
Theory Definition  ──▶  BNFC Grammar  ──▶  Parser/Lexer
       │                     │
       ▼                     ▼
  Validation            Target Language
  (Category)            (Haskell, Scala, etc.)
```

### Example: Generated BNFC

For theory:
```
theory SimpleExpr {
  sort Expr

  constructor num : Int → Expr
  constructor add : Expr × Expr → Expr
  constructor mul : Expr × Expr → Expr
}
```

Generated BNFC:
```
-- Automatically generated by MeTTaIL

entrypoints Expr ;

Num.   Expr ::= Integer ;
Add.   Expr ::= Expr "+" Expr1 ;
Mul.   Expr ::= Expr1 "*" Expr2 ;

coercions Expr 2 ;
```

### Benefits

1. **Consistency**: Parser matches theory exactly
2. **Automation**: No manual parser maintenance
3. **Type safety**: Generated types match theory sorts

---

## Relation to OSLF

### What MeTTaIL Scala Provides

| Feature | Status | Relation to OSLF |
|---------|--------|------------------|
| Theory definition syntax | ✅ Complete | Provides λ-theory input |
| Hypercube transformation | ✅ Working | Related, less expressive |
| Modal types (◇) | 🔄 Partial | Similar goal, different mechanism |
| Category/sort validation | ✅ Complete | Necessary foundation |
| BNFC generation | ✅ Complete | Parser generation |
| Interpretation checking | ✅ Complete | Semantic consistency |

### Gaps for Full OSLF

To implement full OSLF, MeTTaIL Scala would need:

1. **Presheaf construction**
   - Compute P(T) from theory T
   - Implement Yoneda embedding

2. **Internal language extraction**
   - Extract LP(T) from presheaf topos
   - Generate type formation rules

3. **Predicate language**
   - Define predicates φ : A → Ω
   - Support quantification and substitution

4. **Behavioral types**
   - Internalize rewrite rules as graph
   - Implement step modalities F!, F*

### Extending MeTTaIL Scala

The existing infrastructure is a **good foundation**:

```scala
// Current: Theory validation
def validateTheory(t: Theory): ValidationResult = ...

// Extension: Presheaf construction
def presheafConstruction(t: Theory): Presheaf[Theory] = ...

// Extension: Internal language
def internalLanguage(p: Presheaf[Theory]): TypeTheory = ...
```

---

## Current Status

### Implemented Features

| Component | Status | Notes |
|-----------|--------|-------|
| Theory parser | ✅ Complete | Full syntax support |
| Sort validation | ✅ Complete | Category constraints |
| Constructor validation | ✅ Complete | Type checking |
| Equation parsing | ✅ Complete | Axiom support |
| Hypercube transform | ✅ Working | Index lifting |
| Modal annotations | 🔄 Partial | Basic support |
| BNFC generation | ✅ Complete | Multiple targets |
| Interpretation check | ✅ Complete | Semantic validation |

### Known Limitations

1. **No presheaf construction** - fundamental for OSLF
2. **No behavioral types** - cannot express rewrite properties
3. **Limited modal logic** - basic annotations only
4. **No internal language** - types not extracted

### Recommended Path Forward

1. **Keep using MeTTaIL Scala** for theory definition and BNFC generation
2. **Implement OSLF in mettail-rust** (see [02-mettail-rust-prototype.md](./02-mettail-rust-prototype.md))
3. **Bridge the two** via serialized theory format

---

## Usage Examples

### Defining a Theory

```scala
import mettail._

val lambdaTheory = Theory(
  name = "Lambda",
  sorts = List(
    Sort("Term", Category.Set),
    Sort("Type", Category.Set)
  ),
  constructors = List(
    Constructor("var", List("Nat"), "Term"),
    Constructor("app", List("Term", "Term"), "Term"),
    Constructor("lam", List("Term"), "Term")
  ),
  equations = List()
)

val result = Validator.validate(lambdaTheory)
val bnfc = BNFCGenerator.generate(lambdaTheory)
```

### Applying Hypercube

```scala
val typedTheory = Hypercube.transform(lambdaTheory, "Type")
// Result: Term[Type] indexed by types
```

---

## Summary

The MeTTaIL Scala prototype provides:

1. **Theory definition language** for λ-theories
2. **Category-based validation** of sorts and constructors
3. **Hypercube transformation** for type indexing
4. **BNFC generation** for parser creation

It is a solid foundation for semantic type checking, but requires extension for
full OSLF implementation. The recommended approach is to use MeTTaIL Scala for
theory definition and BNFC, while implementing OSLF in mettail-rust.

---

## References

- MeTTaIL Scala source: `/home/dylon/Workspace/f1r3fly.io/MeTTaIL/`
- BNFC documentation: https://bnfc.digitalgrammars.com/
- See [bibliography.md](../reference/bibliography.md) for complete references.
