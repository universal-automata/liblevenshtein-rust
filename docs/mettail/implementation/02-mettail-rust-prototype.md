# MeTTaIL Rust Prototype

This document describes the mettail-rust prototype, its architecture, and how it
can be extended for full semantic type checking.

**Location**: `/home/dylon/Workspace/f1r3fly.io/mettail-rust/`

---

## Table of Contents

1. [Overview](#overview)
2. [Architecture](#architecture)
3. [Core Components](#core-components)
4. [Rewrite Engine](#rewrite-engine)
5. [Ascent Datalog Integration](#ascent-datalog-integration)
6. [Relation to OSLF](#relation-to-oslf)
7. [Extension Plan](#extension-plan)

---

## Overview

The mettail-rust prototype is a **Rust implementation** of MeTTaIL focused on:

1. High-performance rewrite execution
2. Category-based type checking
3. Datalog-powered analysis (via Ascent)
4. Foundation for OSLF implementation

### Design Goals

- **Performance**: Rust's zero-cost abstractions for fast execution
- **Safety**: Strong typing prevents runtime errors
- **Extensibility**: Modular architecture for adding OSLF components
- **Integration**: Compatible with Rholang's Rust runtime

---

## Architecture

### High-Level Structure

```
┌─────────────────────────────────────────────────────────────────┐
│                       mettail-rust                              │
│                                                                 │
│  ┌──────────────┐  ┌───────────────┐  ┌───────────────────┐    │
│  │    Parser    │  │    Theory     │  │    Type           │    │
│  │   (LALRPOP)  │──│    Model      │──│    Checker        │    │
│  └──────────────┘  └───────────────┘  └───────────────────┘    │
│         │                │                    │                 │
│         ▼                ▼                    ▼                 │
│  ┌──────────────┐  ┌───────────────┐  ┌───────────────────┐    │
│  │     AST      │  │   Rewrite     │  │    Ascent         │    │
│  │              │──│   Engine      │──│    Datalog        │    │
│  └──────────────┘  └───────────────┘  └───────────────────┘    │
└─────────────────────────────────────────────────────────────────┘
```

### Module Organization

```
mettail-rust/
├── src/
│   ├── lib.rs           # Library root
│   ├── parser/          # LALRPOP grammar and AST
│   ├── theory/          # Theory representation
│   ├── types/           # Type checking logic
│   ├── rewrite/         # Rewrite engine
│   ├── datalog/         # Ascent integration
│   └── codegen/         # Code generation
├── tests/               # Test suite
└── benches/             # Benchmarks
```

---

## Core Components

### Theory Representation

```rust
/// A complete theory definition
pub struct Theory {
    pub name: String,
    pub sorts: Vec<Sort>,
    pub constructors: Vec<Constructor>,
    pub equations: Vec<Equation>,
    pub rewrites: Vec<RewriteRule>,
}

/// A sort (type in the theory)
pub struct Sort {
    pub name: String,
    pub category: Category,
}

/// A constructor (operation)
pub struct Constructor {
    pub name: String,
    pub params: Vec<Param>,
    pub result: SortRef,
}

/// A rewrite rule
pub struct RewriteRule {
    pub name: String,
    pub lhs: Pattern,
    pub rhs: Term,
    pub conditions: Vec<Condition>,
}
```

### Category Constraints

Sorts are validated against categorical constraints:

```rust
pub enum Category {
    Set,        // Plain sets
    Preorder,   // Reflexive, transitive
    Poset,      // Antisymmetric preorder
    Category,   // General category
    Groupoid,   // All morphisms invertible
}

impl Category {
    /// Check if a sort satisfies its category constraints
    pub fn validate(&self, sort: &Sort, theory: &Theory) -> Result<(), TypeError> {
        match self {
            Category::Preorder => self.check_preorder_axioms(sort, theory),
            Category::Poset => self.check_poset_axioms(sort, theory),
            // ...
        }
    }
}
```

### Type Checking

Type checking validates constructor usage:

```rust
pub struct TypeChecker {
    theory: Theory,
    context: Context,
}

impl TypeChecker {
    /// Type check a term against expected sort
    pub fn check(&self, term: &Term, expected: &Sort) -> Result<(), TypeError> {
        let inferred = self.infer(term)?;
        if self.is_subtype(&inferred, expected) {
            Ok(())
        } else {
            Err(TypeError::Mismatch { expected, found: inferred })
        }
    }

    /// Infer the sort of a term
    pub fn infer(&self, term: &Term) -> Result<Sort, TypeError> {
        match term {
            Term::Var(v) => self.context.lookup(v),
            Term::App(ctor, args) => {
                let ctor_def = self.theory.get_constructor(ctor)?;
                for (arg, param) in args.iter().zip(&ctor_def.params) {
                    self.check(arg, &param.sort)?;
                }
                Ok(ctor_def.result.clone())
            }
        }
    }
}
```

---

## Rewrite Engine

The rewrite engine executes transformation rules efficiently.

### Pattern Matching

```rust
/// A substitution maps variables to terms
pub type Substitution = HashMap<Var, Term>;

/// Match a pattern against a term
pub fn match_pattern(pattern: &Pattern, term: &Term) -> Option<Substitution> {
    let mut subst = Substitution::new();
    match_impl(pattern, term, &mut subst)?;
    Some(subst)
}

fn match_impl(pattern: &Pattern, term: &Term, subst: &mut Substitution) -> Option<()> {
    match (pattern, term) {
        (Pattern::Var(v), t) => {
            if let Some(existing) = subst.get(v) {
                if existing == t { Some(()) } else { None }
            } else {
                subst.insert(v.clone(), t.clone());
                Some(())
            }
        }
        (Pattern::Ctor(p_name, p_args), Term::App(t_name, t_args)) => {
            if p_name != t_name || p_args.len() != t_args.len() {
                return None;
            }
            for (p, t) in p_args.iter().zip(t_args) {
                match_impl(p, t, subst)?;
            }
            Some(())
        }
        _ => None,
    }
}
```

### Rewrite Step

```rust
/// Apply a single rewrite rule
pub fn rewrite_step(term: &Term, rule: &RewriteRule) -> Option<Term> {
    if let Some(subst) = match_pattern(&rule.lhs, term) {
        if rule.conditions.iter().all(|c| c.evaluate(&subst)) {
            Some(rule.rhs.substitute(&subst))
        } else {
            None
        }
    } else {
        None
    }
}

/// Apply rewriting to normal form
pub fn normalize(term: Term, rules: &[RewriteRule]) -> Term {
    let mut current = term;
    loop {
        let mut changed = false;
        for rule in rules {
            if let Some(result) = rewrite_step(&current, rule) {
                current = result;
                changed = true;
                break;
            }
        }
        if !changed {
            break;
        }
    }
    current
}
```

### Strategy Control

Different evaluation strategies are supported:

```rust
pub enum Strategy {
    Innermost,    // Reduce innermost redexes first
    Outermost,    // Reduce outermost redexes first
    Leftmost,     // Left-to-right evaluation
    Parallel,     // All redexes simultaneously
}

impl Strategy {
    pub fn select_redex(&self, term: &Term, rules: &[RewriteRule]) -> Option<Position> {
        match self {
            Strategy::Innermost => self.find_innermost(term, rules),
            Strategy::Outermost => self.find_outermost(term, rules),
            // ...
        }
    }
}
```

---

## Ascent Datalog Integration

mettail-rust integrates with **Ascent**, a Datalog engine for Rust.

### What is Ascent?

Ascent is a Datalog implementation that:
- Compiles to efficient Rust code
- Supports stratified negation
- Enables relational queries over data

### Usage in mettail-rust

```rust
use ascent::ascent;

ascent! {
    // Relations (facts)
    relation sort(String);
    relation constructor(String, Vec<String>, String);
    relation subtype(String, String);

    // Rules (derived facts)

    // Transitive closure of subtyping
    subtype(a, c) <-- subtype(a, b), subtype(b, c);

    // Well-typed terms
    relation well_typed(Term, String);

    well_typed(Term::App(c, args), result) <--
        constructor(c, params, result),
        args.iter().zip(params).all(|(arg, param)| {
            well_typed(arg, param)
        });
}
```

### Benefits for OSLF

Ascent can express OSLF queries:

```rust
ascent! {
    // Predicates as relations
    relation predicate(String, Term);  // φ(t)

    // Substitution
    relation substituted(String, Term, Term);  // φ[f](t)

    substituted(phi, t, f_t) <--
        predicate(phi, t),
        applies(f, t, f_t);

    // Quantification
    relation forall(String, String, Term);  // ∀x:A. φ(x)

    forall(phi, sort, term) <--
        sort(sort),
        predicate(phi, term),
        of_sort(term, sort);
}
```

---

## Relation to OSLF

### Current Capabilities

| Feature | Status | Notes |
|---------|--------|-------|
| Category-based type checking | ✅ Complete | Basic foundation |
| Constructor validation | ✅ Complete | Type inference |
| Rewrite engine | ✅ Complete | Efficient normalization |
| Pattern matching | ✅ Complete | Unification |
| Ascent Datalog | 🔄 In progress | Query infrastructure |
| Predicate types | 📋 Planned | Future goal |

### What's Missing for Full OSLF

1. **Presheaf representation**
   ```rust
   // Needed: Representable presheaves
   pub struct Presheaf<T> {
       repr: Box<dyn Fn(&T) -> Set>,
   }
   ```

2. **Subobject classifier**
   ```rust
   // Needed: The type of propositions
   pub struct Omega;

   pub trait Predicate<A> {
       fn classify(&self, a: &A) -> bool;
   }
   ```

3. **Internal hom**
   ```rust
   // Needed: Function spaces as presheaves
   pub fn internal_hom<P, Q>(p: Presheaf<P>, q: Presheaf<Q>) -> Presheaf<(P, Q)> {
       // Natural transformations from p to q
   }
   ```

4. **Behavioral types**
   ```rust
   // Needed: Step modalities
   pub fn possible_step<S>(graph: &Graph<S>, phi: Predicate<S>) -> Predicate<S> {
       // F!(φ) = ∃ successor satisfying φ
   }
   ```

---

## Extension Plan

### Phase 1: Predicate Infrastructure

Add predicate representation and Datalog encoding:

```rust
/// A predicate over a sort
pub struct Predicate {
    pub name: String,
    pub domain: Sort,
    pub definition: PredicateDef,
}

pub enum PredicateDef {
    Atomic(String),           // Named predicate
    And(Box<Predicate>, Box<Predicate>),
    Or(Box<Predicate>, Box<Predicate>),
    Not(Box<Predicate>),
    Forall(Var, Sort, Box<Predicate>),
    Exists(Var, Sort, Box<Predicate>),
    Substituted(Box<Predicate>, Morphism),
}
```

### Phase 2: Presheaf Construction

Implement the P functor:

```rust
/// Presheaf over a theory
pub struct Presheaf<T: Theory> {
    pub base: T,
    pub sections: HashMap<Object<T>, Set>,
    pub restrictions: HashMap<Morphism<T>, Function>,
}

impl<T: Theory> Presheaf<T> {
    /// Yoneda embedding: y(c) = Hom(-, c)
    pub fn yoneda(c: &Object<T>) -> Self {
        // ...
    }

    /// Internal hom
    pub fn hom(p: &Self, q: &Self) -> Self {
        // ...
    }
}
```

### Phase 3: Behavioral Types

Add graph internalization and modalities:

```rust
/// Internal graph of rewrites
pub struct InternalGraph<S> {
    pub edges: Vec<Edge<S>>,
    pub source: Box<dyn Fn(&Edge<S>) -> S>,
    pub target: Box<dyn Fn(&Edge<S>) -> S>,
}

impl<S> InternalGraph<S> {
    /// F!(φ): Some next step satisfies φ
    pub fn possible(&self, phi: &Predicate<S>) -> Predicate<S> {
        // ...
    }

    /// F*(φ): All next steps satisfy φ
    pub fn necessary(&self, phi: &Predicate<S>) -> Predicate<S> {
        // ...
    }
}
```

### Phase 4: Integration

Connect with Rholang via the existing mettatron bridge:

```rust
/// Bridge to Rholang Par representation
pub trait ToRholang {
    fn to_par(&self) -> rholang::Par;
}

/// Type check before compilation
pub fn compile_with_types(source: &str) -> Result<rholang::Par, TypeError> {
    let theory = parse(source)?;
    let type_checked = type_check(&theory)?;
    Ok(type_checked.to_par())
}
```

---

## Current Status

### Implemented

- ✅ Theory parsing (LALRPOP)
- ✅ Sort and constructor representation
- ✅ Basic type checking
- ✅ Rewrite engine with strategies
- ✅ Pattern matching with unification
- ✅ Ascent Datalog integration (partial)

### In Progress

- 🔄 Predicate language design
- 🔄 Datalog encoding of type rules
- 🔄 Benchmark suite

### Planned

- 📋 Presheaf construction
- 📋 Internal language extraction
- 📋 Behavioral type modalities
- 📋 Rholang integration

---

## Usage Examples

### Defining and Checking a Theory

```rust
use mettail::*;

fn main() -> Result<(), Error> {
    let source = r#"
        theory Lambda {
            sort Term
            sort Type

            constructor var : Nat -> Term
            constructor app : Term, Term -> Term
            constructor lam : Term -> Term
        }
    "#;

    let theory = parse(source)?;
    let validated = validate(&theory)?;

    println!("Theory {} is valid", validated.name);
    Ok(())
}
```

### Using the Rewrite Engine

```rust
use mettail::rewrite::*;

let rules = vec![
    RewriteRule::new("β",
        pattern!((app (lam ?body) ?arg)),
        term!(substitute(?body, ?arg))
    ),
];

let term = parse_term("(app (lam (var 0)) (var 1))")?;
let normal = normalize(term, &rules);
// normal = (var 1)
```

---

## Summary

The mettail-rust prototype provides:

1. **High-performance rewrite engine** for operational semantics
2. **Category-based type checking** foundation
3. **Ascent Datalog integration** for declarative analysis
4. **Modular architecture** ready for OSLF extension

It is the recommended platform for implementing full OSLF semantic type checking
due to its performance characteristics and integration with Rholang's Rust runtime.

---

## References

- mettail-rust source: `/home/dylon/Workspace/f1r3fly.io/mettail-rust/`
- Ascent Datalog: https://github.com/s-arash/ascent
- See [bibliography.md](../reference/bibliography.md) for complete references.
