# Gap Analysis: Current State to Full OSLF

This document provides a detailed analysis of what is currently implemented and
what remains to be built for full semantic type checking in MeTTa via OSLF.

---

## Table of Contents

1. [Current Capabilities](#current-capabilities)
2. [Required Components](#required-components)
3. [Gap Matrix](#gap-matrix)
4. [Priority Assessment](#priority-assessment)
5. [Effort Estimates](#effort-estimates)

---

## Current Capabilities

### MeTTaIL Scala Prototype

| Component | Status | Description |
|-----------|--------|-------------|
| Theory definition syntax | ✅ Complete | Full grammar for sorts, constructors, equations |
| Sort validation | ✅ Complete | Category-theoretic constraints |
| Constructor validation | ✅ Complete | Type checking of operations |
| Equation parsing | ✅ Complete | Axiom support |
| Hypercube transformation | ✅ Working | Type indexing lift |
| Modal annotations | 🔄 Partial | Basic ◊ support |
| BNFC generation | ✅ Complete | Multi-target parser generation |
| Interpretation checking | ✅ Complete | Semantic consistency |

### mettail-rust Prototype

| Component | Status | Description |
|-----------|--------|-------------|
| Theory parsing | ✅ Complete | LALRPOP grammar |
| Sort/constructor representation | ✅ Complete | Core data structures |
| Basic type checking | ✅ Complete | Sort-based validation |
| Rewrite engine | ✅ Complete | Pattern matching, normalization |
| Strategy control | ✅ Complete | Innermost, outermost, etc. |
| Ascent Datalog | 🔄 In progress | Query infrastructure |

### Rholang (f1r3node)

| Component | Status | Description |
|-----------|--------|-------------|
| Tree-sitter parser | ✅ Complete | Full Rholang syntax |
| Normalizer | ✅ Complete | AST to Par transformation |
| DebruijnInterpreter | ✅ Complete | RHO calculus execution |
| MeTTa bridge (mettatron) | ✅ Active | Compile contract, PathMap |
| Dynamic type extractors | ✅ Complete | Runtime type checking |

---

## Required Components

### For Gph-enriched Lawvere (Phase 1)

```
┌─────────────────────────────────────────────────────────────────┐
│                    Gph-theory Components                        │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│  ┌─────────────────────┐  ┌─────────────────────┐              │
│  │  Graph-enriched     │  │  Reduction context  │              │
│  │  hom-sets           │  │  markers            │              │
│  │  ❌ Not implemented │  │  ❌ Not implemented │              │
│  └─────────────────────┘  └─────────────────────┘              │
│                                                                 │
│  ┌─────────────────────┐  ┌─────────────────────┐              │
│  │  Gas/resource       │  │  Strategy-aware     │              │
│  │  tracking           │  │  reduction          │              │
│  │  ❌ Not implemented │  │  ✅ Exists in mettail│              │
│  └─────────────────────┘  └─────────────────────┘              │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```

**Gaps**:
1. Reductions not represented as graph edges in hom-sets
2. No reduction context markers (R : T → T)
3. No gas consumption modeling
4. No connection between strategies and graph structure

### For Predicate Infrastructure (Phase 2)

```
┌─────────────────────────────────────────────────────────────────┐
│                    Predicate Components                         │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│  ┌─────────────────────┐  ┌─────────────────────┐              │
│  │  Predicate syntax   │  │  Predicate          │              │
│  │                     │  │  evaluation         │              │
│  │  ❌ Not implemented │  │  ❌ Not implemented │              │
│  └─────────────────────┘  └─────────────────────┘              │
│                                                                 │
│  ┌─────────────────────┐  ┌─────────────────────┐              │
│  │  Substitution       │  │  Quantification     │              │
│  │  (φ[f])             │  │  (∀, ∃)             │              │
│  │  ❌ Not implemented │  │  ❌ Not implemented │              │
│  └─────────────────────┘  └─────────────────────┘              │
│                                                                 │
│  ┌─────────────────────┐                                       │
│  │  Datalog encoding   │                                       │
│  │                     │                                       │
│  │  🔄 Partial (Ascent)│                                       │
│  └─────────────────────┘                                       │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```

**Gaps**:
1. No predicate AST or syntax
2. No predicate evaluation engine
3. No substitution operation for predicates
4. No quantifier handling
5. Ascent infrastructure exists but not for predicates

### For Behavioral Types (Phase 3)

```
┌─────────────────────────────────────────────────────────────────┐
│                    Behavioral Type Components                   │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│  ┌─────────────────────┐  ┌─────────────────────┐              │
│  │  Internal graph     │  │  Step modalities    │              │
│  │  representation     │  │  (F!, F*)           │              │
│  │  ❌ Not implemented │  │  ❌ Not implemented │              │
│  └─────────────────────┘  └─────────────────────┘              │
│                                                                 │
│  ┌─────────────────────┐  ┌─────────────────────┐              │
│  │  Reachability       │  │  Fixed point        │              │
│  │  (◇, □)             │  │  computation        │              │
│  │  ❌ Not implemented │  │  ❌ Not implemented │              │
│  └─────────────────────┘  └─────────────────────┘              │
│                                                                 │
│  ┌─────────────────────┐                                       │
│  │  Bisimulation       │                                       │
│  │  encoding           │                                       │
│  │  ❌ Not implemented │                                       │
│  └─────────────────────┘                                       │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```

**Gaps**:
1. Rewrite rules not internalized as graph
2. No step operators (possible, necessary)
3. No temporal modalities
4. No fixed point computation
5. No bisimulation as inductive type

### For Full OSLF (Phase 4)

```
┌─────────────────────────────────────────────────────────────────┐
│                    OSLF Components                              │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│  ┌─────────────────────┐  ┌─────────────────────┐              │
│  │  Presheaf           │  │  Yoneda embedding   │              │
│  │  construction (P)   │  │                     │              │
│  │  ❌ Not implemented │  │  ❌ Not implemented │              │
│  └─────────────────────┘  └─────────────────────┘              │
│                                                                 │
│  ┌─────────────────────┐  ┌─────────────────────┐              │
│  │  Internal hom       │  │  Subobject          │              │
│  │  [P, Q]             │  │  classifier (Ω)     │              │
│  │  ❌ Not implemented │  │  ❌ Not implemented │              │
│  └─────────────────────┘  └─────────────────────┘              │
│                                                                 │
│  ┌─────────────────────┐  ┌─────────────────────┐              │
│  │  Internal language  │  │  Refined binding    │              │
│  │  extraction (L)     │  │  [φ, ψ]             │              │
│  │  ❌ Not implemented │  │  ❌ Not implemented │              │
│  └─────────────────────┘  └─────────────────────┘              │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```

**Gaps**:
1. No presheaf category representation
2. No Yoneda embedding implementation
3. No internal hom computation
4. No subobject classifier
5. No internal language extraction
6. No refined binding types

### For Correction WFST Integration (Phase 5)

```
┌─────────────────────────────────────────────────────────────────┐
│                    WFST Integration Components                   │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│  ┌─────────────────────┐  ┌─────────────────────┐              │
│  │  FuzzySource trait  │  │  Candidate lattice  │              │
│  │  for PathMap        │  │  generation         │              │
│  │  ❌ Not implemented │  │  ❌ Not implemented │              │
│  └─────────────────────┘  └─────────────────────┘              │
│                                                                 │
│  ┌─────────────────────┐  ┌─────────────────────┐              │
│  │  MORK grammar       │  │  Type predicate     │              │
│  │  storage            │  │  storage in MORK    │              │
│  │  🔄 Partial         │  │  ❌ Not implemented │              │
│  └─────────────────────┘  └─────────────────────┘              │
│                                                                 │
│  ┌─────────────────────┐  ┌─────────────────────┐              │
│  │  Tier 1↔2↔3         │  │  Weight composition │              │
│  │  pipeline           │  │  (semirings)        │              │
│  │  ❌ Not implemented │  │  ✅ In liblevenshtein│             │
│  └─────────────────────┘  └─────────────────────┘              │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```

**Gaps**:
1. No FuzzySource trait implementation for PathMap/MORK
2. No candidate lattice data structure
3. No grammar storage in MORK Space
4. No type predicate storage integration
5. No unified tier pipeline
6. BUT: Semiring infrastructure exists in liblevenshtein

### For Rholang Integration (Phase 6)

```
┌─────────────────────────────────────────────────────────────────┐
│                    Integration Components                       │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│  ┌─────────────────────┐  ┌─────────────────────┐              │
│  │  Type annotation    │  │  Type checker API   │              │
│  │  syntax             │  │                     │              │
│  │  ❌ Not implemented │  │  ❌ Not implemented │              │
│  └─────────────────────┘  └─────────────────────┘              │
│                                                                 │
│  ┌─────────────────────┐  ┌─────────────────────┐              │
│  │  Compiler pipeline  │  │  Behavioral type    │              │
│  │  integration        │  │  enforcement        │              │
│  │  ❌ Not implemented │  │  ❌ Not implemented │              │
│  └─────────────────────┘  └─────────────────────┘              │
│                                                                 │
│  ┌─────────────────────┐                                       │
│  │  Gradual typing     │                                       │
│  │  mode               │                                       │
│  │  ❌ Not implemented │                                       │
│  └─────────────────────┘                                       │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```

**Gaps** (but foundation exists):
1. No type annotation syntax in Rholang grammar
2. No type checker API
3. No compiler pipeline insertion point
4. No behavioral enforcement
5. No gradual typing mode
6. BUT: mettatron bridge provides PathMap conversion

---

## TOGL Graph Foundations

TOGL (Theory of Graphs) provides the algebraic foundation for graph-based semantic
reasoning in OSLF. The theory defines graphs as algebraic objects that can be
composed with operational semantics to derive type systems.

**Source**: `/home/dylon/Workspace/f1r3fly.io/rho4u/togl/togl.md`

### TOGL Core Concepts

#### The Graph Functor

The fundamental construction is the graph functor:

```
G[X, V] = X + V × G[X, V] × G[X, V]
```

Where:
- `X` = Type of leaves (atoms/terminals)
- `V` = Type of internal nodes (vertex labels)
- `G[X,V]` = Recursive graph structure

This defines graphs as:
- Either a leaf of type X
- Or a vertex of type V with two child graphs (left and right)

#### Recursive Domain Definition

For self-referential structures, TOGL uses:

```
D = G[1 + D, 1 + D]
```

Where:
- `1` = Unit type (single element)
- `1 + D` = Optional D (either unit or D)
- Result: Graphs where both leaves and vertices can optionally contain D values

This captures recursive data structures common in operational semantics.

### TOGL Well-Formedness Judgments

TOGL provides well-formedness judgments for graph operations:

```
┌─────────────────────────────────────────────────────────────────┐
│                    TOGL Judgment Forms                          │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│  Γ ⊢ g : G[X, V]         Graph g is well-formed                │
│                                                                 │
│  Γ ⊢ leaf(x) : G[X, V]   Leaf node well-formedness             │
│                          where x : X                            │
│                                                                 │
│  Γ ⊢ node(v, l, r) : G[X, V]                                   │
│                          Internal node well-formedness          │
│                          where v : V, l : G[X,V], r : G[X,V]   │
│                                                                 │
│  Γ ⊢ g₁ ≡ g₂ : G[X, V]   Graph equivalence judgment            │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```

### OSLF and Graphs Connection

TOGL connects to OSLF through the following pathway:

```
┌─────────────────────────────────────────────────────────────────┐
│              TOGL → OSLF Connection                              │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│   Operational          Graph              Presheaf     Type     │
│   Semantics      →    Structure     →     Topos   →   System   │
│      (λ)               G[X,V]              P(λ)       LP(λ)    │
│                                                                 │
│  ┌─────────────┐   ┌─────────────┐   ┌─────────────┐           │
│  │ Terms       │ → │ Leaves      │   │             │           │
│  │ States      │   │   (X)       │   │ Presheaves  │           │
│  └─────────────┘   └─────────────┘   │ over        │           │
│                                       │ G-category  │           │
│  ┌─────────────┐   ┌─────────────┐   │             │           │
│  │ Reductions  │ → │ Edges       │   │ Internal    │           │
│  │ (→)         │   │ (V nodes)   │   │ Language    │           │
│  └─────────────┘   └─────────────┘   └─────────────┘           │
│                                                                 │
│  Key insight: Operational semantics as internal graphs         │
│  in a topos provides native behavioral predicates              │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```

**Key TOGL-OSLF Relationships**:
1. **Terms as leaves**: Operational terms map to graph leaves
2. **Reductions as edges**: Reduction steps map to internal nodes (edges)
3. **Paths as computations**: Paths through the graph = computation sequences
4. **Bisimulation as path equivalence**: Behavioral equivalence via graph structure

### TOGL Component Gaps

```
┌─────────────────────────────────────────────────────────────────┐
│                    TOGL Components                              │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│  ┌─────────────────────┐  ┌─────────────────────┐              │
│  │  Graph functor      │  │  Graph type         │              │
│  │  G[X,V]             │  │  checking           │              │
│  │  ❌ Not implemented │  │  ❌ Not implemented │              │
│  └─────────────────────┘  └─────────────────────┘              │
│                                                                 │
│  ┌─────────────────────┐  ┌─────────────────────┐              │
│  │  Recursive domain   │  │  Well-formedness    │              │
│  │  D = G[1+D, 1+D]    │  │  judgments          │              │
│  │  ❌ Not implemented │  │  ❌ Not implemented │              │
│  └─────────────────────┘  └─────────────────────┘              │
│                                                                 │
│  ┌─────────────────────┐  ┌─────────────────────┐              │
│  │  Graph equivalence  │  │  Path enumeration   │              │
│  │  (≡)                │  │  and analysis       │              │
│  │  ❌ Not implemented │  │  ❌ Not implemented │              │
│  └─────────────────────┘  └─────────────────────┘              │
│                                                                 │
│  ┌─────────────────────┐  ┌─────────────────────┐              │
│  │  OSLF graph         │  │  Behavioral         │              │
│  │  embedding          │  │  predicate lift     │              │
│  │  ❌ Not implemented │  │  ❌ Not implemented │              │
│  └─────────────────────┘  └─────────────────────┘              │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```

**Specific TOGL Gaps**:
1. **Graph functor type**: No `G[X,V]` type constructor in any implementation
2. **Recursive domain**: No support for `D = G[1+D, 1+D]` recursive types
3. **Well-formedness**: No judgment infrastructure for graph validity
4. **Graph equivalence**: No structural/behavioral equivalence on graphs
5. **Path analysis**: No path enumeration for reachability analysis
6. **OSLF embedding**: No functor from λ-theory graphs to presheaves
7. **Behavioral lift**: No mechanism to lift graph predicates to type predicates

### TOGL Implementation Requirements

#### Minimal TOGL Implementation

For basic graph-based reasoning, implement:

```rust
/// Graph functor representation
pub enum Graph<X, V> {
    /// Leaf node containing terminal value
    Leaf(X),
    /// Internal node with vertex label and two children
    Node(V, Box<Graph<X, V>>, Box<Graph<X, V>>),
}

/// Recursive domain for operational semantics
pub type OpGraph = Graph<Term, Reduction>;

impl<X: Eq, V: Eq> Graph<X, V> {
    /// Check structural equivalence
    pub fn structurally_equiv(&self, other: &Self) -> bool { ... }

    /// Enumerate all paths from root to leaves
    pub fn paths(&self) -> impl Iterator<Item = Path<V>> { ... }

    /// Check if a path exists satisfying predicate
    pub fn path_exists<P: Fn(&Path<V>) -> bool>(&self, pred: P) -> bool { ... }
}
```

#### Advanced TOGL Implementation

For full OSLF integration, add:

```rust
/// Well-formedness judgment
pub trait WellFormed<Ctx> {
    fn well_formed(&self, ctx: &Ctx) -> Result<(), WellFormednessError>;
}

/// Graph equivalence judgment (bisimulation)
pub trait GraphEquiv {
    fn bisimilar(&self, other: &Self) -> bool;
}

/// OSLF embedding functor
pub trait OslfEmbed {
    type Presheaf;
    fn embed(&self) -> Self::Presheaf;
}

/// Behavioral predicate from graph structure
pub trait BehavioralPredicate<G> {
    fn reachable(&self, from: &G, to: &G) -> bool;
    fn eventually(&self, from: &G, pred: impl Fn(&G) -> bool) -> bool;
    fn always(&self, from: &G, pred: impl Fn(&G) -> bool) -> bool;
}
```

### TOGL Effort Estimates

| Component | Complexity | Estimated Effort |
|-----------|------------|------------------|
| Graph functor type | Low | 1-2 days |
| Recursive domain | Medium | 2-3 days |
| Well-formedness judgments | Medium | 3-5 days |
| Graph equivalence | High | 5-7 days |
| Path enumeration | Medium | 2-3 days |
| OSLF embedding | Very High | 10-15 days |
| Behavioral predicate lift | High | 5-8 days |
| **Total TOGL** | | **28-43 days** |

### TOGL Integration Path

TOGL components should be integrated as follows:

1. **Phase 0.5** (before Phase 1): Basic graph functor and path enumeration
   - Enables graph representation of operational semantics
   - Provides foundation for Gph-theories (Phase 1)

2. **Phase 1** (Gph-theories): Use TOGL for hom-graph representation
   - Reductions become edges in `Graph<Term, Reduction>`
   - Reduction contexts become path patterns

3. **Phase 3** (Behavioral Types): Use TOGL for internal graph
   - Step modalities via path analysis
   - Reachability via path existence

4. **Phase 4** (Full OSLF): Use TOGL for presheaf construction
   - OSLF embedding functor
   - Behavioral predicate lifting

---

## Gap Matrix

### Summary by Phase

| Phase | Total Components | Implemented | Partial | Not Started |
|-------|-----------------|-------------|---------|-------------|
| 0.5: TOGL Foundations | 8 | 0 | 0 | 8 |
| 1: Gph-theories | 4 | 1 | 0 | 3 |
| 2: Predicates | 5 | 0 | 1 | 4 |
| 3: Behavioral | 5 | 0 | 0 | 5 |
| 4: Full OSLF | 6 | 0 | 0 | 6 |
| 5: WFST Integration | 6 | 1 | 1 | 4 |
| 6: Rholang Integration | 5 | 0 | 0 | 5 |
| **Total** | **39** | **2** | **2** | **35** |

### Gap Categories

**Foundational Gaps** (blocking further work):
- TOGL graph functor type G[X,V]
- TOGL recursive domain D = G[1+D, 1+D]
- Predicate language and evaluation
- Graph-enriched hom-sets
- Internal graph representation

**Extension Gaps** (can be added incrementally):
- Gas/resource tracking
- Reduction contexts
- Temporal modalities

**Integration Gaps** (require external coordination):
- Rholang grammar changes
- Compiler pipeline modification
- Gradual typing infrastructure
- FuzzySource trait for PathMap/MORK
- Unified tier pipeline

**WFST Infrastructure Gaps** (liblevenshtein integration):
- Candidate lattice generation
- Grammar storage in MORK Space
- Type predicate storage integration

---

## Priority Assessment

### Critical Path (Must Have)

1. **Predicate language** - Foundation for all type predicates
2. **Internal graph** - Required for behavioral types
3. **Step modalities** - Core of behavioral reasoning
4. **Type checker API** - Integration point for Rholang

### High Value (Should Have)

1. **Gph-theory representation** - Cleaner operational semantics
2. **Reachability modalities** - Common behavioral properties
3. **Compiler integration** - Practical type checking

### Nice to Have

1. **Full presheaf construction** - Maximum expressiveness
2. **Refined binding** - Advanced pattern types
3. **Bisimulation encoding** - Process equivalence

---

## Effort Estimates

### By Component

| Component | Complexity | Estimated Effort |
|-----------|------------|------------------|
| Predicate AST | Low | 1-2 days |
| Predicate evaluation | Medium | 3-5 days |
| Substitution | Medium | 2-3 days |
| Quantification | Medium | 3-5 days |
| Datalog encoding | Medium | 3-5 days |
| Internal graph | Medium | 2-3 days |
| Step modalities | Medium | 3-5 days |
| Reachability | High | 5-7 days |
| Fixed points | High | 5-7 days |
| Presheaf construction | Very High | 10-15 days |
| Internal hom | Very High | 7-10 days |
| Internal language | Very High | 10-15 days |
| Type annotation syntax | Low | 1-2 days |
| Type checker API | Medium | 3-5 days |
| Compiler integration | Medium | 5-7 days |
| FuzzySource trait | Low | 2-3 days |
| Candidate lattice | Medium | 3-5 days |
| Grammar storage (MORK) | Medium | 3-5 days |
| Type predicate storage | Medium | 3-5 days |
| Tier pipeline | High | 5-8 days |

### By Phase

| Phase | Total Effort | Dependencies |
|-------|--------------|--------------|
| 0.5: TOGL Foundations | 28-43 days | None |
| 1: Gph-theories | 5-8 days | Phase 0.5 (partial) |
| 2: Predicates | 12-18 days | Phase 1 |
| 3: Behavioral | 15-22 days | Phase 2, Phase 0.5 |
| 4: Full OSLF | 30-45 days | Phase 3, Phase 0.5 |
| 5: WFST Integration | 15-25 days | liblevenshtein, MORK, PathMap |
| 6: Rholang Integration | 10-15 days | Phase 3+ |

### Total Estimate

- **Minimum viable** (Phases 0.5-basic + 1-3 + Rholang): 50-80 days
- **With WFST** (Phases 0.5-basic + 1-3 + WFST + Rholang): 65-105 days
- **Full OSLF with TOGL** (all phases): 115-175 days

**Note**: TOGL Phase 0.5 can be partially implemented. Basic graph functor and
path enumeration (8-12 days) are required for Phase 1. Full TOGL (well-formedness,
equivalence, OSLF embedding) is only needed for Phase 4.

---

## Recommendations

### Immediate Actions

0. **Implement basic TOGL graph functor** (Phase 0.5 prerequisite)
   - Define `Graph<X, V>` enum with Leaf and Node variants
   - Implement path enumeration
   - Add basic structural equivalence

1. **Start with predicates** in mettail-rust
   - Define Predicate enum
   - Implement evaluation
   - Add Datalog encoding

2. **Add internal graph** alongside existing rewrite engine
   - Use TOGL `Graph<Term, Reduction>` for rewrite representation
   - Rewrite rules → graph edges
   - Expose successor/predecessor queries via path analysis

### Short-term Goals

3. **Implement step modalities**
   - F! (possible) and F* (necessary)
   - Test on termination/progress properties

4. **Create type checker API**
   - Define trait interface
   - Stub implementation

### Medium-term Goals

5. **WFST integration** (liblevenshtein)
   - Implement FuzzySource trait for PathMap
   - Build candidate lattice generation
   - Connect to MORK grammar storage

6. **Rholang integration**
   - Grammar extensions
   - Compiler pipeline insertion
   - Gradual typing mode

7. **Behavioral type examples**
   - Termination checking
   - Deadlock detection
   - Namespace isolation

### WFST-Specific Goals

8. **Tier 1 integration** (lexical correction)
   - FuzzySource trait for PathMap/MORK
   - Semiring weight composition
   - Candidate lattice generation

9. **Tier 2 integration** (syntactic validation)
   - Grammar storage in MORK Space
   - Lattice parsing pipeline
   - Error recovery strategies

10. **Tier 3 integration** (semantic type checking)
    - Type predicate storage in MORK
    - Unified three-tier pipeline
    - Cross-tier weight composition

---

## Summary

The current implementations provide:
- ✅ Theory definition and validation
- ✅ Rewrite execution
- ✅ MeTTa-Rholang bridge
- ✅ Semiring infrastructure (liblevenshtein)
- 🔄 MORK grammar storage (partial)

Major gaps remain in:
- ❌ TOGL graph functor infrastructure
- ❌ Predicate infrastructure
- ❌ Behavioral types
- ❌ OSLF construction
- ❌ Rholang type integration
- ❌ WFST tier pipeline
- ❌ FuzzySource trait for PathMap/MORK

The recommended approach is incremental:

0. **TOGL foundations** (Phase 0.5): Implement basic graph functor `G[X,V]`
   and path enumeration. This provides the algebraic foundation for all
   subsequent phases.

1. **Core semantic types** (Phases 1-3): Start with predicates and behavioral
   types before attempting full OSLF. Use TOGL graphs for rewrite representation.

2. **WFST integration** (Phase 5): Build on existing liblevenshtein semiring
   infrastructure and MORK pattern matching to create the three-tier correction
   pipeline.

3. **Rholang integration** (Phase 6): Add type annotations and behavioral
   enforcement to the Rholang compiler, leveraging the mettatron bridge.

4. **Full OSLF** (Phase 4, optional): For maximum expressiveness, implement
   the complete presheaf construction and internal language extraction,
   using full TOGL for OSLF embedding.

This layered approach builds toward the complete vision while providing
practical value at each stage. TOGL provides the mathematical rigor for
graph-based semantic reasoning that underlies all subsequent phases.
