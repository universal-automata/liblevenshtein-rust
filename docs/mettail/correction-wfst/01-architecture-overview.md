# Unified Correction WFST Architecture

This document introduces the three-tier Weighted Finite State Transducer (WFST)
architecture for correction across written, spoken, and programming languages.

**Sources**:
- liblevenshtein: `/home/dylon/Workspace/f1r3fly.io/liblevenshtein-rust/`
- MORK: `/home/dylon/Workspace/f1r3fly.io/MORK/`
- MeTTaTron: `/home/dylon/Workspace/f1r3fly.io/MeTTa-Compiler/`

**Related Integration Docs**:
- [MORK Integration Overview](../../integration/mork/README.md) - Phase A-D implementation
- [FuzzySource Implementation](../../integration/mork/fuzzy_source.md) - Phase A details
- [Lattice Integration](../../integration/mork/lattice_integration.md) - Phase B details
- [WFST Composition](../../integration/mork/wfst_composition.md) - Phase C details
- [Grammar Correction](../../integration/mork/grammar_correction.md) - Phase D details
- [PathMap Integration](../../integration/pathmap/README.md) - Shared storage layer

---

## Table of Contents

1. [Problem Statement](#problem-statement)
2. [Three-Tier Architecture](#three-tier-architecture)
3. [MORK Integration Phases](#mork-integration-phases)
4. [Why Layered Correction?](#why-layered-correction)
5. [PathMap as Universal Storage](#pathmap-as-universal-storage)
6. [Performance Considerations](#performance-considerations)

---

## Problem Statement

Error correction spans multiple domains with distinct requirements:

| Domain | Error Types | Correction Needs |
|--------|-------------|------------------|
| **Written Text** | Typos, spelling, grammar | Dictionary lookup, context |
| **Spoken Language** | Phonetic confusion, homophones | Phoneme similarity, ASR lattices |
| **Programming Languages** | Syntax errors, type mismatches | Grammar validation, semantic types |

A unified architecture must handle all these while maintaining:
- **Efficiency**: Real-time correction for interactive use
- **Accuracy**: High precision without false corrections
- **Extensibility**: Easy addition of new languages/domains

---

## Three-Tier Architecture

The correction system uses three progressively refined tiers:

```
┌─────────────────────────────────────────────────────────────────────┐
│           UNIFIED CORRECTION WFST ARCHITECTURE                       │
├─────────────────────────────────────────────────────────────────────┤
│                                                                      │
│  INPUT: Erroneous text (written/spoken/code)                        │
│                                                                      │
│  ┌──────────────────────────────────────────────────────────────┐   │
│  │                    Tier 1: Lexical Correction                 │   │
│  │                       (liblevenshtein)                        │   │
│  │  ┌─────────────┐  ┌─────────────┐  ┌─────────────┐          │   │
│  │  │ Edit Dist.  │  │  Phonetic   │  │   Custom    │          │   │
│  │  │ Automata    │  │   Rules     │  │   Weights   │          │   │
│  │  └──────┬──────┘  └──────┬──────┘  └──────┬──────┘          │   │
│  │         └─────────────────┼─────────────────┘                │   │
│  │                           ▼                                   │   │
│  │              ┌────────────────────────┐                      │   │
│  │              │   Candidate Lattice    │                      │   │
│  │              └───────────┬────────────┘                      │   │
│  └──────────────────────────┼───────────────────────────────────┘   │
│                             ▼                                        │
│  ┌──────────────────────────────────────────────────────────────┐   │
│  │                  Tier 2: Syntactic Validation                 │   │
│  │                     (CFG + MORK/PathMap)                      │   │
│  │  ┌─────────────────────────────────────────────────────────┐ │   │
│  │  │                     MORK Space                          │ │   │
│  │  │  ┌─────────────┐  ┌─────────────┐  ┌─────────────┐     │ │   │
│  │  │  │  Grammar    │  │  Pattern    │  │   Bloom +   │     │ │   │
│  │  │  │  Rules      │  │  Matching   │  │   LRU       │     │ │   │
│  │  │  └──────┬──────┘  └──────┬──────┘  └──────┬──────┘     │ │   │
│  │  │         └─────────────────┼─────────────────┘           │ │   │
│  │  │                           ▼                             │ │   │
│  │  │               ┌─────────────────────┐                   │ │   │
│  │  │               │      PathMap        │                   │ │   │
│  │  │               │  (Shared Storage)   │                   │ │   │
│  │  │               └──────────┬──────────┘                   │ │   │
│  │  └──────────────────────────┼──────────────────────────────┘ │   │
│  │                             ▼                                 │   │
│  │              ┌────────────────────────┐                      │   │
│  │              │  Syntactically Valid   │                      │   │
│  │              │     Candidates         │                      │   │
│  │              └───────────┬────────────┘                      │   │
│  └──────────────────────────┼───────────────────────────────────┘   │
│                             ▼                                        │
│  ┌──────────────────────────────────────────────────────────────┐   │
│  │                Tier 3: Semantic Type Checking                 │   │
│  │                (MeTTaIL / MeTTaTron / Rholang)                │   │
│  │  ┌─────────────────────────────────────────────────────────┐ │   │
│  │  │                    MeTTaTron                            │ │   │
│  │  │  ┌─────────────┐  ┌─────────────┐  ┌─────────────┐     │ │   │
│  │  │  │   MeTTa     │  │   Type      │  │  Behavioral │     │ │   │
│  │  │  │   Atomspace │  │   Checking  │  │   Predicates│     │ │   │
│  │  │  └──────┬──────┘  └──────┬──────┘  └──────┬──────┘     │ │   │
│  │  │         └─────────────────┼─────────────────┘           │ │   │
│  │  │                           ▼                             │ │   │
│  │  │        ┌──────────────────────────────────┐             │ │   │
│  │  │        │ OSLF Predicate Evaluation        │             │ │   │
│  │  │        │ (structural + behavioral types)  │             │ │   │
│  │  │        └───────────────┬──────────────────┘             │ │   │
│  │  └────────────────────────┼────────────────────────────────┘ │   │
│  │                           │                                   │   │
│  │  ┌────────────────────────┼────────────────────────────────┐ │   │
│  │  │                   Rholang Bridge                        │ │   │
│  │  │  PathMap <-> MeTTa State <-> Rholang Par                │ │   │
│  │  │  (Enables cross-language semantic checking)              │ │   │
│  │  └────────────────────────┼────────────────────────────────┘ │   │
│  │                           ▼                                   │   │
│  │              ┌────────────────────────┐                      │   │
│  │              │  Semantically Valid    │                      │   │
│  │              │     Corrections        │                      │   │
│  │              └───────────┬────────────┘                      │   │
│  └──────────────────────────┼───────────────────────────────────┘   │
│                             ▼                                        │
│  OUTPUT: Ranked corrections with confidence scores                   │
│                                                                      │
└─────────────────────────────────────────────────────────────────────┘
```

### Tier Summary

| Tier | Component | Purpose | Speed |
|------|-----------|---------|-------|
| **1** | liblevenshtein | Lexical candidates via edit distance | Fastest |
| **2** | MORK/PathMap | Syntactic filtering via CFG | Fast |
| **3** | MeTTaIL/Rholang | Semantic type checking | Thorough |

---

## MORK Integration Phases

The three-tier architecture is implemented through four progressive phases, each building
on the previous. See the [MORK Integration Overview](../../integration/mork/README.md) for
complete implementation details.

```
┌─────────────────────────────────────────────────────────────────────┐
│                    MORK Integration Phases                           │
├─────────────────────────────────────────────────────────────────────┤
│                                                                      │
│  Phase A: FuzzySource Trait                                         │
│  ┌─────────────────────────────────────────────────────────────┐   │
│  │  • Trait abstraction for fuzzy dictionary backends          │   │
│  │  • PathMap + DAWG + DoubleArrayTrie implementations         │   │
│  │  • Integration point: liblevenshtein → MORK                 │   │
│  └─────────────────────────────────────────────────────────────┘   │
│                              ↓                                       │
│  Phase B: Lattice Infrastructure                                    │
│  ┌─────────────────────────────────────────────────────────────┐   │
│  │  • Weighted DAG for multi-candidate representation          │   │
│  │  • K-best path extraction (Dijkstra-based)                  │   │
│  │  • LatticeZipper for MORK ProductZipper integration         │   │
│  └─────────────────────────────────────────────────────────────┘   │
│                              ↓                                       │
│  Phase C: WFST Composition                                          │
│  ┌─────────────────────────────────────────────────────────────┐   │
│  │  • Semiring weights (Tropical, Log, Probability)            │   │
│  │  • Phonetic NFA via Thompson's construction                 │   │
│  │  • FST ∘ FST ∘ Trie composition operators                   │   │
│  └─────────────────────────────────────────────────────────────┘   │
│                              ↓                                       │
│  Phase D: Grammar Correction                                        │
│  ┌─────────────────────────────────────────────────────────────┐   │
│  │  • CFG rules as pattern/template pairs                      │   │
│  │  • MORK match2() for structural matching                    │   │
│  │  • query_multi_i() for O(K×N) lattice processing            │   │
│  └─────────────────────────────────────────────────────────────┘   │
│                                                                      │
└─────────────────────────────────────────────────────────────────────┘
```

### Phase A: FuzzySource Trait

**Documentation**: [FuzzySource Implementation](../../integration/mork/fuzzy_source.md)

The `FuzzySource` trait provides a unified interface for fuzzy dictionary lookups across
different storage backends:

```rust
/// Unified trait for fuzzy dictionary sources.
pub trait FuzzySource {
    /// Query with fuzzy matching up to max_distance.
    fn fuzzy_lookup(&self, query: &[u8], max_distance: u8)
        -> impl Iterator<Item = (Vec<u8>, u8)>;
}
```

**Implementations**:
- `PathMap`: Trie-based storage with zipper navigation
- `DynamicDawg` / `DynamicDawgChar`: SIMD-optimized for runtime updates
- `DoubleArrayTrie` / `DoubleArrayTrieChar`: Optimized for static dictionaries

**Integration Point**: Tier 1 (Lexical Correction) uses FuzzySource for candidate generation.

### Phase B: Lattice Infrastructure

**Documentation**: [Lattice Integration](../../integration/mork/lattice_integration.md)

Lattices represent the space of correction candidates as weighted directed acyclic graphs:

```
Query Term: "teh"
    │
    ▼
Transducer::query_lattice()
    │
    │ Builds DAG of candidates with weighted edges
    ▼
Lattice { nodes, edges, vocab }
    │
    ▼
LatticeZipper (MORK adapter)
    │
    │ Iterates paths by total weight
    ▼
ProductZipper → Unification → Ranked Results
```

**Key Components**:
- `Lattice`: Core DAG structure with vocabulary deduplication
- `LatticeBuilder`: Incremental construction API
- `PathIterator` / `k_best()`: Path extraction algorithms
- `LatticeZipper`: Adapter for MORK's ProductZipper

**Integration Point**: Bridge between Tier 1 and Tier 2.

### Phase C: WFST Composition

**Documentation**: [WFST Composition](../../integration/mork/wfst_composition.md)

Full Weighted Finite State Transducer infrastructure with phonetic NFA composition:

```
Query Pattern: "(ph|f)(o|oa)(n|ne)"
    │
    ▼
PhoneticNfa::compile()      ← Thompson's construction
    │
    ▼
ComposedAutomaton::new(phonetic_nfa, levenshtein, dictionary)
    │
    │ FST ∘ FST ∘ Trie composition
    ▼
Lattice with phonetic-weighted edges
```

**Key Concepts**:

| Semiring | ⊕ (combine) | ⊗ (extend) | Use Case |
|----------|-------------|------------|----------|
| **Tropical** | min | + | Shortest path (Viterbi) |
| **Log** | log-sum-exp | + | Probabilistic (forward-backward) |
| **Probability** | + | × | Raw probabilities |

**Integration Point**: Tier 1 phonetic expansion before Tier 2 filtering.

### Phase D: Grammar Correction

**Documentation**: [Grammar Correction](../../integration/mork/grammar_correction.md)

CFG-based error correction using MORK's pattern matching as the rule engine:

```metta
; CFG Rule: Subject-Verb Agreement Error
Pattern:  (s (np ?Subj :number singular) (vp (v ?V :number plural) ?Rest))
Template: (s (np ?Subj :number singular) (vp (v (singularize ?V)) ?Rest))
Cost: 1.0
```

**Key MORK Functions**:

| Function | Location | Purpose |
|----------|----------|---------|
| `match2()` | expr/src/lib.rs:921 | Recursive structural matching |
| `unify()` | expr/src/lib.rs:1849 | Variable binding + constraints |
| `query_multi_i()` | kernel/src/space.rs:992 | O(K×N) lattice queries |
| `transform_multi_multi_()` | kernel/src/space.rs:1221 | Pattern→template application |

**Integration Point**: Tier 2 (Syntactic Validation) rule engine.

### Phase Integration Summary

| Phase | Tier | Primary Function | Output |
|-------|------|------------------|--------|
| **A** | 1 | Fuzzy lookup | Raw candidates |
| **B** | 1→2 | Lattice construction | Weighted DAG |
| **C** | 1 | Phonetic expansion | Expanded candidates |
| **D** | 2 | Grammar filtering | Valid corrections |

---

## Why Layered Correction?

### Progressive Refinement

Each tier reduces the candidate set before the next:

```
Input Error: "teh" in "teh cat sat"
    │
    ▼ Tier 1 (Lexical)
Candidates: [the, tea, ten, tee, tech, ...]  (~100 candidates)
    │
    ▼ Tier 2 (Syntactic)
Valid in context: [the, tea]  (grammar allows determiner or noun)
    │
    ▼ Tier 3 (Semantic)
Best correction: "the"  (matches "cat sat" semantic context)
```

### Computational Efficiency

| Tier | Complexity | Candidates |
|------|------------|------------|
| 1 | O(n × d) | Generate many |
| 2 | O(n × g) | Filter structurally |
| 3 | O(n × t) | Verify semantically |

Where:
- n = number of candidates
- d = edit distance bound
- g = grammar size
- t = type checking cost

By filtering at each tier, expensive semantic checks only run on valid candidates.

### Separation of Concerns

Each tier has distinct expertise:

| Tier | Knowledge Required |
|------|-------------------|
| 1 | Character/phoneme similarity |
| 2 | Language grammar |
| 3 | Type system, domain semantics |

---

## PathMap as Universal Storage

PathMap serves as the shared storage layer across all tiers:

```
┌─────────────────────────────────────────────────────────────────┐
│                    PathMap Integration                           │
├─────────────────────────────────────────────────────────────────┤
│                                                                  │
│  ┌─────────────────┐                                            │
│  │  liblevenshtein │                                            │
│  │  Dictionary     │──────┐                                     │
│  └─────────────────┘      │                                     │
│                           │                                     │
│  ┌─────────────────┐      │      ┌─────────────────────────┐   │
│  │  MORK Grammar   │──────┼─────>│       PathMap           │   │
│  │  Rules          │      │      │  (Trie-based Storage)   │   │
│  └─────────────────┘      │      └─────────────────────────┘   │
│                           │                 │                   │
│  ┌─────────────────┐      │                 │                   │
│  │  MeTTa Type     │──────┘                 ▼                   │
│  │  Predicates     │           ┌────────────────────────────┐  │
│  └─────────────────┘           │  Shared Query Interface     │  │
│                                │  - Pattern matching          │  │
│                                │  - Fuzzy lookup              │  │
│                                │  - Type queries              │  │
│                                └────────────────────────────┘  │
│                                                                  │
└─────────────────────────────────────────────────────────────────┘
```

### Benefits

1. **No Serialization Overhead**: All tiers operate on same data format
2. **Shared Indexing**: Pattern matching works uniformly
3. **Cross-Tier Queries**: Type predicates can reference grammar rules
4. **Merkleization**: Content-addressed caching across tiers

---

## Performance Considerations

### Tier 1 Optimizations

- **SIMD**: DynamicDawg uses SIMD for parallel character comparison
- **Bloom Filter**: Fast negative lookups before trie traversal
- **Lazy Iteration**: Candidates generated on-demand

### Tier 2 Optimizations

- **Lattice Parsing**: 3-10x speedup over exhaustive enumeration
- **LRU Cache**: Hot grammar rules cached
- **Incremental Parsing**: Reuse partial parses for nearby errors

### Tier 3 Optimizations

- **Predicate Caching**: Common type queries cached
- **Lazy Evaluation**: Type checking on-demand
- **Parallel Checking**: Independent candidates checked in parallel

### Memory Budget

| Component | Typical Size |
|-----------|-------------|
| Dictionary (English) | 50-100 MB |
| Grammar (Programming Language) | 10-50 MB |
| Type Predicates | 5-20 MB |
| Working Set (LRU) | 10-50 MB |

---

## Summary

The three-tier architecture provides:

1. **Comprehensive Correction**: Lexical, syntactic, and semantic
2. **Efficient Filtering**: Each tier reduces candidates
3. **Unified Storage**: PathMap as shared layer
4. **Extensible Design**: New tiers or languages easily added

Key integration points:
- **liblevenshtein** ↔ **PathMap**: FuzzySource trait
- **MORK** ↔ **PathMap**: Native storage backend
- **MeTTaTron** ↔ **PathMap**: Type predicate storage
- **Rholang** ↔ **PathMap**: Par conversion

---

## References

- See [02-tier1-lexical-correction.md](./02-tier1-lexical-correction.md) for Tier 1 details
- See [03-tier2-syntactic-validation.md](./03-tier2-syntactic-validation.md) for Tier 2 details
- See [04-tier3-semantic-type-checking.md](./04-tier3-semantic-type-checking.md) for Tier 3 details
- See [05-data-flow.md](./05-data-flow.md) for complete data flow
- See [bibliography.md](../reference/bibliography.md) for complete references
