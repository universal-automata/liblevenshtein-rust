# liblevenshtein Algorithm Documentation

**Comprehensive guide to the algorithms, data structures, and optimizations in liblevenshtein-rust.**

This documentation provides in-depth coverage of all algorithmic layers, complete with theory, diagrams, usage examples, performance analysis, and references to academic literature.

---

## Table of Contents

1. [Overview](#overview)
2. [Quick Start](#quick-start)
3. [Algorithmic Layers](#algorithmic-layers)
4. [Performance Summary](#performance-summary)
5. [Use Case Guide](#use-case-guide)
6. [References](#references)

---

## Overview

liblevenshtein-rust is a high-performance fuzzy string matching library based on **Levenshtein automata**. It combines multiple algorithmic layers to provide fast approximate string matching against large dictionaries.

### Architecture

The library is organized into 9 distinct algorithmic layers:

```
┌─────────────────────────────────────────────────────────┐
│  Application Layer (Your Code)                          │
├─────────────────────────────────────────────────────────┤
│  8. Caching Layer (LRU, LFU, TTL, etc.)                │
├─────────────────────────────────────────────────────────┤
│  7. Contextual Completion (Scope-aware, Hierarchical)   │
├─────────────────────────────────────────────────────────┤
│  6. Zipper Navigation (Functional Traversal)            │
├─────────────────────────────────────────────────────────┤
│  3. Intersection/Traversal (Query Iterators)            │
├─────────────────────────────────────────────────────────┤
│  2. Levenshtein Automata (Finite State Machines)        │
├─────────────────────────────────────────────────────────┤
│  1. Dictionary Layer (Tries, DAWGs, Suffix Automata)    │
├─────────────────────────────────────────────────────────┤
│  9. Value Storage (Term → Value Mappings)               │
├─────────────────────────────────────────────────────────┤
│  5. SIMD Optimization (Vectorized Hot Paths)            │
├─────────────────────────────────────────────────────────┤
│  4. Distance Calculation (Direct DP Algorithms)         │
└─────────────────────────────────────────────────────────┘
```

### Key Features

- **9 Dictionary Backends** - Tries, DAWGs, Suffix Automata (byte & char variants)
- **3 Levenshtein Algorithms** - Standard, Transposition, Merge-and-Split
- **SIMD Acceleration** - 20-64% speedup with AVX2/SSE4.1
- **Value Storage** - Associate arbitrary data with terms (fuzzy maps)
- **Unicode Support** - Correct character-level edit distances
- **Contextual Completion** - Scope-aware code completion
- **Flexible Caching** - 9 eviction strategies

---

## Quick Start

### Basic Fuzzy Search

```rust
use liblevenshtein::prelude::*;

// Create dictionary
let dict = DoubleArrayTrie::from_terms(vec![
    "apple", "application", "apply", "apricot"
]);

// Fuzzy search with max distance 2
let results: Vec<String> = dict
    .fuzzy_search("aple", 2)
    .collect();

// Results: ["apple", "apply"]
```

### With Values (Fuzzy Maps)

```rust
// Dictionary with associated values
let dict = DoubleArrayTrie::from_terms_with_values(vec![
    ("apple", 1),
    ("banana", 2),
    ("cherry", 3),
]);

// Search with value filtering (10-100x faster!)
let results: Vec<(String, i32)> = dict
    .fuzzy_search_filtered("aple", 2, |v| *v < 3)
    .collect();

// Results: [("apple", 1)]
```

### Unicode Support

```rust
// Character-level for proper Unicode
let dict = DoubleArrayTrieChar::from_terms(vec![
    "café", "naïve", "中文", "🎉"
]);

// Correct character-level distance
let results: Vec<String> = dict
    .fuzzy_search("cafe", 1)  // Missing accent = 1 character edit
    .collect();

// Results: ["café"]
```

---

## Algorithmic Layers

### [Layer 1: Dictionary Layer](01-dictionary-layer/)

**Purpose:** Efficient storage and traversal of term collections

**Implementations:**
- [**DoubleArrayTrie**](01-dictionary-layer/implementations/double-array-trie.md) ⭐ **Recommended**
  - 6-8 bytes/char, 3x faster queries than DAWG
  - Use case: General purpose, static/append-only dictionaries
- [**DoubleArrayTrieChar**](01-dictionary-layer/implementations/double-array-trie-char.md) ⭐ **Unicode**
  - Character-level for proper Unicode semantics
  - Use case: International text, CJK, emoji
- [**DynamicDawg**](01-dictionary-layer/implementations/dynamic-dawg.md)
  - Thread-safe insert/remove operations
  - Use case: Frequently changing dictionaries
- [**OptimizedDawg**](01-dictionary-layer/implementations/optimized-dawg.md)
  - 75% memory reduction, 20-25% faster
  - Use case: Large static dictionaries
- [**SuffixAutomaton**](01-dictionary-layer/implementations/suffix-automaton.md)
  - Substring/infix matching
  - Use case: Full-text search

**Key Topics:**
- [Data Structures](01-dictionary-layer/data-structures/node-representations.md)
- [Value Storage](01-dictionary-layer/data-structures/value-storage.md)
- [Performance Comparison](01-dictionary-layer/performance/benchmarks.md)

---

### [Layer 2: Levenshtein Automata](02-levenshtein-automata/)

**Purpose:** Finite state machines for approximate string matching

**Algorithms:**
- [**Standard**](02-levenshtein-automata/algorithms/standard-algorithm.md) (Insert, Delete, Substitute)
  - Use case: General fuzzy matching
- [**Transposition**](02-levenshtein-automata/algorithms/transposition-algorithm.md) (+Adjacent Swap)
  - Use case: Typo tolerance, keyboard errors
- [**Merge-and-Split**](02-levenshtein-automata/algorithms/merge-and-split.md) (+Merge/Split ops)
  - Use case: OCR errors, scanning artifacts

**Core Concepts:**
- [Position Representation](02-levenshtein-automata/theory/position-representation.md): `(term_index, num_errors, is_special)`
- [Subsumption](02-levenshtein-automata/theory/subsumption-theory.md): 3.3x faster with online pruning
- [State Composition](02-levenshtein-automata/implementation/state-representation.md): SmallVec optimization

**Performance:**
- Online subsumption: O(kn) vs O(n²) batch
- SIMD acceleration: 3-4x on characteristic vector

---

### [Layer 3: Intersection & Traversal](03-intersection-traversal/)

**Purpose:** Execute queries by traversing Dictionary × Automaton

**Query Types:**
- [**QueryIterator**](03-intersection-traversal/query-iterators/query-iterator.md)
  - Unordered results, streaming
  - Use case: Large result sets
- [**OrderedQueryIterator**](03-intersection-traversal/query-iterators/ordered-query.md)
  - Distance-first ordering
  - Use case: Autocomplete, top-k results
- [**ValueFilteredQueryIterator**](03-intersection-traversal/query-iterators/value-filtered-query.md)
  - Filter during traversal (10-100x faster!)
  - Use case: Scope-aware code completion
- [**ZipperQueryIterator**](03-intersection-traversal/query-iterators/zipper-query.md)
  - Hierarchical navigation
  - Use case: Context-preserving search

**Key Topics:**
- [Product Construction](03-intersection-traversal/theory/product-construction.md)
- [Path Tracking](03-intersection-traversal/implementation/path-tracking.md): 15-25% speedup
- [Lazy Evaluation](03-intersection-traversal/implementation/lazy-evaluation.md)

---

### [Layer 4: Distance Calculation](04-distance-calculation/)

**Purpose:** Direct string distance computation (non-automaton approach)

**Algorithms:**
- [Iterative DP](04-distance-calculation/algorithms/iterative-dp.md): 2-row optimization, O(mn) time, O(min(m,n)) space
- [Recursive + Memoization](04-distance-calculation/algorithms/recursive-memoization.md): C++-style with caching
- [Optimizations](04-distance-calculation/algorithms/optimizations.md): Prefix/suffix stripping, early termination

**Use Cases:**
- Direct comparison without dictionary
- Validation of automaton results
- Benchmarking

---

### [Layer 5: SIMD Optimization](05-simd-optimization/)

**Purpose:** Vectorize hot paths for 20-64% performance gains

**Optimized Operations:**
- [**Characteristic Vector**](05-simd-optimization/implementations/characteristic-vector-simd.md)
  - AVX2 (8-wide), SSE4.1 (4-wide)
  - 3-4x speedup in automaton transitions
- [**Distance Matrix**](05-simd-optimization/implementations/distance-matrix-simd.md)
  - Vectorized DP row updates
  - 20-30% speedup for strings ≥16 chars
- [**Edge Lookup**](05-simd-optimization/implementations/edge-lookup-simd.md)
  - Optimal for exactly 4 edges

**Key Topics:**
- [Runtime Detection](05-simd-optimization/implementations/runtime-detection.md): CPU feature flags
- [Threshold Analysis](05-simd-optimization/performance/threshold-analysis.md): When SIMD helps
- [Benchmarks](05-simd-optimization/performance/simd-benchmarks.md): 950+ lines of analysis

---

### [Layer 6: Zipper Navigation](06-zipper-navigation/)

**Purpose:** Functional, context-preserving traversal of data structures

**Pattern:** Huet's Zipper (1997) - functional navigation with context

**Implementations:**
- [DictZipper](06-zipper-navigation/implementations/dict-zipper.md): Navigate dictionaries
- [ValuedDictZipper](06-zipper-navigation/implementations/valued-zipper.md): Access values during navigation
- [AutomatonZipper](06-zipper-navigation/implementations/automaton-zipper.md): Track automaton state
- [IntersectionZipper](06-zipper-navigation/implementations/intersection-zipper.md): Compose dictionary + automaton

**Use Cases:**
- [Hierarchical Completion](06-zipper-navigation/use-cases/hierarchical-completion.md)
- [Scope-aware Search](06-zipper-navigation/use-cases/scope-aware-search.md)
- [Backtracking](06-zipper-navigation/use-cases/backtracking.md)

---

### [Layer 7: Contextual Completion](07-contextual-completion/)

**Purpose:** Scope-aware, hierarchical code completion

**Components:**
- [**ContextualCompletionEngine**](07-contextual-completion/implementation/completion-engine.md)
  - Query fusion (drafts + finalized)
  - Context tree management
- [**ContextTree**](07-contextual-completion/implementation/context-tree.md)
  - Lexical scope hierarchy
  - Visibility rules
- [**DraftBuffer**](07-contextual-completion/implementation/draft-buffer.md)
  - In-memory work-in-progress terms
- [**CheckpointStack**](07-contextual-completion/implementation/checkpoint-system.md)
  - Time-travel undo/redo

**Use Cases:**
- [IDE Code Completion](07-contextual-completion/use-cases/code-completion.md)
- [Incremental Editing](07-contextual-completion/use-cases/incremental-editing.md)
- [LSP Integration](07-contextual-completion/examples/lsp-completion.rs)

---

### [Layer 8: Caching](08-caching-layer/)

**Purpose:** Query result caching with configurable eviction

**Eviction Policies:**
- [LRU](08-caching-layer/eviction-policies/lru.md) - Temporal locality
- [LFU](08-caching-layer/eviction-policies/lfu.md) - Frequency-based
- [TTL](08-caching-layer/eviction-policies/ttl.md) - Time-based expiration
- [Cost-Aware](08-caching-layer/eviction-policies/cost-aware.md) - Size/computation aware
- [Memory Pressure](08-caching-layer/eviction-policies/memory-pressure.md) - System memory monitoring

**Features:**
- Lock-free concurrency (DashMap)
- Compact metadata storage
- Fuzzy multimap support

---

### [Layer 9: Value Storage](09-value-storage/)

**Purpose:** Associate arbitrary data with dictionary terms (fuzzy maps)

**Architecture:**
```
Terms → States (via transitions) → Values (via state index)

Example:
"apple" → state 5 → value: Some(1)
"app"   → state 3 → value: None (not final)
```

**Implementation:**
- `values: Arc<Vec<Option<V>>>` indexed by state number
- Only final states can have `Some(value)`
- Cloned on access for Rust ownership

**Use Cases:**
- [Scope IDs](09-value-storage/use-cases/scope-ids.md) for code completion
- [Categorization](09-value-storage/use-cases/categorization.md) and metadata
- [Fuzzy Maps](09-value-storage/use-cases/fuzzy-maps.md) - approximate key-value lookup
- [Filtered Queries](09-value-storage/use-cases/filtered-queries.md) - 10-100x speedup

**Key Topics:**
- [Term-Value Mapping](09-value-storage/theory/term-value-mapping.md)
- [Memory Layout](09-value-storage/theory/term-value-mapping.md#memory-layout)
- [Performance Impact](09-value-storage/implementations/comparison.md)

---

## Performance Summary

### Dictionary Comparison (10,000 words)

| Backend | Construction | Exact Match | Distance 1 | Distance 2 | Memory |
|---------|--------------|-------------|------------|------------|--------|
| **DoubleArrayTrie** | 3.2ms | **6.6µs** | **12.9µs** | **16.3µs** | **8 bytes/char** |
| DynamicDawg | 4.1ms | 19.8µs | 319µs | 2,150µs | ~12 bytes/char |
| PathMap | 3.5ms | 71.1µs | 888µs | 5,919µs | Variable |

### SIMD Performance Gains

| Component | Scalar | AVX2 | Speedup |
|-----------|--------|------|---------|
| Characteristic Vector | 100% | 3-4x | 300-400% |
| Distance Matrix (≥16 chars) | 100% | 1.2-1.3x | 20-30% |
| Overall Workload | 100% | 1.2-1.64x | 20-64% |

### Value Filtering Speedup

| Selectivity | Post-Filter | During-Traversal | Speedup |
|-------------|-------------|------------------|---------|
| 10% | 100ms | 10ms | **10x** |
| 1% | 100ms | 1ms | **100x** |

---

## Use Case Guide

### Decision Tree: Which Dictionary?

```
Need to remove terms?
├─ YES → DynamicDawg (thread-safe insert/remove)
└─ NO
    ├─ Unicode text?
    │  ├─ YES → DoubleArrayTrieChar (character-level)
    │  └─ NO  → DoubleArrayTrie ⭐ (recommended)
    │
    └─ Substring search?
       └─ YES → SuffixAutomaton (infix matching)
```

### Common Scenarios

**Autocomplete / Spell Checking**
- Dictionary: `DoubleArrayTrie`
- Algorithm: `Standard` (distance 1-2)
- Iterator: `OrderedQueryIterator` (top-10 results)

**Typo Tolerance**
- Dictionary: `DoubleArrayTrie`
- Algorithm: `Transposition` (keyboard errors)
- Iterator: `QueryIterator` (all matches)

**International Text**
- Dictionary: `DoubleArrayTrieChar`
- Algorithm: `Standard` or `Transposition`
- Iterator: Depends on use case

**Code Completion (Scope-aware)**
- Dictionary: `DoubleArrayTrie` with scope IDs
- Algorithm: `Standard`
- Iterator: `ValueFilteredQueryIterator` (10-100x faster)

**Full-Text Search**
- Dictionary: `SuffixAutomaton`
- Algorithm: `Standard`
- Iterator: `QueryIterator`

**Live Dictionary Updates**
- Dictionary: `DynamicDawg` (thread-safe)
- Algorithm: Any
- Iterator: Any

---

## Example Index

### Getting Started
- [Hello Fuzzy Search](../examples/01-getting-started/hello-fuzzy.rs)
- [Basic Query Patterns](../examples/01-getting-started/basic-query.rs)
- [Distance Calculation](../examples/01-getting-started/distance-calculation.rs)

### Dictionaries
- [DoubleArrayTrie Demo](../examples/02-dictionaries/double-array-trie-demo.rs)
- [Dynamic DAWG Demo](../examples/02-dictionaries/dynamic-dawg-demo.rs)
- [Unicode Handling](../examples/02-dictionaries/unicode-handling.rs)
- [Dictionary Comparison](../examples/02-dictionaries/dictionary-comparison.rs)

### Algorithms
- [Standard Levenshtein](../examples/03-algorithms/standard-levenshtein.rs)
- [Transposition Demo](../examples/03-algorithms/transposition-demo.rs)
- [Merge-and-Split Demo](../examples/03-algorithms/merge-split-demo.rs)

### Value Storage
- [Term-Value Storage](../examples/05-values/term-value-storage.rs)
- [Scope-Aware Completion](../examples/05-values/scope-aware-completion.rs)
- [Fuzzy Map](../examples/05-values/fuzzy-map.rs)
- [Value Filtering](../examples/05-values/value-filtering.rs)

### Real-World Applications
- [Spell Checker](../examples/08-real-world/spell-checker.rs)
- [Autocomplete Server](../examples/08-real-world/autocomplete-server.rs)
- [Fuzzy Finder](../examples/08-real-world/fuzzy-finder.rs)
- [LSP Completion](../examples/08-real-world/lsp-completion.rs)

---

## References

### Academic Papers (Open Access)

1. **Schulz & Mihov (2002)** - "Fast string correction with Levenshtein automata"
   - International Journal on Document Analysis and Recognition 5.1
   - [Available on ResearchGate](https://www.researchgate.net/)

2. **Blumer et al. (1985)** - "The smallest automaton recognizing the subwords of a text"
   - Theoretical Computer Science 40
   - Core suffix automaton algorithm

3. **Aoe (1989)** - "An Efficient Digital Search Algorithm by Using a Double-Array Structure"
   - IEEE Transactions on Software Engineering
   - Double-array trie foundation

4. **Damerau (1964)** - "A technique for computer detection and correction of spelling errors"
   - Communications of the ACM 7.3
   - Transposition distance

5. **Wagner & Fischer (1974)** - "The String-to-String Correction Problem"
   - Journal of the ACM 21.1
   - Dynamic programming for edit distance

6. **Huet (1997)** - "The Zipper"
   - Journal of Functional Programming 7.5
   - Functional data structure pattern

See [complete reference list](../references/papers.md) for more papers and resources.

---

## Navigation

**By Layer:**
- [01-dictionary-layer/](01-dictionary-layer/)
- [02-levenshtein-automata/](02-levenshtein-automata/)
- [03-intersection-traversal/](03-intersection-traversal/)
- [04-distance-calculation/](04-distance-calculation/)
- [05-simd-optimization/](05-simd-optimization/)
- [06-zipper-navigation/](06-zipper-navigation/)
- [07-contextual-completion/](07-contextual-completion/)
- [08-caching-layer/](08-caching-layer/)
- [09-value-storage/](09-value-storage/)

**By Topic:**
- [Theory Documents](01-dictionary-layer/theory/) (All layers)
- [Implementation Guides](01-dictionary-layer/implementations/) (All layers)
- [Usage Examples](../examples/)
- [Performance Analysis](01-dictionary-layer/performance/)
- [Diagrams & Visualizations](../diagrams/)

**Quick Links:**
- [Value Storage Guide](09-value-storage/) (NEW in Phase 6!)
- [DoubleArrayTrie Guide](01-dictionary-layer/implementations/double-array-trie.md) (Recommended)
- [Unicode Support](01-dictionary-layer/implementations/double-array-trie-char.md)
- [Algorithm Comparison](02-levenshtein-automata/algorithms/)
- [Performance Benchmarks](benchmarks/)

---

## Contributing

Found an issue or have suggestions? See [CONTRIBUTING.md](../../CONTRIBUTING.md) for guidelines on improving this documentation.

## License

Documentation is licensed under [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/).
Code examples are licensed under the same license as the library (MIT or Apache 2.0).
