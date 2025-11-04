# liblevenshtein-rust

[![CI](https://github.com/universal-automata/liblevenshtein-rust/actions/workflows/ci.yml/badge.svg)](https://github.com/universal-automata/liblevenshtein-rust/actions/workflows/ci.yml)
[![Nightly Tests](https://github.com/universal-automata/liblevenshtein-rust/actions/workflows/nightly.yml/badge.svg)](https://github.com/universal-automata/liblevenshtein-rust/actions/workflows/nightly.yml)
[![Release](https://github.com/universal-automata/liblevenshtein-rust/actions/workflows/release.yml/badge.svg)](https://github.com/universal-automata/liblevenshtein-rust/actions/workflows/release.yml)
[![License](https://img.shields.io/badge/license-Apache--2.0-blue.svg)](LICENSE)

A Rust port of [liblevenshtein](https://github.com/universal-automata/liblevenshtein-cpp) for fast approximate string matching using Levenshtein automata (Universal Levenshtein Automata).

> **Note:** Ready for crates.io publication (PathMap dependency is now optional).

## What's New

### v0.5.0 (2025-11-04)

- **DynamicDawgChar** - Unicode support for Dynamic DAWG with character-level operations
- **Contextual Code Completion** - Hierarchical scope-aware completion engine with zipper-based navigation
- **Performance Optimizations** - DynamicDawg with Bloom filters, auto-minimization, and sorted batch insertion
- **UTF-8 Optimization Analysis** - Comprehensive documentation of Unicode performance characteristics
- **Bug Fixes** - Fixed suffix sharing bug, test compilation, GitHub Actions workflow, and all clippy warnings

### v0.4.0 (2025-10-30)

- **Unicode Support** - Character-level dictionary variants for correct Unicode Levenshtein distances
  - `DoubleArrayTrieChar` and `PathMapDictionaryChar` for character-level operations
  - Proper handling of multi-byte UTF-8 sequences (accented chars, CJK, emoji)
  - ~5% performance overhead, 4x memory for edge labels
  - Full test coverage with 19 Unicode-specific tests
- **Phase 4: SIMD Optimization** - Comprehensive SIMD acceleration with **20-64% performance gains**
  - 8 SIMD-optimized components across critical performance paths
  - Data-driven threshold tuning based on empirical benchmarking
  - AVX2/SSE4.1 implementations with runtime CPU feature detection
  - Extensive documentation (950+ lines across 3 analysis documents)

### v0.3.0 (2025-10-26)

- **Package Support**: Debian (.deb), RPM (.rpm), and Arch Linux (.pkg.tar.zst) packages
- **CI Improvements**: Explicit CPU features for better compatibility across platforms
- **Code Quality**: Fixed all clippy warnings without suppressing checks
- **Bug Fixes**: Fixed CLI format auto-detection for text dictionaries

See [CHANGELOG.md](CHANGELOG.md) for complete details.

## Overview

This library provides efficient fuzzy string matching against large dictionaries using finite state automata. It supports multiple Levenshtein distance algorithms and pluggable dictionary backends.

### Features

- **Fast approximate string matching** using Universal Levenshtein Automata
- **Multiple algorithms**:
  - `Standard`: insert, delete, substitute operations
  - `Transposition`: adds character transposition (swap adjacent chars)
  - `MergeAndSplit`: adds merge and split operations
- **Multiple dictionary backends**:
  - **DoubleArrayTrie** (recommended, default) - O(1) transitions with excellent cache locality and minimal memory footprint
  - **DoubleArrayTrieChar** - Character-level variant for correct Unicode Levenshtein distances
  - **PathMap** (optional `pathmap-backend` feature) - high-performance trie with structural sharing, supports dynamic updates
  - **PathMapChar** (optional `pathmap-backend` feature) - Character-level PathMap for Unicode fuzzy matching
  - **DAWG** - Directed Acyclic Word Graph for space-efficient storage
  - **OptimizedDawg** - Arena-based DAWG with 20-25% faster construction
  - **DynamicDawg** - DAWG with online insert/delete/minimize operations
  - **DynamicDawgChar** - Character-level DAWG with Unicode support and online updates
  - **SuffixAutomaton** - For substring/infix matching
  - **SuffixAutomatonChar** - Character-level suffix automaton for Unicode substring matching
  - Extensible trait-based design for custom backends
- **Ordered results**: `OrderedQueryIterator` returns results sorted by distance first, then lexicographically
- **Filtering and prefix matching**: Filter results with custom predicates, enable prefix mode for code completion
- **Serialization support** (optional `serialization` feature):
  - **Multiple formats**: Bincode (binary), JSON, Plain Text (newline-delimited UTF-8), Protobuf
  - **Optimized Protobuf formats**: V2 (62% smaller), DAT-specific, SuffixAutomaton-specific
  - **Gzip compression** (optional `compression` feature) - 85% file size reduction
  - Save and load dictionaries to/from disk
- **Full-featured CLI tool** (optional `cli` feature):
  - Interactive REPL for exploration
  - Query, insert, delete, convert operations
  - Support for all serialization formats including compressed variants
- **Runtime dictionary updates**:
  - Thread-safe insert, remove, and clear operations (PathMap, DynamicDawg)
  - Queries automatically see updates via `RwLock`-based interior mutability
  - Concurrent queries during modifications
- **Lazy evaluation** - results generated on-demand
- **Efficient memory usage** - shared dictionary state across transducers
- **SIMD acceleration** (optional `simd` feature, x86_64 only):
  - AVX2/SSE4.1 optimized operations with runtime CPU feature detection
  - **20-64% faster** query performance across all workloads
  - Optimized characteristic vectors, position subsumption, state operations
  - Dictionary edge lookup with data-driven threshold tuning
  - Distance matrix computation with vectorized operations
  - Automatic fallback to scalar implementation when SIMD unavailable

## Installation

### From crates.io (Recommended)

Add to your `Cargo.toml`:

```toml
[dependencies]
liblevenshtein = "0.5"

# Or with SIMD acceleration (x86_64 only, requires SSE4.1/AVX2):
liblevenshtein = { version = "0.5", features = ["simd"] }
```

Or install the CLI tool:

```bash
cargo install liblevenshtein --features cli,compression,protobuf
```

**Note:** The PathMap backend is not available from crates.io (git dependency). All other backends (DoubleArrayTrie, DAWG, etc.) are fully supported.

### From GitHub (For PathMap Backend)

To use the PathMap backend, install from source:

```toml
[dependencies]
liblevenshtein = { git = "https://github.com/universal-automata/liblevenshtein-rust", tag = "v0.5.0", features = ["pathmap-backend"] }
```

Or install the CLI with PathMap:

```bash
cargo install --git https://github.com/universal-automata/liblevenshtein-rust --tag v0.5.0 \
  --features cli,pathmap-backend,compression,protobuf liblevenshtein
```

### Pre-built Packages

Download pre-built packages from the [GitHub Releases](https://github.com/universal-automata/liblevenshtein-rust/releases) page:

- **Debian/Ubuntu**: `.deb` packages
- **Fedora/RHEL/CentOS**: `.rpm` packages
- **Arch Linux**: `.pkg.tar.zst` packages
- **Binaries**: `.tar.gz` and `.zip` archives for Linux and macOS (x86_64 and ARM64)

## Usage

### Basic Querying

```rust
use liblevenshtein::prelude::*;

// Create a dictionary from terms (using DoubleArrayTrie for best performance)
let terms = vec!["test", "testing", "tested", "tester"];
let dict = DoubleArrayTrie::from_terms(terms);

// Create a transducer with Standard algorithm
let transducer = Transducer::new(dict, Algorithm::Standard);

// Query for terms within edit distance 2
for term in transducer.query("tset", 2) {
    println!("Match: {}", term);
}

// Query with distances
for candidate in transducer.query_with_distance("tset", 2) {
    println!("Match: {} (distance: {})", candidate.term, candidate.distance);
}
```

**Output:**
```
Match: test
Match: tester
Match: test (distance: 1)
Match: tester (distance: 2)
```

### Unicode Support

For correct character-level Levenshtein distances with Unicode text, use the character-level dictionary variants:

```rust
use liblevenshtein::dictionary::double_array_trie_char::DoubleArrayTrieChar;
use liblevenshtein::prelude::*;

// Create a character-level dictionary for Unicode content
let terms = vec!["café", "naïve", "中文", "🎉"];
let dict = DoubleArrayTrieChar::from_terms(terms);
let transducer = Transducer::new(dict, Algorithm::Standard);

// Character-level distance: "" → "¡" is distance 1 (one character)
// Byte-level would incorrectly report distance 2 (two UTF-8 bytes)
let results: Vec<_> = transducer.query("", 1).collect();
// Results include single-character Unicode terms

// Works with accented characters
for candidate in transducer.query_with_distance("cafe", 1) {
    println!("{}: {}", candidate.term, candidate.distance);
    // Output: café: 1 (one character substitution: e→é)
}
```

**Character-level backends**:
- `DoubleArrayTrieChar` - Character-level Double-Array Trie
- `PathMapDictionaryChar` (requires `pathmap-backend` feature) - Character-level PathMap with dynamic updates

**When to use**:
- ✅ Dictionaries containing non-ASCII Unicode (accented characters, CJK, emoji)
- ✅ When edit distance must count characters, not bytes
- ✅ Multi-language applications requiring correct Unicode semantics

**Performance**: ~5% overhead for UTF-8 decoding, 4x memory for edge labels (char vs u8).

### Runtime Dictionary Updates

The **DynamicDawg** backend supports **thread-safe runtime updates**:

```rust
use liblevenshtein::prelude::*;

// Create dictionary with runtime update support
let dict = DynamicDawg::from_terms(vec!["cat", "dog"]);
let transducer = Transducer::new(dict.clone(), Algorithm::Standard);

// Insert new terms at runtime
dict.insert("cot");
dict.insert("bat");

// Queries immediately see the new terms
let results: Vec<_> = transducer.query("cot", 1).collect();
// Results: ["cat", "cot"]

// Remove terms
dict.remove("dog");
```

**Thread Safety**: The dictionary uses `RwLock` for interior mutability:
- Multiple concurrent queries are allowed (read locks)
- Modifications acquire exclusive write locks
- Active `Transducer` instances automatically see updates

**Performance Optimizations**: Configure Bloom filter and auto-minimization for better performance:

```rust
use liblevenshtein::prelude::*;

// Enable Bloom filter for 10x faster contains() operations
let dict = DynamicDawg::with_config(
    f32::INFINITY,  // Auto-minimize threshold (disabled)
    Some(10000),    // Bloom filter capacity (enabled)
);

// Or enable auto-minimization for bulk insertions (30% faster for large datasets)
let dict = DynamicDawg::with_config(
    1.5,            // Auto-minimize at 50% growth
    None,           // Bloom filter (disabled)
);

// Or enable both optimizations
let dict = DynamicDawg::with_config(
    1.5,            // Auto-minimize threshold
    Some(10000),    // Bloom filter capacity
);
```

**Optimization Guide**:
- **Bloom Filter**: Use when frequently checking if terms exist (88-93% faster `contains()`)
- **Auto-Minimization**: Use for bulk insertions of 1000+ terms (30% faster, prevents memory bloat)
- Default: Both disabled for maximum flexibility and minimal overhead on small datasets

**Note**: PathMapDictionary also supports runtime updates but requires the optional `pathmap-backend` feature.

See [`examples/dynamic_dictionary.rs`](examples/dynamic_dictionary.rs) for a complete demonstration.

### Value-Mapped Dictionaries

Store metadata with dictionary terms using **value-mapped dictionaries**:

```rust
use liblevenshtein::prelude::*;
use std::collections::HashSet;

// DynamicDawg with integer values (e.g., word frequencies)
let dict: DynamicDawg<u32> = DynamicDawg::new();
dict.insert_with_value("apple", 42);
dict.insert_with_value("apply", 17);

// Retrieve values
assert_eq!(dict.get_value("apple"), Some(42));
assert_eq!(dict.get_value("banana"), None);

// Use with FuzzyMap for fuzzy lookups with values
let map = FuzzyMap::new(dict, Algorithm::Standard);
let results = map.get_with_distance("aple", 1);  // fuzzy lookup
// Results include both terms and their values

// Or use FuzzyMultiMap to aggregate multiple values
let dict: DynamicDawg<HashSet<u32>> = DynamicDawg::new();
dict.insert_with_value("test", HashSet::from([1, 2, 3]));
```

**Supported backends**:
- `DynamicDawg<V>` - Dynamic dictionary with values of type `V`
- `DynamicDawgChar<V>` - Character-level dynamic dictionary with Unicode support
- `PathMapDictionary<V>` - PathMap with values (requires `pathmap-backend`)
- `PathMapDictionaryChar<V>` - Character-level PathMap with values

**Common value types**:
- `u32` / `u64` - Frequencies, scores, IDs
- `HashSet<T>` - Multiple associations per term
- `Vec<T>` - Ordered collections
- Any type implementing `Clone + Send + Sync + 'static`

**Integration with contextual completion**:
```rust
use liblevenshtein::prelude::*;

// Use DynamicDawg backend for contextual completion
let dict: DynamicDawg<Vec<u32>> = DynamicDawg::new();
let engine = ContextualCompletionEngine::with_dictionary(
    dict,
    Algorithm::Standard
);

// Insert terms with context IDs
let ctx = engine.create_root_context();
engine.insert_finalized(ctx, "variable", vec![ctx]);
```

### Ordered Results

Get results sorted by edit distance first, then alphabetically:

```rust
use liblevenshtein::prelude::*;

let dict = DoubleArrayTrie::from_terms(vec!["apple", "apply", "ape", "app"]);
let transducer = Transducer::new(dict, Algorithm::Standard);

// Results ordered by distance, then alphabetically
for candidate in transducer.query_ordered("aple", 1) {
    println!("{}: {}", candidate.term, candidate.distance);
}
```

**Output:**
```
ape: 1
apple: 1
apply: 1
```

### Filtering and Prefix Matching

Filter results and enable prefix matching for code completion:

```rust
use liblevenshtein::prelude::*;

let dict = DoubleArrayTrie::from_terms(vec![
    "getValue", "getVariable", "setValue", "setVariable"
]);
let transducer = Transducer::new(dict, Algorithm::Standard);

// Prefix matching with filtering
for candidate in transducer
    .query_ordered("getVal", 1)
    .prefix()  // Match terms starting with query ± edits
    .filter(|c| c.term.starts_with("get"))  // Only getter methods
{
    println!("{}: {}", candidate.term, candidate.distance);
}
```

**Output:**
```
getValue: 0
getVariable: 1
```

See [`examples/code_completion_demo.rs`](examples/code_completion_demo.rs) and [`examples/contextual_filtering_optimization.rs`](examples/contextual_filtering_optimization.rs) for more examples.

### Dictionary Backend Comparison

The library provides multiple dictionary backends optimized for different use cases:

| Backend | Best For | Performance Highlights |
|---------|----------|----------------------|
| **DoubleArrayTrie** | **General use** (recommended) | 3x faster queries, 30x faster contains, 8 bytes/state |
| **DoubleArrayTrieChar** | Unicode text, character-level distances | Correct Unicode semantics, ~5% overhead |
| **PathMap** | Dynamic updates, runtime modifications | Thread-safe insert/delete, fastest dynamic backend |
| **PathMapChar** | Unicode + dynamic updates | Character-level distances with runtime modifications |
| **DAWG** | Static dictionaries, moderate size | Good balance of speed and memory |
| **OptimizedDawg** | Static dictionaries, construction speed | 20-25% faster construction than DAWG |
| **DynamicDawg** | Occasional modifications | Best fuzzy matching for dynamic use |
| **DynamicDawgChar** | Unicode + occasional modifications | Character-level with insert/remove, ~5% overhead |
| **SuffixAutomaton** | Substring/infix matching | Find patterns anywhere in text |

**Performance Comparison** (10,000 words):

```
Construction:     DAT: 3.2ms   PathMap: 3.5ms   DAWG: 7.2ms
Exact Match:      DAT: 6.6µs   DAWG: 19.8µs     PathMap: 71.1µs
Contains (100):   DAT: 0.22µs  DAWG: 6.7µs      PathMap: 132µs
Distance 1:       DAT: 12.9µs  DAWG: 319µs      PathMap: 888µs
Distance 2:       DAT: 16.3µs  DAWG: 2,150µs    PathMap: 5,919µs
Memory/state:     DAT: ~8B     OptDawg: ~13B    DAWG: ~32B
```

**Prefix Matching Support**: All backends except `SuffixAutomaton` support efficient prefix matching through the `.prefix()` method, making them ideal for code completion and autocomplete applications.

**When to use each backend**:
- **Static dictionaries (ASCII/Latin-1)** → `DoubleArrayTrie` (best overall performance, default choice)
- **Static dictionaries (Unicode)** → `DoubleArrayTrieChar` (correct character-level distances)
- **Dynamic updates (ASCII/Latin-1)** → `DynamicDawg` (thread-safe runtime modifications)
- **Dynamic updates (Unicode)** → `DynamicDawgChar` (character-level with insert/remove, best fuzzy matching)
- **Dynamic updates (Unicode, frequent)** → `PathMapChar` (alternative, requires `pathmap-backend`)
- **Substring search** → `SuffixAutomaton` (finds patterns anywhere in text)
- **Memory-constrained** → `DoubleArrayTrie` (8 bytes/state, most efficient)
- **Multi-language apps** → Character-level variants (`*Char`) for correct Unicode semantics

### Serialization and Compression

Save and load dictionaries with optional compression:

```rust
use liblevenshtein::prelude::*;
use std::fs::File;

let dict = DoubleArrayTrie::from_terms(vec!["test", "testing", "tested"]);

// Save with compression (85% file size reduction)
let file = File::create("dict.bin.gz")?;
GzipSerializer::<BincodeSerializer>::serialize(&dict, file)?;

// Load compressed dictionary
let file = File::open("dict.bin.gz")?;
let dict: DoubleArrayTrie = GzipSerializer::<BincodeSerializer>::deserialize(file)?;

// Or use optimized Protobuf formats
let file = File::create("dict.pb")?;
OptimizedProtobufSerializer::serialize(&dict, file)?;  // 62% smaller than standard
```

Requires `serialization` and `compression` features:

```toml
[dependencies]
liblevenshtein = { git = "https://github.com/universal-automata/liblevenshtein-rust", tag = "v0.3.0", features = ["serialization", "compression"] }
```

### CLI Tool

The library includes a full-featured command-line tool with interactive REPL:

```bash
# Install with CLI support (from GitHub)
cargo install --git https://github.com/universal-automata/liblevenshtein-rust --tag v0.3.0 \
  --features cli,compression,protobuf liblevenshtein

# Or download pre-built binaries from GitHub Releases

# Query a dictionary
liblevenshtein query "test" --dict /usr/share/dict/words -m 2 -s

# Convert between formats with compression
liblevenshtein convert words.txt words.bin.gz \
  --to-format bincode-gz --to-backend path-map

# Launch interactive REPL
liblevenshtein repl --dict words.bin.gz
```

The CLI auto-detects formats from file extensions and supports:
- **Formats**: text, bincode, json, protobuf (plus `-gz` compressed variants)
- **Backends**: path-map, dawg, dynamic-dawg
- **Operations**: query, insert, delete, convert, save, info

See [`docs/developer-guide/building.md`](docs/developer-guide/building.md) for comprehensive CLI documentation.

### FuzzyMultiMap - Aggregating Values

The `FuzzyMultiMap` enables fuzzy lookup of associated values, aggregating results from all matching terms:

```rust
use liblevenshtein::prelude::*;
use liblevenshtein::cache::multimap::FuzzyMultiMap;
use std::collections::HashSet;

// Create a dictionary with values (e.g., user IDs for each name)
let dict = PathMapDictionary::from_terms_with_values([
    ("alice", HashSet::from([101, 102])),
    ("alicia", HashSet::from([103])),
    ("bob", HashSet::from([201])),
    ("robert", HashSet::from([202, 203])),
]);

// Create fuzzy multimap
let fuzzy_map = FuzzyMultiMap::new(dict, Algorithm::Standard);

// Query "alise" - matches both "alice" and "alicia" at distance 1
let user_ids = fuzzy_map.query("alise", 1).unwrap();
// Returns: HashSet {101, 102, 103} - union of all matching values

// Practical use case: find all IDs for fuzzy name search
let ids = fuzzy_map.query("rob", 2).unwrap();
// Returns IDs for both "bob" (distance 1) and "robert" (distance 2)
```

**Supported collection types**:
- `HashSet<T>` - Union of all matching sets
- `BTreeSet<T>` - Union of all matching sets
- `Vec<T>` - Concatenation of all matching vectors

**Use cases**:
- User ID lookup with fuzzy name matching
- Tag aggregation across similar terms
- Multi-valued dictionary queries with error tolerance

### Contextual Code Completion (Zipper-Based)

The `ContextualCompletionEngine` provides hierarchical scope-aware code completion with draft state management:

```rust
use liblevenshtein::contextual::ContextualCompletionEngine;
use liblevenshtein::transducer::Algorithm;

// Create engine (thread-safe, shareable with Arc)
let engine = ContextualCompletionEngine::with_algorithm(Algorithm::Standard);

// Create hierarchical scopes (global → function → block)
let global = engine.create_root_context(0);
let function = engine.create_child_context(1, global).unwrap();
let block = engine.create_child_context(2, function).unwrap();

// Add finalized terms to each scope
engine.finalize_direct(global, "std::vector").unwrap();
engine.finalize_direct(global, "std::string").unwrap();
engine.finalize_direct(function, "parameter").unwrap();
engine.finalize_direct(function, "result").unwrap();

// Incremental typing in block scope (draft state)
engine.insert_str(block, "local_var").unwrap();

// Query completions - sees all visible scopes (block + function + global)
let completions = engine.complete(block, "par", 1);
for comp in completions {
    println!("{} (distance: {}, draft: {}, from context: {:?})",
             comp.term, comp.distance, comp.is_draft, comp.contexts);
}
// Output: parameter (distance: 0, draft: false, from context: [1])

// Checkpoint/undo support for editor integration
engine.checkpoint(block).unwrap();
engine.insert_str(block, "iable").unwrap();  // Now: "local_variable"
engine.undo(block).unwrap();  // Restore to: "local_var"

// Finalize draft to add to dictionary
let term = engine.finalize(block).unwrap();  // Returns "local_var"
assert!(engine.has_term("local_var"));

// Query now sees finalized term
let results = engine.complete(block, "loc", 1);
// Returns: local_var (now finalized, visible in this context)
```

**Features**:
- **Hierarchical visibility**: Child contexts see parent terms (global → function → block)
- **Draft state**: Incremental typing without polluting finalized dictionary
- **Checkpoint/undo**: Editor-friendly state management
- **Thread-safe**: Share engine across threads with `Arc`
- **Mixed queries**: Search both drafts and finalized terms simultaneously

**Performance** (sub-millisecond for interactive use):
- Insert character: ~4 µs
- Checkpoint: ~116 ns
- Query (500 terms, distance 1): ~11.5 µs
- Query (distance 2): ~309 µs

**Use cases**:
- LSP servers with multi-file scope awareness
- Code editors with context-sensitive completion
- REPL environments with session-scoped symbols
- Any application requiring hierarchical fuzzy matching

See [`examples/contextual_completion.rs`](examples/contextual_completion.rs) for a complete example.

### Advanced: Direct Zipper API

For fine-grained control over traversal, use the zipper API directly:

```rust
use liblevenshtein::dictionary::pathmap::PathMapDictionary;
use liblevenshtein::dictionary::pathmap_zipper::PathMapZipper;
use liblevenshtein::transducer::{AutomatonZipper, Algorithm, StatePool};
use liblevenshtein::transducer::intersection_zipper::IntersectionZipper;

// Create dictionary
let dict = PathMapDictionary::<()>::new();
dict.insert("cat");
dict.insert("cats");
dict.insert("dog");

// Create zippers
let dict_zipper = PathMapZipper::new_from_dict(&dict);
let auto_zipper = AutomatonZipper::new("cot".as_bytes(), 1, Algorithm::Standard);

// Intersect dictionary and automaton
let intersection = IntersectionZipper::new(dict_zipper, auto_zipper);

// Manual traversal
let mut pool = StatePool::new();
for (label, child) in intersection.children(&mut pool) {
    if child.is_match() {
        println!("Match: {} (distance: {})",
                 child.term(),
                 child.distance().unwrap());
    }

    // Recurse into child for custom traversal algorithms
    for (_, grandchild) in child.children(&mut pool) {
        // Custom logic here...
    }
}
```

**When to use**:
- Custom traversal algorithms (DFS, A*, beam search)
- Early termination with custom heuristics
- Integration with external data structures
- Research and experimentation

**Note**: Most users should use `Transducer::query()` or `ContextualCompletionEngine` instead. The zipper API is lower-level and requires manual state management.

### Value-Filtered Queries

For performance optimization when querying dictionaries with scoped values:

```rust
use liblevenshtein::prelude::*;
use std::collections::HashSet;

// Dictionary with scope IDs
let dict = PathMapDictionary::from_terms_with_values([
    ("global_var", 0),      // Scope 0 (global)
    ("function_param", 1),  // Scope 1 (function)
    ("local_var", 2),       // Scope 2 (block)
]);

let transducer = Transducer::new(dict, Algorithm::Standard);

// Query only specific scopes (e.g., visible from scope 1)
let visible_scopes = HashSet::from([0, 1]);  // global + function
for term in transducer.query_by_value_set("param", 1, &visible_scopes) {
    println!("{}", term);
}
// Output: function_param (scope 1 is visible)
// Does NOT return: local_var (scope 2 not in visible set)

// Or use custom predicate
for term in transducer.query_filtered("var", 1, |scope_id| *scope_id <= 1) {
    println!("{}", term);
}
// Returns: global_var, function_param (scopes 0, 1)
```

**Performance benefit**: Filtering by value during traversal is **significantly faster** than post-filtering results, especially for large dictionaries with many out-of-scope matches.

**Use cases**:
- Scope-based code completion (only show visible symbols)
- Access control (filter by user permissions)
- Multi-tenancy (filter by tenant ID)

## Documentation

- **[User Guide](docs/user-guide/)** - Getting started, algorithms, backends, and features
- **[Developer Guide](docs/developer-guide/)** - Architecture, building, contributing, and performance
- **[Building and Testing](docs/developer-guide/building.md)** - Comprehensive build instructions and CLI usage
- **[Contributing Guidelines](docs/developer-guide/contributing.md)** - How to contribute to the project
- **[Features Overview](docs/user-guide/features.md)** - Detailed feature documentation
- **[Publishing Guide](docs/developer-guide/publishing.md)** - Requirements for publishing to crates.io
- **[Changelog](CHANGELOG.md)** - Version history and release notes

## Performance

The library is highly optimized for performance:

### Core Optimizations

- **Arc Path Sharing**: Eliminated expensive cloning operations during traversal
- **StatePool**: Object pool pattern for state reuse with exceptional performance gains
- **SmallVec Integration**: Stack-allocated vectors reduce heap allocation pressure
- **Lazy Edge Iteration**: 15-50% faster PathMap edge iteration with zero-copy implementation
- **Aggressive Inlining**: Hot path functions inlined for optimal performance

Benchmarks show 3.3x speedup for DAWG operations and 5-18% improvements across filtering/prefix scenarios.

### SIMD Acceleration (optional `simd` feature)

When compiled with the `simd` feature on x86_64 platforms, the library achieves **20-64% performance gains** through:

- **8 SIMD-optimized components** across critical performance paths
- **AVX2/SSE4.1 implementations** with runtime CPU feature detection
- **Data-driven threshold tuning** based on empirical benchmarking
- **Automatic fallback** to scalar implementation when SIMD unavailable

Key optimizations:
- Characteristic vector operations (vectorized bit manipulation)
- Position subsumption checking (parallel state comparisons)
- State operations (vectorized distance computations)
- Dictionary edge lookups (batched queries with adaptive thresholds)
- Distance matrix computation (vectorized row/column operations)

Performance improvements vary by workload:
- Small dictionaries (< 1,000 terms): 20-30% faster
- Medium dictionaries (1,000-10,000 terms): 30-45% faster
- Large dictionaries (> 10,000 terms): 45-64% faster

See `docs/analysis/` for detailed SIMD performance analysis (950+ lines of documentation).

### Unicode Performance

Character-level dictionary variants (`*Char`) for Unicode support:
- **~5% overhead** for UTF-8 decoding during traversal
- **4x memory** for edge labels (4 bytes per `char` vs 1 byte per `u8`)
- **Zero-cost abstraction** via monomorphization (no runtime polymorphism)
- Same query performance characteristics as byte-level variants

When to use:
- ✅ Use `*Char` variants for multi-language dictionaries with non-ASCII Unicode
- ✅ Use byte-level variants (`DoubleArrayTrie`, `PathMapDictionary`) for ASCII/Latin-1 content

## Theoretical Background

This implementation is based on the paper:

- Schulz, Klaus U., and Stoyan Mihov. "Fast string correction with Levenshtein automata." International Journal on Document Analysis and Recognition 5.1 (2002): 67-85.

## License

Licensed under the Apache License, Version 2.0. See [LICENSE](LICENSE) for details.

## References

- [Original C++ implementation](https://github.com/universal-automata/liblevenshtein-cpp)
- [PathMap backend](https://github.com/Adam-Vandervorst/PathMap)
- [GitHub Repository](https://github.com/universal-automata/liblevenshtein-rust)
- [Release Page](https://github.com/universal-automata/liblevenshtein-rust/releases)
