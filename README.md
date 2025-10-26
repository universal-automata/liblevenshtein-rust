# liblevenshtein-rust

[![CI](https://github.com/F1R3FLY-io/liblevenshtein-rust/actions/workflows/ci.yml/badge.svg)](https://github.com/F1R3FLY-io/liblevenshtein-rust/actions/workflows/ci.yml)
[![Nightly Tests](https://github.com/F1R3FLY-io/liblevenshtein-rust/actions/workflows/nightly.yml/badge.svg)](https://github.com/F1R3FLY-io/liblevenshtein-rust/actions/workflows/nightly.yml)
[![Release](https://github.com/F1R3FLY-io/liblevenshtein-rust/actions/workflows/release.yml/badge.svg)](https://github.com/F1R3FLY-io/liblevenshtein-rust/actions/workflows/release.yml)
[![License](https://img.shields.io/badge/license-Apache--2.0-blue.svg)](LICENSE)
[![Crates.io](https://img.shields.io/crates/v/liblevenshtein.svg)](https://crates.io/crates/liblevenshtein)

A Rust port of [liblevenshtein](https://github.com/universal-automata/liblevenshtein-cpp) for fast approximate string matching using Levenshtein automata (Universal Levenshtein Automata).

## Overview

This library provides efficient fuzzy string matching against large dictionaries using finite state automata. It supports multiple Levenshtein distance algorithms and pluggable dictionary backends.

### Features

- **Fast approximate string matching** using Universal Levenshtein Automata
- **Multiple algorithms**:
  - `Standard`: insert, delete, substitute operations
  - `Transposition`: adds character transposition (swap adjacent chars)
  - `MergeAndSplit`: adds merge and split operations
- **Multiple dictionary backends**:
  - **PathMap** (default) - high-performance trie with structural sharing
  - **DAWG** - Directed Acyclic Word Graph for space-efficient storage
  - **DynamicDawg** - DAWG with online insert/delete/minimize operations
  - Extensible trait-based design for custom backends
- **Ordered results**: `OrderedQueryIterator` returns results sorted by distance first, then lexicographically
- **Filtering and prefix matching**: Filter results with custom predicates, enable prefix mode for code completion
- **Serialization support** (optional `serialization` feature):
  - Bincode (binary), JSON, Protobuf formats
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

## Installation

Add to your `Cargo.toml`:

```toml
[dependencies]
liblevenshtein = "0.1"
```

## Usage

### Basic Querying

```rust
use liblevenshtein::prelude::*;

// Create a dictionary from terms
let terms = vec!["test", "testing", "tested", "tester"];
let dict = PathMapDictionary::from_iter(terms);

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

### Runtime Dictionary Updates

The PathMap backend supports **thread-safe runtime updates**:

```rust
use liblevenshtein::prelude::*;

// Create dictionary
let dict = PathMapDictionary::from_iter(vec!["cat", "dog"]);
let transducer = Transducer::new(dict.clone(), Algorithm::Standard);

// Insert new terms at runtime
dict.insert("cot");
dict.insert("bat");

// Queries immediately see the new terms
let results: Vec<_> = transducer.query("cot", 1).collect();
// Results: ["cat", "cot"]

// Remove terms
dict.remove("dog");

// Clear entire dictionary
dict.clear();
```

**Thread Safety**: The dictionary uses `RwLock` for interior mutability:
- Multiple concurrent queries are allowed (read locks)
- Modifications acquire exclusive write locks
- Active `Transducer` instances automatically see updates

See [`examples/dynamic_dictionary.rs`](examples/dynamic_dictionary.rs) for a complete demonstration.

### Ordered Results

Get results sorted by edit distance first, then alphabetically:

```rust
use liblevenshtein::prelude::*;

let dict = PathMapDictionary::from_iter(vec!["apple", "apply", "ape", "app"]);
let transducer = Transducer::new(dict, Algorithm::Standard);

// Results ordered by distance, then alphabetically
for candidate in transducer.query_ordered("aple", 1) {
    println!("{}: {}", candidate.term, candidate.distance);
}
// Output:
//   ape: 1
//   apple: 1
//   apply: 1
```

### Filtering and Prefix Matching

Filter results and enable prefix matching for code completion:

```rust
use liblevenshtein::prelude::*;

let dict = PathMapDictionary::from_iter(vec![
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
// Output:
//   getValue: 0
//   getVariable: 1
```

See [`examples/code_completion_demo.rs`](examples/code_completion_demo.rs) and [`examples/contextual_filtering_optimization.rs`](examples/contextual_filtering_optimization.rs) for more examples.

### Serialization and Compression

Save and load dictionaries with optional compression:

```rust
use liblevenshtein::prelude::*;
use liblevenshtein::serialization::{BincodeSerializer, GzipSerializer};
use std::fs::File;

let dict = PathMapDictionary::from_iter(vec!["test", "testing", "tested"]);

// Save with compression (85% file size reduction)
let file = File::create("dict.bin.gz")?;
GzipSerializer::<BincodeSerializer>::serialize(&dict, file)?;

// Load compressed dictionary
let file = File::open("dict.bin.gz")?;
let dict: PathMapDictionary = GzipSerializer::<BincodeSerializer>::deserialize(file)?;
```

Requires `serialization` and `compression` features:

```toml
[dependencies]
liblevenshtein = { version = "0.1", features = ["serialization", "compression"] }
```

### CLI Tool

The library includes a full-featured command-line tool:

```bash
# Install with CLI support
cargo install liblevenshtein --features cli,compression,protobuf

# Query a dictionary
liblevenshtein query "test" --dict /usr/share/dict/words -m 2 -s

# Convert between formats with compression
liblevenshtein convert words.txt words.bin.gz \
  --to-format bincode-gz --to-backend path-map

# Launch interactive REPL
liblevenshtein repl --dict words.bin.gz --format bincode-gz
```

See [`BUILD.md`](BUILD.md) for more CLI usage examples.

## Theoretical Background

This implementation is based on the paper:

- Schulz, Klaus U., and Stoyan Mihov. "Fast string correction with Levenshtein automata." International Journal on Document Analysis and Recognition 5.1 (2002): 67-85.

Additional references available in `/home/dylon/Papers/Approximate String Matching/`.

## License

Licensed under the Apache License, Version 2.0. See [LICENSE](LICENSE) for details.

## References

- [Original C++ implementation](https://github.com/universal-automata/liblevenshtein-cpp)
- [PathMap backend](https://github.com/F1R3FLY-io/PathMap)
