# liblevenshtein-rust

[![CI](https://github.com/F1R3FLY-io/liblevenshtein-rust/actions/workflows/ci.yml/badge.svg)](https://github.com/F1R3FLY-io/liblevenshtein-rust/actions/workflows/ci.yml)
[![Nightly Tests](https://github.com/F1R3FLY-io/liblevenshtein-rust/actions/workflows/nightly.yml/badge.svg)](https://github.com/F1R3FLY-io/liblevenshtein-rust/actions/workflows/nightly.yml)
[![Release](https://github.com/F1R3FLY-io/liblevenshtein-rust/actions/workflows/release.yml/badge.svg)](https://github.com/F1R3FLY-io/liblevenshtein-rust/actions/workflows/release.yml)
[![License](https://img.shields.io/badge/license-Apache--2.0-blue.svg)](LICENSE)

A Rust port of [liblevenshtein](https://github.com/universal-automata/liblevenshtein-cpp) for fast approximate string matching using Levenshtein automata (Universal Levenshtein Automata).

> **Note:** Not yet published to crates.io. See [docs/PUBLISHING.md](docs/PUBLISHING.md) for publication requirements.

## What's New in v0.3.0

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

### From GitHub (Current)

Add to your `Cargo.toml`:

```toml
[dependencies]
liblevenshtein = { git = "https://github.com/F1R3FLY-io/liblevenshtein-rust", tag = "v0.3.0" }
```

Or install the CLI tool:

```bash
cargo install --git https://github.com/F1R3FLY-io/liblevenshtein-rust --tag v0.3.0 \
  --features cli,compression,protobuf liblevenshtein
```

### Pre-built Packages

Download pre-built packages from the [GitHub Releases](https://github.com/F1R3FLY-io/liblevenshtein-rust/releases) page:

- **Debian/Ubuntu**: `.deb` packages
- **Fedora/RHEL/CentOS**: `.rpm` packages
- **Arch Linux**: `.pkg.tar.zst` packages
- **Binaries**: `.tar.gz` and `.zip` archives for Linux and macOS (x86_64 and ARM64)

## Usage

### Basic Querying

```rust
use liblevenshtein::prelude::*;

// Create a dictionary from terms
let terms = vec!["test", "testing", "tested", "tester"];
let dict = PathMapDictionary::from_terms(terms);

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

### Runtime Dictionary Updates

The PathMap and DynamicDawg backends support **thread-safe runtime updates**:

```rust
use liblevenshtein::prelude::*;

// Create dictionary
let dict = PathMapDictionary::from_terms(vec!["cat", "dog"]);
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

let dict = PathMapDictionary::from_terms(vec!["apple", "apply", "ape", "app"]);
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

let dict = PathMapDictionary::from_terms(vec![
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

### Serialization and Compression

Save and load dictionaries with optional compression:

```rust
use liblevenshtein::prelude::*;
use liblevenshtein::serialization::{BincodeSerializer, GzipSerializer};
use std::fs::File;

let dict = PathMapDictionary::from_terms(vec!["test", "testing", "tested"]);

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
liblevenshtein = { git = "https://github.com/F1R3FLY-io/liblevenshtein-rust", tag = "v0.3.0", features = ["serialization", "compression"] }
```

### CLI Tool

The library includes a full-featured command-line tool with interactive REPL:

```bash
# Install with CLI support (from GitHub)
cargo install --git https://github.com/F1R3FLY-io/liblevenshtein-rust --tag v0.3.0 \
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

See [`docs/BUILD.md`](docs/BUILD.md) for comprehensive CLI documentation.

## Documentation

- **[Building and Testing](docs/BUILD.md)** - Comprehensive build instructions and CLI usage
- **[Contributing Guidelines](CONTRIBUTING.md)** - How to contribute to the project
- **[Features Overview](docs/FEATURES.md)** - Detailed feature documentation
- **[Publishing Guide](docs/PUBLISHING.md)** - Requirements for publishing to crates.io
- **[Changelog](CHANGELOG.md)** - Version history and release notes

## Performance

The library is highly optimized for performance:

- **Arc Path Sharing**: Eliminated expensive cloning operations during traversal
- **StatePool**: Object pool pattern for state reuse with exceptional performance gains
- **SmallVec Integration**: Stack-allocated vectors reduce heap allocation pressure
- **Lazy Edge Iteration**: 15-50% faster PathMap edge iteration with zero-copy implementation
- **Aggressive Inlining**: Hot path functions inlined for optimal performance

Benchmarks show 3.3x speedup for DAWG operations and 5-18% improvements across filtering/prefix scenarios.

## Theoretical Background

This implementation is based on the paper:

- Schulz, Klaus U., and Stoyan Mihov. "Fast string correction with Levenshtein automata." International Journal on Document Analysis and Recognition 5.1 (2002): 67-85.

## License

Licensed under the Apache License, Version 2.0. See [LICENSE](LICENSE) for details.

## References

- [Original C++ implementation](https://github.com/universal-automata/liblevenshtein-cpp)
- [PathMap backend](https://github.com/Adam-Vandervorst/PathMap)
- [GitHub Repository](https://github.com/F1R3FLY-io/liblevenshtein-rust)
- [Release Page](https://github.com/F1R3FLY-io/liblevenshtein-rust/releases)
