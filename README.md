# liblevenshtein-rust

A Rust port of [liblevenshtein](https://github.com/universal-automata/liblevenshtein-cpp) for fast approximate string matching using Levenshtein automata (Universal Levenshtein Automata).

## Overview

This library provides efficient fuzzy string matching against large dictionaries using finite state automata. It supports multiple Levenshtein distance algorithms and pluggable dictionary backends.

### Features

- **Fast approximate string matching** using Universal Levenshtein Automata
- **Multiple algorithms**:
  - `Standard`: insert, delete, substitute operations
  - `Transposition`: adds character transposition (swap adjacent chars)
  - `MergeAndSplit`: adds merge and split operations
- **Pluggable dictionary backends**:
  - PathMap (default) - high-performance trie with structural sharing
  - Extensible trait-based design for custom backends
- **Runtime dictionary updates**:
  - Thread-safe insert, remove, and clear operations
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

## Theoretical Background

This implementation is based on the paper:

- Schulz, Klaus U., and Stoyan Mihov. "Fast string correction with Levenshtein automata." International Journal on Document Analysis and Recognition 5.1 (2002): 67-85.

Additional references available in `/home/dylon/Papers/Approximate String Matching/`.

## License

Licensed under the Apache License, Version 2.0. See [LICENSE](LICENSE) for details.

## References

- [Original C++ implementation](https://github.com/universal-automata/liblevenshtein-cpp)
- [PathMap backend](https://github.com/F1R3FLY-io/PathMap)
