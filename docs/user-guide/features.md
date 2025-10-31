# Feature Documentation

**Version**: 0.4.0
**Last Updated**: 2025-10-25

This document describes all features available in liblevenshtein-rust.

## Core Features

### 1. Dictionary Implementations

#### PathMap Dictionary
- **Type**: Trie-based using structural sharing
- **Best for**: General purpose, dynamic modifications
- **Thread-safe**: Uses RwLock for concurrent access
- **Usage**:
```rust
use liblevenshtein::prelude::*;

let dict = PathMapDictionary::from_iter(vec!["test", "testing"]);
```

#### DAWG Dictionary
- **Type**: Directed Acyclic Word Graph with suffix sharing
- **Best for**: Large static dictionaries with common patterns
- **Thread-safe**: Fully immutable, no synchronization needed
- **Space efficiency**: Shares both prefixes and suffixes
- **Usage**:
```rust
use liblevenshtein::prelude::*;

let dict = DawgDictionary::from_iter(vec!["testing", "walking", "talking"]);
println!("Terms: {}, Nodes: {}", dict.term_count(), dict.node_count());
```

#### DynamicDawg Dictionary
- **Type**: DAWG with online insert/delete/minimize operations
- **Best for**: Dictionaries needing both space efficiency and runtime updates
- **Thread-safe**: Uses RwLock for concurrent access
- **Space efficiency**: Maintains DAWG properties through incremental minimization
- **Usage**:
```rust
use liblevenshtein::prelude::*;

let dict = DynamicDawgDictionary::from_iter(vec!["test", "testing"]);
dict.insert("tester");  // Online insertion with minimization
dict.remove("test");    // Online deletion
```

### 2. Levenshtein Algorithms

#### Standard Levenshtein
- Operations: Insert, Delete, Substitute
- Use case: General string matching

#### Transposition
- Operations: Standard + Transposition
- Use case: Typos involving swapped characters

#### Merge and Split
- Operations: Standard + Merge + Split
- Use case: OCR errors, concatenation/separation issues

### 3. Transducer Builder Pattern

Fluent API for creating transducers with validation:

```rust
use liblevenshtein::prelude::*;

let transducer = TransducerBuilder::new()
    .dictionary(dict)
    .algorithm(Algorithm::Transposition)
    .build()?;
```

**Benefits**:
- Clear, readable configuration
- Compile-time type checking
- Helpful error messages
- Order-independent method calls

### 4. Query Iterators

#### Standard Query Iterator
- Returns results in discovery order
- Lazy evaluation, no collection overhead
```rust
for term in transducer.query("test", 2) {
    println!("{}", term);
}

for candidate in transducer.query_with_distance("test", 2) {
    println!("{}: {}", candidate.term, candidate.distance);
}
```

#### Ordered Query Iterator (v0.4.0)
- **Distance-first ordering**: Results sorted by edit distance, then lexicographically
- **Perfect for code completion**: Most relevant results first
- **Usage**:
```rust
for candidate in transducer.query_ordered("aple", 1) {
    println!("{}: {}", candidate.term, candidate.distance);
}
// Output:
//   ape: 1
//   apple: 1
//   apply: 1
```

#### Filtering and Prefix Matching (v0.4.0)
- **Custom filters**: Apply arbitrary predicates to results
- **Prefix mode**: Match only terms starting with query ± edits
- **Optimized**: Bitmap masking for efficient context filtering
- **Usage**:
```rust
// Prefix matching for code completion
for candidate in transducer
    .query_ordered("getVal", 1)
    .prefix()  // Only terms starting with "getVal" ± 1 edit
    .filter(|c| c.term.starts_with("get"))
{
    println!("{}: {}", candidate.term, candidate.distance);
}
```

See [CODE_COMPLETION_GUIDE.md](CODE_COMPLETION_GUIDE.md) for detailed examples.

## Optional Features

### Dictionary Serialization

Enable with: `features = ["serialization"]`

**Supported formats**:
- **Bincode**: Fast, compact binary format
- **JSON**: Human-readable, for debugging
- **Protobuf** (optional `protobuf` feature): Cross-language compatibility

**Compression support** (v0.2.0, optional `compression` feature):
- **Gzip compression**: 85% file size reduction
- **Compressed formats**: bincode-gz, json-gz, protobuf-gz
- **Generic wrapper**: `GzipSerializer<S>` works with any serializer

**Usage**:
```rust
use liblevenshtein::prelude::*;
use liblevenshtein::serialization::*;
use std::fs::File;

// Save dictionary with compression (v0.4.0)
let dict = PathMapDictionary::from_iter(vec!["test", "testing"]);
let file = File::create("dict.bin.gz")?;
GzipSerializer::<BincodeSerializer>::serialize(&dict, file)?;

// Load compressed dictionary
let file = File::open("dict.bin.gz")?;
let loaded: PathMapDictionary = GzipSerializer::<BincodeSerializer>::deserialize(file)?;

// Protobuf format (cross-language)
#[cfg(feature = "protobuf")]
{
    let file = File::create("dict.pb.gz")?;
    GzipSerializer::<ProtobufSerializer>::serialize(&dict, file)?;
}
```

**Benefits**:
- **Fast startup** with pre-built dictionaries
- **Share dictionaries** across systems and languages
- **Reduce file size** by 85% with compression
- **Production-ready**: Validated with 470k+ word dictionaries

### CLI Tool

Enable with: `features = ["cli"]`

Build: `cargo build --bin liblevenshtein --features cli,compression,protobuf --release`

**Commands**:

1. **Query**: Search for fuzzy matches
```bash
liblevenshtein query "aple" \\
    --dict words.txt \\
    -m 2 \\
    --algorithm transposition \\
    -s  # Show distances
```

2. **Convert**: Between formats and backends (v0.4.0)
```bash
# Convert to compressed format
liblevenshtein convert words.txt words.bin.gz \\
    --to-format bincode-gz \\
    --to-backend path-map

# Convert between backends
liblevenshtein convert dict.bin dict-dawg.bin \\
    --from-backend path-map \\
    --to-backend dawg
```

3. **Insert/Delete**: Runtime dictionary updates (v0.4.0)
```bash
# Insert terms
liblevenshtein insert "newterm" --dict dict.bin

# Delete terms
liblevenshtein delete "oldterm" --dict dict.bin
```

4. **REPL**: Interactive exploration (v0.4.0)
```bash
liblevenshtein repl --dict words.bin.gz --format bincode-gz
```

5. **Info**: Show dictionary statistics
```bash
liblevenshtein info --dict words.txt --backend path-map
```

**Format Support** (v0.4.0):
- Text (`--format text` or `.txt`)
- Bincode (`--format bincode` or `.bin`)
- JSON (`--format json` or `.json`)
- Protobuf (`--format protobuf` or `.pb`)
- **Compressed**: `bincode-gz`, `json-gz`, `protobuf-gz` (.bin.gz, .json.gz, .pb.gz)

**Backend Options**:
- `path-map`: Default trie-based dictionary
- `dawg`: Space-efficient DAWG
- `dynamic-dawg`: DAWG with runtime updates

**Algorithm Options**:
- `standard`: Insert, delete, substitute
- `transposition`: + character swaps
- `merge-and-split`: + merge/split operations

## Examples

All examples can be run with `cargo run --example <name>`:

1. **serialization**: Dictionary save/load demo
2. **dawg_demo**: DAWG vs PathMap comparison
3. **builder_demo**: TransducerBuilder usage
4. **code_completion_demo** (v0.4.0): IDE-style autocomplete with filtering
5. **advanced_contextual_filtering** (v0.4.0): Bitmap masking for context switching
6. **contextual_filtering_optimization** (v0.4.0): Performance comparison of filtering strategies
7. **dynamic_dictionary**: Runtime dictionary updates with thread safety

## Performance

### Recent Optimizations (Phases 1-6)

The library has undergone extensive optimization work:

- **40-60% faster** than baseline across all workloads
- **StatePool**: Eliminates State allocation overhead
- **Arc path sharing**: Reduces PathMapNode cloning by 72%
- **Lazy iterators**: Eliminates dictionary overhead

See [docs/optimization/OPTIMIZATION_SUMMARY.md](optimization/OPTIMIZATION_SUMMARY.md) for details.

### Benchmarks

Run benchmarks:
```bash
RUSTFLAGS="-C target-cpu=native" cargo bench
```

### Memory Usage

- **PathMap**: ~O(n) for n unique prefixes
- **DAWG**: ~O(m) for m unique substrings (shares prefixes and suffixes)
- **Position**: 17 bytes (Copy semantics, no heap allocation)
- **State pooling**: Reuses allocations, LIFO for cache locality

## Thread Safety

All dictionary implementations are thread-safe:

- **PathMapDictionary**: Uses `Arc<RwLock<...>>` for concurrent access
- **DawgDictionary**: Fully immutable, `SyncStrategy::Persistent`
- **Transducer**: Clone-cheap, can be shared across threads

## Feature Comparison with Java Version

| Feature | Java | Rust | Notes |
|---------|------|------|-------|
| Standard Levenshtein | ✅ | ✅ | Full parity |
| Transposition | ✅ | ✅ | Full parity |
| Merge/Split | ✅ | ✅ | Full parity |
| Dictionary abstraction | ✅ | ✅ | Trait-based in Rust |
| DAWG dictionary | ✅ | ✅ | **New in Rust!** |
| PathMap/Trie | ✅ | ✅ | Full parity |
| Serialization | ✅ | ✅ | **New in Rust!** |
| Builder pattern | ✅ | ✅ | **New in Rust!** |
| CLI tool | ✅ | ✅ | **New in Rust!** |
| State pooling | ✅ | ✅ | **Enhanced in Rust!** |
| Performance | Good | **Excellent** | 40-60% faster after optimizations |

## Rust-Specific Advantages

1. **Zero-cost abstractions**: Generic iterators with no boxing overhead
2. **Compile-time safety**: No null pointers, no type erasure
3. **Memory safety**: No GC pauses, ownership prevents leaks
4. **Copy semantics**: Position is Copy (17 bytes), no clone overhead
5. **Arc sharing**: Cheap reference counting instead of cloning

## Dependencies

### Core
- `pathmap`: Trie implementation
- `smallvec`: Stack-allocated vectors

### Optional
- `serde`, `bincode`, `serde_json`: Serialization (feature: `serialization`)
- `clap`, `anyhow`: CLI (feature: `cli`)

### Dev
- `criterion`: Benchmarking

## Cargo Features

```toml
[features]
default = []
serialization = ["serde", "bincode", "serde_json"]
compression = ["flate2"]  # v0.2.0
protobuf = ["prost", "prost-build"]  # v0.2.0
cli = ["clap", "anyhow", "serialization"]
```

**Feature combinations**:
- `serialization`: Basic save/load support (bincode, JSON)
- `serialization,compression`: Add gzip compression
- `serialization,protobuf`: Add cross-language Protobuf support
- `cli,compression,protobuf`: Full CLI with all formats

## Future Enhancements

See [FUTURE_ENHANCEMENTS.md](FUTURE_ENHANCEMENTS.md) and [JAVA_COMPARISON.md](JAVA_COMPARISON.md) for planned improvements.
