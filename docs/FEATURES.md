# Feature Documentation

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

## Optional Features

### Dictionary Serialization

Enable with: `features = ["serialization"]`

**Supported formats**:
- **Bincode**: Fast, compact binary format
- **JSON**: Human-readable, for debugging

**Usage**:
```rust
use liblevenshtein::prelude::*;
use liblevenshtein::serialization::*;
use std::fs::File;

// Save dictionary
let dict = PathMapDictionary::from_iter(vec!["test", "testing"]);
let file = File::create("dict.bin")?;
BincodeSerializer::serialize(&dict, file)?;

// Load dictionary
let file = File::open("dict.bin")?;
let loaded: PathMapDictionary = BincodeSerializer::deserialize(file)?;
```

**Benefits**:
- Fast startup with pre-built dictionaries
- Share dictionaries across systems
- Reduce memory usage with binary formats

### CLI Tool

Enable with: `features = ["cli"]`

Build: `cargo build --bin liblevenshtein-cli --features cli --release`

**Commands**:

1. **Query**: Search for fuzzy matches
```bash
liblevenshtein-cli query \\
    --dict words.txt \\
    --term "aple" \\
    --distance 2 \\
    --algorithm transposition \\
    --with-distance
```

2. **Info**: Show dictionary statistics
```bash
liblevenshtein-cli info \\
    --dict words.txt \\
    --dict-type dawg
```

**Options**:
- `--dict-type`: Choose `pathmap` or `dawg`
- `--algorithm`: Choose `standard`, `transposition`, or `merge-and-split`
- `--with-distance`: Include edit distances in output

## Examples

All examples can be run with `cargo run --example <name>`:

1. **serialization**: Dictionary save/load demo
2. **dawg_demo**: DAWG vs PathMap comparison
3. **builder_demo**: TransducerBuilder usage

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
cli = ["clap", "anyhow"]
```

## Future Enhancements

See [FUTURE_ENHANCEMENTS.md](FUTURE_ENHANCEMENTS.md) and [JAVA_COMPARISON.md](JAVA_COMPARISON.md) for planned improvements.
