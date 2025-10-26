# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

### Added

#### Compression Support (2025-10-25)
- **Gzip compression for dictionary serialization** ([f8e23b6](https://github.com/F1R3FLY-io/liblevenshtein-rust/commit/f8e23b6))
  - Generic `GzipSerializer<S>` wrapper for any serialization format
  - 85% file size reduction with ~1.6x deserialization overhead
  - New `compression` feature flag
  - Comprehensive benchmarks showing compression tradeoffs

- **CLI integration for compressed formats** ([519e183](https://github.com/F1R3FLY-io/liblevenshtein-rust/commit/519e183))
  - `bincode-gz`, `json-gz`, `protobuf-gz` format variants
  - Automatic file extension handling (.bin.gz, .json.gz, .pb.gz)
  - Seamless convert, query, and save operations with compressed dictionaries

#### Code Completion Features (2025-10-24)
- **Filtering and prefix matching** ([eea90dd](https://github.com/F1R3FLY-io/liblevenshtein-rust/commit/eea90dd))
  - Filter support for `OrderedQueryIterator`
  - Prefix matching mode for autocomplete scenarios
  - Real-world code completion examples

- **Contextual filtering optimizations** ([9c27575](https://github.com/F1R3FLY-io/liblevenshtein-rust/commit/9c27575))
  - Bitmap-based context masking for instant context switching
  - Sub-trie construction for restricted search spaces
  - Examples: `advanced_contextual_filtering.rs`, `contextual_filtering_optimization.rs`
  - Comprehensive performance comparison (post-filtering vs pre-filtering)

- **Code completion guide** ([c3551ee](https://github.com/F1R3FLY-io/liblevenshtein-rust/commit/c3551ee))
  - Detailed documentation for implementing IDE-style autocomplete
  - Performance recommendations for different filtering strategies

#### OrderedQueryIterator (2025-10-23)
- **Distance-first, lexicographic ordering** ([319d4e8](https://github.com/F1R3FLY-io/liblevenshtein-rust/commit/319d4e8))
  - Results ordered by distance first, then alphabetically
  - Efficient heap-based implementation
  - Examples and benchmarks comparing to unordered queries

- **Index-based DAWG query iterator** ([56fc643](https://github.com/F1R3FLY-io/liblevenshtein-rust/commit/56fc643))
  - Memory-efficient index-based state management for DAWGs
  - Eliminates need for cloning nodes during traversal

#### Dictionary Features (2025-10-22)
- **DynamicDawg with online modifications** ([ec76137](https://github.com/F1R3FLY-io/liblevenshtein-rust/commit/ec76137))
  - Insert and delete operations on DAWG structures
  - Minimize/compaction support for optimal memory usage
  - Reference-counted node sharing for efficient mutations

- **DAWG and serialization support** ([4fc3c16](https://github.com/F1R3FLY-io/liblevenshtein-rust/commit/4fc3c16))
  - Directed Acyclic Word Graph (DAWG) backend
  - Bincode, JSON, and Protobuf serialization
  - Builder pattern for dictionary construction
  - Full-featured CLI tool with REPL

- **Real-world dictionary validation** ([4a9ed37](https://github.com/F1R3FLY-io/liblevenshtein-rust/commit/4a9ed37))
  - Benchmarks with system dictionaries (/usr/share/dict/words)
  - Validation against large real-world datasets

### Performance Improvements

#### Filtering and Prefix Optimizations (2025-10-24)
- **Phase 3: Final optimizations** ([5c485a4](https://github.com/F1R3FLY-io/liblevenshtein-rust/commit/5c485a4))
  - Total improvements: 5-18% across all operations
  - Comprehensive benchmark suite for filtering/prefix scenarios

- **Phase 2: Aggressive inlining** ([5cd73f5](https://github.com/F1R3FLY-io/liblevenshtein-rust/commit/5cd73f5))
  - Inlined hot path functions
  - Improved epsilon closure handling

- **Phase 1: Initial optimizations** ([90e1482](https://github.com/F1R3FLY-io/liblevenshtein-rust/commit/90e1482))
  - Optimized filter predicate evaluation
  - Reduced allocation overhead in prefix mode

#### DAWG Performance (2025-10-22)
- **3.3x speedup for DAWG operations** ([3f6bc58](https://github.com/F1R3FLY-io/liblevenshtein-rust/commit/3f6bc58))
  - Major algorithmic improvements
  - Optimized node traversal

- **Lightweight PathNode optimization** ([9fc42b1](https://github.com/F1R3FLY-io/liblevenshtein-rust/commit/9fc42b1))
  - Reduced memory footprint for query nodes
  - Faster node construction and copying

#### Core Engine Optimizations (2025-10-21)
- **Arc Path Sharing** ([9de7421](https://github.com/F1R3FLY-io/liblevenshtein-rust/commit/9de7421))
  - Eliminated expensive cloning operations
  - Shared ownership for path tracking

- **StatePool allocation reuse** ([e375303](https://github.com/F1R3FLY-io/liblevenshtein-rust/commit/e375303))
  - Object pool pattern for state reuse
  - Exceptional performance improvements

- **SmallVec integration** ([44157d5](https://github.com/F1R3FLY-io/liblevenshtein-rust/commit/44157d5))
  - Stack-allocated small vectors
  - Reduced heap allocation pressure

- **Lazy edge iteration** ([10ea210](https://github.com/F1R3FLY-io/liblevenshtein-rust/commit/10ea210))
  - 15-50% faster PathMap edge iteration
  - Zero-copy iterator implementation

### Documentation

- **Comprehensive optimization summary** ([b536a7a](https://github.com/F1R3FLY-io/liblevenshtein-rust/commit/b536a7a))
  - Detailed performance analysis
  - Benchmark results and methodology

- **Code completion guide** ([c3551ee](https://github.com/F1R3FLY-io/liblevenshtein-rust/commit/c3551ee))
  - IDE integration patterns
  - Performance best practices

- **Documentation reorganization** ([8292565](https://github.com/F1R3FLY-io/liblevenshtein-rust/commit/8292565))
  - Cleaned up and structured documentation
  - Improved examples and guides

### Changed

- Updated default serialization format to Protobuf when available
- Improved error messages in CLI tool
- Enhanced benchmark suite with real-world scenarios

### Fixed

- Eliminated State::clone overhead in hot paths
- Fixed unused import warnings in example files
- Corrected dead code warnings in demonstration code

## [0.1.0] - Initial Release

### Added
- Core Levenshtein automaton implementation
- PathMap dictionary backend
- Standard and transposition distance algorithms
- Basic query functionality
- Initial documentation and examples

---

[Unreleased]: https://github.com/F1R3FLY-io/liblevenshtein-rust/compare/v0.1.0...HEAD
[0.1.0]: https://github.com/F1R3FLY-io/liblevenshtein-rust/releases/tag/v0.1.0
