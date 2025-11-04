# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

### Added

#### DynamicDawg Performance Optimizations (2025-11-03)
- **Bloom Filter for fast negative lookups** (88-93% improvement)
  - Probabilistic data structure with 3 hash functions and 10 bits per element
  - Accelerates `contains()` operations by rejecting non-existent terms early
  - Zero false negatives, <1% false positive rate with default configuration
  - Configurable via `with_config()` API: `DynamicDawg::with_config(f32::INFINITY, Some(10000))`
  - Benchmarks: contains() operations improved from ~38µs to ~3µs (10-12x faster)
  - Minimal memory overhead: ~1.25 bytes per term

- **Lazy Auto-Minimization** (30% improvement for large datasets)
  - Automatic minimize() triggering based on configurable growth threshold
  - Default: disabled (threshold = f32::INFINITY), opt-in via `with_config()`
  - Configurable threshold: `DynamicDawg::with_config(1.5, None)` minimizes at 50% growth
  - Benchmark results: 30% faster insertions for 1000+ term datasets
  - Prevents unbounded memory growth during bulk insertions
  - Trade-off: adds ~5-10% overhead for small datasets (<100 terms)

- **Sorted Batch Insertion** (4-8% improvement)
  - `from_terms()` now pre-sorts input before insertion
  - Better prefix/suffix sharing leads to more compact DAWG structure
  - Benchmark results: 4-8% faster construction for typical workloads
  - No API changes required - optimization is transparent

- **Comprehensive optimization analysis**
  - Evaluated 7 optimization candidates with scientific methodology
  - 3 optimizations implemented and kept (sorted insertion, auto-minimize, Bloom filter)
  - 1 optimization rejected after analysis: RCU/Atomic Swapping (-1400% write regression)
  - 3 optimizations skipped with rationale: LRU suffix cache (low ROI), Adaptive edge storage (SmallVec sufficient), Incremental compaction (minimize() already provides this)
  - Full documentation: `docs/optimizations/all_optimizations_final_report.md`

- **New benchmarks for optimization validation**
  - `benches/auto_minimize_benchmark.rs` - Auto-minimization threshold tuning
  - `benches/bloom_filter_benchmark.rs` - Bloom filter performance analysis
  - `benches/compact_benchmark.rs` - Compaction strategy comparison

- **Documentation**
  - `docs/optimizations/all_optimizations_final_report.md` - Comprehensive optimization results (7 candidates analyzed)
  - `docs/optimizations/rcu_assessment.md` - Detailed RCU trade-off analysis
  - `docs/optimizations/dynamic_dawg_optimization_results.md` - Benchmark data and decision log

#### Contextual Code Completion Engine (2025-11-03)
- **Hierarchical scope-aware code completion with zipper-based navigation**
  - Complete 6-phase implementation (Phases 1-6) as documented in roadmap
  - Character-level draft state management with incremental insertion
  - Checkpoint-based undo/redo for editor integration
  - Hierarchical context tree for lexical scope visibility (global → module → function → block)
  - Thread-safe concurrent queries and modifications (Arc/RwLock-based)
  - Mixed queries searching both finalized terms and active drafts simultaneously

- **Zipper architecture for efficient dictionary traversal**
  - `DictZipper` and `ValuedDictZipper` trait abstractions (src/dictionary/zipper.rs)
  - `PathMapZipper` implementation with lock-per-operation pattern
  - `AutomatonZipper` for Levenshtein automaton state tracking
  - `IntersectionZipper` composing dictionary and automaton navigation
  - `ZipperQueryIterator` with BFS-based traversal and StatePool reuse

- **ContextualCompletionEngine API** (src/contextual/)
  - `create_root_context()` / `create_child_context()` - Hierarchical scope creation
  - `insert_char()` / `insert_str()` - Incremental draft building (~4 µs per char)
  - `checkpoint()` / `undo()` - State management for editor undo/redo (~116 ns per checkpoint)
  - `finalize()` / `finalize_direct()` - Promote drafts to permanent dictionary terms
  - `complete()` - Fuzzy query with hierarchical visibility filtering
  - `discard()` / `rollback_char()` - Draft manipulation

- **Value-filtered queries for scoped completions**
  - `query_filtered()` - Custom predicate-based filtering during traversal
  - `query_by_value_set()` - Efficient set-based scope filtering
  - Significantly faster than post-filtering results (filtering during traversal)

- **Performance characteristics**
  - Insert character: ~4 µs (12M chars/sec throughput)
  - Checkpoint creation: ~116 ns per operation
  - Query (500 terms, distance 1): ~11.5 µs
  - Query (500 terms, distance 2): ~309 µs
  - Thread-safe with fine-grained locking (DashMap for drafts, RwLock for dictionary)

- **Comprehensive test coverage**
  - 10 PathMapZipper tests (navigation, finality, values, cloning)
  - 11 AutomatonZipper tests (state transitions, all algorithm variants)
  - 9 IntersectionZipper tests (match detection, distance computation)
  - 7 ZipperQueryIterator tests (lazy evaluation, early termination)
  - Draft lifecycle integration tests (insert → checkpoint → rollback → restore → finalize)
  - Contextual stress tests (concurrent operations, large-scale scenarios)

- **Benchmarks and performance analysis**
  - `benches/contextual_completion_benchmarks.rs` - Single-threaded performance
  - `benches/concurrent_completion_benchmarks.rs` - Concurrency benchmarks
  - `benches/zipper_vs_node_benchmark.rs` - Comparison with node-based queries
  - Zipper-based queries are 1.66-1.97× slower than node-based (acceptable trade-off for architectural benefits)

- **Documentation**
  - `docs/design/contextual-completion-api.md` - Complete API specification (906 lines)
  - `docs/design/contextual-completion-roadmap.md` - 6-phase implementation plan (490 lines)
  - `docs/design/contextual-completion-zipper.md` - Architecture design (745 lines)
  - `docs/design/contextual-completion-progress.md` - Implementation tracking and status
  - `docs/design/zipper-vs-node-performance.md` - Performance analysis and trade-offs
  - Updated README.md with contextual completion examples and zipper API usage

- **Example code**
  - `examples/contextual_completion.rs` - Complete demonstration (221 lines)
    - Hierarchical scope creation (global → function → block)
    - Incremental typing simulation
    - Checkpoint/undo workflows
    - Draft finalization
    - Visibility scoping

- **Use Cases**
  - LSP servers with multi-file scope awareness
  - Code editors with context-sensitive completion
  - REPL environments with session-scoped symbols
  - Any application requiring hierarchical fuzzy matching with dynamic state

- **Performance Notes**
  - Sub-millisecond response times for interactive use
  - Zipper overhead acceptable for contextual use cases (1.66-1.97× vs node-based)
  - Thread-safe: share engine across threads with Arc
  - Memory: ~1KB overhead per active context (within design targets)

## [0.4.0] - 2025-10-31

### Added

#### Unicode Support (2025-10-30)
- **Character-level dictionary variants for correct Unicode Levenshtein distances**
  - `DoubleArrayTrieChar` - Character-level Double-Array Trie implementation
  - `PathMapDictionaryChar` - Character-level PathMap with dynamic updates (requires `pathmap-backend` feature)
  - Proper handling of multi-byte UTF-8 sequences (accented characters, CJK, emoji)
  - Generic `CharUnit` trait abstraction over `u8` (byte-level) and `char` (character-level)
  - ~5% performance overhead for UTF-8 decoding, 4x memory for edge labels (char vs u8)

- **Comprehensive Unicode test coverage**
  - 19 PathMapChar integration tests (all passing)
  - Tests for emoji (4-byte UTF-8), CJK (3-byte UTF-8), accented characters (2-byte UTF-8)
  - Empty query, exact match, one-edit distance, transposition, various distance levels
  - Dynamic operations (insert/remove), value mapping, value filtering
  - Edge cases (empty dictionary, single characters, normalization)

- **Fixed core Unicode issue**: "" → "¡" now correctly requires distance 1 (one character) instead of distance 2 (two bytes)

- **Updated cache eviction nodes**
  - All 8 cache wrapper nodes support generic `Unit` type
  - Noop, LRU, LRU Optimized, LFU, TTL, Age, Cost-Aware, Memory Pressure

- **Documentation**
  - Updated README.md with Unicode support section and examples
  - Character-level backends in dictionary comparison table
  - Guidance on when to use byte-level vs character-level variants
  - `UTF8_IMPLEMENTATION.md` - Complete technical design document (300+ lines)
  - `UTF8_IMPLEMENTATION_STATUS.md` - Implementation status report (250+ lines)


#### Phase 4: SIMD Optimization
- **Comprehensive SIMD acceleration across critical performance paths**
  - 8 SIMD-optimized components with 20-64% real-world performance gains
  - ~2,300 lines of optimized SIMD code with runtime CPU feature detection
  - Data-driven threshold tuning based on empirical benchmarking
  - Extensive documentation (950+ lines across 3 analysis documents)

- **Batch 1: SSE4.1 fallback + SIMD affix stripping**
  - Runtime CPU feature detection (`is_x86_feature_detected!`)
  - SSE4.1 fallback paths for all AVX2 operations
  - SIMD-accelerated prefix/suffix stripping for string comparisons

- **Batch 2A: Transducer state operations**
  - Characteristic vector SIMD (2-3x faster for window sizes ≥8)
  - Position subsumption SIMD (1.5-2x faster for batch operations)
  - State minimum distance SIMD (2x faster for states with 8+ positions)
  - Integrated into `State::min_distance()` and transducer transitions

- **Batch 2B: Dictionary edge lookup SIMD** (commit: 89cb3b8, 488707b, 337fd83)
  - Generic SIMD implementation supporting both `usize` and `u32` targets
  - SSE4.1 implementation: 16-way byte comparison
  - Data-driven threshold optimization: scalar <12 edges, SSE4.1 12-16 edges
  - **Performance impact** (after threshold optimization):
    - Realistic workload: **43% faster** (21.9ns → 38.9ns)
    - Overall queries: **20% faster** (36.4µs → 45.9µs)
    - Distance-1 queries: **5% faster** (2.55µs → 2.69µs)
    - Distance-2 queries: **6% faster** (9.19µs → 9.75µs)
    - Small edge lookups (4 edges): **64% faster** (3.54ns → 10.03ns)
  - Integrated into DAWG and Optimized DAWG dictionaries

- **Batch 3: Distance matrix SIMD** (pre-existing)
  - AVX2 implementation: 8 u32 values in parallel
  - SSE4.1 implementation: 4 u32 values in parallel
  - Automatic dispatch with threshold-based selection
  - Integrated into `distance::standard_distance()` when SIMD feature enabled

- **Comprehensive test coverage**
  - 193 total tests passing with SIMD enabled
  - 14 edge lookup-specific tests with boundary conditions
  - SIMD vs scalar validation for all critical paths
  - Integration tests for DAWG, transducer, and query operations

- **Documentation**
  - `docs/PHASE4_SIMD_COMPLETION_STATUS.md` - Overall completion summary (350+ lines)
  - `docs/BATCH2A_INTEGRATION_ANALYSIS.md` - State operations analysis
  - `docs/BATCH2B_PERFORMANCE_ANALYSIS.md` - Edge lookup detailed analysis (450+ lines)

#### Query Iterator Optimization (2025-10-29)
- **Comprehensive query iterator testing and optimization**
  - Fixed 2 critical bugs in ordered query iterator (result dropping, lexicographic ordering)
  - Added 20 new comprehensive tests covering distances 0-99 and edge cases
  - Created 20 benchmarks for performance analysis (criterion + flamegraph profiling)
  - All 139 tests passing with full coverage of query modifiers

- **Adaptive sorting optimization**
  - Insertion sort for small buffers (≤10 items) for better cache locality
  - Unstable sort for larger buffers (~20-30% faster)
  - Pre-sized buffer allocation to reduce reallocations
  - Performance improvements: 0.7% faster for distance 1 (common case), up to 30% faster for distance 3+

- **Query iterator benchmarks** (`benches/query_iterator_benchmarks.rs`, `benches/query_profiling.rs`)
  - 10 criterion benchmarks covering various query scenarios
  - 10 flamegraph-optimized profiling benchmarks
  - Distance scaling, dictionary size scaling, algorithm comparison
  - Early termination efficiency testing

### Changed

#### Documentation Reorganization - Phase 2 (2025-10-29)
- **Analysis documentation moved to `docs/analysis/`**
  - Created `docs/analysis/fuzzy-maps/` - 7-phase optimization journey (01-07)
  - Created `docs/analysis/hierarchical-scope/` - Design and benchmark analysis
  - Moved 10 analysis files from project root to organized structure
  - Added comprehensive index files (00_README.md, README.md) for navigation
  - 58% reduction in root directory clutter (17 → 7 markdown files)

- **Documentation structure improvements**
  - `docs/analysis/fuzzy-maps/` - Complete fuzzy maps optimization story (-7.1% → +5.8%)
  - `docs/analysis/hierarchical-scope/` - Scope completion design and results
  - `docs/guides/HIERARCHICAL_SCOPE_COMPLETION.md` - User-facing guide
  - Updated `docs/README.md` with new "Analysis & Research" section
  - Fixed broken links after file moves
  - Updated `.gitignore` with LaTeX artifact patterns

#### Documentation Reorganization - Phase 1 (2025-10-29)
- **Optimization documentation moved to `docs/optimization/`**
  - Created organized structure with README.md as entry point
  - 14 optimization documents now properly organized
  - Removed 5 duplicate/obsolete documentation files (~57KB cleanup)
  - Project root now clean with only essential documentation

- **Documentation consolidation**
  - `docs/optimization/README.md` - Main optimization documentation index
  - Query optimization documents (COMPLETE, WORK_SUMMARY, PERFORMANCE_ANALYSIS, FLAMEGRAPH_ANALYSIS)
  - Component optimization reports (STATE_OPERATIONS, TRANSITION, SUBSUMPTION, POOL_INTERSECTION)
  - Analysis documents organized by component

### Fixed

#### Query Iterator Bug Fixes (2025-10-29)
- **Bug #1: Large distance queries dropping results** (`src/transducer/ordered_query.rs:126-197`)
  - Query "quuo" with distance 99 only returned 2 of 5 terms
  - Fixed with distance bucket re-queuing logic
  - Regression test added in `tests/large_distance_test.rs`

- **Bug #2: Lexicographic ordering not maintained** (`src/transducer/ordered_query.rs:64-83, 126-197`)
  - Results at same distance not lexicographically sorted
  - Fixed with sorted_buffer and explicit sorting
  - Comprehensive tests added in `tests/query_comprehensive_test.rs`

## [0.3.0] - 2025-10-26

### Added
- **Arch Linux package support** ([1199173](https://github.com/F1R3FLY-io/liblevenshtein-rust/commit/1199173))
  - `.pkg.tar.zst` packages for x86_64 and aarch64 architectures
  - `packaging/arch/PKGBUILD` with architecture-specific RUSTFLAGS
  - Automated building and testing in CI using Docker with archlinux:latest
  - Sanity tests verify installation and basic functionality

- **RPM package support** ([1199173](https://github.com/F1R3FLY-io/liblevenshtein-rust/commit/1199173))
  - `.rpm` packages for RedHat, Fedora, CentOS distributions
  - RPM metadata in `Cargo.toml` using cargo-generate-rpm
  - Automated building and testing in Fedora 40 container
  - Proper library paths for /usr/lib64

### Changed
- **CI workflow improvements** ([1cd9189](https://github.com/F1R3FLY-io/liblevenshtein-rust/commit/1cd9189))
  - Use explicit CPU features (`-C target-feature=+aes,+sse2` for x86_64, `+aes,+neon` for ARM64)
  - Replaced `-C target-cpu=native` to ensure gxhash dependency compatibility
  - Applied to `nightly.yml` and `release.yml` workflows

### Fixed
- **Code quality improvements** ([0f29a30](https://github.com/F1R3FLY-io/liblevenshtein-rust/commit/0f29a30))
  - Fixed all 15 clippy warnings without suppressing any checks
  - Redundant pattern matching: `if let Err(_) = ...` → `.is_err()` (2 instances)
  - Identical if blocks: Simplified `parse_limit` logic
  - Borrowed box: `&Box<T>` → `&T` (2 instances)
  - Needless range loops: Use iterator patterns with `enumerate()` (5 instances)
  - Method naming: Renamed `from_iter` → `from_terms` to avoid `FromIterator` confusion (44 call sites)
  - Too many arguments: Refactored to use structs (2 functions)

- **Library naming corrections** ([1199173](https://github.com/F1R3FLY-io/liblevenshtein-rust/commit/1199173))
  - Fixed library names to use correct double-lib prefix:
    - `libliblevenshtein.so` (Linux shared library)
    - `libliblevenshtein.rlib` (Rust static library)
    - `libliblevenshtein.dylib` (macOS shared library)
  - Updated across all packaging files and CI workflows

### Added

#### Development Infrastructure (2025-10-25)
- **Git hooks for preventing accidental commits** ([116d617](https://github.com/F1R3FLY-io/liblevenshtein-rust/commit/116d617))
  - Pre-commit hook checks for uncommented `[patch]` sections in Cargo.toml
  - Prevents committing local development overrides (e.g., local PathMap paths)
  - Installation script: `./scripts/install-git-hooks.sh`
  - Clear error messages with fix suggestions
  - Documentation in `.githooks/README.md`

### Changed

#### Dependency Management (2025-10-25)
- **PathMap dependency now uses GitHub repository** ([77e6b56](https://github.com/F1R3FLY-io/liblevenshtein-rust/commit/77e6b56))
  - Changed from local path to `git = "https://github.com/Adam-Vandervorst/PathMap.git"`
  - Added commented `[patch]` section for local development override
  - Removed PathMap checkout steps from GitHub Actions workflows (automatic fetch)
  - Created `.cargo/config.toml.local-example` for local dev setup
  - Updated CONTRIBUTING.md with instructions for both approaches
  - Benefits: cleaner CI/CD, easier for contributors, works from crates.io

#### Documentation (2025-10-25)
- **Comprehensive documentation restructuring** ([d9a52d0](https://github.com/F1R3FLY-io/liblevenshtein-rust/commit/d9a52d0))
  - Created `docs/README.md` as central documentation index (177 lines)
  - Organized documentation into categories (Getting Started, User Guides, Developer Docs, Benchmarks)
  - Archived 20 historical benchmark files to `docs/archive/benchmarks/`
  - Updated `FEATURES.md` for v0.2.0 (DynamicDawg, OrderedQueryIterator, compression, protobuf)
  - Created comprehensive `BUILD.md` (434 lines) with build instructions
  - Updated `CONTRIBUTING.md` for v0.2.0 features and workflows
  - All docs now include version headers and last-updated dates

#### CI/CD (2025-10-25)
- **GitHub Actions workflow badges** ([5c5853a](https://github.com/F1R3FLY-io/liblevenshtein-rust/commit/5c5853a))
  - Added CI, Nightly Tests, Release, License, and Crates.io badges to README

- **Comprehensive GitHub Actions workflows** ([e065043](https://github.com/F1R3FLY-io/liblevenshtein-rust/commit/e065043))
  - `ci.yml`: Main CI with test matrix (Ubuntu + macOS, stable + nightly Rust)
  - `release.yml`: Multi-platform builds (Linux x86_64/ARM64, macOS x86_64/ARM64, .deb packages)
  - `nightly.yml`: Daily validation with code coverage, security audits, benchmark tracking
  - Total: 647 lines of workflow automation

## [0.2.0] - 2025-10-25

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

#### Documentation Reorganization (2025-10-31)
- **Comprehensive documentation restructure for improved discoverability**
  - Moved 16+ files from project root to organized docs/ subdirectories
  - Created intuitive directory structure: user-guide/, developer-guide/, design/, research/, bug-reports/, completion-reports/, implementation-status/, benchmarks/, archive/
  - Clean project root with only essential files (README, CHANGELOG, LICENSE, Cargo.toml, .gitignore)

- **11 new README.md navigation indexes**
  - Each documentation directory has comprehensive README with file descriptions and navigation
  - Clear entry points for users, contributors, and researchers

- **4 new comprehensive user guides** (10,000+ lines total)
  - `getting-started.md` - Installation, basic usage, backend/algorithm selection
  - `algorithms.md` - Deep dive into Standard, Transposition, and MergeAndSplit algorithms
  - `backends.md` - Complete backend comparison with performance characteristics
  - `serialization.md` - Save/load dictionaries with format comparison and best practices

- **Updated all cross-references and internal links**
  - Fixed main README.md documentation section
  - Rewrote docs/README.md as comprehensive documentation index
  - Updated developer-guide references (CONTRIBUTING.md → contributing.md, BUILD.md → building.md)
  - Corrected all version numbers from v0.2.0/v0.3.0 → v0.4.0

- **Consolidated related documentation**
  - 9 SIMD research files → research/simd-optimization/
  - Distance optimization docs → research/distance-optimization/
  - Bug analysis → bug-reports/
  - Historical docs → archive/ (benchmarks/, implementation/, optimization/, performance/)

- **Comprehensive optimization summary** ([b536a7a](https://github.com/F1R3FLY-io/liblevenshtein-rust/commit/b536a7a))
  - Detailed performance analysis
  - Benchmark results and methodology

- **Code completion guide** ([c3551ee](https://github.com/F1R3FLY-io/liblevenshtein-rust/commit/c3551ee))
  - IDE integration patterns
  - Performance best practices

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

[Unreleased]: https://github.com/F1R3FLY-io/liblevenshtein-rust/compare/v0.2.0...HEAD
[0.2.0]: https://github.com/F1R3FLY-io/liblevenshtein-rust/compare/v0.1.0...v0.2.0
[0.1.0]: https://github.com/F1R3FLY-io/liblevenshtein-rust/releases/tag/v0.1.0
