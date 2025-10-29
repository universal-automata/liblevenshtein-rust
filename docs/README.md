# Documentation Index

Comprehensive documentation for liblevenshtein-rust v0.3.0.

**Last Updated:** 2025-10-26

---

## 📚 Getting Started

Start here if you're new to liblevenshtein-rust:

- **[Main README](../README.md)** - Project overview, installation, and quick start examples
- **[BUILD.md](../BUILD.md)** - Building from source, development setup, and CLI usage
- **[CHANGELOG.md](../CHANGELOG.md)** - Version history and release notes (v0.3.0)
- **[CONTRIBUTING.md](../CONTRIBUTING.md)** - Contributing guidelines and development workflow

---

## 📖 User Guides

### Core Features

- **[Features Overview](FEATURES.md)** - Complete feature list and capabilities (v0.2.0)
  - Levenshtein algorithms (Standard, Transposition, MergeAndSplit)
  - Dictionary backends (PathMap, DAWG, DynamicDawg)
  - Serialization formats (Bincode, JSON, Protobuf, compressed variants)
  - CLI tool and interactive REPL

- **[Code Completion Guide](CODE_COMPLETION_GUIDE.md)** - IDE-style autocomplete implementation
  - Filtering with custom predicates
  - Prefix matching for code completion
  - Performance optimization strategies
  - Real-world integration examples

- **[Hierarchical Scope Completion](guides/HIERARCHICAL_SCOPE_COMPLETION.md)** - ⭐ **NEW**
  - Contextual code completion with lexical scoping
  - Sorted vector and bitmask intersection helpers
  - 4.7% faster than HashSet baseline
  - Quick start guide with examples

### Advanced Topics

- **[DAWG Backend](DYNAMIC_DAWG.md)** - Directed Acyclic Word Graph implementation
  - Online insert/delete/minimize operations
  - Space-efficient storage
  - When to use DAWG vs PathMap

- **[Thread Safety](PATHMAP_THREAD_SAFETY.md)** - Concurrent access patterns
  - RwLock-based interior mutability
  - Safe concurrent queries during modifications
  - Multi-threaded usage examples

- **[Protobuf Serialization](PROTOBUF_SERIALIZATION.md)** - Protocol Buffers format
  - Schema definitions
  - Cross-language compatibility
  - Compression support

---

## ⚡ Performance

- **[Performance Optimizations](PERFORMANCE.md)** - **⭐ RECOMMENDED**
  - 40-60% overall performance improvements
  - Key optimizations: Arc path sharing, StatePool, SmallVec, lazy iteration
  - Benchmarking methodology and tools
  - Performance tips for users and contributors

### Archived Performance Documentation

Detailed historical analysis in [`archive/performance/`](archive/performance/):
- Optimization phase reports (Phases 2-6)
- DAWG, serialization, and filtering optimizations
- Comparisons with Java implementation
- Real-world validation results

---

## 🔬 Analysis & Research

In-depth analysis of recent feature development and optimization work:

### Fuzzy Maps Optimization
**[Fuzzy Maps Analysis](analysis/fuzzy-maps/)** - 7-phase optimization journey
- Initial regression: -7.1% after adding generic value support
- Final result: **+5.8% improvement** over baseline
- Comprehensive flame graph profiling and targeted fixes
- Production-ready with all 154 tests passing

### Hierarchical Scope Completion
**[Hierarchical Scope Analysis](analysis/hierarchical-scope/)** - Design and benchmarks
- Evaluated 6 different approaches
- Winner: Sorted Vector (4.7% faster than HashSet)
- Alternative: Bitmask (7.9% faster for ≤64 scopes)
- 4 test scenarios with 10,000 terms each

---

## 🔧 Development

- **[Publishing Guide](PUBLISHING.md)** - Requirements for publishing to crates.io
  - Current blockers (PathMap dependency)
  - Publication checklist and steps
  - Troubleshooting common issues

- **[Future Enhancements](FUTURE_ENHANCEMENTS.md)** - Roadmap and planned features
  - SIMD operations
  - Parallel queries
  - Additional algorithm support

---

## 📂 Documentation Structure

```
docs/
├── README.md (this file)           # Documentation index
│
├── guides/                         # User-facing documentation
│   ├── FEATURES.md                 # Feature overview (v0.2.0)
│   ├── CODE_COMPLETION_GUIDE.md    # Code completion tutorial
│   ├── DYNAMIC_DAWG.md             # DAWG backend guide
│   ├── PATHMAP_THREAD_SAFETY.md    # Thread safety patterns
│   ├── PROTOBUF_SERIALIZATION.md   # Protobuf format guide
│   └── HIERARCHICAL_SCOPE_COMPLETION.md  # ⭐ NEW: Scope completion guide
│
├── analysis/                       # ⭐ NEW: Research & optimization analysis
│   ├── fuzzy-maps/                 # Fuzzy maps 7-phase optimization
│   │   ├── 00_README.md            # Index of optimization journey
│   │   ├── 01_BASELINE_ANALYSIS.md
│   │   ├── 02_PHASE1_OPTIMIZATION.md
│   │   ├── 03_BENCHMARK_RESULTS.md
│   │   ├── 04_PROFILING_ANALYSIS.md
│   │   ├── 05_PHASE4_OPTIMIZATION.md
│   │   ├── 06_SERIALIZATION_ASSESSMENT.md
│   │   └── 07_FINAL_REPORT.md      # ⭐ Complete summary
│   │
│   └── hierarchical-scope/         # Hierarchical scope analysis
│       ├── README.md               # Index of design & results
│       ├── DESIGN.md               # 6 approaches evaluated
│       └── RESULTS.md              # Benchmark results
│
├── optimization/                   # Query optimization work ✅ Well-organized
│   ├── README.md                   # Central index
│   ├── QUERY_OPTIMIZATION_COMPLETE.md
│   └── [Component-specific reports]
│
├── benchmarks/                     # Benchmark results ✅ Well-organized
│   └── [Backend comparison results]
│
├── development/                    # Developer documentation
│   ├── PERFORMANCE.md              # ⭐ Performance overview
│   ├── PUBLISHING.md               # crates.io publication guide
│   └── FUTURE_ENHANCEMENTS.md      # Roadmap
│
└── archive/                        # Historical documentation ✅ Well-organized
    ├── benchmarks/                 # Historical benchmark results
    ├── performance/                # Detailed optimization reports
    └── optimization/               # Phase-by-phase optimization journey
```

---

## 🔍 Quick Reference

### For New Users

1. **[Main README](../README.md)** - Start here for installation and basic usage
2. **[FEATURES.md](FEATURES.md)** - Explore available features
3. **[CODE_COMPLETION_GUIDE.md](CODE_COMPLETION_GUIDE.md)** - Advanced usage for IDE integration
4. **[BUILD.md](../BUILD.md)** - CLI tool usage and build instructions

### For Contributors

1. **[CONTRIBUTING.md](../CONTRIBUTING.md)** - How to contribute
2. **[BUILD.md](../BUILD.md)** - Development setup
3. **[PERFORMANCE.md](PERFORMANCE.md)** - Performance optimization guidelines
4. **[FUTURE_ENHANCEMENTS.md](FUTURE_ENHANCEMENTS.md)** - Future work

### For Performance Analysis

1. **[PERFORMANCE.md](PERFORMANCE.md)** - Start here for performance overview
2. **[archive/performance/OPTIMIZATION_SUMMARY.md](archive/performance/OPTIMIZATION_SUMMARY.md)** - Detailed optimization history
3. **[archive/performance/](archive/performance/)** - Specific optimization reports

### For Integration/IDE Developers

1. **[CODE_COMPLETION_GUIDE.md](CODE_COMPLETION_GUIDE.md)** - Complete integration guide
2. **[PERFORMANCE.md](PERFORMANCE.md)** - Performance tips
3. **[PATHMAP_THREAD_SAFETY.md](PATHMAP_THREAD_SAFETY.md)** - Concurrency patterns
4. **[FEATURES.md](FEATURES.md)** - Available features and APIs

---

## 📈 What's New in v0.3.0

- ✅ **Package Support**: Debian (.deb), RPM (.rpm), and Arch Linux (.pkg.tar.zst) packages
- ✅ **CI Improvements**: Explicit CPU features for better platform compatibility
- ✅ **Code Quality**: Fixed all clippy warnings without suppressing checks
- ✅ **Bug Fixes**: Fixed CLI format auto-detection for text dictionaries
- ✅ **Documentation**: Reorganized and updated for v0.3.0

See [CHANGELOG.md](../CHANGELOG.md) for complete v0.3.0 details.

---

## 📝 Document Status

- **Version**: 0.3.0
- **Last Updated**: 2025-10-26
- **Status**: Active development
- Documentation continuously updated with new features and improvements

---

## 🤝 Contributing to Documentation

Found an issue or want to improve documentation?

1. Check [CONTRIBUTING.md](../CONTRIBUTING.md) for guidelines
2. Submit a pull request
3. Report issues on [GitHub](https://github.com/universal-automata/liblevenshtein-rust/issues)

---

**Navigation**: [← Back to Main README](../README.md) | [Features →](FEATURES.md) | [Performance →](PERFORMANCE.md)
