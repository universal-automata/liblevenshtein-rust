# Documentation Index

Comprehensive documentation for liblevenshtein-rust v0.4.0.

**Last Updated:** 2025-10-31

---

## 📚 Getting Started

Start here if you're new to liblevenshtein-rust:

- **[Main README](../README.md)** - Project overview, installation, and quick start examples
- **[User Guide](user-guide/)** - Getting started, algorithms, backends, features
- **[CHANGELOG.md](../CHANGELOG.md)** - Version history and release notes (v0.4.0)

---

## 📖 User Documentation

### [User Guide](user-guide/)

Complete user-facing documentation:

- **[Getting Started](user-guide/getting-started.md)** - Installation and first queries
- **[Algorithms](user-guide/algorithms.md)** - Levenshtein distance algorithms
- **[Dictionary Backends](user-guide/backends.md)** - Backend comparison and selection
- **[Serialization](user-guide/serialization.md)** - Save and load dictionaries
- **[Features Overview](user-guide/features.md)** - Complete feature list (v0.4.0)
- **[Code Completion Guide](user-guide/code-completion.md)** - IDE-style autocomplete
- **[Thread Safety](user-guide/thread-safety.md)** - Concurrent access patterns

---

## 🔧 Developer Documentation

### [Developer Guide](developer-guide/)

For contributors and maintainers:

- **[Architecture](developer-guide/architecture.md)** - System design and core traits
- **[Building](developer-guide/building.md)** - Build instructions and CLI usage
- **[Contributing](developer-guide/contributing.md)** - Contribution guidelines
- **[Performance](developer-guide/performance.md)** - Optimization guide
- **[Publishing](developer-guide/publishing.md)** - Release procedures

---

## 🏗️ Design Documents

### [Design](design/)

Technical specifications for major features:

- **[Dynamic DAWG](design/dynamic-dawg.md)** - Dynamic dictionary implementation
- **[Hierarchical Correction](design/hierarchical-correction.md)** - Multi-level error correction
- **[Prefix Matching](design/prefix-matching.md)** - Prefix-based search optimization
- **[Protobuf Serialization](design/protobuf-serialization.md)** - Protobuf format specification
- **[Suffix Automaton](design/suffix-automaton.md)** - Suffix automaton design

---

## 🔬 Research & Analysis

### [Research](research/)

Performance research and optimization analysis:

- **[SIMD Optimization](research/simd-optimization/)** - SIMD vectorization research
- **[Distance Optimization](research/distance-optimization/)** - Distance computation optimization
- **[Comparative Analysis](research/comparative-analysis/)** - Algorithm comparisons
- **[Eviction Wrapper](research/eviction-wrapper/)** - Cache eviction strategy research
- **[Future Enhancements](research/future-enhancements.md)** - Roadmap and planned features

---

## ⚡ Performance & Benchmarks

### [Benchmarks](benchmarks/)

Performance measurements and analysis:

- **[Backend Performance Comparison](benchmarks/BACKEND_PERFORMANCE_COMPARISON.md)** - All backends compared
- **[DAT Optimization Results](benchmarks/DAT_OPTIMIZATION_RESULTS.md)** - Double Array Trie optimizations
- **[DAWG Optimization Analysis](benchmarks/DAWG_OPTIMIZATION_ANALYSIS.md)** - DAWG performance analysis
- **[Optimization Summary](benchmarks/OPTIMIZATION_SUMMARY.md)** - Overall optimization results

---

## 🐛 Bug Reports & Fixes

### [Bug Reports](bug-reports/)

Detailed bug analysis and fixes:

- **[Merge-Split Algorithm](bug-reports/merge-split-algorithm.md)** - MergeAndSplit algorithm fixes
- **[Transposition Bug](bug-reports/transposition-bug.md)** - Transposition operation bug
- **[Cross-Validation Issues](bug-reports/cross-validation-bug.md)** - Cross-validation fixes

---

## ✅ Completion Reports

### [Completion Reports](completion-reports/)

Project milestone reports:

- **[Project Summary](completion-reports/project-summary.md)** - Overall project completion
- **[Phase 2 Complete](completion-reports/phase2-complete.md)** - Phase 2 milestone
- **[Optimization Complete](completion-reports/optimization-complete.md)** - Optimization phase
- **[Next Steps](completion-reports/next-steps.md)** - Future work

---

## 📋 Implementation Status

### [Implementation Status](implementation-status/)

Current feature status:

- **[UTF-8 Implementation](implementation-status/utf8-implementation.md)** - UTF-8 support details
- **[UTF-8 Status](implementation-status/utf8-status.md)** - Current UTF-8 status

---

## 📂 Archive

### [Archive](archive/)

Historical documentation (for reference only):

- **[Benchmarks](archive/benchmarks/)** - Historical benchmark results
- **[Implementation](archive/implementation/)** - Historical implementation plans
- **[Optimization](archive/optimization/)** - Phase-by-phase optimization history
- **[Performance](archive/performance/)** - Archived performance analysis

---

## 🔍 Quick Reference

### For New Users

1. **[User Guide](user-guide/)** - Start here for installation and basic usage
2. **[Getting Started](user-guide/getting-started.md)** - Quick start guide
3. **[Algorithms](user-guide/algorithms.md)** - Choose the right algorithm
4. **[Backends](user-guide/backends.md)** - Choose the right backend

### For Contributors

1. **[Contributing](developer-guide/contributing.md)** - How to contribute
2. **[Building](developer-guide/building.md)** - Development setup
3. **[Architecture](developer-guide/architecture.md)** - System design
4. **[Performance](developer-guide/performance.md)** - Performance optimization guidelines

### For Performance Analysis

1. **[Performance Guide](developer-guide/performance.md)** - Performance overview
2. **[Benchmarks](benchmarks/)** - Detailed benchmark results
3. **[Research](research/)** - Optimization research

### For Integration/IDE Developers

1. **[Code Completion Guide](user-guide/code-completion.md)** - Complete integration guide
2. **[Thread Safety](user-guide/thread-safety.md)** - Concurrency patterns
3. **[Serialization](user-guide/serialization.md)** - Dictionary persistence
4. **[Features](user-guide/features.md)** - Available features and APIs

---

## 📈 What's New in v0.4.0

- ✅ **Unicode Support**: Character-level dictionaries (`*Char` variants) for correct Unicode Levenshtein distances
- ✅ **Phase 4 SIMD Optimization**: 20-64% performance gains with AVX2/SSE4.1
- ✅ **Documentation Reorganization**: Intuitive structure with user-guide/, developer-guide/, design/, research/, etc.
- ✅ **Comprehensive User Guides**: New getting-started, algorithms, backends, and serialization guides
- ✅ **Full Test Coverage**: 19 Unicode-specific tests, comprehensive doctest coverage

See [CHANGELOG.md](../CHANGELOG.md) for complete v0.4.0 details.

---

## 📝 Documentation Status

- **Version**: 0.4.0
- **Last Updated**: 2025-10-31
- **Status**: Active development
- Documentation continuously updated with new features and improvements

---

## 🤝 Contributing to Documentation

Found an issue or want to improve documentation?

1. Check [Contributing Guidelines](developer-guide/contributing.md)
2. Submit a pull request
3. Report issues on [GitHub](https://github.com/universal-automata/liblevenshtein-rust/issues)

---

**Navigation**: [← Back to Main README](../README.md) | [User Guide →](user-guide/) | [Developer Guide →](developer-guide/)
