# Documentation Index

Comprehensive documentation for liblevenshtein-rust v0.2.0.

## 📚 Getting Started

- **[Main README](../README.md)** - Project overview, installation, and quick start
- **[BUILD.md](../BUILD.md)** - Building from source and development setup
- **[CHANGELOG.md](../CHANGELOG.md)** - Version history and release notes (v0.2.0)
- **[CONTRIBUTING.md](../CONTRIBUTING.md)** - Contributing guidelines

## 🎯 User Guides

### Core Features
- **[Features Overview](FEATURES.md)** - Complete feature list and capabilities
- **[Code Completion Guide](CODE_COMPLETION_GUIDE.md)** - IDE-style autocomplete with filtering and prefix matching
- **[Code Completion Performance](CODE_COMPLETION_PERFORMANCE.md)** - Optimization strategies for filtering

### Dictionary Backends
- **[DAWG Backend](DYNAMIC_DAWG.md)** - Directed Acyclic Word Graph implementation with online modifications
- **[DAWG Comparison](DAWG_COMPARISON.md)** - DAWG vs PathMap performance analysis
- **[PathMap Thread Safety](PATHMAP_THREAD_SAFETY.md)** - Concurrent access patterns and thread safety

### Serialization & Storage
- **[Protobuf Serialization](PROTOBUF_SERIALIZATION.md)** - Protocol Buffers format support
- **Compression** - See v0.2.0 features in [CHANGELOG](../CHANGELOG.md)
  - Gzip compression (85% file size reduction)
  - Compressed format variants: bincode-gz, json-gz, protobuf-gz

## 🔧 Developer Documentation

### Performance & Optimization

**Start Here:**
- **[Optimization Summary](OPTIMIZATION_SUMMARY.md)** - **⭐ RECOMMENDED** - Complete optimization overview
  - 40-60% performance improvements
  - Profiling-guided approach
  - Key takeaways and lessons learned

**Detailed Reports:**
- **[optimization/](optimization/)** - Phase-by-phase optimization journey
  - [Optimization README](optimization/README.md) - Detailed overview
  - [Phase 4: SmallVec Investigation](optimization/PHASE4_SMALLVEC_INVESTIGATION.md)
  - [Phase 5: StatePool Results](optimization/PHASE5_STATEPOOL_RESULTS.md) - Exceptional results
  - [Phase 6: Arc Path Results](optimization/PHASE6_ARC_PATH_RESULTS.md) - Highly successful
  - [Profiling Comparison](optimization/PROFILING_COMPARISON.md)

**Additional Performance Docs:**
- [ARC Optimization Results](ARC_OPTIMIZATION_RESULTS.md)
- [DAWG Optimization Results](DAWG_OPTIMIZATION_RESULTS.md)
- [PathNode Optimization Results](PATHNODE_OPTIMIZATION_RESULTS.md)
- [Threshold Tuning Results](THRESHOLD_TUNING_RESULTS.md)
- [PGO Impact Analysis](PGO_IMPACT_ANALYSIS.md)

### Architecture & Implementation
- **[Contextual Filtering Optimization](CONTEXTUAL_FILTERING_OPTIMIZATION.md)** - Bitmap masking strategies
- **[Index-Based Query](INDEX_BASED_QUERY_RESULTS.md)** - Memory-efficient DAWG queries
- **[Query ARC Analysis](QUERY_ARC_ANALYSIS.md)** - Arc usage patterns in queries
- **[Future Enhancements](FUTURE_ENHANCEMENTS.md)** - Roadmap and planned features

## 📊 Benchmarks & Validation

- **[Real World Validation](REAL_WORLD_VALIDATION.md)** - Tests with system dictionaries
- **[Java Comparison](JAVA_COMPARISON.md)** - Performance vs original Java implementation
- **[Serialization Optimization Results](SERIALIZATION_OPTIMIZATION_RESULTS.md)** - Compression benchmarks

### Archived Data
Historical benchmark results in [`archive/benchmarks/`](archive/benchmarks/):
- PGO build logs
- DAWG benchmarks (baseline, adaptive, optimized)
- Serialization benchmarks
- Profiling results
- 20+ benchmark result files

## 🗂️ Documentation Organization

```
docs/
├── README.md (this file)          # Main documentation index
│
├── User Guides
│   ├── FEATURES.md                 # Feature overview
│   ├── CODE_COMPLETION_GUIDE.md    # Code completion tutorial
│   ├── CODE_COMPLETION_PERFORMANCE.md
│   ├── DYNAMIC_DAWG.md             # DAWG backend guide
│   ├── PROTOBUF_SERIALIZATION.md
│   └── PATHMAP_THREAD_SAFETY.md
│
├── Performance & Optimization
│   ├── OPTIMIZATION_SUMMARY.md     # ⭐ Start here
│   ├── ARC_OPTIMIZATION_RESULTS.md
│   ├── DAWG_OPTIMIZATION_RESULTS.md
│   ├── PATHNODE_OPTIMIZATION_RESULTS.md
│   ├── THRESHOLD_TUNING_RESULTS.md
│   ├── PGO_IMPACT_ANALYSIS.md
│   └── SERIALIZATION_OPTIMIZATION_RESULTS.md
│
├── Architecture & Analysis
│   ├── CONTEXTUAL_FILTERING_OPTIMIZATION.md
│   ├── INDEX_BASED_QUERY_RESULTS.md
│   ├── QUERY_ARC_ANALYSIS.md
│   ├── DAWG_COMPARISON.md
│   └── JAVA_COMPARISON.md
│
├── Validation & Benchmarks
│   ├── REAL_WORLD_VALIDATION.md
│   └── archive/benchmarks/        # Historical data
│
├── optimization/                   # Detailed phase reports
│   ├── README.md
│   ├── PHASE4_SMALLVEC_INVESTIGATION.md
│   ├── PHASE5_STATEPOOL_RESULTS.md
│   ├── PHASE6_ARC_PATH_RESULTS.md
│   ├── PROFILING_COMPARISON.md
│   ├── benchmarks/
│   └── profiling/
│
└── FUTURE_ENHANCEMENTS.md          # Roadmap
```

## 🔍 Quick Reference

### For New Users
1. Start: [Main README](../README.md)
2. Features: [FEATURES.md](FEATURES.md)
3. Code completion: [CODE_COMPLETION_GUIDE.md](CODE_COMPLETION_GUIDE.md)
4. Changelog: [CHANGELOG.md](../CHANGELOG.md)

### For Contributors
1. Contributing: [CONTRIBUTING.md](../CONTRIBUTING.md)
2. Build setup: [BUILD.md](../BUILD.md)
3. Performance: [OPTIMIZATION_SUMMARY.md](OPTIMIZATION_SUMMARY.md)
4. Future work: [FUTURE_ENHANCEMENTS.md](FUTURE_ENHANCEMENTS.md)

### For Performance Analysts
1. **Overview**: [OPTIMIZATION_SUMMARY.md](OPTIMIZATION_SUMMARY.md)
2. **Detailed**: [optimization/README.md](optimization/README.md)
3. **Specific areas**:
   - DAWG: [DAWG_OPTIMIZATION_RESULTS.md](DAWG_OPTIMIZATION_RESULTS.md)
   - Serialization: [SERIALIZATION_OPTIMIZATION_RESULTS.md](SERIALIZATION_OPTIMIZATION_RESULTS.md)
   - Code completion: [CODE_COMPLETION_PERFORMANCE.md](CODE_COMPLETION_PERFORMANCE.md)

### For Integration/IDE Developers
1. [CODE_COMPLETION_GUIDE.md](CODE_COMPLETION_GUIDE.md) - Complete integration guide
2. [CODE_COMPLETION_PERFORMANCE.md](CODE_COMPLETION_PERFORMANCE.md) - Performance tips
3. [CONTEXTUAL_FILTERING_OPTIMIZATION.md](CONTEXTUAL_FILTERING_OPTIMIZATION.md) - Optimization strategies
4. [PATHMAP_THREAD_SAFETY.md](PATHMAP_THREAD_SAFETY.md) - Concurrency patterns

## 📈 Recent Updates (v0.2.0)

- ✅ Compression support (85% file size reduction)
- ✅ CLI integration with compressed formats
- ✅ OrderedQueryIterator for sorted results
- ✅ Filtering and prefix matching optimizations
- ✅ Comprehensive GitHub Actions CI/CD
- ✅ Multi-platform release builds

See [CHANGELOG.md](../CHANGELOG.md) for complete v0.2.0 details.

## 📝 Document Status

- **Version**: 0.2.0
- **Last Updated**: 2025-10-25
- **Status**: Active development
- Documentation continuously updated with new features and improvements

## 🤝 Contributing to Documentation

Found an issue or want to improve documentation?
1. Check [CONTRIBUTING.md](../CONTRIBUTING.md)
2. Submit a pull request
3. Report issues on GitHub

---

**Navigation**: [← Back to Main README](../README.md) | [Features →](FEATURES.md) | [Optimization Summary →](OPTIMIZATION_SUMMARY.md)
