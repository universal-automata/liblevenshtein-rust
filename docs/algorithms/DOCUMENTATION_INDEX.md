# Documentation Index

This index shows what's documented and where to find it. The documentation is organized by algorithmic layers, with detailed implementation guides for core components.

## Quick Navigation by Topic

### Dictionary Types

**All dictionary types** are documented in [01-dictionary-layer/README.md](01-dictionary-layer/README.md), which includes:

| Dictionary Type | Coverage | Location |
|-----------------|----------|----------|
| **DoubleArrayTrie** | ⭐ Comprehensive (recommended default) | [Detailed guide](01-dictionary-layer/implementations/double-array-trie.md) |
| **DoubleArrayTrieChar** | ⭐ Comprehensive (Unicode support) | [Detailed guide](01-dictionary-layer/implementations/double-array-trie-char.md) |
| **DynamicDawg** | ✅ Overview + comparison + examples | [Layer README](01-dictionary-layer/README.md#3-dynamicdawg) |
| **DynamicDawgChar** | ✅ Overview + comparison + examples | [Layer README](01-dictionary-layer/README.md#4-dynamicdawgchar-unicode--dynamic) |
| **PathMapDictionary** | ✅ Overview + comparison + examples | [Layer README](01-dictionary-layer/README.md#6-pathmapdictionary-feature-pathmap-backend) |
| **PathMapDictionaryChar** | ✅ Overview + comparison | [Layer README](01-dictionary-layer/README.md) |
| **DawgDictionary** | ✅ Overview + comparison | [Layer README](01-dictionary-layer/README.md#7-dawgdictionary) |
| **OptimizedDawg** | ✅ Overview + comparison | [Layer README](01-dictionary-layer/README.md#8-optimizeddawg) |
| **SuffixAutomaton** | ✅ Overview + comparison + examples | [Layer README](01-dictionary-layer/README.md#5-suffixautomaton) |

**Key sections in Dictionary Layer README**:
- Decision flowchart for choosing a dictionary type
- Detailed comparison table (performance, features, use cases)
- Benchmarks for all types
- Memory characteristics
- Common use cases with code examples

### Levenshtein Automata

**All algorithm variants** are documented in [02-levenshtein-automata/README.md](02-levenshtein-automata/README.md):

| Algorithm Variant | Coverage | Location |
|-------------------|----------|----------|
| **Standard** | ⭐ Complete theory + examples | [Automata README](02-levenshtein-automata/README.md#1-standard-classic-levenshtein) |
| **Transposition** | ⭐ Complete theory + examples | [Automata README](02-levenshtein-automata/README.md#2-transposition-damerau-levenshtein) |
| **Merge-and-Split** | ⭐ Complete theory + examples | [Automata README](02-levenshtein-automata/README.md#3-merge-and-split) |

**Key sections**:
- Levenshtein distance theory with examples
- Finite automata approach explanation
- State representation and transitions
- Algorithm selection guide
- Performance analysis
- 6 detailed usage examples

### Zipper Pattern

Comprehensive documentation in [06-zipper-navigation/README.md](06-zipper-navigation/README.md):

| Zipper Type | Coverage |
|-------------|----------|
| **DoubleArrayTrieZipper** | ⭐ Complete with examples |
| **DoubleArrayTrieCharZipper** | ⭐ Complete with examples |
| **PathMapZipper** | ⭐ Complete with examples |

**Includes**:
- Huet's zipper theory
- 8 detailed usage examples
- Performance analysis
- Advanced patterns (DFS, BFS, parallel exploration)

### Value Storage

Comprehensive documentation in [09-value-storage/README.md](09-value-storage/README.md):

**Covers**:
- Architecture with diagrams
- 5 detailed use cases (code completion, categorization, fuzzy maps, metadata, hierarchical scopes)
- Performance analysis (10-100x speedup)
- Implementation details for all backends

### Core Algorithms

| Layer | Status | Location |
|-------|--------|----------|
| **Intersection/Traversal** | ⭐ Complete | [03-intersection-traversal/README.md](03-intersection-traversal/README.md) |
| **SIMD Optimization** | ⭐ Complete | [05-simd-optimization/README.md](05-simd-optimization/README.md) |
| **Distance Calculation** | 📝 Covered in Automata README | [02-levenshtein-automata/README.md](02-levenshtein-automata/README.md) |

## Documentation by Component

### Layer 1: Dictionary Layer
**File**: [01-dictionary-layer/README.md](01-dictionary-layer/README.md)

**Contents** (~800 lines):
- Overview of all 9 dictionary implementations
- Quick selection flowchart
- Detailed comparison table
- Performance benchmarks (construction, queries, fuzzy search)
- Memory characteristics
- Thread safety details
- Common use cases with examples
- Integration with automata

**Implementation Guides**:
- [DoubleArrayTrie](01-dictionary-layer/implementations/double-array-trie.md) (~1000 lines)
  - BASE/CHECK algorithm theory
  - Data structure diagrams
  - Construction algorithm
  - 8 usage examples
  - Performance analysis
  - Advanced topics (serialization, Redis, memory-mapping)

- [DoubleArrayTrieChar](01-dictionary-layer/implementations/double-array-trie-char.md) (~950 lines)
  - Why character-level matters (UTF-8 problem)
  - Unicode fundamentals
  - 9 usage examples (emoji, CJK, accented characters)
  - Performance overhead analysis
  - Advanced Unicode topics (normalization, grapheme clusters)

### Layer 2: Levenshtein Automata
**File**: [02-levenshtein-automata/README.md](02-levenshtein-automata/README.md)

**Contents** (~850 lines):
- Levenshtein distance theory
- Finite automata approach
- All three algorithm variants (Standard, Transposition, Merge-and-Split)
- State representation
- 6 usage examples
- Performance analysis
- Algorithm selection guide

### Layer 3: Intersection & Traversal
**File**: [03-intersection-traversal/README.md](03-intersection-traversal/README.md)

**Contents** (~700 lines):
- Synchronized traversal algorithm
- State representation with AutomatonZipper
- Traversal strategies (DFS, BFS, priority queue)
- Optimization techniques
- 4 usage examples
- Performance analysis

### Layer 5: SIMD Optimization
**File**: [05-simd-optimization/README.md](05-simd-optimization/README.md)

**Contents** (~900 lines):
- SIMD fundamentals
- Edge label scanning with AVX2/SSE4.1
- Benchmark results (2-4x speedup)
- Implementation details
- Runtime detection
- Platform support
- Performance tuning guide

### Layer 6: Zipper Navigation
**File**: [06-zipper-navigation/README.md](06-zipper-navigation/README.md)

**Contents** (~850 lines):
- Huet's zipper theory
- DictZipper and ValuedDictZipper traits
- All zipper implementations
- 8 detailed usage examples
- Performance analysis
- Advanced patterns

### Layer 9: Value Storage
**File**: [09-value-storage/README.md](09-value-storage/README.md)

**Contents** (~900 lines):
- Architecture explanation with diagrams
- Memory layout visualization
- Complete trait documentation
- 5 extensive use cases
- Performance analysis (10-100x speedup)
- Implementation details for all backends
- Best practices guide

### Main Overview
**File**: [README.md](README.md)

**Contents** (~450 lines):
- Architecture diagram showing all 9 layers
- Quick start examples
- Performance comparison tables
- Use case decision trees
- Navigation hub with links to all layers

## What's NOT Yet Documented (Future Work)

The following could be added if needed:

### Additional Dictionary Implementation Guides

While all dictionary types are covered in the layer overview with comparisons, examples, and benchmarks, detailed implementation guides could be added for:

- [ ] DynamicDawg implementation details
- [ ] DynamicDawgChar implementation details
- [ ] PathMapDictionary implementation details
- [ ] SuffixAutomaton implementation details

**Note**: These are lower priority because:
1. The layer README provides comprehensive coverage for choosing and using these
2. DoubleArrayTrie variants are recommended for 80%+ of use cases
3. The existing documentation covers the concepts that apply to all types

### Additional Layers

- [ ] Distance Calculation (currently covered within Automata layer)
- [ ] Caching Layer (lower priority - straightforward wrapper)
- [ ] Contextual Completion (combines existing documented components)

## How to Find What You Need

### "How do I choose a dictionary type?"
→ [01-dictionary-layer/README.md](01-dictionary-layer/README.md) (decision flowchart + comparison table)

### "How do I use DoubleArrayTrie?"
→ [01-dictionary-layer/implementations/double-array-trie.md](01-dictionary-layer/implementations/double-array-trie.md) (8 examples)

### "How do I handle Unicode text?"
→ [01-dictionary-layer/implementations/double-array-trie-char.md](01-dictionary-layer/implementations/double-array-trie-char.md) (complete guide)

### "How does fuzzy matching work?"
→ [02-levenshtein-automata/README.md](02-levenshtein-automata/README.md) (theory + algorithms)

### "Should I use Standard or Transposition algorithm?"
→ [02-levenshtein-automata/README.md#algorithm-selection-guide](02-levenshtein-automata/README.md#algorithm-selection-guide)

### "How do I store values with terms?"
→ [09-value-storage/README.md](09-value-storage/README.md) (complete architecture guide)

### "How do I navigate the trie with zippers?"
→ [06-zipper-navigation/README.md](06-zipper-navigation/README.md) (8 examples)

### "How do DynamicDawg and PathMapDictionary compare?"
→ [01-dictionary-layer/README.md#detailed-comparison-table](01-dictionary-layer/README.md#detailed-comparison-table)

### "What's the performance difference between dictionary types?"
→ [01-dictionary-layer/README.md#performance-benchmarks](01-dictionary-layer/README.md#performance-benchmarks)

### "How does SIMD optimization work?"
→ [05-simd-optimization/README.md](05-simd-optimization/README.md) (complete guide)

## Documentation Statistics

- **Total markdown files**: 9
- **Total documentation lines**: ~7,500 lines
- **Code examples**: 50+ complete, runnable examples
- **Benchmarks**: Comprehensive performance data across all components
- **Diagrams**: ASCII art for data structures and algorithms
- **Academic references**: 25+ papers and resources

## Contributing Documentation

If you'd like to add documentation for components not yet covered in detail:

1. Follow the existing structure (see any layer README as template)
2. Include: Theory, Usage Examples, Performance Analysis, References
3. Add diagrams where helpful (ASCII art is fine)
4. Link from/to related documentation
5. Update this index

---

**Last Updated**: 2025-11-04
**Coverage**: Core components (80%+ of use cases) comprehensively documented
