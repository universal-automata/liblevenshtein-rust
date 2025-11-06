# WallBreaker Algorithm - Implementation Research

## Overview

**WallBreaker** is a similarity search algorithm that overcomes the "wall effect" in traditional left-to-right Levenshtein automata traversal. This directory contains research, analysis, and implementation planning for adding WallBreaker to liblevenshtein-rust.

### The Wall Effect Problem

Traditional approximate string matching starts from the left edge of the pattern and must explore **all prefixes** up to error bound `b` before any filtering occurs. For example, with `max_distance = 16`, the algorithm must visit all dictionary prefixes of length 0-16, even though most lead to dead ends.

### WallBreaker Solution

Instead of left-to-right traversal:
1. **Split** pattern P into b+1 pieces
2. **Find** exact matches for pattern pieces (at least one will match if word is within distance b)
3. **Extend** bidirectionally from exact matches using Levenshtein filters
4. **Verify** total distance meets bound

This avoids the wasteful initial exploration, dramatically improving performance for large error bounds.

## Original Paper

**Title:** "WallBreaker - overcoming the wall effect in similarity search"
**Authors:** Stefan Gerdjikov, Stoyan Mihov, Petar Mitankin, Klaus U. Schulz
**Published:** EDBT/ICDT 2013
**Location:** `/home/dylon/Papers/Approximate String Matching/WallBreaker - overcoming the wall effect in similarity search.pdf`

**Key Result:** 0.088ms average query time for 100-character patterns with 16 errors in 750K word lexicon.

## Documentation Index

### Analysis Documents
- **[technical-analysis.md](./technical-analysis.md)** - Detailed analysis of current codebase architecture, gaps, and requirements
- **[decision-matrix.md](./decision-matrix.md)** - Comparison of three implementation approaches with effort/benefit analysis

### Planning Documents
- **[implementation-plan.md](./implementation-plan.md)** - Detailed phase-by-phase implementation plan for each approach
- **[architectural-sketches.md](./architectural-sketches.md)** - Code designs, new traits, and integration points
- **[benchmarking-plan.md](./benchmarking-plan.md)** - Performance validation strategy and success criteria

### Tracking Documents
- **[progress-tracker.md](./progress-tracker.md)** - Task breakdown, status tracking, and milestone monitoring

## Current Status

**Status:** Research Phase - Not Yet Implemented
**Decision:** Pending selection of implementation approach
**Estimated Effort:** 3-4 weeks (Index-based) to 21-31 weeks (Full SCDAWG)

## Quick Start

### For Researchers
1. Read [technical-analysis.md](./technical-analysis.md) to understand current architecture
2. Review [decision-matrix.md](./decision-matrix.md) to see implementation options
3. Check WallBreaker paper for algorithm details

### For Implementers
1. Select implementation approach from [decision-matrix.md](./decision-matrix.md)
2. Follow phase-by-phase plan in [implementation-plan.md](./implementation-plan.md)
3. Track progress in [progress-tracker.md](./progress-tracker.md)
4. Validate with benchmarks from [benchmarking-plan.md](./benchmarking-plan.md)

## Implementation Options Summary

| Approach | Effort | Performance | Recommendation |
|----------|--------|-------------|----------------|
| **Full SCDAWG** | 21-31 weeks | Maximum | For long-term, production deployment |
| **Hybrid** | 6-9 weeks | 60-70% of full | **Recommended** - best effort/benefit ratio |
| **Index-based** | 3-4 weeks | 40-50% of full | Quick win, proof of concept |

See [decision-matrix.md](./decision-matrix.md) for detailed comparison.

## Key Requirements

### Critical Missing Components
- ❌ Bidirectional dictionary traversal
- ❌ SCDAWG (Symmetric Compact Directed Acyclic Word Graph) backend
- ⚠️ Exact substring search (partial - SuffixAutomaton only)
- ❌ Pattern splitting algorithms
- ❌ Left/right extension filters

### Current Architecture Constraints
- All dictionary backends only support forward traversal
- `DictionaryNode` trait lacks parent links and position tracking
- State transitions assume strict left-to-right character consumption
- No substring query capabilities exposed through public API

## Performance Expectations

### When WallBreaker Helps Most
- **Large error bounds:** b ≥ 4
- **Long patterns:** ≥ 50 characters
- **Large dictionaries:** ≥ 100K terms
- **Cases where wall effect dominates runtime**

### When Traditional May Be Better
- **Small error bounds:** b ≤ 2
- **Short patterns:** < 20 characters
- **Small dictionaries:** < 10K terms
- **Memory-constrained environments**

## Related Documentation

### Library Documentation
- [Levenshtein Automata](/docs/algorithms/02-levenshtein-automata/README.md) - Current automata implementation
- [Dictionary Layer](/docs/algorithms/01-dictionary-layer/) - Available dictionary backends
- [Future Enhancements](/docs/research/future-enhancements.md) - Other planned improvements

### Code Locations
- `/src/transducer/query.rs` - Main query iterator (lines 86-188)
- `/src/transducer/transition.rs` - State transitions (lines 591-668)
- `/src/dictionary/mod.rs` - Dictionary traits (lines 182-239)
- `/src/dictionary/suffix_automaton.rs` - Substring matching reference (lines 100+)

## Contact & Discussion

For questions or discussion about WallBreaker implementation:
- Review existing analysis in this directory
- Check GitHub issues for related discussions
- Refer to original paper for algorithmic details

## License

Documentation follows the same Apache-2.0 license as the main library.

---

**Last Updated:** 2025-11-06
**Status:** Research & Planning Phase
**Next Step:** Select implementation approach and begin Phase 1
