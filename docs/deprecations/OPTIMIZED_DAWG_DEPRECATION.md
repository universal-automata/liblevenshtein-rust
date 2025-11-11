# OptimizedDawg Deprecation Notice

**Status**: Deprecated in version 0.7.0
**Replacement**: [`DynamicDawg`](../user-guide/backends.md#dynamicdawg)
**Removal Timeline**: May be removed in version 2.0.0

## Summary

`OptimizedDawg` is deprecated in favor of `DynamicDawg`, which provides:
- **11× faster construction** (1.40ms vs 16.0ms @ 1,000 words)
- **Full feature support** (MappedDictionary, ValuedDictZipper, mutability)
- **Active development** with ongoing optimizations

## Background

OptimizedDawg was an experimental implementation created to improve DAWG performance through arena-based edge storage. The hypothesis was that storing all edges in a contiguous memory arena would provide:
- Better cache locality
- Reduced memory fragmentation
- Faster query performance

## Analysis Results

Comprehensive benchmarking (2025-11-11) revealed that OptimizedDawg:

1. **Does NOT contain Double-Array Trie features** despite the name
   - No BASE/CHECK arrays
   - No O(1) transitions
   - Standard DAWG with arena storage (not a DAT hybrid)

2. **Performance is worse than DynamicDawg**:

| Dictionary Size | OptimizedDawg | DynamicDawg | Difference |
|-----------------|---------------|-------------|------------|
| 1,000 words     | 16.0 ms       | 1.40 ms     | **11× slower** |
| 10,000 words    | 317 ms        | 58.3 ms     | **5.4× slower** |
| 32,000 words    | 738 ms        | 139 ms      | **5.3× slower** |

**Throughput**:
| Dictionary Size | OptimizedDawg | DynamicDawg | Difference |
|-----------------|---------------|-------------|------------|
| 1,000 words     | 62K elem/s    | 716K elem/s | **11× faster** |
| 10,000 words    | 31.5K elem/s  | 171K elem/s | **5.4× faster** |
| 32,000 words    | 43.3K elem/s  | 231K elem/s | **5.3× faster** |

3. **Missing critical features**:
   - ❌ No `MappedDictionary` trait (cannot store values)
   - ❌ No `ValuedDictZipper` trait (no hierarchical navigation with values)
   - ❌ No mutability support (immutable after construction)
   - ❌ No bloom filter optimization
   - ❌ No suffix caching

4. **Arena storage incompatible with mutability**:
   - DynamicDawg requires per-node edge storage for insertions/deletions
   - Arena-based storage requires knowing edge count at allocation time
   - Cannot merge OptimizedDawg's features into DynamicDawg

## Migration Guide

### Simple Replacement

**Before**:
```rust
use liblevenshtein::prelude::*;

let dict = OptimizedDawg::from_terms(vec!["apple", "application", "apply"]);
assert!(dict.contains("apple"));
```

**After**:
```rust
use liblevenshtein::prelude::*;

let dict = DynamicDawg::from_terms(vec!["apple", "application", "apply"]);
assert!(dict.contains("apple"));
```

### With Values (New Feature)

DynamicDawg supports value storage, which OptimizedDawg never did:

```rust
use liblevenshtein::prelude::*;

let dict: DynamicDawg<u32> = DynamicDawg::from_terms_with_values(vec![
    ("apple", 1),
    ("application", 2),
    ("apply", 3),
]);

assert_eq!(dict.get_value("apple"), Some(1));
assert!(dict.contains_with_value("application", |v| *v > 1));
```

### With Mutability (New Feature)

DynamicDawg supports runtime modifications:

```rust
use liblevenshtein::prelude::*;

let dict = DynamicDawg::new();

// Insert at runtime
dict.insert("test");
dict.insert("testing");

// Remove at runtime
dict.remove("test");

// Compact to restore minimality
dict.compact();
```

### With Zipper Navigation (New Feature)

DynamicDawg supports zipper-based navigation:

```rust
use liblevenshtein::prelude::*;
use liblevenshtein::dictionary::zipper::{DictZipper, ValuedDictZipper};

let dict: DynamicDawg<u32> = DynamicDawg::from_terms_with_values(vec![
    ("cat", 1),
    ("catch", 2),
]);

let zipper = DynamicDawgZipper::new_from_dict(&dict);

// Navigate to "cat"
let z = zipper
    .descend(b'c')
    .and_then(|z| z.descend(b'a'))
    .and_then(|z| z.descend(b't'))
    .unwrap();

assert!(z.is_final());
assert_eq!(z.value(), Some(1));
```

## Performance Comparison

### Construction Time (Norvig Corpus)

```
Dictionary Size: 1,000 words
├─ OptimizedDawg:  16.0 ms  (62.7K elem/s)
└─ DynamicDawg:     1.40 ms (716K elem/s) ✅ 11× FASTER

Dictionary Size: 10,000 words
├─ OptimizedDawg:  317 ms   (31.5K elem/s)
└─ DynamicDawg:     58.3 ms (171K elem/s) ✅ 5.4× FASTER

Dictionary Size: 32,000 words
├─ OptimizedDawg:  738 ms   (43.3K elem/s)
└─ DynamicDawg:    139 ms   (231K elem/s) ✅ 5.3× FASTER
```

### Memory Usage

```
OptimizedDawg: 8 bytes/node  (compact, arena-based)
DynamicDawg:   13-32 bytes/node (includes ref_count, values, SmallVec)
```

**Verdict**: DynamicDawg uses more memory per node but provides far superior performance and features. The memory overhead is worth it for the 11× construction speedup and full feature support.

## Deprecation Timeline

- **Version 0.6.0**: OptimizedDawg introduced as experimental
- **Version 0.7.0**: OptimizedDawg deprecated after benchmarking analysis
  - All public types marked with `#[deprecated]`
  - Migration guide provided
  - Tests and benchmarks retained for regression coverage
- **Version 1.0.0**: OptimizedDawg remains deprecated
  - Continues to emit deprecation warnings
  - Still available for backward compatibility
- **Version 2.0.0**: OptimizedDawg MAY be removed
  - Decision based on usage metrics
  - Breaking change with migration period

## Rationale for Deprecation

1. **Performance**: 11× slower than DynamicDawg contradicts "optimized" name
2. **Features**: Missing critical functionality (values, zippers, mutability)
3. **Maintenance burden**: Supporting two similar backends is inefficient
4. **User confusion**: Misleading name implies it's the best choice
5. **No unique niche**: DynamicDawg is faster AND more feature-complete

## Why Not Remove Immediately?

1. **Backward compatibility**: Users may have existing code depending on OptimizedDawg
2. **Serialized data**: Existing serialized OptimizedDawg dictionaries need migration path
3. **Graceful transition**: Deprecation warnings provide time to migrate
4. **Test coverage**: Regression tests remain valuable

## Technical Details

### What OptimizedDawg Actually Is

OptimizedDawg is a standard DAWG with:
- **Arena-based edge storage**: Single `Vec<(u8, u32)>` for all edges
- **Compact nodes**: 8 bytes (offset: u32, count: u8, is_final: bool)
- **Hybrid search**: Linear (≤4 edges), binary (>4 edges), optional SIMD
- **Immutable**: Built once via OptimizedDawgBuilder

### What It Is NOT

OptimizedDawg does NOT have:
- BASE/CHECK arrays (Double-Array Trie feature)
- O(1) transitions (still uses edge search)
- XOR-based relocation (DAT optimization)
- Free list management (DAT feature)

### Why Arena Storage Doesn't Help

Arena storage was expected to improve:
- **Cache locality**: ✅ Theoretical benefit
- **Memory fragmentation**: ✅ Reduced allocations

But construction dominates total time:
- Construction: 16.0ms (OptimizedDawg) vs 1.40ms (DynamicDawg)
- Query: ~5-10µs (both backends, negligible)

**Result**: Arena storage optimizes the wrong bottleneck (query, not construction).

## Alternatives

If you need specific OptimizedDawg features:

| Feature | Alternative |
|---------|-------------|
| Arena-based storage | DynamicDawg (better performance despite per-node storage) |
| Compact nodes | DynamicDawg with SmallVec (inline storage for ≤4 edges) |
| SIMD edge search | Could be ported to DynamicDawg (future work) |
| Immutable structure | DynamicDawg + don't call insert/remove |
| Memory efficiency | DoubleArrayTrie (6-8 bytes/char vs 8 bytes/node) |

## Support

For migration assistance:
- **GitHub Issues**: https://github.com/universal-automata/liblevenshtein-rust/issues
- **Documentation**: [DynamicDawg User Guide](../user-guide/backends.md#dynamicdawg)
- **Examples**: See `examples/` directory

## References

- **Initial Analysis**: 2025-11-11 comprehensive benchmarking
- **Benchmark Results**: `benches/corpus_benchmarks.rs`
- **Source Code**: `src/dictionary/dawg_optimized.rs`
- **DynamicDawg Implementation**: `src/dictionary/dynamic_dawg.rs`

---

**Note**: This deprecation is based on empirical evidence from production benchmarks using standard corpora (Norvig's big.txt). If you have a use case where OptimizedDawg outperforms DynamicDawg, please file an issue with benchmark details.
