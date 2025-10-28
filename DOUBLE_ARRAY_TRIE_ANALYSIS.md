# Double-Array Trie Analysis for liblevenshtein-rust

## Executive Summary

**Recommendation**: **YES, with caveats** - A double-array trie backend would be beneficial for specific use cases, but should be added as an additional option rather than replacing existing backends.

**Best fit for**: Static, large dictionaries where memory efficiency and cache locality are critical (e.g., spell checkers, NLP applications with 100k+ terms).

## What is a Double-Array Trie?

A double-array trie (DAT) is a space-efficient trie implementation using two parallel arrays:
- `BASE[]`: Stores base indices for transitions
- `CHECK[]`: Validates transitions belong to correct parent

**Key Properties:**
- O(1) transition time (array lookup)
- Excellent cache locality (sequential memory access)
- Space-efficient: typically 4-8 bytes per character
- Static: difficult to modify after construction
- Fast lookups: minimal pointer chasing

## Comparison with Existing Backends

### Current Backends

| Backend | Construction | Memory | Query Speed | Dynamic | Best Use Case |
|---------|--------------|--------|-------------|---------|---------------|
| **PathMap** | Fast (1.43ms) | High | Very Fast (683ns) | No | In-memory, speed-critical |
| **DAWG** | Medium | Low | Fast | No | Static dictionaries |
| **DynamicDAWG** | Medium | Low | Fast | Yes | Evolving dictionaries |
| **SuffixAutomaton** | Slow (6.18ms) | Medium | Medium (27µs @ d=1) | Yes | Substring matching |

### Double-Array Trie (Projected)

| Metric | Expected Performance | Notes |
|--------|---------------------|-------|
| Construction | **Slow** (5-15ms for 5k words) | Requires solving placement problem |
| Memory | **Very Low** (4-8 bytes/char) | Most space-efficient |
| Query Speed | **Very Fast** (400-600ns @ d=0) | Excellent cache locality |
| Dynamic | **No** (or very slow) | Static structure |
| Best Use | Large static dictionaries | 100k+ terms, memory-constrained |

## Performance Analysis

### Memory Comparison (5000-word dictionary, avg 8 chars/word)

| Backend | Estimated Memory | Bytes/Word |
|---------|-----------------|------------|
| PathMap | ~640 KB | 128 |
| DAWG | ~160 KB | 32 |
| DynamicDAWG | ~200 KB | 40 |
| **DoubleArray** | **~160 KB** | **32** |
| SuffixAutomaton | ~320 KB | 64 |

**Analysis**: DAT would match DAWG in space efficiency while potentially offering better query performance.

### Query Speed Projection

Based on literature and similar implementations:

| Distance | PathMap | DAWG (est) | **DoubleArray (proj)** | Improvement |
|----------|---------|------------|----------------------|-------------|
| 0 | 712 ns | ~800 ns | **500-600 ns** | 15-30% faster |
| 1 | 8.7 µs | ~9.5 µs | **8.0-8.5 µs** | 5-15% faster |
| 2 | 83.9 µs | ~90 µs | **80-85 µs** | 5-10% faster |

**Key advantage**: Cache-friendly memory layout benefits Levenshtein automaton traversal.

## Implementation Considerations

### 1. Construction Algorithm

**Challenge**: Finding optimal BASE values to minimize collisions

**Options:**

a) **Simple Incremental** (easiest, slower):
```rust
fn find_base(node: &Node, check: &[i32]) -> usize {
    let mut base = 1;
    loop {
        if all_children_fit(node, base, check) {
            return base;
        }
        base += 1;
    }
}
```
- Time: O(n²) worst case
- Easy to implement
- Works well for small dictionaries

b) **Dynamic Programming** (optimal, complex):
- Minimize total array size
- Time: O(n² log n)
- Best space utilization
- Complex implementation

c) **Heuristic-based** (good balance):
```rust
fn find_base_heuristic(node: &Node, check: &[i32]) -> usize {
    // Try common patterns first: ASCII range, vowels/consonants clusters
    // Fall back to incremental search
}
```
- Time: O(n log n) typical
- Good space utilization (within 10-20% of optimal)
- Moderate complexity

**Recommendation**: Start with heuristic-based approach.

### 2. Memory Layout

```rust
pub struct DoubleArrayTrie {
    /// BASE array: stores transition base indices
    /// BASE[s] + c gives the index for transition on character c
    base: Vec<i32>,

    /// CHECK array: validates transitions
    /// CHECK[BASE[s] + c] must equal s for valid transition
    check: Vec<i32>,

    /// Final states: bitmap or separate array
    /// Marks dictionary word boundaries
    is_final: BitVec,

    /// Metadata
    num_terms: usize,
}
```

### 3. Dictionary Trait Implementation

```rust
impl Dictionary for DoubleArrayTrie {
    type Node = usize; // Just an index into the arrays

    fn root(&self) -> Self::Node {
        0 // Root is always at index 0
    }

    fn is_final(&self, node: &Self::Node) -> bool {
        self.is_final[*node]
    }

    fn edges<'a>(&'a self, node: &Self::Node) -> Box<dyn Iterator<Item = (u8, Self::Node)> + 'a> {
        // Iterate through possible transitions from this node
        Box::new((0..=255u8).filter_map(move |c| {
            let next = self.base[*node] + c as i32;
            if next >= 0 && (next as usize) < self.check.len() && self.check[next as usize] == *node as i32 {
                Some((c, next as usize))
            } else {
                None
            }
        }))
    }
}
```

**Issue**: The `edges()` implementation iterates all 256 possible bytes, which is inefficient.

**Solution**: Add auxiliary structure to track which edges actually exist:
```rust
pub struct DoubleArrayTrie {
    base: Vec<i32>,
    check: Vec<i32>,
    is_final: BitVec,
    // NEW: Store actual edges for efficient iteration
    edge_lists: Vec<SmallVec<[u8; 4]>>, // Most nodes have few edges
}
```

### 4. Construction Implementation

```rust
impl DoubleArrayTrie {
    pub fn from_terms<I, S>(terms: I) -> Self
    where
        I: IntoIterator<Item = S>,
        S: AsRef<str>,
    {
        // 1. Build sorted term list
        let mut sorted_terms: Vec<String> = terms
            .into_iter()
            .map(|s| s.as_ref().to_string())
            .collect();
        sorted_terms.sort();
        sorted_terms.dedup();

        // 2. Build trie structure first (temporary)
        let trie = build_trie(&sorted_terms);

        // 3. Convert to double-array representation
        let (base, check, is_final, edge_lists) = convert_to_double_array(&trie);

        Self {
            base,
            check,
            is_final,
            edge_lists,
            num_terms: sorted_terms.len(),
        }
    }
}
```

## Benchmarks Comparison (Projected)

### Construction Time (5000 words)

| Backend | Current | DAT (Projected) |
|---------|---------|-----------------|
| PathMap | 1.43 ms | - |
| DAWG | ~2.0 ms | - |
| **DoubleArray** | - | **3-8 ms** |

**Analysis**: DAT construction would be slower than PathMap but comparable to DAWG.

### Query Performance (distance=1)

| Backend | Current | DAT (Projected) |
|---------|---------|-----------------|
| PathMap | 30.0 µs | - |
| **DoubleArray** | - | **27-29 µs** |

**Analysis**: DAT should be competitive with or slightly faster than PathMap due to cache locality.

## When to Use Each Backend

### PathMap
- ✅ **Best for**: Small to medium dictionaries (< 10k terms)
- ✅ **Best for**: When construction time matters
- ✅ **Best for**: Maximum query speed regardless of memory
- ❌ **Avoid**: Large dictionaries (> 50k terms) with memory constraints

### DAWG
- ✅ **Best for**: Static, space-efficient storage
- ✅ **Best for**: Medium to large dictionaries
- ✅ **Best for**: Serialization and persistence
- ❌ **Avoid**: When you need modifications

### DynamicDAWG
- ✅ **Best for**: Evolving dictionaries
- ✅ **Best for**: Applications with frequent updates
- ✅ **Best for**: User dictionaries, learning systems
- ❌ **Avoid**: Static dictionaries (overhead for dynamism)

### SuffixAutomaton
- ✅ **Best for**: Substring matching
- ✅ **Best for**: Code search, document search
- ✅ **Best for**: Pattern matching within text
- ❌ **Avoid**: Standard word matching (overkill)

### DoubleArrayTrie (Proposed)
- ✅ **Best for**: Large static dictionaries (100k+ terms)
- ✅ **Best for**: Memory-constrained environments
- ✅ **Best for**: Cache-sensitive applications
- ✅ **Best for**: Embedded systems, mobile devices
- ✅ **Best for**: NLP, spell checking at scale
- ❌ **Avoid**: Small dictionaries (< 10k terms) - overhead not worth it
- ❌ **Avoid**: Dynamic dictionaries - reconstruction is expensive

## Implementation Roadmap

### Phase 1: Basic Implementation (2-3 days)
1. Define `DoubleArrayTrie` struct
2. Implement construction with simple incremental algorithm
3. Implement `Dictionary` trait
4. Add basic tests

### Phase 2: Optimization (1-2 days)
1. Implement heuristic-based construction
2. Add edge list auxiliary structure
3. Optimize memory layout (consider alignment, padding)
4. Add compression for sparse regions

### Phase 3: Integration (1 day)
1. Add to `DictionaryBackend` enum
2. Update `DictionaryFactory`
3. Add benchmarks
4. Update CLI to support DAT backend

### Phase 4: Serialization (1 day)
1. Implement efficient serialization
2. Memory-mapped file support (zero-copy loading)
3. Add to serialization benchmarks

## Code Size Estimate

```
src/dictionary/double_array_trie.rs:  ~800-1000 lines
  - Struct definition: ~50 lines
  - Construction algorithm: ~300 lines
  - Dictionary trait impl: ~200 lines
  - Helper functions: ~200 lines
  - Tests: ~200 lines
  - Documentation: ~50 lines

Total new code: ~800-1000 lines
Impact on compile time: +5-10 seconds
Binary size increase: ~50-80 KB
```

## Existing Rust Implementations

### 1. `yada` crate
- Mature implementation
- Good performance
- MIT licensed
- Could be used as reference or dependency

### 2. `darts` crate
- Port of C++ DARTS library
- Widely tested
- Less idiomatic Rust

### 3. Build from scratch
- Full control
- Optimized for this use case
- Learning opportunity
- More work

**Recommendation**: Build from scratch, using `yada` as reference for algorithms.

## Pros and Cons

### Pros
1. **Excellent cache locality** - sequential memory access pattern
2. **Space-efficient** - comparable to DAWG (4-8 bytes/char)
3. **Fast lookups** - O(1) transition time, minimal pointer chasing
4. **Predictable performance** - no hash collisions, no tree rebalancing
5. **Memory-mapped friendly** - can be loaded with zero-copy
6. **Scales well** - performance doesn't degrade with dictionary size
7. **Industry proven** - used in Japanese morphological analyzers (MeCab, Kuromoji)

### Cons
1. **Construction complexity** - finding optimal BASE values is non-trivial
2. **Construction time** - slower than PathMap, similar to DAWG
3. **Static structure** - difficult to modify (requires reconstruction)
4. **Implementation effort** - ~1000 lines of new code
5. **Maintenance burden** - another backend to maintain and test
6. **Marginal improvement** - only 10-30% faster than PathMap in best case
7. **Edge iteration overhead** - requires auxiliary structure for efficient iteration

## Recommendation: YES, with Conditions

### When to Implement

**High Priority IF:**
- You have users with large dictionaries (100k+ terms)
- Memory efficiency is a primary concern
- You're targeting embedded/mobile platforms
- You need memory-mapped dictionary loading

**Low Priority IF:**
- Current backends meet all use cases
- Development resources are limited
- No user demand for this feature

### Implementation Strategy

1. **Start with prototype** - 2-3 days to implement basic version
2. **Benchmark against existing** - verify projected performance gains
3. **If promising** - complete implementation with optimizations
4. **If not worth it** - document findings and defer

### Alternative: Optimize Existing DAWG

Instead of adding DAT, consider:
1. Optimize DAWG memory layout for better cache locality
2. Add memory-mapped loading to DAWG
3. Implement better edge iteration for DAWG

This might achieve 80% of the benefit with 20% of the effort.

## Conclusion

A double-array trie backend **would be beneficial** for liblevenshtein-rust, particularly for:
- Large-scale NLP applications
- Memory-constrained environments
- Applications requiring fast startup (memory-mapped dictionaries)

However, the benefit is **incremental** (10-30% improvement) rather than transformational. The decision should be based on:

1. **User demand** - are users hitting memory/performance limits with current backends?
2. **Resource availability** - is there time to implement and maintain another backend?
3. **Strategic fit** - does this align with the library's roadmap?

**Recommended approach**: Implement as an **experimental** backend, gather user feedback, and promote to stable if widely adopted.

## References

1. Aoe, J. (1989). "An Efficient Digital Search Algorithm by Using a Double-Array Structure". IEEE Transactions on Software Engineering.
2. Yata, S. (2007). "A Fast String Search Engine Based on Double-Array Structures" (Darts).
3. MeCab - Japanese morphological analyzer using double-array tries
4. `yada` crate: https://docs.rs/yada/

## Next Steps if Proceeding

1. Create `src/dictionary/double_array_trie.rs` skeleton
2. Implement basic construction algorithm
3. Add to benchmarks
4. Compare performance with existing backends
5. Decide: continue or defer based on results
