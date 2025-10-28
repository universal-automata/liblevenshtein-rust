# Double-Array Trie Performance Analysis

## Executive Summary

Performance profiling has identified a **critical bottleneck** in the DAT `edges()` implementation that severely impacts Levenshtein automaton composition performance.

**Key Finding**: The current `edges()` implementation causes **7-36% performance regression** in distance matching operations.

## Benchmark Results

### Layer 1: DAT as Dictionary (baseline performance)

| Operation | Time | Status |
|-----------|------|--------|
| **Construction** (10k words) | 2.99 ms | ✅ Good (7% improvement) |
| **Exact matching** | 6.59 µs | ✅ Excellent |
| **Contains operation** | 232 ns | ✅ Excellent (30x faster than DAWG) |
| **Memory construction** | 2.63 ms | ✅ Good (7% improvement) |

### Layer 2: Levenshtein Automaton + DAT (BOTTLENECK IDENTIFIED)

| Operation | Time | Status | Change |
|-----------|------|--------|--------|
| **Distance 1 matching** | 13.86 µs | ⚠️ **Regressed** | +7.1% slower |
| **Distance 2 matching** | 22.40 µs | ❌ **Regressed** | +35.4% slower |

**Root Cause**: Inefficient `edges()` implementation in DAT node traversal.

## Critical Bottleneck: `edges()` Implementation

### Current Implementation (src/dictionary/double_array_trie.rs:384-419)

```rust
fn edges(&self) -> Box<dyn Iterator<Item = (u8, Self)> + '_> {
    let state = self.state;
    let base = if state < self.base.len() {
        self.base[state]
    } else {
        -1
    };

    if base < 0 {
        return Box::new(std::iter::empty());
    }

    // ❌ BOTTLENECK: Iterates through ALL 256 possible bytes
    let edges: Vec<(u8, Self)> = (0u8..=255)
        .filter_map(|byte| {
            let next = (base as usize).wrapping_add(byte as usize);

            if next < self.check.len() && self.check[next] == state as i32 {
                // ❌ BOTTLENECK: 3 Arc clones per valid edge
                Some((
                    byte,
                    DoubleArrayTrieNode {
                        state: next,
                        base: Arc::clone(&self.base),
                        check: Arc::clone(&self.check),
                        is_final: Arc::clone(&self.is_final),
                    },
                ))
            } else {
                None
            }
        })
        .collect(); // ❌ BOTTLENECK: Collects into Vec

    Box::new(edges.into_iter())
}
```

### Performance Issues

1. **Exhaustive Byte Iteration**: Checks ALL 256 possible byte values
   - Most nodes have 1-5 edges
   - 95-98% of checks are wasted
   - Cache misses from scattered memory access

2. **Excessive Arc Cloning**: 3 Arc clones × number of edges
   - Arc clone = atomic reference count increment
   - Not free even though no actual allocation
   - Multiplied by every Levenshtein state transition

3. **Unnecessary Vec Collection**: Pre-collects all edges
   - Allocation overhead
   - Prevents lazy evaluation
   - Cache pollution

4. **Called Frequently**: Levenshtein automaton composition
   - Called for EVERY state in the Levenshtein automaton
   - Distance 2 can have hundreds of states
   - Each state calls `edges()` multiple times during traversal

### Why This Matters for Levenshtein Matching

The Levenshtein automaton works by composing with the dictionary:

```
For each Levenshtein state:
    For each dictionary edge:  ← edges() called here
        Compute next Levenshtein state
        Recurse
```

**Impact Calculation** (distance 2, query "test"):
- ~200 Levenshtein states visited
- Each calls `edges()` on current dictionary node
- Average 3 edges per node
- Total: 200 × 256 checks = 51,200 byte checks
- Total: 200 × 3 × 3 Arc clones = 1,800 atomic operations

## Proposed Optimizations

### Option 1: Store Edge List (Trade Space for Speed)

Store actual edges during construction:

```rust
struct DoubleArrayTrieNode {
    state: usize,
    edges: Arc<Vec<u8>>,  // NEW: Actual edges for this state
    base: Arc<Vec<i32>>,
    check: Arc<Vec<i32>>,
    is_final: Arc<Vec<bool>>,
}

fn edges(&self) -> Box<dyn Iterator<Item = (u8, Self)> + '_> {
    let base = self.base[self.state];

    Box::new(self.edges[self.state].iter().map(move |&byte| {
        let next = (base as usize) + (byte as usize);
        (byte, DoubleArrayTrieNode {
            state: next,
            edges: Arc::clone(&self.edges),
            base: Arc::clone(&self.base),
            check: Arc::clone(&self.check),
            is_final: Arc::clone(&self.is_final),
        })
    }))
}
```

**Pros**:
- Only iterate over actual edges (3-5 vs 256)
- ~50x fewer checks
- Much better cache locality

**Cons**:
- ~10-20% memory overhead (store edge lists)
- Construction slightly slower

**Expected Improvement**: 30-50% faster Levenshtein matching

### Option 2: Lazy Iterator (Zero Copy)

Return an iterator that checks on-demand:

```rust
struct DATEdgeIterator {
    byte: u8,
    base: Arc<Vec<i32>>,
    check: Arc<Vec<i32>>,
    is_final: Arc<Vec<bool>>,
    state: usize,
    base_value: i32,
}

impl Iterator for DATEdgeIterator {
    type Item = (u8, DoubleArrayTrieNode);

    fn next(&mut self) -> Option<Self::Item> {
        while self.byte < 255 {
            let byte = self.byte;
            self.byte += 1;

            let next = (self.base_value as usize) + (byte as usize);
            if next < self.check.len() && self.check[next] == self.state as i32 {
                return Some((byte, DoubleArrayTrieNode { ... }));
            }
        }
        None
    }
}
```

**Pros**:
- No Vec allocation
- True lazy evaluation
- No upfront edge collection

**Cons**:
- Still checks all 256 bytes (less efficiently)
- Still has Arc clone per edge

**Expected Improvement**: 10-20% faster

### Option 3: Shared Arc References (Reduce Cloning)

Share Arc references across all nodes from same DAT:

```rust
#[derive(Clone)]
struct DATSharedData {
    base: Arc<Vec<i32>>,
    check: Arc<Vec<i32>>,
    is_final: Arc<Vec<bool>>,
    edges: Arc<Vec<Vec<u8>>>,  // Edge lists per state
}

struct DoubleArrayTrieNode {
    state: usize,
    shared: DATSharedData,  // Single clone for all 3-4 Arcs
}
```

**Pros**:
- Single Arc structure clone vs 3 separate clones
- Better data locality
- Can combine with Option 1

**Cons**:
- Slightly more complex structure

**Expected Improvement**: 15-25% faster

### Recommended Approach: Option 1 + Option 3

Combine edge list storage with shared Arc structure:

1. Store edge lists during construction (~10% memory overhead)
2. Use shared Arc structure (single clone)
3. Lazy iterator over edge list only

**Expected Total Improvement**: 40-60% faster Levenshtein matching

## Implementation Priority

### High Priority (Immediate)
1. **Option 1**: Store edge lists
   - Biggest performance impact
   - Straightforward implementation
   - Acceptable memory tradeoff

### Medium Priority (Follow-up)
2. **Option 3**: Shared Arc references
   - Incremental improvement
   - Clean architecture
   - Combines well with Option 1

### Low Priority (Future)
3. Further optimizations:
   - SIMD for byte checking
   - Bloom filter for quick edge rejection
   - Adaptive strategy (switch methods based on edge count)

## Testing Strategy

### Benchmark Suite

```bash
# Before optimization
cargo bench --bench dat_levenshtein_profiling

# After optimization
cargo bench --bench dat_levenshtein_profiling

# Compare
cargo bench --bench backend_comparison -- DoubleArrayTrie
```

### Expected Results

| Metric | Before | After | Improvement |
|--------|--------|-------|-------------|
| Distance 1 | 13.86 µs | ~9-10 µs | **30-40%** |
| Distance 2 | 22.40 µs | ~14-16 µs | **30-40%** |
| Edge iteration | 256 checks | 3-5 checks | **50x** |
| Arc clones/edge | 3 | 1 | **3x** |

## Conclusion

The DAT has **excellent baseline performance** as a dictionary (6.59 µs exact matching, 232 ns contains).

However, the `edges()` implementation creates a **severe bottleneck** for Levenshtein automaton composition, causing 7-36% performance regression.

**Recommended Action**: Implement Option 1 (edge list storage) immediately. This is the critical path for the project's core value proposition: fast approximate string matching with Levenshtein automata.

---

**Analysis Date**: 2025-10-28
**Profiling Tools**: cargo bench, flamegraph
**Test Dataset**: 10,000 words from /usr/share/dict/words
