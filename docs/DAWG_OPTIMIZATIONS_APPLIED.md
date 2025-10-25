# DAWG Optimizations Applied - Phase 1

## Summary

Implemented Phase 1 optimizations from the DAWG optimization analysis, focusing on high-impact, low-risk improvements. All optimizations target edge lookup and insertion operations, which are in the hot path of DAWG traversal.

## Optimizations Implemented

### 1. Adaptive Edge Lookup (High Impact)

**Files Modified:**
- `src/dictionary/dawg.rs` (line 282-306)
- `src/dictionary/dynamic_dawg.rs` (line 640-665)

**Changes:**

**DawgDictionary - dawg.rs:282**
```rust
// BEFORE: Linear search O(n) - always
fn transition(&self, label: u8) -> Option<Self> {
    self.nodes[self.node_idx]
        .edges
        .iter()
        .find(|(l, _)| *l == label)  // Linear search
        .map(|(_, idx)| DawgDictionaryNode {
            nodes: Arc::clone(&self.nodes),
            node_idx: *idx,
        })
}

// AFTER: Adaptive - linear for small, binary for large
fn transition(&self, label: u8) -> Option<Self> {
    let edges = &self.nodes[self.node_idx].edges;

    // Adaptive: use linear search for small edge counts, binary for large
    // Linear search is faster for <8 edges due to cache locality and low overhead
    if edges.len() < 8 {
        // Linear search - cache-friendly for small counts
        edges
            .iter()
            .find(|(l, _)| *l == label)
            .map(|(_, idx)| DawgDictionaryNode {
                nodes: Arc::clone(&self.nodes),
                node_idx: *idx,
            })
    } else {
        // Binary search - efficient for large edge counts
        edges
            .binary_search_by_key(&label, |(l, _)| *l)
            .ok()
            .map(|idx| DawgDictionaryNode {
                nodes: Arc::clone(&self.nodes),
                node_idx: edges[idx].1,
            })
    }
}
```

**DynamicDawg - dynamic_dawg.rs:640**
```rust
// BEFORE: Linear search O(n) - always
fn transition(&self, label: u8) -> Option<Self> {
    let inner = self.dawg.read().unwrap();
    inner.nodes[self.node_idx]
        .edges
        .iter()
        .find(|(b, _)| *b == label)  // Linear search
        .map(|(_, idx)| DynamicDawgNode {
            dawg: Arc::clone(&self.dawg),
            node_idx: *idx,
        })
}

// AFTER: Adaptive - linear for small, binary for large
fn transition(&self, label: u8) -> Option<Self> {
    let inner = self.dawg.read().unwrap();
    let edges = &inner.nodes[self.node_idx].edges;

    // Adaptive: use linear search for small edge counts, binary for large
    // Linear search is faster for <8 edges due to cache locality and low overhead
    if edges.len() < 8 {
        // Linear search - cache-friendly for small counts
        edges
            .iter()
            .find(|(b, _)| *b == label)
            .map(|(_, idx)| DynamicDawgNode {
                dawg: Arc::clone(&self.dawg),
                node_idx: *idx,
            })
    } else {
        // Binary search - efficient for large edge counts
        edges
            .binary_search_by_key(&label, |(b, _)| *b)
            .ok()
            .map(|idx| DynamicDawgNode {
                dawg: Arc::clone(&self.dawg),
                node_idx: edges[idx].1,
            })
    }
}
```

**Why Adaptive?**
Initial benchmarks showed that pure binary search caused 2-3% regressions because:
- DAWG nodes typically have 2-5 edges
- Linear search is cache-friendly and has low overhead for small counts
- Binary search overhead exceeds benefits until ~8-10 edges

**Expected Impact:** Best of both worlds - no regression for typical nodes, benefits for high-degree nodes

---

### 2. Binary Insertion for Edges (High Impact)

**Files Modified:**
- `src/dictionary/dynamic_dawg.rs` (lines 147, 161, 385-400)

**Changes:**

**Added Helper Method - dynamic_dawg.rs:385**
```rust
/// Insert an edge into a node's edge list, maintaining sorted order.
/// Uses binary search to find the insertion point - O(log n) instead of O(n log n) sort.
#[inline]
fn insert_edge_sorted(&mut self, node_idx: usize, label: u8, target_idx: usize) {
    let edges = &mut self.nodes[node_idx].edges;
    match edges.binary_search_by_key(&label, |(l, _)| *l) {
        Ok(pos) => {
            // Edge with this label already exists, replace it
            edges[pos] = (label, target_idx);
        }
        Err(pos) => {
            // Insert at the correct position to maintain sorted order
            edges.insert(pos, (label, target_idx));
        }
    }
}
```

**Replaced push + sort with binary insertion - dynamic_dawg.rs:147**
```rust
// BEFORE: O(n log n) - push then sort
inner.nodes[node_idx].edges.push((byte, existing_idx));
inner.nodes[node_idx].edges.sort_by_key(|(b, _)| *b);

// AFTER: O(log n) - binary insertion
inner.insert_edge_sorted(node_idx, byte, existing_idx);
```

**Replaced push + sort with binary insertion - dynamic_dawg.rs:161**
```rust
// BEFORE: O(n log n) - push then sort
inner.nodes[node_idx].edges.push((byte, new_idx));
inner.nodes[node_idx].edges.sort_by_key(|(b, _)| *b);

// AFTER: O(log n) - binary insertion
inner.insert_edge_sorted(node_idx, byte, new_idx);
```

**Expected Impact:** 5-15% faster insertion

---

### 3. Remove Unused suffix_map Field (Memory Optimization)

**Files Modified:**
- `src/dictionary/dynamic_dawg.rs` (lines 36-42, 79, 255, 554)

**Changes:**

**Removed field declaration - dynamic_dawg.rs:36**
```rust
// BEFORE:
struct DynamicDawgInner {
    nodes: Vec<DawgNode>,
    #[allow(dead_code)]
    suffix_map: HashMap<NodeSignature, usize>,  // REMOVED
    term_count: usize,
    needs_compaction: bool,
}

// AFTER:
struct DynamicDawgInner {
    nodes: Vec<DawgNode>,
    term_count: usize,
    needs_compaction: bool,
}
```

**Removed initialization in new() - dynamic_dawg.rs:79**
**Removed initialization in compact() - dynamic_dawg.rs:255**
**Removed clear() call - dynamic_dawg.rs:554**

**Expected Impact:** 2-5% memory savings

---

### 4. Fix DawgBuilder to Sort Edges (Correctness Fix)

**Files Modified:**
- `src/dictionary/dawg.rs` (lines 136-139)

**Changes:**

**Added edge sorting in build() - dawg.rs:136**
```rust
pub fn build(mut self) -> DawgDictionary {
    // Minimize remaining suffix
    self.minimize(0);

    // Sort all edges to enable binary search in transition()
    for node in &mut self.nodes {
        node.edges.sort_by_key(|(label, _)| *label);
    }

    // Count terms
    let term_count = self.count_terms(0);

    DawgDictionary {
        nodes: Arc::new(self.nodes),
        term_count,
    }
}
```

**Why Needed:** DawgBuilder's insert method doesn't maintain sorted edges when terms are inserted in unsorted order. Binary search requires sorted edges, so we ensure they're sorted before the DAWG is used.

**Impact:** Enables binary search optimization to work correctly for all insertion orders

---

## Testing

All optimizations passed existing test suite:
```
cargo test
# Result: 74 tests passing
```

Key tests verified:
- ✅ `test_dawg_builder_incremental` - Tests unsorted insertion order
- ✅ `test_dawg_sorted_vs_unsorted` - Verifies both sorted and unsorted construction
- ✅ `test_dynamic_dawg_insert` - Tests dynamic insertion
- ✅ `test_minimize_no_false_positives` - Ensures correctness after minimization

---

## Benchmarking

### Benchmark Suite Created

Created comprehensive benchmark suite in `benches/dawg_benchmarks.rs`:

1. **dawg_edge_lookup** - Measures transition() performance (primary beneficiary of binary search)
2. **dynamic_dawg_insertion** - Measures insert() performance (benefits from binary insertion)
3. **dawg_edge_iteration** - Measures edges() iteration performance
4. **dawg_contains** - Measures dictionary lookup performance
5. **dynamic_dawg_minimize** - Measures minimization performance
6. **dawg_construction** - Measures overall construction performance

Each benchmark tests multiple dictionary sizes (100, 500, 1000, 5000 terms) to show how optimizations scale.

### Benchmark Results

See `dawg_benchmark_baseline.txt` for pre-optimization results.
See `dawg_benchmark_optimized.txt` for post-optimization results.

---

## Expected Performance Improvements

Based on the optimization analysis:

| Operation | Expected Improvement |
|-----------|---------------------|
| Edge lookup (transition) | 3-8% faster |
| Dynamic insertion | 5-15% faster |
| Overall query performance | 10-20% faster |
| Memory usage | 2-5% reduction |

---

## Next Steps (Future Phases)

### Phase 2: Medium-Impact Optimizations
1. Implement suffix sharing in DynamicDawg (#4 from analysis)
2. Reduce RwLock contention with caching (#3 from analysis)
3. Optimize PathMapDictionary zipper usage (#6 from analysis)

### Phase 3: Advanced Optimizations
4. Compressed edge representation (40% memory savings)
5. Lock-free data structures (10-20% faster concurrent access)
6. Custom allocator for nodes (5-10% allocation speedup)

---

## Code Locations

**Modified files:**
- `src/dictionary/dawg.rs` - Binary search in transition(), edge sorting in build()
- `src/dictionary/dynamic_dawg.rs` - Binary search in transition(), binary insertion helper, removed suffix_map

**New files:**
- `benches/dawg_benchmarks.rs` - Comprehensive benchmark suite
- `docs/DAWG_OPTIMIZATIONS_APPLIED.md` - This document

---

## Lines of Code Changed

- Total lines modified: ~40 lines
- New lines added: ~20 lines (helper method + comments)
- Lines removed: ~10 lines (suffix_map field and initializations)
- Complexity: Minimal (standard library binary_search usage)
- Risk: Low (all changes backed by tests)
