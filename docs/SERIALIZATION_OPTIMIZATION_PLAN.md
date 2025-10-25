# Serialization Optimization Plan

## Identified Optimization Opportunities

### 1. String Allocation in `extract_terms()` (Line 151)

**Current Code:**
```rust
if let Ok(term) = String::from_utf8(current_term.clone()) {
    terms.push(term);
}
```

**Issue:** Clones the `current_term` Vec<u8> for every final node, causing unnecessary allocations.

**Optimization:**
```rust
// Pre-allocate a String buffer and reuse it
let mut term_buffer = String::new();
if let Ok(term_str) = std::str::from_utf8(current_term) {
    term_buffer.clear();
    term_buffer.push_str(term_str);
    terms.push(term_buffer.clone());
}
```

**Expected Impact:** Reduce allocations by ~50% for dictionaries with many terms.

---

### 2. Vector Pre-Allocation

**Current Code:**
```rust
let mut node_ids = Vec::new();
let mut final_node_ids = Vec::new();
let mut edges = Vec::new();
```

**Issue:** Vectors grow dynamically, causing multiple reallocations during DFS traversal.

**Optimization:**
```rust
// Estimate capacity based on dictionary size
let est_size = dict.len().unwrap_or(100);
let mut node_ids = Vec::with_capacity(est_size * 2); // Estimate nodes
let mut final_node_ids = Vec::with_capacity(est_size);
let mut edges = Vec::with_capacity(est_size * 3); // Estimate edges
```

**Expected Impact:** Reduce reallocation overhead by 60-80%.

---

### 3. HashMap Pre-Sizing in Deserialization (Line 347)

**Current Code:**
```rust
let mut adjacency: HashMap<u64, Vec<(u8, u64)>> = HashMap::new();
for edge in &proto_dict.edge {
    adjacency.entry(edge.source_id)
        .or_insert_with(Vec::new)
        .push((edge.label as u8, edge.target_id));
}
```

**Issue:** HashMap grows dynamically, causing rehashing.

**Optimization:**
```rust
// Pre-size based on node count
let est_nodes = proto_dict.node_id.len();
let mut adjacency: HashMap<u64, Vec<(u8, u64)>> = HashMap::with_capacity(est_nodes);
```

**Expected Impact:** Reduce deserialization time by 10-15%.

---

### 4. Reduce Edge Struct Allocations

**Current Code:**
```rust
edges.push(proto::dictionary::Edge {
    source_id: node_id,
    label: label as u32,
    target_id: child_id,
});
```

**Issue:** Creates a new struct for each edge (already optimized in V2 with packed format).

**Status:** Already optimized in OptimizedProtobufSerializer using flat array.

---

### 5. Use `SmallVec` for `current_term` in DFS

**Current Code:**
```rust
let mut current_term = Vec::new();
```

**Issue:** Most terms are short (<= 16 bytes), but we heap-allocate every time.

**Optimization:**
```rust
use smallvec::{SmallVec, smallvec};
let mut current_term: SmallVec<[u8; 16]> = smallvec![];
```

**Expected Impact:** Reduce heap allocations for short terms by 100%.

---

### 6. Batch String Conversions

**Current Code:** Converts bytes to String one at a time during DFS.

**Optimization:** Collect all byte vectors, then batch convert to strings.

```rust
// Collect byte vectors first
let mut term_bytes: Vec<Vec<u8>> = Vec::new();
// ... DFS collects byte vectors ...

// Batch convert to strings
let terms: Vec<String> = term_bytes.into_iter()
    .filter_map(|bytes| String::from_utf8(bytes).ok())
    .collect();
```

**Expected Impact:** Better cache locality, reduce allocation overhead by 20%.

---

## Optimization Priority

1. **High Impact, Easy:**
   - Vector pre-allocation (#2)
   - HashMap pre-sizing (#3)

2. **Medium Impact, Easy:**
   - String allocation optimization (#1)
   - SmallVec for current_term (#5)

3. **Lower Impact, Medium Complexity:**
   - Batch string conversions (#6)

## Implementation Plan

### Phase 1: Low-Hanging Fruit
1. Add capacity hints to all Vec::new() calls
2. Pre-size HashMap with known capacity
3. Benchmark impact

### Phase 2: Memory Optimizations
1. Replace Vec<u8> with SmallVec for current_term
2. Optimize string conversions
3. Benchmark impact

### Phase 3: Advanced Optimizations (if needed)
1. Consider using arena allocators for temporary data
2. Explore zero-copy deserialization with prost
3. Profile and identify remaining bottlenecks

## Success Metrics

- **Serialization:** 20-30% improvement
- **Deserialization:** 30-40% improvement
- **Memory usage:** 15-25% reduction during serialization

## Benchmarking

Run benchmarks before and after each phase:
```bash
cargo bench --bench serialization_benchmarks --features protobuf
```

Compare results using criterion's built-in comparison tools.
