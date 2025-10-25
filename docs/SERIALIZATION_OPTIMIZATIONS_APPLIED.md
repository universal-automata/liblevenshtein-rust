# Serialization Optimizations Applied - Phase 1

## Summary

Implemented Phase 1 optimizations focusing on vector and HashMap pre-allocation to reduce reallocation overhead during serialization and deserialization.

## Changes Made

### 1. Optimized `extract_terms()` Function

**Location:** `src/serialization/mod.rs:140`

**Changes:**
- Pre-allocate `terms` vector with dictionary size estimate
- Pre-allocate `current_term` buffer with 32-byte capacity

**Code:**
```rust
let est_size = dict.len().unwrap_or(100);
let mut terms = Vec::with_capacity(est_size);
let mut current_term = Vec::with_capacity(32); // Most words < 32 bytes
```

**Expected Impact:** Reduce allocation overhead by 40-50% for term extraction.

---

### 2. Optimized Protobuf V1 Serialization (`extract_graph`)

**Location:** `src/serialization/mod.rs:258`

**Changes:**
- Pre-allocate `node_ids` vector (2x dictionary size estimate)
- Pre-allocate `final_node_ids` vector (dictionary size estimate)
- Pre-allocate `edges` vector (3x dictionary size estimate)

**Code:**
```rust
let est_size = dict.len().unwrap_or(100);
let mut node_ids = Vec::with_capacity(est_size * 2);
let mut final_node_ids = Vec::with_capacity(est_size);
let mut edges = Vec::with_capacity(est_size * 3);
```

**Expected Impact:** Eliminate 60-80% of vector reallocations during graph extraction.

---

### 3. Optimized Protobuf V1 Deserialization

**Location:** `src/serialization/mod.rs:351`

**Changes:**
- Pre-size HashMap with node count
- Pre-allocate HashSet for final nodes
- Pre-allocate terms and current_term vectors

**Code:**
```rust
let est_nodes = proto_dict.node_id.len();
let mut adjacency: HashMap<u64, Vec<(u8, u64)>> = HashMap::with_capacity(est_nodes);

let mut final_set: std::collections::HashSet<u64> =
    std::collections::HashSet::with_capacity(proto_dict.final_node_id.len());
final_set.extend(proto_dict.final_node_id.iter().copied());

let est_terms = proto_dict.final_node_id.len();
let mut terms = Vec::with_capacity(est_terms);
let mut current_term = Vec::with_capacity(32);
```

**Expected Impact:** Reduce hash map rehashing overhead by 70-80%, reduce allocation overhead by 40%.

---

### 4. Optimized Protobuf V2 Serialization (`extract_graph_v2`)

**Location:** `src/serialization/mod.rs:428`

**Changes:**
- Pre-allocate `final_node_ids` vector
- Pre-allocate `edge_data` vector (9x dictionary size estimate for packed format)

**Code:**
```rust
let est_size = dict.len().unwrap_or(100);
let mut final_node_ids = Vec::with_capacity(est_size);
let mut edge_data = Vec::with_capacity(est_size * 9); // 3 values/edge, ~3 edges/term
```

**Expected Impact:** Eliminate 60-80% of vector reallocations.

---

### 5. Optimized Protobuf V2 Deserialization

**Location:** `src/serialization/mod.rs:537`

**Changes:**
- Pre-allocate `final_node_ids` with delta count
- Estimate node count from edge count and pre-size HashMap
- Pre-allocate HashSet and vectors

**Code:**
```rust
let mut final_node_ids = Vec::with_capacity(proto_dict.final_node_delta.len());

let num_edges = proto_dict.edge_data.len() / 3;
let est_nodes = (num_edges as f64 * 0.6) as usize; // Estimate from edges
let mut adjacency: HashMap<u64, Vec<(u8, u64)>> = HashMap::with_capacity(est_nodes);

let mut final_set: std::collections::HashSet<u64> =
    std::collections::HashSet::with_capacity(final_node_ids.len());
final_set.extend(final_node_ids.iter().copied());

let est_terms = final_node_ids.len();
let mut terms = Vec::with_capacity(est_terms);
let mut current_term = Vec::with_capacity(32);
```

**Expected Impact:** Reduce allocation and rehashing overhead by 40-60%.

---

## Benchmarking Plan

1. **Baseline**: Benchmark BEFORE optimizations
2. **Optimized**: Benchmark AFTER optimizations
3. **Comparison**: Use Criterion's built-in comparison to measure improvement

### Key Metrics

- **Serialization Time**: Time to serialize dictionary to bytes
- **Deserialization Time**: Time to deserialize bytes to dictionary
- **Throughput**: Elements per second
- **Memory Allocations**: (would need profiling tools like heaptrack)

### Expected Improvements

Based on the optimizations:

| Operation | Expected Improvement |
|-----------|---------------------|
| Bincode Serialize | 15-25% faster |
| Bincode Deserialize | 20-30% faster |
| JSON Serialize | 15-25% faster |
| JSON Deserialize | 20-30% faster |
| Protobuf V1 Serialize | 25-35% faster |
| Protobuf V1 Deserialize | 30-40% faster |
| Protobuf V2 Serialize | 25-35% faster |
| Protobuf V2 Deserialize | 30-40% faster |

## Testing

All tests pass with optimizations:
```bash
cargo test --features protobuf serialization
# Result: 11 serialization tests passing
```

## Next Steps (Future Phases)

### Phase 2: Memory Optimizations
- Replace Vec<u8> with SmallVec for current_term
- Optimize string conversions
- Reduce cloning overhead

### Phase 3: Advanced Optimizations
- Consider arena allocators for temporary data
- Explore zero-copy deserialization
- Profile for remaining bottlenecks

## Files Modified

- `src/serialization/mod.rs` - All optimization changes
- `benches/serialization_benchmarks.rs` - New benchmark suite (created)
- `Cargo.toml` - Added serialization_benchmarks bench target
- `docs/SERIALIZATION_OPTIMIZATION_PLAN.md` - Optimization plan (created)
