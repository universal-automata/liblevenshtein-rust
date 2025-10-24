# Future Enhancements

This document outlines planned future enhancements for liblevenshtein-rust.

## Priority Queue for Ordered Results

**Goal**: Produce spelling candidates lazily in order of least distance from the query term.

**Approach**: Implement a variation that uses:
- **Priority Queue (Min-Heap)**: Store intersections ordered by inferred distance
- **Dijkstra-like Search**: Explore intersections in order of increasing distance
- **A* Heuristic**: Use remaining query length as heuristic for distance-to-goal
- **BFS with Distance Tracking**: Current BFS could be modified to prioritize lower distances

**Implementation Sketch**:
```rust
pub struct PriorityQueryIterator<N: DictionaryNode> {
    // Min-heap ordered by (distance, intersection)
    pending: BinaryHeap<Reverse<(usize, Box<Intersection<N>>)>>,
    query: Vec<u8>,
    max_distance: usize,
    algorithm: Algorithm,
}
```

**Challenges**:
- Need to compute or estimate distance efficiently at each node
- Balance between accuracy (actual distance) and performance (heuristic)
- May need to explore more nodes than BFS before finding next match

**References**:
- Dijkstra's algorithm for single-source shortest paths
- A* search for informed heuristic search
- Best-first search variations

## WallBreaker Support

**Paper**: "WallBreaker - overcoming the wall effect in similarity search"
**Location**: `/home/dylon/Papers/Approximate String Matching/WallBreaker - overcoming the wall effect in similarity search.pdf`

**Goal**: Overcome the "wall effect" where matches beyond a certain edit distance become computationally expensive.

**Requirements**:
- Likely requires a different dictionary backend than PathMap
- May need specialized data structures for wall-breaking
- Could involve:
  - Multi-level indexing
  - Approximate distance bounds
  - Pruning strategies beyond subsumption

**Integration Points**:
- Dictionary trait is already designed to support multiple backends
- Can implement `WallBreakerDictionary` similar to `PathMapDictionary`
- May need extensions to the `DictionaryNode` trait

## Additional Algorithm Support

### Damerau-Levenshtein (Full)
Current Transposition implementation is simplified. Full Damerau-Levenshtein considers:
- Multiple transpositions
- Restricted vs unrestricted variants

### Custom Edit Cost Models
Allow users to specify custom costs for different operations:
```rust
pub struct EditCosts {
    insertion: usize,
    deletion: usize,
    substitution: usize,
    transposition: usize,
}
```

## Performance Optimizations

### SIMD Acceleration
- Vectorized characteristic vector computation
- Parallel state transitions
- Batch distance calculations

### Lazy PathMap Zippers
PathMap's zipper API is already lazy, but we recreate zippers frequently.
Consider:
- Caching zippers at frequently-visited nodes
- Using PathMap's owned zippers more effectively

### Parallel Dictionary Traversal
For very large dictionaries:
- Partition search space
- Use Rayon for parallel exploration
- Merge results from multiple threads

## Serialization

### Dictionary Serialization
Enable saving/loading dictionaries:
```rust
impl PathMapDictionary {
    pub fn save(&self, path: &Path) -> Result<()>;
    pub fn load(path: &Path) -> Result<Self>;
}
```

### Automata Precomputation
For common query patterns, precompute and cache automata states.

## Extended API Features

### Fuzzy Matching Modes
```rust
pub enum MatchMode {
    Exact,           // Only exact distance
    AtMost(usize),   // Current behavior
    Range(usize, usize),  // Between min and max
}
```

### Custom Filters
```rust
pub trait MatchFilter {
    fn accept(&self, term: &str, distance: usize) -> bool;
}
```

### Suggestions API
```rust
pub struct Suggestion {
    term: String,
    distance: usize,
    frequency: f64,  // If dictionary has frequency data
    confidence: f64,
}
```

## Alternative Dictionary Backends

### Trie Backend
Port the C++ trie implementation for comparison.

### Double Array Trie
Implement or integrate a double-array trie for:
- Lower memory usage
- Faster transitions
- Compact serialization

### Suffix Array Backend
For certain use cases, suffix arrays might be more appropriate.

### FST (Finite State Transducer)
Integrate with the `fst` crate for additional functionality.

## Documentation Improvements

- Comprehensive API documentation with examples
- Performance benchmarking guide
- Tutorial for building custom dictionary backends
- Comparison with other fuzzy matching libraries
- Interactive examples in the documentation

## Testing

- Property-based testing with `proptest`
- Fuzzing with `cargo-fuzz`
- Benchmark suite comparing algorithms
- Large-scale dictionary tests (millions of terms)

## Build Features

Enable/disable features via Cargo:
```toml
[features]
default = ["pathmap"]
pathmap = []
trie = []
wallbreaker = []
priority-queue = []
simd = []
```
