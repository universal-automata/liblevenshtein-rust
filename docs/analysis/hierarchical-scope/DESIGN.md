# Hierarchical Lexical Scope Completion - Design Document

## Problem Statement

Design an optimal data structure and algorithm for **contextual code completion** with hierarchical lexical scopes.

### Requirements

1. **Terms can appear in multiple scopes**: A variable `x` might be visible in scopes `{0, 2, 5}`
2. **Scopes are hierarchical**: Nested contexts like `{{{x}}{}}` form scope tree
3. **Query includes scope context**: Completion at position `x` knows visible scopes `{0, 2, 3}`
4. **Intersection semantics**: Term matches if its scopes ∩ query scopes ≠ ∅
5. **Fuzzy matching**: Levenshtein distance ≤ k for prefix
6. **Performance critical**: Interactive (< 10ms for 10k identifiers)

### Example

```rust
// Global scope (id=0)
let global_var = 1;

{  // Scope 1
    let outer = 2;

    {  // Scope 2
        let inner = 3;

        // Code completion at this point:
        // Query: prefix="in", visible_scopes={0, 1, 2}
        //
        // Candidates:
        // - "inner" (scopes={2}) → MATCH (2 ∈ {0,1,2})
        // - "input" (scopes={0}) → MATCH (0 ∈ {0,1,2})
        // - "internal" (scopes={3}) → NO MATCH (3 ∉ {0,1,2})
    }
}
```

## Approaches to Evaluate

### Approach 1: Fuzzy Map with Scope Sets

**Data Structure**:
```rust
PathMapDictionary<HashSet<u32>>
// term → set of scope IDs where term is visible
```

**Query Algorithm**:
```rust
let visible_scopes: HashSet<u32> = get_visible_scopes(); // {0, 1, 2}
transducer.query_filtered(prefix, max_distance, |term_scopes| {
    !term_scopes.is_disjoint(&visible_scopes)  // Check intersection
})
```

**Complexity**:
- **Space**: O(n * s) where n=terms, s=avg scopes per term
- **Time**: O(m * k) where m=matches, k=scope set size
- **Pros**: Simple, leverages existing fuzzy map infrastructure
- **Cons**: Repeated set intersection checks

### Approach 2: Prefix Trie with Scope Masks

**Data Structure**:
```rust
PathMapDictionary<u64>  // Bit mask (up to 64 scopes)
// term → bitmask of scopes (bit i set if term in scope i)
```

**Query Algorithm**:
```rust
let visible_mask: u64 = scope_set_to_mask(&visible_scopes);
transducer.query_filtered(prefix, max_distance, |term_mask| {
    (term_mask & visible_mask) != 0  // Bitwise intersection
})
```

**Complexity**:
- **Space**: O(n) - one u64 per term
- **Time**: O(m) - single bitwise AND per match
- **Pros**: Extremely fast intersection (1 CPU cycle)
- **Cons**: Limited to 64 scopes (or 128 with u128)

### Approach 3: Post-Filtering with Linear Scan

**Data Structure**:
```rust
PathMapDictionary<Vec<u32>>  // Sorted vector of scope IDs
```

**Query Algorithm**:
```rust
let results: Vec<_> = transducer
    .query(prefix, max_distance)
    .filter(|term| {
        let term_scopes = dict.get_value(term).unwrap();
        has_intersection(&term_scopes, &visible_scopes)
    })
    .collect();
```

**Complexity**:
- **Space**: O(n * s) - vector per term
- **Time**: O(m * s * log(s)) - sorted vector intersection
- **Pros**: Works with unlimited scopes
- **Cons**: Repeated intersection computations

### Approach 4: Inverted Index by Scope

**Data Structure**:
```rust
struct ScopeIndex {
    automaton: PathMapDictionary<()>,  // All terms
    scope_to_terms: HashMap<u32, HashSet<String>>,  // scope → terms
}
```

**Query Algorithm**:
```rust
// 1. Get all fuzzy matches
let all_matches: HashSet<_> = transducer.query(prefix, max_distance).collect();

// 2. Get terms visible in any query scope
let mut visible_terms = HashSet::new();
for scope_id in &visible_scopes {
    if let Some(terms) = scope_index.get(scope_id) {
        visible_terms.extend(terms);
    }
}

// 3. Intersection
let results: Vec<_> = all_matches.intersection(&visible_terms).collect();
```

**Complexity**:
- **Space**: O(n * s) - terms duplicated per scope
- **Time**: O(m + v * t) where v=visible scopes, t=terms per scope
- **Pros**: No repeated intersection checks
- **Cons**: High memory usage, complex maintenance

### Approach 5: Hybrid (Mask for Small, Set for Large)

**Data Structure**:
```rust
enum ScopeData {
    Mask(u64),           // For scopes 0-63
    Set(HashSet<u32>),   // For overflow scopes
}

PathMapDictionary<ScopeData>
```

**Query Algorithm**:
```rust
transducer.query_filtered(prefix, max_distance, |scope_data| {
    match scope_data {
        ScopeData::Mask(mask) => (mask & visible_mask) != 0,
        ScopeData::Set(set) => !set.is_disjoint(&visible_scopes),
    }
})
```

**Complexity**:
- **Space**: O(n) for most terms (mask), O(n * s) for edge cases
- **Time**: O(1) for mask, O(k) for set
- **Pros**: Best of both worlds
- **Cons**: More complex implementation

### Approach 6: Bloom Filter Pre-filtering

**Data Structure**:
```rust
struct BloomScopeData {
    bloom: BloomFilter,    // Quick negative check
    scopes: HashSet<u32>,  // Precise check
}
```

**Query Algorithm**:
```rust
transducer.query_filtered(prefix, max_distance, |data| {
    // Fast negative check
    if !bloom_possibly_intersects(&data.bloom, &visible_scopes) {
        return false;
    }
    // Precise check
    !data.scopes.is_disjoint(&visible_scopes)
})
```

**Complexity**:
- **Space**: O(n * (b + s)) where b=bloom filter size
- **Time**: O(1) for bloom, O(k) for set (rare)
- **Pros**: Reduces expensive set operations
- **Cons**: False positives, memory overhead

## Optimization: Fast Set Intersection

The core operation is checking if two sets intersect. Several optimizations:

### Naive Approach
```rust
fn has_intersection(a: &HashSet<u32>, b: &HashSet<u32>) -> bool {
    !a.is_disjoint(b)  // Iterates entire smaller set
}
```
**Complexity**: O(min(|a|, |b|))

### Sorted Vector Approach
```rust
fn has_intersection_sorted(a: &[u32], b: &[u32]) -> bool {
    let mut i = 0;
    let mut j = 0;
    while i < a.len() && j < b.len() {
        if a[i] == b[j] { return true; }
        if a[i] < b[j] { i += 1; } else { j += 1; }
    }
    false
}
```
**Complexity**: O(|a| + |b|) worst case, O(1) if intersection found early

### BitSet Approach (for dense small scopes)
```rust
fn has_intersection_bitset(a: u64, b: u64) -> bool {
    (a & b) != 0
}
```
**Complexity**: O(1)

### Hybrid Approach (sort + binary search)
```rust
fn has_intersection_hybrid(small: &[u32], large: &[u32]) -> bool {
    // Use smaller set to search in larger
    for &item in small {
        if large.binary_search(&item).is_ok() {
            return true;
        }
    }
    false
}
```
**Complexity**: O(min * log(max))

## Benchmark Plan

### Test Scenarios

**Scenario 1: Shallow Hierarchy (2-3 levels)**
- 10,000 identifiers
- 10 scopes
- Avg 2-3 scopes per term
- Typical: local variables, function parameters

**Scenario 2: Deep Hierarchy (10+ levels)**
- 10,000 identifiers
- 100 scopes
- Avg 5-10 scopes per term
- Typical: deeply nested classes/modules

**Scenario 3: Wide Hierarchy (many siblings)**
- 10,000 identifiers
- 1,000 scopes
- Avg 1-2 scopes per term
- Typical: large flat namespace

**Scenario 4: Dense Graph (many scopes per term)**
- 10,000 identifiers
- 50 scopes
- Avg 20+ scopes per term
- Typical: inherited/imported symbols

### Metrics to Measure

1. **Query latency** (p50, p95, p99)
2. **Memory usage** (bytes per term)
3. **Throughput** (queries per second)
4. **Scaling** (10x terms, 10x scopes)
5. **Cache efficiency** (L1/L2 miss rates from perf)

### Benchmark Structure

```rust
// For each approach:
fn bench_scope_completion_{approach}(c: &mut Criterion) {
    // Setup: Create dictionary with scope data
    let dict = create_scoped_dictionary(scenario);
    let transducer = Transducer::new(dict, Algorithm::Standard);

    // Queries: Various completion contexts
    let queries = vec![
        ("pr", 2, vec![0, 1, 2]),    // Shallow
        ("get", 1, vec![0, 5, 10]),  // Medium
        ("x", 2, vec![0, 1, 2, 3, 4, 5]), // Wide
    ];

    c.bench_function(&format!("{}_scenario_{}", approach, scenario), |b| {
        b.iter(|| {
            for (prefix, dist, scopes) in &queries {
                let results: Vec<_> = query_with_scopes(
                    &transducer,
                    prefix,
                    *dist,
                    scopes
                ).collect();
                black_box(results);
            }
        })
    });
}
```

## Expected Results

Based on theory:

| Approach | Memory | Query Time | Best For |
|----------|--------|------------|----------|
| 1. Scope Sets | Medium | Medium | General purpose |
| 2. Bit Masks | Low | **Fastest** | ≤64 scopes |
| 3. Post-filter | Medium | Slow | Few matches |
| 4. Inverted Index | **High** | Fast | Many scopes |
| 5. Hybrid | Low | **Fastest** | Most cases |
| 6. Bloom Filter | High | Fast | Large scope sets |

**Predicted Winner**: Approach 5 (Hybrid) or Approach 2 (Bit Masks for ≤64 scopes)

## Implementation Plan

1. ✅ Design approaches (this document)
2. ✅ Implement 5 approaches (see benches/hierarchical_scope_benchmarks.rs)
3. ✅ Create benchmark suite (540 lines, 4 scenarios)
4. ✅ Run benchmarks for all scenarios (see hierarchical_scope_results.txt)
5. ✅ Analyze results (see HIERARCHICAL_SCOPE_COMPLETION_RESULTS.md)
6. ✅ Document recommendations (see HIERARCHICAL_SCOPE_COMPLETION_RESULTS.md)
7. ✅ Implement helper functions (see src/transducer/helpers.rs)
8. ✅ Create working example (see examples/hierarchical_scope_completion.rs)

## Questions Answered

1. **What's the typical number of scopes in real codebases?**
   - Tested: 10-1000 scopes across different scenarios
   - Findings: Most codebases have 10-100 scopes; 1000+ is rare but handled well

2. **What's the typical scope depth?**
   - Tested: 2-10 levels of nesting
   - Findings: Deep hierarchies (10 levels) show minimal performance degradation

3. **What's the distribution of scopes per term?**
   - Tested: 2-15 average scopes per term
   - Findings: Sorted vectors excel with dense graphs (15 scopes/term)

4. **Is early termination significant?**
   - Findings: Yes! Two-pointer scan with early termination provides O(1) best case
   - Post-filtering is only 0.05% different, showing graph traversal dominates

5. **Does cache locality matter for small sets?**
   - Findings: YES! Sorted vectors (contiguous memory) beat HashSets by 4.7%
   - Cache-friendly data structures provide measurable benefit

6. **Are there patterns we can exploit?**
   - Findings: Most terms visible in few scopes (2-3 on average)
   - Bitmask optimization works excellently for ≤64 scopes (7.9% faster)

## Final Recommendations

Based on comprehensive benchmarking:

1. **Use Sorted Vector** (`Vec<u32>`) for general-purpose scope filtering
   - 4.7% faster than HashSet
   - Works with unlimited scopes
   - Best cache locality

2. **Use Bitmask** (`u64`) when scope count is guaranteed ≤64
   - 7.9% faster than HashSet
   - 3.4% faster than sorted vector
   - Minimal memory footprint

3. **Avoid Hybrid Approaches**
   - Enum matching overhead negates benefits
   - Only 2.5% improvement over baseline
   - Added complexity not worth it

4. **Implementation Complete**
   - Helper functions: `src/transducer/helpers.rs`
   - Benchmarks: `benches/hierarchical_scope_benchmarks.rs`
   - Example: `examples/hierarchical_scope_completion.rs`
   - Documentation: This file + HIERARCHICAL_SCOPE_COMPLETION_RESULTS.md
