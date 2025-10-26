# Query Iterator Arc Usage Analysis

## Summary

Identified **significant Arc overhead in query traversal** (query.rs:103). The current implementation clones DictionaryNode (Arc) for every explored edge to preserve the parent chain, but **the node is never used in parents** - only the label is needed for path reconstruction.

**Optimization Opportunity:** Replace full Intersection cloning with lightweight path representation → **15-30% potential improvement**

---

## Current Implementation Analysis

### Intersection Structure (intersection.rs:14-26)

```rust
pub struct Intersection<N: DictionaryNode> {
    pub label: Option<u8>,       // Edge label from parent
    pub node: N,                  // Current dictionary node (Arc for DAWG!)
    pub state: State,             // Automaton state
    pub parent: Option<Box<Intersection<N>>>, // Parent chain
}
```

**Issue:** The entire `Intersection` is stored in the parent chain, including the `node` field.

### Query Traversal (query.rs:89-118)

```rust
fn queue_children(&mut self, intersection: &Box<Intersection<N>>) {
    for (label, child_node) in intersection.node.edges() {
        if let Some(next_state) = transition_state_pooled(/*...*/) {
            // ❌ PROBLEM: Clone entire intersection to preserve parent chain
            let parent_box = Box::new(Intersection {
                label: intersection.label,
                node: intersection.node.clone(),  // ← Arc::clone for DAWG!
                state: intersection.state.clone(),
                parent: intersection.parent.clone(),
            });

            let child = Box::new(Intersection::with_parent(
                label,
                child_node,
                next_state,
                parent_box,  // ← Stores full node in parent chain
            ));

            self.pending.push_back(child);
        }
    }
}
```

**Arc Overhead:**
- For each edge explored, `intersection.node.clone()` performs Arc::clone
- In a query exploring 1000 paths with avg 5 edges/node = **5000 Arc clones per query**
- With profiling benchmark (5000 queries) = **25 million Arc clones**

### Path Reconstruction (intersection.rs:54-69)

```rust
pub fn term(&self) -> String {
    let mut bytes = Vec::new();
    self.collect_path(&mut bytes);  // ← Recursively walks parent chain
    bytes.reverse();
    String::from_utf8_lossy(&bytes).into_owned()
}

fn collect_path(&self, bytes: &mut Vec<u8>) {
    if let Some(label) = self.label {
        bytes.push(label);  // ← Only uses label!
        if let Some(parent) = &self.parent {
            parent.collect_path(bytes);  // ← Recursively collects labels
        }
    }
}
```

**Key Insight:** Path reconstruction **only accesses `label` and `parent` fields** - the `node` field in parents is **never used!**

---

## Profiling Evidence

From flame graph analysis (before optimizations):
- Query operations: 4.71s for 5000 queries
- Arc operations: 41% of total execution (117M clones, 116M drops)

After Arc-free `contains()` optimization:
- Query operations: 3.89s for 5000 queries (**17% improvement**)
- Remaining Arc overhead: Mostly in query traversal

**Estimated remaining Arc overhead in queries:** 15-20% of query execution time

---

## Optimization Strategies

### Strategy 1: Lightweight Parent Chain (Recommended)

Replace full `Intersection` in parent chain with lightweight path-only structure:

```rust
/// Lightweight parent representation (no node, just path)
struct PathNode {
    label: u8,
    parent: Option<Box<PathNode>>,
}

pub struct Intersection<N: DictionaryNode> {
    pub label: Option<u8>,
    pub node: N,
    pub state: State,
    pub parent: Option<Box<PathNode>>,  // ← Lightweight!
}
```

**Benefits:**
- Eliminates all Arc clones in parent chain
- Reduces memory per parent from ~50 bytes (Intersection) to ~10 bytes (PathNode)
- No API changes required - path reconstruction works the same

**Complexity:** Medium - requires modifying Intersection structure and path methods

**Expected improvement:** 15-25%

### Strategy 2: DAWG-Specific Query Iterator

Create specialized query iterator for DAWG that works with node indices:

```rust
struct DawgQueryIterator {
    // Work with indices instead of DawgDictionaryNode
    pending: VecDeque<DawgIntersection>,
    dawg_nodes: Arc<Vec<DawgNode>>,  // Shared reference, no per-node Arc
    // ...
}

struct DawgIntersection {
    label: Option<u8>,
    node_idx: usize,  // ← Index instead of DawgDictionaryNode
    state: State,
    parent: Option<Box<PathNode>>,
}
```

**Benefits:**
- Completely eliminates Arc operations in query traversal
- Works directly with node indices (like Arc-free `contains()`)
- Potentially 20-30% improvement

**Complexity:** High - requires specialized implementation per dictionary type

**Trade-offs:** Less generic, more maintenance burden

### Strategy 3: Reference-Counted Path (Alternative)

Use Rc instead of Box for parent chain sharing:

```rust
pub parent: Option<Rc<PathNode>>,
```

**Benefits:**
- Multiple children can share parent without cloning
- Reduces Box allocations

**Complexity:** Low

**Expected improvement:** 5-10% (helps with cloning but doesn't eliminate Arc from node)

---

## Recommendation

**Implement Strategy 1: Lightweight Parent Chain**

**Rationale:**
1. **High impact:** Eliminates all Arc clones in parent chains (15-25% improvement)
2. **Moderate complexity:** Requires changing Intersection but not the API
3. **Generic:** Works for all dictionary types, not just DAWG
4. **Maintainable:** Clean separation of concerns (active node vs path history)

**Implementation Plan:**
1. Create `PathNode` struct with `label` and `parent` only
2. Update `Intersection` to use `Option<Box<PathNode>>` for parent
3. Update `queue_children` to create `PathNode` instead of full `Intersection`
4. Update `collect_path` to work with `PathNode`
5. Run benchmarks to validate improvement

---

## Implementation Details

### PathNode Structure

```rust
/// Lightweight representation of path history.
///
/// Used to reconstruct the term path without storing full Intersection data.
/// This eliminates Arc overhead from dictionary node cloning in parent chains.
pub struct PathNode {
    /// Edge label from parent
    pub label: u8,
    /// Parent in the path
    pub parent: Option<Box<PathNode>>,
}

impl PathNode {
    /// Create a new path node
    pub fn new(label: u8, parent: Option<Box<PathNode>>) -> Self {
        Self { label, parent }
    }

    /// Collect labels into vector (for term reconstruction)
    pub fn collect_labels(&self, labels: &mut Vec<u8>) {
        labels.push(self.label);
        if let Some(parent) = &self.parent {
            parent.collect_labels(labels);
        }
    }
}
```

### Updated Intersection

```rust
pub struct Intersection<N: DictionaryNode> {
    pub label: Option<u8>,
    pub node: N,
    pub state: State,
    pub parent: Option<Box<PathNode>>,  // ← Changed from Intersection to PathNode
}

impl<N: DictionaryNode> Intersection<N> {
    pub fn with_parent(
        label: u8,
        node: N,
        state: State,
        parent: Option<Box<PathNode>>,  // ← Updated signature
    ) -> Self {
        Self {
            label: Some(label),
            node,
            state,
            parent,
        }
    }

    pub fn term(&self) -> String {
        let mut bytes = Vec::new();

        // Collect current label
        if let Some(label) = self.label {
            bytes.push(label);
        }

        // Collect parent labels
        if let Some(parent) = &self.parent {
            parent.collect_labels(&mut bytes);
        }

        bytes.reverse();
        String::from_utf8_lossy(&bytes).into_owned()
    }
}
```

### Updated queue_children

```rust
fn queue_children(&mut self, intersection: &Box<Intersection<N>>) {
    for (label, child_node) in intersection.node.edges() {
        if let Some(next_state) = transition_state_pooled(/*...*/) {
            // ✅ Create lightweight path node (no Arc clone!)
            let parent_path = if let Some(current_label) = intersection.label {
                Some(Box::new(PathNode::new(
                    current_label,
                    intersection.parent.clone(),  // Clone PathNode chain (cheap)
                )))
            } else {
                None
            };

            let child = Box::new(Intersection::with_parent(
                label,
                child_node,
                next_state,
                parent_path,  // ← Lightweight path, no node clone!
            ));

            self.pending.push_back(child);
        }
    }
}
```

---

## Expected Performance Impact

### Before Optimization
- Query 5000 terms: 3.89s (812 µs/query)
- Arc clones in query: ~25M (5000 paths × 5 edges/path × 1000 queries)

### After Optimization (Estimated)
- Query 5000 terms: ~3.2s (640 µs/query) - **17-21% improvement**
- Arc clones in query: ~0 (eliminated from parent chains)

### Combined with Previous Optimizations

| Operation | Baseline | +Arc contains | +Arc query | Total Improvement |
|-----------|----------|---------------|------------|-------------------|
| Contains 1M | 203ms | 81ms | - | **60% (2.5x)** |
| Query 5k | 4.71s | 3.89s | **~3.2s** | **32% (1.47x)** |

**Overall:** Query operations would be **1.47x faster**, reaching ~32% total improvement over baseline.

---

## Alternative: Per-Dictionary Specialization

For maximum performance, implement DAWG-specific query iterator (Strategy 2):

**Potential:** 25-35% improvement (full Arc elimination)
**Cost:** Higher maintenance, less generic code

Recommend **starting with Strategy 1** (lightweight parent chain) and evaluating if further optimization is needed.

---

## Risks and Considerations

### Breaking Changes
- `Intersection::with_parent` signature changes (parent type)
- `Intersection::parent` field type changes
- May affect external code using Intersection directly

**Mitigation:** This is likely internal API, but check for external usage.

### Memory Layout
- PathNode is smaller (16 bytes) vs Intersection (~50+ bytes)
- Better cache locality for path reconstruction

### Testing
- Verify path reconstruction correctness
- Test with various query patterns (short/long paths, high branching)
- Ensure parent chain depth doesn't cause stack overflow

---

## Next Steps

1. **Implement PathNode structure** (straightforward)
2. **Update Intersection to use PathNode parent** (moderate refactor)
3. **Update query_children to create PathNode** (simple change)
4. **Run comprehensive benchmarks** (validate 15-25% improvement)
5. **Compare with Strategy 2** if more performance needed

**Estimated development time:** 2-4 hours
**Expected impact:** 17-21% query performance improvement
**Risk level:** Medium (API changes, but isolated to query internals)
