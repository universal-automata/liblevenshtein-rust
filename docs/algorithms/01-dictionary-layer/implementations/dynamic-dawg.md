# DynamicDawg Implementation

**Navigation**: [← Dictionary Layer](../README.md) | [DoubleArrayTrie](double-array-trie.md) | [Algorithms Home](../../README.md)

## Table of Contents

1. [Overview](#overview)
2. [Theory: DAWG Structure](#theory-dawg-structure)
3. [Dynamic Modifications](#dynamic-modifications)
4. [Data Structure](#data-structure)
5. [Key Algorithms](#key-algorithms)
6. [Union Operations](#union-operations)
7. [Usage Examples](#usage-examples)
8. [Performance Analysis](#performance-analysis)
9. [When to Use](#when-to-use)
10. [References](#references)

## Overview

`DynamicDawg` is a **Directed Acyclic Word Graph** that supports **runtime insertions and deletions** while maintaining thread-safe access. Unlike static DAWG implementations, DynamicDawg allows the dictionary to evolve during application lifetime.

### Key Advantages

- 🔄 **Full dynamic updates**: Insert AND remove terms at runtime
- 🔒 **Thread-safe**: Safe for concurrent reads and exclusive writes
- 💾 **Space-efficient**: Shares common suffixes (20-40% reduction)
- ⚡ **Good performance**: Suitable for dictionaries with frequent updates
- 📊 **Reference counting**: Safe deletion without orphaning nodes

### When to Use

✅ **Use DynamicDawg when:**
- Dictionary changes frequently (adds and removes)
- Need thread-safe concurrent access
- Building dynamic word lists (user dictionaries, session-specific terms)
- Real-time collaborative applications

⚠️ **Consider alternatives when:**
- Dictionary is static or append-only → Use `DoubleArrayTrie` (3x faster)
- Need maximum query performance → Use `DoubleArrayTrie`
- Working with Unicode → Use `DynamicDawgChar`

## Theory: DAWG Structure

### What is a DAWG?

A **Directed Acyclic Word Graph** is a compressed trie that shares common suffixes, not just prefixes.

**Example**: Terms ["car", "card", "cart", "star", "start"]

```
Regular Trie (prefix sharing only):
       (root)
       /    \
      c      s
      |      |
      a      t
      |      |
      r      a
     / \     |
    d   t    r
            / \
           t   (nothing - "star")

DAWG (prefix AND suffix sharing):
       (root)
       /    \
      c      s
      |      |
      a      t
      |      |
      r ─────┘  ← Shares "ar" suffix
     / \
    d   t
```

**Space savings**: DAWG nodes = ~50-70% of trie nodes for natural language.

### Suffix Sharing

Multiple prefixes can point to the same suffix:
```
"card" = c→a→r→d(final)
"cart" = c→a→r→t(final)
"hard" = h→a→r→d(final)  ← Shares "r→d" with "card"
"hart" = h→a→r→t(final)  ← Shares "r→t" with "cart"
```

This is achieved by **hashing node signatures** and reusing nodes with identical right languages.

## Dynamic Modifications

### Insertion Algorithm

Adding a term while maintaining minimality:

```rust
fn insert(&self, term: &str) {
    let mut lock = self.inner.write();  // Exclusive lock

    // Traverse existing path
    let mut node_idx = 0;  // Root
    let mut path = Vec::new();

    for byte in term.bytes() {
        path.push(node_idx);

        // Find or create edge
        node_idx = match lock.find_edge(node_idx, byte) {
            Some(child_idx) => child_idx,
            None => {
                // Create new suffix
                let new_suffix = lock.create_suffix(&term[pos..]);
                lock.add_edge(node_idx, byte, new_suffix);
                return;
            }
        };
    }

    // Mark final
    lock.nodes[node_idx].is_final = true;
}
```

**Complexity**: O(m) where m = term length

### Deletion Algorithm

Removing a term requires reference counting:

```rust
fn remove(&self, term: &str) -> bool {
    let mut lock = self.inner.write();

    // Traverse to term
    let mut node_idx = 0;
    let mut path = Vec::new();

    for byte in term.bytes() {
        path.push(node_idx);
        node_idx = lock.find_edge(node_idx, byte)?;
    }

    if !lock.nodes[node_idx].is_final {
        return false;  // Term not in dictionary
    }

    // Mark as non-final
    lock.nodes[node_idx].is_final = false;

    // Decrement reference counts along path
    for &idx in path.iter().rev() {
        lock.nodes[idx].ref_count -= 1;

        // Delete node if no longer referenced
        if lock.nodes[idx].ref_count == 0 && !lock.nodes[idx].is_final {
            lock.delete_node(idx);
        } else {
            break;  // Still in use
        }
    }

    lock.needs_compaction = true;
    true
}
```

**Complexity**: O(m)

### Compaction

Over time, deletions create orphaned branches. Compaction restores minimality:

```rust
pub fn compact(&self) {
    let mut lock = self.inner.write();

    if !lock.needs_compaction {
        return;
    }

    // Rebuild suffix cache
    lock.suffix_cache.clear();
    lock.rebuild_suffix_cache();

    // Merge equivalent nodes
    lock.merge_equivalent_nodes();

    lock.needs_compaction = false;
}
```

**Complexity**: O(n) where n = total nodes

**When to compact**:
- After many deletions (10%+ of dictionary removed)
- When query performance degrades
- During maintenance windows

## Data Structure

### Core Components

```rust
pub struct DynamicDawg<V: DictionaryValue = ()> {
    inner: Arc<RwLock<DynamicDawgInner<V>>>,
}

struct DynamicDawgInner<V: DictionaryValue> {
    nodes: Vec<DawgNode<V>>,           // Node storage
    term_count: usize,                 // Number of terms
    needs_compaction: bool,            // Deletion flag
    suffix_cache: FxHashMap<u64, usize>, // Hash → node index
    bloom_filter: Option<BloomFilter>, // Fast negative lookups
    auto_minimize_threshold: f32,      // Lazy minimization trigger
}

struct DawgNode<V: DictionaryValue> {
    edges: SmallVec<[(u8, usize); 4]>, // Label → child index
    is_final: bool,                    // Marks valid term
    ref_count: usize,                  // For safe deletion
    value: Option<V>,                  // Associated value
}
```

### Memory Layout

```
┌─────────────────┬─────────────┬────────────────┐
│ Component       │ Size        │ Per Node       │
├─────────────────┼─────────────┼────────────────┤
│ SmallVec edges  │ Inline ≤4   │ ~16 bytes      │
│ is_final        │ 1 byte      │ 1 byte         │
│ ref_count       │ 8 bytes     │ 8 bytes        │
│ value (Option)  │ V or 1 byte │ Varies         │
├─────────────────┼─────────────┼────────────────┤
│ Total per node  │ ~25+ bytes  │ ~25 bytes      │
│ Overhead        │ Arc+RwLock  │ 16 bytes total │
└─────────────────┴─────────────┴────────────────┘
```

**Example**: 10,000-term dictionary ≈ 250KB (nodes) + 32KB (suffix cache)

### Clone Behavior & Memory Semantics

`DynamicDawg` uses `Arc<RwLock<...>>` internally, making `.clone()` a **shallow copy** that shares all underlying data structures between clones:

```rust
use liblevenshtein::dictionary::dynamic_dawg::DynamicDawg;

let dict1 = DynamicDawg::from_iter(vec!["test", "testing"]);
let dict2 = dict1.clone();  // O(1) - only increments Arc refcount

// Both dict1 and dict2 point to the SAME underlying data
dict1.insert("new_term");
assert!(dict2.contains("new_term"));  // ✅ Mutations visible through dict2!

// Term count reflects changes made via either clone
assert_eq!(dict1.len(), Some(3));
assert_eq!(dict2.len(), Some(3));  // Same count
```

#### Characteristics

| Property | Behavior | Impact |
|----------|----------|--------|
| **Time Complexity** | O(1) | Single atomic increment |
| **Space Complexity** | O(1) | ~16 bytes (Arc pointer only) |
| **Data Sharing** | ✅ Complete | All clones share same node graph |
| **Mutation Visibility** | ✅ Global | Changes via any clone affect all |
| **Thread Safety** | ✅ RwLock | Multiple readers OR single writer |
| **Independence** | ❌ None | No isolation between clones |

#### How Clone Works

The clone operation only increments an atomic reference counter:

```rust
pub struct DynamicDawg<V> {
    inner: Arc<RwLock<DynamicDawgInner<V>>>,  // ← Single Arc
}

// Cloning increments Arc's atomic refcount
let dict2 = dict1.clone();
// Equivalent to: Arc::clone(&dict1.inner)
// Cost: ~1-2 CPU cycles (atomic increment)
```

**What gets cloned:**
- ✅ Arc smart pointer (~16 bytes on stack)
- ❌ NOT the RwLock
- ❌ NOT the node graph (Vec<DawgNode>)
- ❌ NOT the suffix cache or bloom filter
- ❌ NOT any internal structures

**Memory allocation:**
- Zero heap allocation
- Only stack space for new Arc pointer
- All data remains shared

#### When to Use Cloning

✅ **Good use cases:**

1. **Multi-threaded access** - Share across threads:
   ```rust
   use std::thread;

   let dict = DynamicDawg::from_iter(vec!["hello", "world"]);

   let handles: Vec<_> = (0..4).map(|_| {
       let dict_clone = dict.clone();  // Cheap clone for each thread
       thread::spawn(move || {
           // Each thread can read concurrently
           dict_clone.contains("hello")
       })
   }).collect();
   ```

2. **Storing in multiple data structures:**
   ```rust
   let mut map1 = HashMap::new();
   let mut map2 = HashMap::new();

   let dict = DynamicDawg::from_iter(vec!["term1", "term2"]);
   map1.insert("key1", dict.clone());
   map2.insert("key2", dict.clone());  // Same underlying data
   ```

3. **Convenience aliases:**
   ```rust
   let system_dict = DynamicDawg::from_iter(vec!["system"]);
   let dict = system_dict.clone();  // Short alias
   ```

❌ **Bad use cases (common mistakes):**

1. **Expecting independent copies:**
   ```rust
   let dict1 = DynamicDawg::from_iter(vec!["original"]);
   let dict2 = dict1.clone();

   dict1.insert("modified");
   // ❌ WRONG: Expecting dict2 to still have only "original"
   // ✅ REALITY: dict2 also contains "modified"
   ```

2. **Avoiding mutation visibility:**
   ```rust
   let dict1 = build_dictionary();
   let dict2 = dict1.clone();  // ❌ Won't create independent copy

   modify_dictionary(&dict1);
   // dict2 sees all modifications - they share data!
   ```

3. **Creating snapshots:**
   ```rust
   let dict = DynamicDawg::from_iter(vec!["v1"]);
   let snapshot = dict.clone();  // ❌ NOT a snapshot!

   dict.insert("v2");
   // "snapshot" now also contains "v2" - not a true snapshot
   ```

#### Alternative: True Independence

If you need **independent copies** where modifications don't affect other instances, `clone()` is insufficient. Options include:

**Option 1: Serialize/Deserialize**
```rust
use serde::{Serialize, Deserialize};

// Create deep copy via serialization
let bytes = bincode::serialize(&dict1)?;
let dict2: DynamicDawg = bincode::deserialize(&bytes)?;

// Now dict1 and dict2 are truly independent
dict1.insert("new");
assert!(!dict2.contains("new"));  // ✅ Independent
```

**Option 2: Rebuild from terms**
```rust
// Extract all terms
let terms: Vec<String> = dict1.iter().collect();

// Build new independent dictionary
let dict2 = DynamicDawg::from_iter(terms);

// dict2 is now completely independent
```

**Cost comparison:**

| Method | Time | Space | Independence |
|--------|------|-------|--------------|
| `.clone()` | O(1) | O(1) | ❌ Shared |
| Serialize/Deserialize | O(n) | O(n) | ✅ Full |
| Rebuild from terms | O(n·m) | O(n) | ✅ Full |

#### Comparison with Other Dictionaries

Different dictionary implementations have different clone semantics:

| Dictionary | Clone Type | Cost | Shared Data? |
|------------|------------|------|--------------|
| **DynamicDawg** | Shallow (Arc) | O(1) | ✅ Yes |
| **DynamicDawgChar** | Shallow (Arc) | O(1) | ✅ Yes |
| **PathMapDictionary** | Shallow (Arc) | O(1) | ✅ Yes |
| **DoubleArrayTrie** | Deep copy | O(n) | ❌ No |
| **DoubleArrayTrieChar** | Deep copy | O(n) | ❌ No |

**Why the difference?**
- **Mutable dictionaries** (DynamicDawg, PathMap) use Arc for shared ownership with interior mutability
- **Immutable dictionaries** (DoubleArrayTrie) don't use Arc, so clone creates full independent copies

#### Thread Safety Considerations

The Arc-based clone enables safe concurrent access patterns:

```rust
use std::sync::Arc;
use std::thread;

let dict = DynamicDawg::from_iter(vec!["concurrent", "access"]);

// Multiple concurrent readers (fast - no blocking)
let readers: Vec<_> = (0..10).map(|i| {
    let dict = dict.clone();
    thread::spawn(move || {
        dict.contains(&format!("term{}", i))  // Many readers OK
    })
}).collect();

// Single writer (blocks readers during write)
let writer = {
    let dict = dict.clone();
    thread::spawn(move || {
        dict.insert("new_term")  // Exclusive write access
    })
};
```

**RwLock semantics:**
- **Multiple readers** can access simultaneously (read locks don't block each other)
- **Single writer** gets exclusive access (write lock blocks all readers and other writers)
- Write operations: `insert()`, `remove()`, `union_with()`, `compact()`
- Read operations: `contains()`, `get_value()`, `len()`, iteration

**Performance impact:**
- Read locks: ~10-20ns overhead (atomic operations)
- Write locks: ~50-100ns + potential thread wake-up costs
- Contention: High write frequency can create bottlenecks

#### Summary

**Key Takeaways:**
1. 🔗 `.clone()` creates a **shallow copy** - all clones share the same data
2. 🚀 **O(1)** time and space - just increments atomic reference count
3. 🔄 **Mutations are visible** across all clones (by design)
4. 🔒 **Thread-safe** through RwLock (multiple readers, single writer)
5. 📊 For **independence**, use serialization or rebuild from terms (O(n) cost)

### Optimizations

#### 1. SmallVec for Edges

Most nodes have ≤4 edges. `SmallVec` avoids heap allocation:

```rust
// Inline storage for ≤4 edges (stack allocated)
edges: SmallVec<[(u8, usize); 4]>

// Typical case: 2 edges → no heap allocation
// Rare case: >4 edges → heap allocation
```

**Impact**: 30-40% faster node access

#### 2. Suffix Cache

Hash node signatures to detect identical suffixes:

```rust
fn compute_signature(node: &DawgNode) -> u64 {
    let mut hasher = FxHasher::default();

    node.is_final.hash(&mut hasher);

    for (label, child_idx) in &node.edges {
        label.hash(&mut hasher);
        child_signature(child_idx).hash(&mut hasher);
    }

    hasher.finish()
}

// Check cache before creating new nodes
if let Some(&existing_idx) = suffix_cache.get(&signature) {
    return existing_idx;  // Reuse existing
}
```

**Impact**: 20-40% space reduction

#### 3. Bloom Filter

Fast negative lookup rejection:

```rust
fn contains(&self, term: &str) -> bool {
    let lock = self.inner.read();

    // Fast rejection (no DAWG traversal needed)
    if let Some(ref bloom) = lock.bloom_filter {
        if !bloom.might_contain(term) {
            return false;  // Definitely not present
        }
    }

    // Full DAWG traversal
    lock.traverse(term)
}
```

**Impact**: 5-10x faster negative lookups

#### 4. Lazy Minimization

Defer expensive minimization until threshold reached:

```rust
// Minimize only when node count grows significantly
if nodes.len() > last_minimized * auto_minimize_threshold {
    self.minimize();
    last_minimized = nodes.len();
}
```

**Impact**: Amortizes O(n) cost over many insertions

## Key Algorithms

### Insert with Suffix Sharing

```rust
fn insert_with_sharing(&mut self, term: &[u8], value: Option<V>) {
    let mut node_idx = 0;

    for (i, &byte) in term.iter().enumerate() {
        // Try to follow existing edge
        if let Some(child_idx) = self.find_edge(node_idx, byte) {
            node_idx = child_idx;
            continue;
        }

        // Need to create new branch
        // Check if remainder matches existing suffix
        let remainder = &term[i..];
        let signature = self.compute_suffix_signature(remainder, value.clone());

        if let Some(&cached_idx) = self.suffix_cache.get(&signature) {
            // Reuse existing suffix!
            self.add_edge(node_idx, byte, cached_idx);
            self.nodes[cached_idx].ref_count += 1;
            return;
        }

        // Create new suffix
        let new_idx = self.create_suffix(remainder, value);
        self.add_edge(node_idx, byte, new_idx);
        self.suffix_cache.insert(signature, new_idx);
        return;
    }

    // Mark final
    self.nodes[node_idx].is_final = true;
    self.nodes[node_idx].value = value;
}
```

### Reference-Counted Deletion

```rust
fn remove_with_ref_counting(&mut self, term: &[u8]) -> bool {
    // Traverse and record path
    let mut path = Vec::new();
    let mut node_idx = 0;

    for &byte in term {
        path.push((node_idx, byte));
        node_idx = self.find_edge(node_idx, byte)?;
    }

    if !self.nodes[node_idx].is_final {
        return false;
    }

    // Unmark final
    self.nodes[node_idx].is_final = false;
    self.nodes[node_idx].value = None;

    // Decrement reference counts
    for (parent_idx, label) in path.iter().rev() {
        let child_idx = self.find_edge(*parent_idx, *label).unwrap();
        self.nodes[child_idx].ref_count -= 1;

        // Delete if unreferenced
        if self.nodes[child_idx].ref_count == 0 &&
           !self.nodes[child_idx].is_final &&
           self.nodes[child_idx].edges.is_empty() {
            self.remove_edge(*parent_idx, *label);
        } else {
            break;  // Still in use
        }
    }

    self.needs_compaction = true;
    true
}
```

## Union Operations

### Overview

The `union_with()` and `union_replace()` methods enable **merging two DynamicDawg dictionaries** with custom value combination logic. This is essential for scenarios like:

- 📊 Aggregating statistics across multiple data sources
- 🔄 Merging user-specific and global dictionaries
- 🗂️ Combining category hierarchies
- 🔢 Building composite symbol tables

**Key Characteristics**:
- 🔒 **Thread-safe**: Operations use RwLock for concurrent access
- 💾 **DAWG-preserving**: Maintains minimization through `insert_with_value()`
- ⚡ **Efficient**: O(n·m) traversal with minimal memory overhead
- 🎯 **Flexible**: Custom merge functions for value conflicts

### union_with() - Merge with Custom Logic

Combines two dictionaries by inserting all terms from the source dictionary, applying a custom merge function when values conflict.

**Signature**:
```rust
fn union_with<F>(&self, other: &Self, merge_fn: F) -> usize
where
    F: Fn(&Self::Value, &Self::Value) -> Self::Value,
    Self::Value: Clone
```

**Parameters**:
- `other`: Source dictionary to merge from
- `merge_fn`: Function `(existing_value, new_value) -> merged_value` for conflicts
- **Returns**: Number of terms processed from `other`

**Algorithm**: Depth-First Search (DFS) traversal
1. Initialize stack with root node `(node_idx=0, path=Vec::new())`
2. Pop `(node_idx, path)` from stack
3. If node is final:
   - Convert path bytes to UTF-8 string
   - Check if term exists in `self`
   - If exists: Apply `merge_fn` and update
   - If new: Insert with original value
4. Push all children onto stack (reversed for consistent ordering)
5. Repeat until stack empty

**Complexity**:
- **Time**: O(n·m) where n = terms in `other`, m = average term length
  - O(n·m) for DFS traversal
  - O(m) per term for `insert_with_value()`
- **Space**: O(d) where d = maximum trie depth (typically < 50)
  - DFS stack size proportional to deepest path
  - Constant additional memory

### Example 1: Sum Aggregation

Merge term counts by summing conflicting values:

```rust
use liblevenshtein::dictionary::dynamic_dawg::DynamicDawg;
use liblevenshtein::dictionary::MutableMappedDictionary;

// First dataset: word frequencies
let dict1: DynamicDawg<u32> = DynamicDawg::new();
dict1.insert_with_value("apple", 10);
dict1.insert_with_value("banana", 5);
dict1.insert_with_value("cherry", 3);

// Second dataset: more frequencies
let dict2: DynamicDawg<u32> = DynamicDawg::new();
dict2.insert_with_value("apple", 7);   // Overlap - will sum
dict2.insert_with_value("banana", 2);  // Overlap - will sum
dict2.insert_with_value("date", 4);    // New entry

// Merge by summing counts
let processed = dict1.union_with(&dict2, |left, right| left + right);

// Results:
// - apple: 17 (10 + 7)
// - banana: 7 (5 + 2)
// - cherry: 3 (unchanged)
// - date: 4 (new)
assert_eq!(dict1.get_value("apple"), Some(17));
assert_eq!(dict1.get_value("date"), Some(4));
assert_eq!(processed, 3); // Processed 3 terms from dict2
```

### Example 2: Set Union with Deduplication

Merge lists of associated IDs, eliminating duplicates:

```rust
use liblevenshtein::dictionary::dynamic_dawg::DynamicDawg;
use liblevenshtein::dictionary::MutableMappedDictionary;

// First dictionary: terms with associated document IDs
let dict1: DynamicDawg<Vec<u32>> = DynamicDawg::new();
dict1.insert_with_value("algorithm", vec![1, 2, 5]);
dict1.insert_with_value("database", vec![3, 7]);

// Second dictionary: more document associations
let dict2: DynamicDawg<Vec<u32>> = DynamicDawg::new();
dict2.insert_with_value("algorithm", vec![2, 4, 5]); // Overlap: [2,5]
dict2.insert_with_value("distributed", vec![6, 8]);

// Merge by concatenating and deduplicating
dict1.union_with(&dict2, |left, right| {
    let mut merged = left.clone();
    merged.extend(right.clone());
    merged.sort_unstable();
    merged.dedup();
    merged
});

// Results:
// - algorithm: [1, 2, 4, 5] (merged and deduplicated)
// - database: [3, 7] (unchanged)
// - distributed: [6, 8] (new)
assert_eq!(dict1.get_value("algorithm"), Some(vec![1, 2, 4, 5]));
```

### Example 3: Maximum Value Selection

Keep the highest value when terms conflict:

```rust
use liblevenshtein::dictionary::dynamic_dawg::DynamicDawg;
use liblevenshtein::dictionary::MutableMappedDictionary;

// Dictionary 1: initial scores
let dict1: DynamicDawg<i32> = DynamicDawg::new();
dict1.insert_with_value("performance", 85);
dict1.insert_with_value("reliability", 92);

// Dictionary 2: updated scores
let dict2: DynamicDawg<i32> = DynamicDawg::new();
dict2.insert_with_value("performance", 90); // Higher score
dict2.insert_with_value("reliability", 88); // Lower score
dict2.insert_with_value("security", 95);    // New metric

// Keep maximum value for conflicts
dict1.union_with(&dict2, |left, right| (*left).max(*right));

// Results:
// - performance: 90 (max of 85, 90)
// - reliability: 92 (max of 92, 88)
// - security: 95 (new)
assert_eq!(dict1.get_value("performance"), Some(90));
assert_eq!(dict1.get_value("reliability"), Some(92));
```

### Example 4: Shared Prefix Handling

Demonstrates correct behavior with terms sharing common prefixes:

```rust
use liblevenshtein::dictionary::dynamic_dawg::DynamicDawg;
use liblevenshtein::dictionary::MutableMappedDictionary;

// Dictionary with "test" prefix family
let dict1: DynamicDawg<u32> = DynamicDawg::new();
dict1.insert_with_value("test", 1);
dict1.insert_with_value("testing", 2);
dict1.insert_with_value("tester", 3);

// More "test" variants
let dict2: DynamicDawg<u32> = DynamicDawg::new();
dict2.insert_with_value("test", 10);      // Conflict
dict2.insert_with_value("tested", 4);     // New, shares "test" prefix
dict2.insert_with_value("testimony", 5);  // New, shares "test" prefix

dict1.union_with(&dict2, |left, right| left + right);

// All terms preserved correctly despite shared prefixes
assert_eq!(dict1.len().unwrap(), 5);
assert_eq!(dict1.get_value("test"), Some(11));       // 1 + 10
assert_eq!(dict1.get_value("tested"), Some(4));      // New
assert_eq!(dict1.get_value("testimony"), Some(5));   // New
```

### union_replace() - Keep Right Values

Convenience method equivalent to `union_with(other, |_, right| right.clone())`. Keeps values from `other` when terms conflict.

**Signature**:
```rust
fn union_replace(&self, other: &Self) -> usize
where
    Self::Value: Clone
```

**Example**:
```rust
use liblevenshtein::dictionary::dynamic_dawg::DynamicDawg;
use liblevenshtein::dictionary::MutableMappedDictionary;

let dict1: DynamicDawg<&str> = DynamicDawg::new();
dict1.insert_with_value("version", "1.0");
dict1.insert_with_value("status", "beta");

let dict2: DynamicDawg<&str> = DynamicDawg::new();
dict2.insert_with_value("version", "2.0");    // Override
dict2.insert_with_value("author", "alice");   // New

// Replace conflicting values with those from dict2
dict1.union_replace(&dict2);

// Results:
// - version: "2.0" (replaced)
// - status: "beta" (unchanged)
// - author: "alice" (new)
assert_eq!(dict1.get_value("version"), Some("2.0"));
assert_eq!(dict1.get_value("status"), Some("beta"));
```

### Implementation Details

The union operation uses **iterative depth-first search** to traverse all terms in the source dictionary:

```rust
// Simplified pseudocode
fn union_with<F>(&self, other: &Self, merge_fn: F) -> usize {
    let other_inner = other.inner.read();
    let mut processed = 0;

    // Initialize DFS with root: (node_index, accumulated_path)
    let mut stack: Vec<(usize, Vec<u8>)> = vec![(0, Vec::new())];

    while let Some((node_idx, path)) = stack.pop() {
        let node = &other_inner.nodes[node_idx];

        // Process final nodes (complete terms)
        if node.is_final {
            if let Ok(term) = std::str::from_utf8(&path) {
                processed += 1;

                if let Some(other_value) = &node.value {
                    if let Some(self_value) = self.get_value(term) {
                        // Term exists - merge values
                        let merged = merge_fn(&self_value, other_value);
                        self.insert_with_value(term, merged);
                    } else {
                        // New term - insert directly
                        self.insert_with_value(term, other_value.clone());
                    }
                }
            }
        }

        // Push children onto stack (reversed for consistent order)
        for &(label, target_idx) in node.edges.iter().rev() {
            let mut child_path = path.clone();
            child_path.push(label);
            stack.push((target_idx, child_path));
        }
    }

    processed
}
```

**Why Iterative DFS?**
- ✅ **No stack overflow**: Handles very deep tries (e.g., long terms)
- ✅ **Memory efficient**: O(d) space vs O(n) for recursion
- ✅ **Consistent ordering**: Reversed edges ensure predictable traversal
- ✅ **Debuggable**: Explicit stack state visible at each step

**Why Use `insert_with_value()`?**

The implementation delegates to `insert_with_value()` rather than manipulating nodes directly. This design choice:

1. **Preserves DAWG minimization**: Insertion logic handles suffix sharing and node deduplication
2. **Maintains reference counts**: Proper accounting for shared nodes
3. **Simpler and safer**: Avoids complex graph manipulation bugs
4. **Future-proof**: Benefits from optimizations to insertion algorithm

**Trade-off**: Slightly slower than direct node manipulation, but correctness > speed for complex structures.

### Performance Characteristics

| Operation | Time Complexity | Space Complexity | Typical Performance (10K terms) |
|-----------|----------------|------------------|--------------------------------|
| `union_with()` | O(n·m) | O(d) | ~50ms |
| `union_replace()` | O(n·m) | O(d) | ~50ms |
| DFS traversal | O(n) | O(d) | ~20ms |
| Per-term insertion | O(m) | O(1) amortized | ~2-5µs |

**Variables**:
- n = number of terms in source dictionary
- m = average term length (typically 5-15 bytes)
- d = maximum trie depth (typically 20-50)

**Memory Profile**:
```
Stack size: ~200-2000 bytes (depth × 40 bytes per frame)
Peak allocation: O(m) for path accumulation
No heap allocations during traversal (Vec reused)
```

**Benchmark Results** (AMD Ryzen 9 5950X):

| Dictionary Size | union_with() | Throughput |
|----------------|-------------|------------|
| 1,000 terms    | 4.2ms       | 238K terms/s |
| 10,000 terms   | 48ms        | 208K terms/s |
| 100,000 terms  | 520ms       | 192K terms/s |

*Note*: Performance includes merge function execution. Simple operations (e.g., sum) add minimal overhead.

### When to Use Union Operations

✅ **Use `union_with()` when:**
- Merging user-specific and system dictionaries
- Aggregating statistics from multiple sources (word counts, frequencies)
- Combining hierarchical categories or tags
- Building composite symbol tables in compilers/interpreters
- Synchronizing dictionaries across distributed systems
- Implementing set operations on labeled data

✅ **Use `union_replace()` when:**
- Updating dictionaries with newer data (last-writer-wins semantics)
- Applying configuration overrides (defaults + user settings)
- Merging dictionaries where conflicts indicate stale data

⚠️ **Consider alternatives when:**
- **Dictionaries are static**: Pre-merge at build time with [`from_terms_with_values()`](dynamic-dawg.md#example-2-dictionary-with-values)
- **One dictionary much larger**: Iterate the smaller dictionary and insert into larger (avoids traversing large dict)
- **No value merging needed**: Use simple iteration: `for (term, value) in dict2.iter() { dict1.insert_with_value(term, value); }`
- **Frequent unions on same dictionaries**: Cache union result or use different data structure (e.g., separate indices)

### Thread Safety Considerations

Union operations are **fully thread-safe** due to RwLock usage:

```rust
use std::sync::Arc;
use std::thread;

let dict1 = Arc::new(DynamicDawg::new());
let dict2 = Arc::new(DynamicDawg::new());

// Populate dictionaries from multiple threads
let handles: Vec<_> = (0..4).map(|i| {
    let d1 = Arc::clone(&dict1);
    let d2 = Arc::clone(&dict2);

    thread::spawn(move || {
        if i % 2 == 0 {
            d1.insert_with_value(&format!("term_{}", i), i);
        } else {
            d2.insert_with_value(&format!("term_{}", i), i);
        }
    })
}).collect();

for h in handles { h.join().unwrap(); }

// Merge from any thread
dict1.union_with(&dict2, |a, b| a + b);
```

**Lock Contention**: Union acquires a read lock on `other` and write lock on `self`. This blocks:
- ❌ Concurrent mutations to `self` (expected)
- ❌ Concurrent reads from `self` (temporary)
- ✅ Concurrent reads from `other` (allowed)

For high-concurrency scenarios, consider:
1. Performing union on a clone
2. Batching multiple unions
3. Using snapshot-and-merge patterns

## Usage Examples

### Example 1: Basic Usage

```rust
use liblevenshtein::dictionary::dynamic_dawg::DynamicDawg;

// Create empty DAWG
let dict = DynamicDawg::new();

// Insert terms
dict.insert("test");
dict.insert("testing");
dict.insert("tested");

assert!(dict.contains("test"));
assert_eq!(dict.len(), Some(3));

// Remove term
dict.remove("tested");
assert!(!dict.contains("tested"));
assert_eq!(dict.len(), Some(2));
```

### Example 2: With Values

```rust
use liblevenshtein::dictionary::dynamic_dawg::DynamicDawg;
use liblevenshtein::dictionary::MappedDictionary;

let dict: DynamicDawg<u32> = DynamicDawg::new();

// Insert with values
dict.insert_with_value("test", 1);
dict.insert_with_value("testing", 2);

// Query values
assert_eq!(dict.get_value("test"), Some(1));
assert_eq!(dict.get_value("testing"), Some(2));

// Remove preserves other terms
dict.remove("test");
assert_eq!(dict.get_value("testing"), Some(2));
```

### Example 3: From Existing Terms

```rust
use liblevenshtein::dictionary::dynamic_dawg::DynamicDawg;

let dict = DynamicDawg::from_terms(vec![
    "algorithm", "approximate", "automaton"
]);

// Add new terms at runtime
dict.insert("analysis");

assert!(dict.contains("algorithm"));
assert!(dict.contains("analysis"));
```

### Example 4: Thread-Safe Updates

```rust
use liblevenshtein::dictionary::dynamic_dawg::DynamicDawg;
use std::sync::Arc;
use std::thread;

let dict = Arc::new(DynamicDawg::from_terms(vec!["initial"]));

// Spawn writer thread
let dict_writer = Arc::clone(&dict);
let writer = thread::spawn(move || {
    dict_writer.insert("new_term");
});

// Spawn reader threads
let handles: Vec<_> = (0..4).map(|_| {
    let dict_reader = Arc::clone(&dict);
    thread::spawn(move || {
        dict_reader.contains("initial")
    })
}).collect();

writer.join().unwrap();
for handle in handles {
    assert!(handle.join().unwrap());
}
```

### Example 5: Compaction

```rust
use liblevenshtein::dictionary::dynamic_dawg::DynamicDawg;

let dict = DynamicDawg::from_terms(vec![
    "test1", "test2", "test3", "test4", "test5"
]);

println!("Before deletion: {} nodes", dict.node_count());

// Remove many terms
for i in 1..=4 {
    dict.remove(&format!("test{}", i));
}

println!("After deletion: {} nodes (may have orphans)", dict.node_count());

// Compact to restore minimality
dict.compact();

println!("After compaction: {} nodes", dict.node_count());
```

### Example 6: Fuzzy Search with Dynamic Updates

```rust
use liblevenshtein::dictionary::dynamic_dawg::DynamicDawg;
use liblevenshtein::levenshtein::Algorithm;
use liblevenshtein::levenshtein_automaton::LevenshteinAutomaton;

let dict = DynamicDawg::from_terms(vec!["test", "testing"]);

// Fuzzy search
let automaton = LevenshteinAutomaton::new("tset", 1, Algorithm::Standard);
let results: Vec<String> = automaton.query(&dict).collect();
println!("{:?}", results);  // ["test"]

// Add term dynamically
dict.insert("tester");

// Search again (sees new term)
let results: Vec<String> = automaton.query(&dict).collect();
println!("{:?}", results);  // ["test", "tester"]
```

## Performance Analysis

### Time Complexity

| Operation | Complexity | Notes |
|-----------|-----------|-------|
| **Insert** | O(m) | m = term length |
| **Remove** | O(m) | Plus ref count updates |
| **Contains** | O(m) | With Bloom filter: O(1) rejection |
| **Compact** | O(n) | n = total nodes |
| **Query (fuzzy)** | O(m×d²×b) | d = distance, b = branching |

### Benchmark Results

#### Construction

```
Build from 10,000 terms:
  DynamicDawg:      4.1ms
  DoubleArrayTrie:  3.2ms  (22% faster)
```

#### Runtime Operations

```
Single insertion (amortized):
  DynamicDawg:      ~800ns

Single deletion:
  DynamicDawg:      ~1.2µs

Contains check:
  With Bloom filter:    ~150ns (negative)
  Without Bloom filter: ~350ns (negative)
  Positive lookup:      ~450ns
```

#### Fuzzy Search

```
Query "test" (distance 2) in 10K-term dict:
  DynamicDawg:      42.3µs
  DoubleArrayTrie:  16.3µs  (2.6x faster)
```

### Memory Usage

```
10,000-term dictionary:
  Nodes:          ~250KB
  Suffix cache:   ~32KB
  Bloom filter:   ~12KB
  Total:          ~294KB

vs DoubleArrayTrie: ~100KB (3x smaller)
```

**Trade-off**: DynamicDawg uses more memory for update flexibility

### Compaction Impact

```
After removing 30% of terms:
  Before compaction:  350KB (orphaned nodes)
  After compaction:   210KB (40% reduction)

Compaction time:      ~8ms for 10K terms
```

## When to Use

### Decision Matrix

| Scenario | Recommended | Alternative |
|----------|-------------|-------------|
| **Frequent adds + removes** | ✅ DynamicDawg | - |
| **Append-only** | ⚠️ DoubleArrayTrie | 3x faster |
| **Static dictionary** | ⚠️ DoubleArrayTrie | 3x faster, 3x smaller |
| **Unicode text** | ⚠️ DynamicDawgChar | Correct distances |
| **Maximum performance** | ⚠️ DoubleArrayTrie | Faster queries |
| **Real-time collaboration** | ✅ DynamicDawg | Thread-safe |

### Ideal Use Cases

1. **User Dictionaries**
   - Add custom words during session
   - Remove typos or unwanted entries
   - Personal vocabulary evolves

2. **Session-Specific Terms**
   - Add terms from current document
   - Clear when document closes
   - Dynamic scope-based dictionaries

3. **Collaborative Editing**
   - Multiple users add/remove terms
   - Thread-safe concurrent access
   - Real-time updates

4. **Adaptive Systems**
   - Learn new terms from user input
   - Remove deprecated entries
   - Evolving vocabulary

## Related Documentation

- [Dictionary Layer](../README.md) - Overview of all dictionary types
- [DynamicDawgChar](dynamic-dawg-char.md) - Unicode variant
- [DoubleArrayTrie](double-array-trie.md) - Faster alternative for static/append-only
- [Value Storage](../../09-value-storage/README.md) - Using values with DynamicDawg

## References

### Academic Papers

1. **Blumer, A., Blumer, J., Haussler, D., McConnell, R., & Ehrenfeucht, A. (1987)**. "Complete inverted files for efficient text retrieval and analysis"
   - *Journal of the ACM*, 34(3), 578-595
   - DOI: [10.1145/28869.28873](https://doi.org/10.1145/28869.28873)
   - 📄 DAWG construction algorithms

2. **Crochemore, M., & Vérin, R. (1997)**. "Direct construction of compact directed acyclic word graphs"
   - *Annual Symposium on Combinatorial Pattern Matching*, 116-129
   - DOI: [10.1007/3-540-63220-4_55](https://doi.org/10.1007/3-540-63220-4_55)
   - 📄 Incremental DAWG construction

3. **Inenaga, S., Hoshino, H., Shinohara, A., Takeda, M., & Arikawa, S. (2001)**. "On-line construction of compact directed acyclic word graphs"
   - *Annual Symposium on Combinatorial Pattern Matching*, 83-97
   - DOI: [10.1007/3-540-48194-X_8](https://doi.org/10.1007/3-540-48194-X_8)
   - 📄 Online DAWG modifications

### Textbooks

4. **Gusfield, D. (1997)**. *Algorithms on Strings, Trees, and Sequences*
   - Cambridge University Press, Chapter 6
   - ISBN: 978-0521585194
   - 📚 Suffix structures and DAWGs

## Next Steps

- **Unicode**: Learn about [DynamicDawgChar](dynamic-dawg-char.md)
- **Performance**: Compare with [DoubleArrayTrie](double-array-trie.md)
- **Values**: Explore [Value Storage](../../09-value-storage/README.md)

---

**Navigation**: [← Dictionary Layer](../README.md) | [DoubleArrayTrie](double-array-trie.md) | [Algorithms Home](../../README.md)
