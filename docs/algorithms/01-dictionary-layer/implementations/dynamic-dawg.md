# DynamicDawg Implementation

**Navigation**: [← Dictionary Layer](../README.md) | [DoubleArrayTrie](double-array-trie.md) | [Algorithms Home](../../README.md)

## Table of Contents

1. [Overview](#overview)
2. [Theory: DAWG Structure](#theory-dawg-structure)
3. [Dynamic Modifications](#dynamic-modifications)
4. [Data Structure](#data-structure)
5. [Key Algorithms](#key-algorithms)
6. [Usage Examples](#usage-examples)
7. [Performance Analysis](#performance-analysis)
8. [When to Use](#when-to-use)
9. [References](#references)

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
