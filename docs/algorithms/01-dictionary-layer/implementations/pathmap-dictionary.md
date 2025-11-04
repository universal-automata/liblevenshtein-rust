# PathMapDictionary Implementation

**Navigation**: [← Dictionary Layer](../README.md) | [DoubleArrayTrie](double-array-trie.md) | [Algorithms Home](../../README.md)

## Table of Contents

1. [Overview](#overview)
2. [Theory: Persistent Data Structures](#theory-persistent-data-structures)
3. [PathMap Library](#pathmap-library)
4. [Data Structure](#data-structure)
5. [Usage Examples](#usage-examples)
6. [Performance Analysis](#performance-analysis)
7. [When to Use](#when-to-use)
8. [References](#references)

## Overview

`PathMapDictionary` is a dictionary backend built on the **PathMap** library, which provides persistent (immutable) trie structures with structural sharing. It's the simplest dynamic dictionary option but trades performance for simplicity and immutability guarantees.

### Key Advantages

- 🔄 **Full dynamic updates**: Insert AND remove at runtime
- 🔒 **Thread-safe**: Safe concurrent reads, exclusive writes
- 📦 **Simple implementation**: Thin wrapper around PathMap
- 💎 **Persistent semantics**: Structural sharing between versions
- 🎯 **Easy to use**: Straightforward API

### Key Trade-offs

- ⚠️ **Slower queries**: 2-3x slower than DoubleArrayTrie
- ⚠️ **Higher memory**: More overhead than specialized tries
- ⚠️ **Feature-gated**: Requires `pathmap-backend` feature

### When to Use

✅ **Use PathMapDictionary when:**
- Simplicity is more important than maximum performance
- Need full insert/remove capabilities
- Prefer well-tested external library
- Experimenting or prototyping

⚠️ **Consider alternatives when:**
- Performance is critical → Use `DoubleArrayTrie` (3x faster)
- Need maximum efficiency → Use `DynamicDawg`
- Unicode required → Use `PathMapDictionaryChar`

## Theory: Persistent Data Structures

### What are Persistent Data Structures?

**Persistent** data structures preserve previous versions after modifications through **structural sharing**.

**Example**: Adding "test" to dictionary containing ["best", "rest"]

**Mutable approach** (traditional):
```
Before:  root → 'b'/'r' → 'est'
After:   root → 'b'/'r'/'t' → 'est'  (modifies in-place)
Old version lost!
```

**Persistent approach** (PathMap):
```
Version 1:  root₁ → 'b'/'r' → 'est'
Version 2:  root₂ → 'b'/'r'/'t' → 'est'
                     ↑   ↑    ↑
                     └───┴────┘
                   Shared nodes (not copied)

Both versions coexist!
```

### Structural Sharing

Only changed path from root is copied; rest is shared:

```
Insert "team" into {"test", "testing"}:

Old tree:
  root → 't' → 'e' → 's' → 't' (final)
                      ↓
                     'i' → 'n' → 'g' (final)

New tree (after adding "team"):
  root' → 't' → 'e' → 's' → 't' (final)  ← Shared
                ↓       ↓
               'a'     'i' → 'n' → 'g' (final)  ← Shared
                ↓
               'm' (final)  ← New

Nodes marked "Shared" are reused, not copied
```

**Memory**: Only O(m) new nodes for m-character insert

## PathMap Library

### External Dependency

PathMapDictionary wraps the `pathmap` crate:
- **Repository**: [https://github.com/Adam-Vandervorst/PathMap](https://github.com/Adam-Vandervorst/PathMap)
- **Purpose**: Persistent trie data structure
- **License**: MIT

### Enabling PathMapDictionary

Add to `Cargo.toml`:

```toml
[dependencies]
liblevenshtein = { version = "0.4", features = ["pathmap-backend"] }
```

Or use CLI:

```bash
cargo add liblevenshtein --features pathmap-backend
```

### PathMap Features

- **Persistent**: Old versions preserved
- **Structural sharing**: Efficient memory use
- **Thread-safe**: Immutable data structures
- **Generic values**: Map terms to arbitrary types

## Data Structure

### Core Components

```rust
pub struct PathMapDictionary<V: DictionaryValue = ()> {
    map: Arc<RwLock<PathMap<V>>>,       // Underlying PathMap
    term_count: Arc<RwLock<usize>>,     // Term count tracking
}
```

### Wrapper Design

PathMapDictionary is a thin wrapper that:
1. Manages PathMap lifecycle
2. Tracks term count
3. Provides liblevenshtein Dictionary trait
4. Handles thread safety via RwLock

### Memory Layout

```
┌─────────────────┬─────────────────┐
│ Component       │ Overhead        │
├─────────────────┼─────────────────┤
│ Arc pointers    │ 16 bytes        │
│ RwLock          │ 8 bytes         │
│ PathMap         │ ~32 bytes/node  │
│ term_count      │ 8 bytes         │
└─────────────────┴─────────────────┘
```

**Per-node overhead**: ~32 bytes (HashMap-based)

**Example**: 10,000-term dictionary ≈ 320 KB

## Usage Examples

### Example 1: Basic Usage

```rust
use liblevenshtein::dictionary::pathmap::PathMapDictionary;

// Create empty dictionary
let dict: PathMapDictionary<()> = PathMapDictionary::new();

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

### Example 2: From Existing Terms

```rust
use liblevenshtein::dictionary::pathmap::PathMapDictionary;

let dict = PathMapDictionary::from_terms(vec![
    "algorithm",
    "approximate",
    "automaton",
]);

assert!(dict.contains("algorithm"));
assert_eq!(dict.len(), Some(3));

// Add more terms
dict.insert("analysis");
assert_eq!(dict.len(), Some(4));
```

### Example 3: With Values

```rust
use liblevenshtein::dictionary::pathmap::PathMapDictionary;
use liblevenshtein::dictionary::MappedDictionary;

// Map terms to category IDs
let dict: PathMapDictionary<u32> = PathMapDictionary::from_terms_with_values(vec![
    ("test", 1),
    ("testing", 1),
    ("production", 2),
]);

// Query values
assert_eq!(dict.get_value("test"), Some(1));
assert_eq!(dict.get_value("production"), Some(2));

// Update value
dict.insert_with_value("test", 99);
assert_eq!(dict.get_value("test"), Some(99));
```

### Example 4: Fuzzy Search

```rust
use liblevenshtein::dictionary::pathmap::PathMapDictionary;
use liblevenshtein::levenshtein::Algorithm;
use liblevenshtein::levenshtein_automaton::LevenshteinAutomaton;

let dict = PathMapDictionary::from_terms(vec![
    "test", "testing", "tested", "best", "rest"
]);

// Fuzzy search
let automaton = LevenshteinAutomaton::new("tset", 1, Algorithm::Standard);
let results: Vec<String> = automaton.query(&dict).collect();

println!("{:?}", results);
// Output: ["test"] (distance 1: transposition)
```

### Example 5: Thread-Safe Updates

```rust
use liblevenshtein::dictionary::pathmap::PathMapDictionary;
use std::sync::Arc;
use std::thread;

let dict = Arc::new(PathMapDictionary::from_terms(vec!["initial"]));

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

### Example 6: Dynamic User Dictionary

```rust
use liblevenshtein::dictionary::pathmap::PathMapDictionary;

// User's personal dictionary
let user_dict = PathMapDictionary::new();

// User adds custom words
user_dict.insert("refactoring");
user_dict.insert("debugging");
user_dict.insert("profiling");

assert_eq!(user_dict.len(), Some(3));

// User removes a word
user_dict.remove("debugging");
assert_eq!(user_dict.len(), Some(2));

// Check existence
assert!(user_dict.contains("refactoring"));
assert!(!user_dict.contains("debugging"));
```

### Example 7: Metadata Storage

```rust
use liblevenshtein::dictionary::pathmap::PathMapDictionary;
use liblevenshtein::dictionary::MappedDictionary;

#[derive(Clone, Debug)]
struct TermMetadata {
    frequency: u32,
    last_used: u64,
}

impl liblevenshtein::dictionary::DictionaryValue for TermMetadata {}

let dict: PathMapDictionary<TermMetadata> = PathMapDictionary::new();

// Add terms with metadata
dict.insert_with_value("test", TermMetadata {
    frequency: 100,
    last_used: 1234567890,
});

dict.insert_with_value("testing", TermMetadata {
    frequency: 50,
    last_used: 1234567891,
});

// Query metadata
if let Some(meta) = dict.get_value("test") {
    println!("Frequency: {}", meta.frequency);
}
```

### Example 8: Prototyping

```rust
use liblevenshtein::dictionary::pathmap::PathMapDictionary;
use liblevenshtein::levenshtein::Algorithm;
use liblevenshtein::levenshtein_automaton::LevenshteinAutomaton;

// Quick prototype for fuzzy matching
fn prototype_fuzzy_matcher(words: Vec<&str>, query: &str) {
    let dict = PathMapDictionary::from_terms(words);

    let automaton = LevenshteinAutomaton::new(query, 2, Algorithm::Standard);
    let results: Vec<String> = automaton.query(&dict).collect();

    println!("Matches for '{}': {:?}", query, results);
}

prototype_fuzzy_matcher(
    vec!["hello", "world", "test"],
    "helo"  // Typo
);
// Output: Matches for 'helo': ["hello"]
```

## Performance Analysis

### Time Complexity

| Operation | Complexity | Notes |
|-----------|-----------|-------|
| **Insert** | O(m log n) | m = term length, n = dict size |
| **Remove** | O(m log n) | HashMap operations |
| **Contains** | O(m log n) | Tree traversal + lookups |
| **Fuzzy search** | O(m×d²×b×log n) | Additional log factor |

### Benchmark Results

#### Construction

```
Build from 10,000 terms:
  PathMapDictionary:  3.5ms
  DoubleArrayTrie:    3.2ms   (8% faster)
  DynamicDawg:        4.1ms   (15% slower)
```

#### Runtime Operations

```
Single insertion:
  PathMapDictionary:  ~2.1µs
  DynamicDawg:        ~800ns  (2.6x faster)
  DoubleArrayTrie:    N/A (append-only)

Single deletion:
  PathMapDictionary:  ~2.5µs
  DynamicDawg:        ~1.2µs  (2x faster)

Contains check:
  PathMapDictionary:  ~350ns
  DoubleArrayTrie:    ~120ns  (2.9x faster)
  DynamicDawg:        ~450ns  (slower)
```

#### Fuzzy Search

```
Query "test" (distance 1) in 10K-term dict:
  PathMapDictionary:  38.7µs
  DoubleArrayTrie:    12.9µs  (3x faster)
  DynamicDawg:        42.3µs  (similar)

Query "test" (distance 2):
  PathMapDictionary:  91.2µs
  DoubleArrayTrie:    16.3µs  (5.6x faster)
  DynamicDawg:        68.9µs  (1.3x faster)
```

### Memory Usage

```
10,000-term dictionary:
  PathMapDictionary:  ~320 KB
  DoubleArrayTrie:    ~100 KB  (3.2x smaller)
  DynamicDawg:        ~294 KB  (similar)

Memory overhead:
  PathMapDictionary:  ~32 bytes/node (HashMap)
  DoubleArrayTrie:    ~10 bytes/state
  DynamicDawg:        ~25 bytes/node
```

### Comparison Summary

```
                    Construction  Memory   Contains  Fuzzy(d=2)  Insert  Remove
─────────────────────────────────────────────────────────────────────────────────
PathMapDictionary   3.5ms        320KB    350ns     91.2µs      2.1µs   2.5µs
DoubleArrayTrie     3.2ms        100KB    120ns     16.3µs      N/A     N/A
DynamicDawg         4.1ms        294KB    450ns     68.9µs      800ns   1.2µs
```

**Verdict**: PathMapDictionary is 2-3x slower than optimized alternatives, but provides simplicity and full dynamic updates.

## When to Use

### Decision Matrix

| Scenario | Recommended | Reason |
|----------|-------------|--------|
| **Prototyping** | ✅ PathMapDictionary | Quick to use |
| **Simple applications** | ✅ PathMapDictionary | Easy API |
| **Maximum performance** | ⚠️ DoubleArrayTrie | 3x faster |
| **Memory-constrained** | ⚠️ DoubleArrayTrie | 3x smaller |
| **Dynamic + fast** | ⚠️ DynamicDawg | 2x faster updates |

### Ideal Use Cases

1. **Prototyping**
   - Quick experiments
   - Proof of concept
   - Algorithm validation

2. **Small Dictionaries**
   - <1000 terms
   - Performance not critical
   - Simplicity valued

3. **Educational/Learning**
   - Understanding fuzzy matching
   - Teaching examples
   - Simple demonstrations

4. **Low-Traffic Applications**
   - Infrequent queries
   - Small user base
   - Development/testing

### When to Migrate Away

Consider switching to specialized dictionaries when:

✅ **DoubleArrayTrie** if:
- Query performance becomes bottleneck
- Dictionary becomes mostly static
- Memory usage is concern

✅ **DynamicDawg** if:
- Frequent updates needed
- Better update performance required
- Still need full dynamic capabilities

## Related Documentation

- [Dictionary Layer](../README.md) - Overview of all dictionary types
- [DoubleArrayTrie](double-array-trie.md) - Faster alternative
- [DynamicDawg](dynamic-dawg.md) - Faster dynamic alternative
- [PathMapDictionaryChar](pathmap-dictionary-char.md) - Unicode variant
- [Value Storage](../../09-value-storage/README.md) - Using values

## References

### PathMap Library

1. **PathMap Repository**
   - 📦 [https://github.com/Adam-Vandervorst/PathMap](https://github.com/Adam-Vandervorst/PathMap)
   - Underlying persistent trie implementation

### Persistent Data Structures

2. **Okasaki, C. (1999)**. *Purely Functional Data Structures*
   - Cambridge University Press
   - ISBN: 978-0521663502
   - 📚 Comprehensive coverage of persistent structures

3. **Driscoll, J. R., Sarnak, N., Sleator, D. D., & Tarjan, R. E. (1989)**. "Making data structures persistent"
   - *Journal of Computer and System Sciences*, 38(1), 86-124
   - DOI: [10.1016/0022-0000(89)90034-2](https://doi.org/10.1016/0022-0000(89)90034-2)
   - 📄 Foundational paper on persistence

### Trie Structures

4. **Fredkin, E. (1960)**. "Trie memory"
   - *Communications of the ACM*, 3(9), 490-499
   - DOI: [10.1145/367390.367400](https://doi.org/10.1145/367390.367400)
   - 📄 Original trie paper

## Next Steps

- **Performance**: Compare with [DoubleArrayTrie](double-array-trie.md)
- **Dynamic**: Explore [DynamicDawg](dynamic-dawg.md)
- **Unicode**: Check [PathMapDictionaryChar](pathmap-dictionary-char.md)
- **Values**: Learn about [Value Storage](../../09-value-storage/README.md)

---

**Navigation**: [← Dictionary Layer](../README.md) | [DoubleArrayTrie](double-array-trie.md) | [Algorithms Home](../../README.md)
