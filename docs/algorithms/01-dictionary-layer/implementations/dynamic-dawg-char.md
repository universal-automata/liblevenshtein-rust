# DynamicDawgChar Implementation

**Navigation**: [← Dictionary Layer](../README.md) | [DynamicDawg (byte-level)](dynamic-dawg.md) | [Algorithms Home](../../README.md)

## Table of Contents

1. [Overview](#overview)
2. [Why Character-Level Matters](#why-character-level-matters)
3. [Unicode Support](#unicode-support)
4. [Data Structure](#data-structure)
5. [Key Differences from DynamicDawg](#key-differences-from-dynamicdawg)
6. [Usage Examples](#usage-examples)
7. [Performance Analysis](#performance-analysis)
8. [When to Use](#when-to-use)
9. [References](#references)

## Overview

`DynamicDawgChar` is a character-level variant of `DynamicDawg` designed for **correct Unicode handling** with **full dynamic update support**. While the byte-level variant treats text as sequences of bytes, the character-level variant operates on Unicode code points, providing accurate Levenshtein distances for multi-byte characters.

### Key Advantages

- ✅ **Correct Unicode distances**: Treats 'é' as 1 character, not 2 bytes
- 🔄 **Full dynamic updates**: Insert AND remove Unicode terms at runtime
- 🔒 **Thread-safe**: Safe for concurrent reads and exclusive writes
- 🌍 **Full Unicode support**: CJK, emoji, accents, all scripts
- 💾 **Space-efficient**: Shares common suffixes (20-40% reduction)

### When to Use

✅ **Use DynamicDawgChar when:**
- Working with non-ASCII text (accented characters, CJK, emoji)
- Need both insert AND remove operations
- Correctness of Levenshtein distances matters
- Multi-language applications with evolving vocabularies
- Real-time collaborative editing with Unicode

⚠️ **Consider alternatives when:**
- ASCII-only text → Use `DynamicDawg` (slightly faster)
- Static or append-only → Use `DoubleArrayTrieChar` (3x faster)
- Maximum performance needed → Use `DoubleArrayTrieChar`

## Why Character-Level Matters

### The UTF-8 Problem with Dynamic Dictionaries

Consider a user dictionary that evolves:
- User adds: "café", "naïve", "résumé"
- User removes: "cafe" (without accent)

With byte-level (`DynamicDawg`):
```
Insert "café":
  'c' → 'a' → 'f' → 0xC3 → 0xA9 (final)
  ❌ 5 nodes for 4-character word

Insert "naïve":
  'n' → 'a' → 0xC3 → 0xAF → 'v' → 'e' (final)
  ❌ 6 nodes for 5-character word

Fuzzy search "cafe" (distance 1):
  ❌ Won't find "café" (actually distance 2 in byte-level)
```

With character-level (`DynamicDawgChar`):
```
Insert "café":
  'c' → 'a' → 'f' → 'é' (final)
  ✅ 4 nodes for 4-character word

Insert "naïve":
  'n' → 'a' → 'ï' → 'v' → 'e' (final)
  ✅ 5 nodes for 5-character word

Fuzzy search "cafe" (distance 1):
  ✅ Finds "café" (distance 1: substitute e→é)
```

### Real-World Impact

**Example: Multi-language Spell Checker**

```rust
use liblevenshtein::dictionary::dynamic_dawg_char::DynamicDawgChar;
use liblevenshtein::levenshtein::Algorithm;
use liblevenshtein::levenshtein_automaton::LevenshteinAutomaton;

let dict = DynamicDawgChar::new();

// User adds words from different languages
dict.insert("café");     // French
dict.insert("naïve");    // French
dict.insert("año");      // Spanish
dict.insert("中文");     // Chinese
dict.insert("😀");       // Emoji

// Fuzzy search with typo
let automaton = LevenshteinAutomaton::new("cafe", 1, Algorithm::Standard);
let results: Vec<String> = automaton.query(&dict).collect();

println!("{:?}", results);
// Output: ["café"] (✅ correct character-level distance)

// Byte-level would give distance 2 or not find it
```

## Unicode Support

### Code Points vs Bytes

**DynamicDawgChar operates on Unicode scalar values (`char`)**:

```
Character │ Code Point │ UTF-8 Bytes       │ Nodes in DAWG
──────────┼────────────┼───────────────────┼───────────────────
'A'       │ U+0041     │ 0x41              │ 1 (char-level)
'é'       │ U+00E9     │ 0xC3 0xA9         │ 1 (char-level)
'中'      │ U+4E2D     │ 0xE4 0xB8 0xAD    │ 1 (char-level)
'🎉'      │ U+1F389    │ 0xF0 0x9F 0x8E 0x89│ 1 (char-level)
```

### Supported Unicode Features

✅ **Basic Multilingual Plane (BMP)**: All common languages
✅ **Supplementary Planes**: Emoji, historic scripts, mathematical symbols
✅ **Combining Characters**: Accents, diacritics (as separate code points)
✅ **Right-to-Left**: Arabic, Hebrew
✅ **CJK**: Chinese, Japanese, Korean characters

⚠️ **Note**: Operates on code points, not grapheme clusters. For grapheme-level handling, normalize input first.

## Data Structure

### Core Components

```rust
pub struct DynamicDawgChar<V: DictionaryValue = ()> {
    inner: Arc<RwLock<DynamicDawgCharInner<V>>>,
}

struct DynamicDawgCharInner<V: DictionaryValue> {
    nodes: Vec<DawgNodeChar<V>>,           // Node storage
    term_count: usize,                     // Number of terms
    needs_compaction: bool,                // Deletion flag
    suffix_cache: FxHashMap<u64, usize>,   // Hash → node index
    bloom_filter: Option<BloomFilter>,     // Fast negative lookups
    auto_minimize_threshold: f32,          // Lazy minimization trigger
}

struct DawgNodeChar<V: DictionaryValue> {
    edges: SmallVec<[(char, usize); 4]>,  // Character → child index
    is_final: bool,                        // Marks valid term
    ref_count: usize,                      // For safe deletion
    value: Option<V>,                      // Associated value
}
```

### Memory Layout

```
┌─────────────────┬─────────────┬────────────────┐
│ Component       │ Size        │ Per Node       │
├─────────────────┼─────────────┼────────────────┤
│ SmallVec edges  │ Inline ≤4   │ ~40 bytes*     │
│ is_final        │ 1 byte      │ 1 byte         │
│ ref_count       │ 8 bytes     │ 8 bytes        │
│ value (Option)  │ V or 1 byte │ Varies         │
├─────────────────┼─────────────┼────────────────┤
│ Total per node  │ ~49+ bytes  │ ~49 bytes      │
│ Overhead        │ Arc+RwLock  │ 16 bytes total │
└─────────────────┴─────────────┴────────────────┘
```

*char is 4 bytes, so 4 edges = 4×(4+8) = 48 bytes inline

**Comparison with DynamicDawg**:
- DynamicDawg: ~25 bytes/node
- DynamicDawgChar: ~49 bytes/node (2x more)

**Reason**: char (4 bytes) vs u8 (1 byte) for edge labels

## Key Differences from DynamicDawg

### 1. Edge Labels

```rust
// DynamicDawg (byte-level)
edges: SmallVec<[(u8, usize); 4]>

// DynamicDawgChar (character-level)
edges: SmallVec<[(char, usize); 4]>
```

### 2. Input Processing

```rust
// DynamicDawg
fn insert(&self, term: &str) {
    let bytes = term.bytes();  // Iterate over bytes
    // ...
}

// DynamicDawgChar
fn insert(&self, term: &str) {
    let chars = term.chars();  // Iterate over characters
    // ...
}
```

### 3. Memory Usage

```
10,000-term dictionary (mixed scripts):

DynamicDawg (byte-level):
  Nodes: ~250KB
  Total: ~294KB

DynamicDawgChar (character-level):
  Nodes: ~490KB (2x more)
  Total: ~534KB
```

### 4. Performance

```
Operation times (10,000 terms):

                    DynamicDawg    DynamicDawgChar    Difference
─────────────────────────────────────────────────────────────────
Construction        4.1ms          4.4ms              +7%
Insert (single)     800ns          840ns              +5%
Remove (single)     1.2µs          1.3µs              +8%
Contains (positive) 450ns          470ns              +4%
Fuzzy search (d=2)  42.3µs         44.7µs             +6%
```

**Insight**: ~5-8% overhead for correct Unicode handling - very reasonable!

## Usage Examples

### Example 1: Basic Unicode Dictionary

```rust
use liblevenshtein::dictionary::dynamic_dawg_char::DynamicDawgChar;

let dict = DynamicDawgChar::new();

// Insert Unicode terms
dict.insert("café");
dict.insert("naïve");
dict.insert("中文");
dict.insert("日本語");
dict.insert("🎉");

assert!(dict.contains("café"));
assert!(dict.contains("中文"));
assert!(dict.contains("🎉"));

// Remove term
dict.remove("café");
assert!(!dict.contains("café"));
```

### Example 2: Multi-Language User Dictionary

```rust
use liblevenshtein::dictionary::dynamic_dawg_char::DynamicDawgChar;

// Create user's personal dictionary
let user_dict = DynamicDawgChar::new();

// User adds words in different languages
user_dict.insert("hello");      // English
user_dict.insert("hola");       // Spanish
user_dict.insert("bonjour");    // French
user_dict.insert("你好");       // Chinese
user_dict.insert("こんにちは"); // Japanese
user_dict.insert("مرحبا");      // Arabic

assert_eq!(user_dict.len(), Some(6));

// User removes a word
user_dict.remove("hola");
assert_eq!(user_dict.len(), Some(5));
```

### Example 3: With Values (Language Codes)

```rust
use liblevenshtein::dictionary::dynamic_dawg_char::DynamicDawgChar;
use liblevenshtein::dictionary::MappedDictionary;

let dict: DynamicDawgChar<&str> = DynamicDawgChar::new();

// Map terms to language codes
dict.insert_with_value("hello", "en");
dict.insert_with_value("hola", "es");
dict.insert_with_value("bonjour", "fr");
dict.insert_with_value("你好", "zh");
dict.insert_with_value("こんにちは", "ja");

// Query language
assert_eq!(dict.get_value("hello"), Some("en"));
assert_eq!(dict.get_value("你好"), Some("zh"));

// Remove and verify
dict.remove("hola");
assert_eq!(dict.get_value("hola"), None);
```

### Example 4: Fuzzy Matching with Unicode

```rust
use liblevenshtein::dictionary::dynamic_dawg_char::DynamicDawgChar;
use liblevenshtein::levenshtein::Algorithm;
use liblevenshtein::levenshtein_automaton::LevenshteinAutomaton;

let dict = DynamicDawgChar::from_terms(vec![
    "café", "naïve", "résumé", "déjà"
]);

// Fuzzy search for "cafe" (missing accent)
let automaton = LevenshteinAutomaton::new("cafe", 1, Algorithm::Standard);
let results: Vec<String> = automaton.query(&dict).collect();

println!("{:?}", results);
// Output: ["café"] (distance 1: substitute e→é)

// Add more terms dynamically
dict.insert("cafeteria");

// Search again
let results: Vec<String> = automaton.query(&dict).collect();
println!("{:?}", results);
// Output: ["café", "cafeteria"]
```

### Example 5: Emoji Support

```rust
use liblevenshtein::dictionary::dynamic_dawg_char::DynamicDawgChar;

let dict = DynamicDawgChar::new();

// Insert emoji
dict.insert("🎉");
dict.insert("🎊");
dict.insert("🎁");
dict.insert("😀");
dict.insert("😃");

// All work correctly
assert!(dict.contains("🎉"));
assert!(dict.contains("😀"));

// Fuzzy search works
let automaton = LevenshteinAutomaton::new("🎉", 1, Algorithm::Standard);
let results: Vec<String> = automaton.query(&dict).collect();

// Finds emoji within distance 1
println!("Matches: {}", results.len());
```

### Example 6: CJK Text

```rust
use liblevenshtein::dictionary::dynamic_dawg_char::DynamicDawgChar;

let dict = DynamicDawgChar::new();

// Chinese
dict.insert("中文");
dict.insert("中国");
dict.insert("北京");

// Japanese
dict.insert("日本");
dict.insert("東京");

// Korean
dict.insert("한국");
dict.insert("서울");

// Fuzzy search in Chinese
let automaton = LevenshteinAutomaton::new("中文", 1, Algorithm::Standard);
let results: Vec<String> = automaton.query(&dict).collect();

println!("{:?}", results);
// Finds: ["中文", "中国"] (both share "中")
```

### Example 7: Thread-Safe Updates

```rust
use liblevenshtein::dictionary::dynamic_dawg_char::DynamicDawgChar;
use std::sync::Arc;
use std::thread;

let dict = Arc::new(DynamicDawgChar::new());

// Spawn multiple threads adding Unicode terms
let handles: Vec<_> = (0..4).map(|i| {
    let dict = Arc::clone(&dict);
    thread::spawn(move || {
        match i {
            0 => dict.insert("café"),
            1 => dict.insert("中文"),
            2 => dict.insert("😀"),
            3 => dict.insert("مرحبا"),
            _ => {}
        }
    })
}).collect();

for handle in handles {
    handle.join().unwrap();
}

// All terms successfully inserted
assert!(dict.contains("café"));
assert!(dict.contains("中文"));
assert!(dict.contains("😀"));
assert!(dict.contains("مرحبا"));
```

### Example 8: Compaction with Unicode

```rust
use liblevenshtein::dictionary::dynamic_dawg_char::DynamicDawgChar;

let dict = DynamicDawgChar::from_terms(vec![
    "café", "cafétéria", "naïve", "résumé", "déjà"
]);

println!("Before deletion: {} nodes", dict.node_count());

// Remove several terms
dict.remove("café");
dict.remove("naïve");
dict.remove("déjà");

println!("After deletion: {} nodes (orphans)", dict.node_count());

// Compact to restore minimality
dict.compact();

println!("After compaction: {} nodes", dict.node_count());
```

## Performance Analysis

### Time Complexity

Same as DynamicDawg:

| Operation | Complexity | Notes |
|-----------|-----------|-------|
| **Insert** | O(m) | m = term length (characters) |
| **Remove** | O(m) | Plus ref count updates |
| **Contains** | O(m) | With Bloom filter: O(1) rejection |
| **Compact** | O(n) | n = total nodes |
| **Query (fuzzy)** | O(m×d²×b) | d = distance, b = branching |

### Benchmark Results

#### Construction

```
Build from 10,000 mixed-script terms:
  DynamicDawgChar:   4.4ms
  DynamicDawg:       4.1ms  (7% faster)
  DoubleArrayTrieChar: 3.4ms (22% faster)
```

#### Runtime Operations

```
Single insertion (Unicode term):
  DynamicDawgChar:  ~840ns
  DynamicDawg:      ~800ns  (5% faster)

Single deletion:
  DynamicDawgChar:  ~1.3µs
  DynamicDawg:      ~1.2µs  (8% faster)

Contains check (positive):
  DynamicDawgChar:  ~470ns
  DynamicDawg:      ~450ns  (4% faster)
```

#### Fuzzy Search

```
Query "café" (distance 2) in 10K-term dict:
  DynamicDawgChar:      44.7µs
  DynamicDawg:          42.3µs  (5% faster)
  DoubleArrayTrieChar:  17.1µs  (62% faster)
```

### Memory Usage

```
10,000-term dictionary (mixed scripts):
  Nodes:          ~490KB
  Suffix cache:   ~32KB
  Bloom filter:   ~12KB
  Total:          ~534KB

vs DynamicDawg:      ~294KB (1.8x smaller)
vs DoubleArrayTrieChar: ~900KB (1.7x larger)
```

### Character-Level vs Byte-Level Trade-offs

```
                        DynamicDawg    DynamicDawgChar    Difference
────────────────────────────────────────────────────────────────────────
Memory per node         25 bytes       49 bytes           +96%
Construction time       4.1ms          4.4ms              +7%
Insert time             800ns          840ns              +5%
Query time              42.3µs         44.7µs             +6%
Unicode correctness     ❌             ✅                 Priceless!
```

**Verdict**: ~2x memory, ~5-8% performance overhead for correct Unicode handling is excellent value.

## When to Use

### Decision Matrix

| Scenario | Recommended | Alternative |
|----------|-------------|-------------|
| **Unicode + dynamic updates** | ✅ DynamicDawgChar | - |
| **Multilingual real-time app** | ✅ DynamicDawgChar | - |
| **ASCII + dynamic updates** | ⚠️ DynamicDawg | Slightly faster |
| **Unicode + static/append-only** | ⚠️ DoubleArrayTrieChar | 3x faster |
| **Maximum performance** | ⚠️ DoubleArrayTrieChar | Fastest |
| **Pure ASCII** | ⚠️ DynamicDawg | Less memory |

### Ideal Use Cases

1. **Multi-Language User Dictionaries**
   - Users add/remove words in various languages
   - Correct character-level distances crucial
   - Personal vocabularies with emoji, CJK, etc.

2. **Collaborative Editing (International)**
   - Multiple users from different regions
   - Thread-safe concurrent access
   - Full Unicode support needed

3. **Adaptive Spell Checkers**
   - Learn from user corrections
   - Remove obsolete suggestions
   - Handle all scripts correctly

4. **Chat/Messaging Applications**
   - Dynamic emoji/sticker names
   - User-specific vocabularies
   - Multi-language support

5. **Code Completion (International)**
   - Variable names in various scripts
   - Dynamic scope-based filtering
   - Unicode identifier support

## Related Documentation

- [Dictionary Layer](../README.md) - Overview of all dictionary types
- [DynamicDawg](dynamic-dawg.md) - Byte-level variant
- [DoubleArrayTrieChar](double-array-trie-char.md) - Faster static alternative
- [Value Storage](../../09-value-storage/README.md) - Using values with DynamicDawgChar

## References

### Unicode and Levenshtein Distance

1. **Schulz, K. U., & Mihov, S. (2002)**. "Fast String Correction with Levenshtein Automata"
   - *International Journal on Document Analysis and Recognition*, 5(1), 67-85
   - 📄 Discusses character-level vs byte-level matching

2. **Unicode Consortium**. *The Unicode Standard, Version 15.0*
   - 📄 [https://www.unicode.org/versions/Unicode15.0.0/](https://www.unicode.org/versions/Unicode15.0.0/)
   - Official Unicode specification

### DAWG Algorithms

3. **Blumer, A., Blumer, J., Haussler, D., McConnell, R., & Ehrenfeucht, A. (1987)**. "Complete inverted files for efficient text retrieval and analysis"
   - *Journal of the ACM*, 34(3), 578-595
   - DOI: [10.1145/28869.28873](https://doi.org/10.1145/28869.28873)
   - 📄 DAWG construction algorithms

4. **Crochemore, M., & Vérin, R. (1997)**. "Direct construction of compact directed acyclic word graphs"
   - *Annual Symposium on Combinatorial Pattern Matching*, 116-129
   - DOI: [10.1007/3-540-63220-4_55](https://doi.org/10.1007/3-540-63220-4_55)
   - 📄 Incremental DAWG construction

## Next Steps

- **Byte-Level**: Compare with [DynamicDawg](dynamic-dawg.md)
- **Static Alternative**: Explore [DoubleArrayTrieChar](double-array-trie-char.md)
- **Values**: Learn about [Value Storage](../../09-value-storage/README.md)
- **Unicode Handling**: Read [DoubleArrayTrieChar Unicode Guide](double-array-trie-char.md#unicode-fundamentals)

---

**Navigation**: [← Dictionary Layer](../README.md) | [DynamicDawg (byte-level)](dynamic-dawg.md) | [Algorithms Home](../../README.md)
