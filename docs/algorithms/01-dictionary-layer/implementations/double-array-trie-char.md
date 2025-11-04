# DoubleArrayTrieChar Implementation

**Navigation**: [← Dictionary Layer](../README.md) | [DoubleArrayTrie (byte-level)](double-array-trie.md) | [Algorithms Home](../../README.md)

## Table of Contents

1. [Overview](#overview)
2. [Why Character-Level Matters](#why-character-level-matters)
3. [Unicode Fundamentals](#unicode-fundamentals)
4. [Data Structure](#data-structure)
5. [Construction Algorithm](#construction-algorithm)
6. [Usage Examples](#usage-examples)
7. [Performance Analysis](#performance-analysis)
8. [Byte-Level vs Character-Level](#byte-level-vs-character-level)
9. [Advanced Topics](#advanced-topics)
10. [References](#references)

## Overview

`DoubleArrayTrieChar` is a character-level variant of `DoubleArrayTrie` designed for **correct Unicode handling**. While the byte-level variant treats text as sequences of bytes (UTF-8 encoding units), the character-level variant operates on Unicode code points, providing accurate Levenshtein distances for multi-byte characters.

### Key Advantages

- ✅ **Correct Unicode distances**: Treats 'é' as 1 character, not 2 bytes
- 🌍 **Full Unicode support**: CJK, emoji, accents, combining marks
- 📊 **~5% overhead**: Minimal performance cost vs byte-level
- 🎯 **Same cache efficiency**: Maintains BASE/CHECK array benefits
- 🔧 **Append-only updates**: Can add Unicode terms at runtime

### When to Use

✅ **Use DoubleArrayTrieChar when:**
- Working with non-ASCII text (accented characters, CJK, emoji)
- Correctness of Levenshtein distances matters
- Multi-language applications
- User-facing applications with diverse character sets

⚠️ **Use DoubleArrayTrie instead when:**
- Working exclusively with ASCII/Latin-1 text
- Absolute maximum performance is critical
- Memory footprint must be minimized
- Byte-level semantics are acceptable

## Why Character-Level Matters

### The UTF-8 Problem

UTF-8 encodes Unicode code points using 1-4 bytes. Multi-byte characters cause incorrect distances with byte-level algorithms.

**Example: "café"**

```
Byte-level representation:
'c' = 0x63      (1 byte)
'a' = 0x61      (1 byte)
'f' = 0x66      (1 byte)
'é' = 0xC3 0xA9 (2 bytes)  ← é is TWO bytes
Total: 5 bytes

Character-level representation:
'c', 'a', 'f', 'é'
Total: 4 characters
```

### Distance Calculation Differences

Computing distance from "cafe" to "café":

```
Byte-level (DoubleArrayTrie):
  "cafe"  = [c, a, f, e]           (4 bytes)
  "café"  = [c, a, f, 0xC3, 0xA9]  (5 bytes)

  Distance = 2 operations:
    1. Delete 'e'
    2. Insert 0xC3
    3. Insert 0xA9

  ❌ Wrong! Human expectation is distance 1

Character-level (DoubleArrayTrieChar):
  "cafe" = [c, a, f, e]    (4 chars)
  "café" = [c, a, f, é]    (4 chars)

  Distance = 1 operation:
    1. Substitute 'e' → 'é'

  ✅ Correct! Matches human intuition
```

### Real-World Examples

#### Example 1: Spanish

```rust
// Byte-level: Incorrect distances
let byte_dist = levenshtein_bytes("año", "ano");
assert_eq!(byte_dist, 2);  // ❌ ñ is 2 bytes

// Character-level: Correct
let char_dist = levenshtein_chars("año", "ano");
assert_eq!(char_dist, 1);  // ✅ Substitute ñ ↔ n
```

#### Example 2: Chinese

```rust
// Byte-level: Meaningless
let byte_dist = levenshtein_bytes("中文", "中国");
assert_eq!(byte_dist, 6);  // ❌ Each Chinese char is 3 bytes

// Character-level: Correct
let char_dist = levenshtein_chars("中文", "中国");
assert_eq!(char_dist, 1);  // ✅ Substitute 文 ↔ 国
```

#### Example 3: Emoji

```rust
// Byte-level: Very wrong
let byte_dist = levenshtein_bytes("🎉", "🎊");
assert_eq!(byte_dist, 4);  // ❌ Each emoji is 4 bytes

// Character-level: Correct
let char_dist = levenshtein_chars("🎉", "🎊");
assert_eq!(char_dist, 1);  // ✅ Substitute one emoji for another
```

## Unicode Fundamentals

### Code Points vs Bytes

**Unicode Code Point**: Abstract character identity (U+0000 to U+10FFFF)
**UTF-8 Encoding**: Variable-length byte encoding (1-4 bytes per code point)

```
Character │ Code Point │ UTF-8 Bytes       │ Byte Count
──────────┼────────────┼───────────────────┼────────────
'A'       │ U+0041     │ 0x41              │ 1
'é'       │ U+00E9     │ 0xC3 0xA9         │ 2
'中'      │ U+4E2D     │ 0xE4 0xB8 0xAD    │ 3
'🎉'      │ U+1F389    │ 0xF0 0x9F 0x8E 0x89│ 4
```

### Rust's char Type

Rust's `char` type represents a **Unicode scalar value** (code point):

```rust
let c: char = 'é';           // Single character
let bytes: &[u8] = "é".as_bytes();  // [0xC3, 0xA9]

assert_eq!(c.len_utf8(), 2);  // Takes 2 bytes in UTF-8
```

### Grapheme Clusters (Advanced)

Some "characters" are multiple code points:

```
"é" can be:
  Single code point: U+00E9 (é)
  OR
  Two code points: U+0065 + U+0301 (e + combining acute accent)
```

`DoubleArrayTrieChar` operates on **code points**, not grapheme clusters. For grapheme-level handling, additional normalization is needed (see [Advanced Topics](#advanced-topics)).

## Data Structure

### Core Components

```rust
pub struct DoubleArrayTrieChar<V: DictionaryValue = ()> {
    shared: DATSharedChar<V>,
}

pub(crate) struct DATSharedChar<V: DictionaryValue = ()> {
    pub(crate) base: Arc<Vec<i32>>,      // BASE array
    pub(crate) check: Arc<Vec<i32>>,     // CHECK array
    pub(crate) is_final: Arc<Vec<bool>>, // Final state markers
    pub(crate) edges: Arc<Vec<Vec<char>>>, // Character labels (not u8!)
    pub(crate) values: Arc<Vec<Option<V>>>, // Associated values
}
```

### Key Difference from DoubleArrayTrie

The critical difference is the `edges` field:

```rust
// DoubleArrayTrie (byte-level)
edges: Arc<Vec<Vec<u8>>>    // Edge labels are bytes

// DoubleArrayTrieChar (character-level)
edges: Arc<Vec<Vec<char>>>  // Edge labels are characters
```

### Memory Layout

For a dictionary with N states:

```
┌────────────────┬────────┬─────────────┐
│ Component      │ Size   │ Per State   │
├────────────────┼────────┼─────────────┤
│ BASE array     │ 4N     │ 4 bytes     │
│ CHECK array    │ 4N     │ 4 bytes     │
│ is_final       │ N      │ 1 byte      │
│ edges (chars)  │ ~8N    │ ~8 bytes*   │
│ values (none)  │ N      │ 1 byte      │
├────────────────┼────────┼─────────────┤
│ Total          │ ~18N   │ ~18 bytes   │
└────────────────┴────────┴─────────────┘
```

*char is 4 bytes, average ~2 edges per state = 8 bytes

**Comparison**:
- DoubleArrayTrie: ~10 bytes/state
- DoubleArrayTrieChar: ~18 bytes/state (80% more)

**Example**: 50,000-term dictionary
- Byte-level: ~500 KB
- Char-level: ~900 KB (+80%)

## Construction Algorithm

### Overview

Construction is nearly identical to byte-level, but operates on `char` sequences:

```rust
pub fn from_terms<I, S>(terms: I) -> Self
where
    I: IntoIterator<Item = S>,
    S: AsRef<str>,
{
    // Step 1: Collect terms as character sequences
    let mut char_terms: Vec<Vec<char>> = terms
        .into_iter()
        .map(|s| s.as_ref().chars().collect())  // ← chars(), not bytes()
        .collect();

    // Step 2: Sort lexicographically
    char_terms.sort_unstable();
    char_terms.dedup();

    // Step 3: Build via incremental construction
    let mut builder = DoubleArrayTrieCharBuilder::new();
    for term in char_terms {
        builder.insert(&term, ());
    }

    builder.build()
}
```

### Character Code as Edge Label

Transitions use `char` as u32:

```rust
fn descend(&self, label: char) -> Option<Self> {
    let base = self.shared.base[self.state];
    if base < 0 {
        return None;
    }

    // Convert char to u32 for indexing
    let char_code = label as u32;
    let next = (base as u32).wrapping_add(char_code) as usize;

    if next >= self.shared.check.len() ||
       self.shared.check[next] != self.state as i32 {
        return None;
    }

    Some(/* new zipper at state 'next' */)
}
```

### Handling Large Character Codes

Unicode code points range from U+0000 to U+10FFFF (~1.1 million possible values). However:

- Most applications use a small subset (<10,000 unique characters)
- BASE value selection adapts to actual character distribution
- Arrays grow only as needed for actual states

**Example**:
```rust
// Only these characters used: 'a', 'é', '中', '🎉'
// Code points: 0x61, 0xE9, 0x4E2D, 0x1F389

// Arrays only allocate states for these specific codes
// No need for 1.1M-entry arrays!
```

## Usage Examples

### Example 1: Basic Unicode Dictionary

```rust
use liblevenshtein::dictionary::double_array_trie_char::DoubleArrayTrieChar;

let dict = DoubleArrayTrieChar::from_terms(vec![
    "café",      // French: accented e
    "naïve",     // French: diaeresis
    "año",       // Spanish: ñ
    "中文",      // Chinese
    "日本語",    // Japanese
    "한국어",    // Korean
    "🎉🎊",      // Emoji
]);

// All terms correctly recognized
assert!(dict.contains("café"));
assert!(dict.contains("中文"));
assert!(dict.contains("🎉🎊"));

assert_eq!(dict.len(), Some(7));
```

### Example 2: Correct Unicode Distances

```rust
use liblevenshtein::dictionary::double_array_trie_char::DoubleArrayTrieChar;
use liblevenshtein::levenshtein::Algorithm;
use liblevenshtein::levenshtein_automaton::LevenshteinAutomaton;

let dict = DoubleArrayTrieChar::from_terms(vec![
    "café", "naïve", "año"
]);

// Find terms within distance 1 of "cafe" (no accents)
let automaton = LevenshteinAutomaton::new("cafe", 1, Algorithm::Standard);
let results: Vec<String> = automaton.query(&dict).collect();

// "café" matches! (distance 1: substitute e → é)
assert!(results.contains(&"café".to_string()));

// Byte-level would give distance 2 (incorrect)
```

### Example 3: Multi-Language Search

```rust
use liblevenshtein::dictionary::double_array_trie_char::DoubleArrayTrieChar;
use liblevenshtein::levenshtein::Algorithm;
use liblevenshtein::levenshtein_automaton::LevenshteinAutomaton;

// Mixed-language dictionary
let dict = DoubleArrayTrieChar::from_terms(vec![
    // English
    "hello", "world",
    // Spanish
    "hola", "mundo",
    // French
    "bonjour", "monde",
    // Chinese
    "你好", "世界",
    // Japanese
    "こんにちは", "世界",
]);

// Fuzzy search in Chinese
let automaton = LevenshteinAutomaton::new("你好", 1, Algorithm::Standard);
let results: Vec<String> = automaton.query(&dict).collect();

println!("Chinese matches: {:?}", results);
// Finds: ["你好"] (exact match)

// Fuzzy search with typo
let automaton = LevenshteinAutomaton::new("bonjpur", 2, Algorithm::Standard);
let results: Vec<String> = automaton.query(&dict).collect();

println!("French matches: {:?}", results);
// Finds: ["bonjour"] (distance 2: substitute p→o, delete p)
```

### Example 4: Value Storage with Unicode

```rust
use liblevenshtein::dictionary::double_array_trie_char::DoubleArrayTrieChar;

// Map terms to language codes
let dict = DoubleArrayTrieChar::from_terms_with_values(vec![
    ("hello", "en"),
    ("world", "en"),
    ("hola", "es"),
    ("mundo", "es"),
    ("bonjour", "fr"),
    ("monde", "fr"),
    ("你好", "zh"),
    ("世界", "zh"),
]);

// Query language for each term
assert_eq!(dict.get_value("hello"), Some("en"));
assert_eq!(dict.get_value("hola"), Some("es"));
assert_eq!(dict.get_value("你好"), Some("zh"));

// Filter by language
let french_terms: Vec<String> = /* iterate and filter by "fr" */;
```

### Example 5: Emoji Handling

```rust
use liblevenshtein::dictionary::double_array_trie_char::DoubleArrayTrieChar;

let dict = DoubleArrayTrieChar::from_terms(vec![
    "🎉",     // Party popper
    "🎊",     // Confetti ball
    "🎁",     // Wrapped gift
    "🎂",     // Birthday cake
    "🎈",     // Balloon
]);

// All single-character emoji
assert!(dict.contains("🎉"));
assert!(dict.contains("🎂"));

// Fuzzy matching works correctly
let automaton = LevenshteinAutomaton::new("🎉", 1, Algorithm::Standard);
let results: Vec<String> = automaton.query(&dict).collect();

// Finds nearby emoji (distance 1 substitutions)
println!("{:?}", results);
// Output: ["🎉", "🎊", "🎁", "🎂", "🎈"] (all within distance 1)
```

### Example 6: Combining Characters

```rust
use liblevenshtein::dictionary::double_array_trie_char::DoubleArrayTrieChar;

// Two representations of "é"
let composed = "café";        // é as single code point (U+00E9)
let decomposed = "cafe\u{0301}";  // e (U+0065) + combining acute (U+0301)

let dict = DoubleArrayTrieChar::from_terms(vec![composed]);

// Exact match requires same normalization
assert!(dict.contains(composed));
assert!(!dict.contains(decomposed));  // Different representation!

// For grapheme-level matching, normalize first (see Advanced Topics)
```

### Example 7: CJK Text Processing

```rust
use liblevenshtein::dictionary::double_array_trie_char::DoubleArrayTrieChar;
use liblevenshtein::levenshtein::Algorithm;
use liblevenshtein::levenshtein_automaton::LevenshteinAutomaton;

// Chinese city names
let dict = DoubleArrayTrieChar::from_terms(vec![
    "北京", // Beijing
    "上海", // Shanghai
    "广州", // Guangzhou
    "深圳", // Shenzhen
]);

// Fuzzy search for "北京" with typo
let automaton = LevenshteinAutomaton::new("北亰", 1, Algorithm::Standard);
let results: Vec<String> = automaton.query(&dict).collect();

println!("{:?}", results);
// Finds: ["北京"] (distance 1: substitute 亰 → 京)

// Character-level distances are meaningful for CJK
```

### Example 8: Runtime Insertions

```rust
use liblevenshtein::dictionary::double_array_trie_char::DoubleArrayTrieChar;

let mut dict = DoubleArrayTrieChar::from_terms(vec![
    "hello", "world"
]);

// Add Unicode term at runtime
dict.insert("你好");

assert!(dict.contains("hello"));
assert!(dict.contains("你好"));

// Supports mixed scripts
dict.insert("مرحبا");  // Arabic
dict.insert("שלום");    // Hebrew
dict.insert("Привет");  // Russian

assert!(dict.contains("مرحبا"));
```

### Example 9: Zipper Navigation

```rust
use liblevenshtein::dictionary::double_array_trie_char::DoubleArrayTrieChar;
use liblevenshtein::dictionary::double_array_trie_char_zipper::DoubleArrayTrieCharZipper;
use liblevenshtein::dictionary::zipper::{DictZipper, ValuedDictZipper};

let dict = DoubleArrayTrieChar::from_terms_with_values(vec![
    ("café", 1),
    ("中文", 2),
]);

let zipper = DoubleArrayTrieCharZipper::new_from_dict(&dict);

// Navigate character by character (not byte by byte!)
let cafe = zipper
    .descend('c')
    .and_then(|z| z.descend('a'))
    .and_then(|z| z.descend('f'))
    .and_then(|z| z.descend('é'))  // Single character!
    .unwrap();

assert!(cafe.is_final());
assert_eq!(cafe.value(), Some(1));
assert_eq!(cafe.path(), vec!['c', 'a', 'f', 'é']);

// CJK navigation
let chinese = zipper
    .descend('中')
    .and_then(|z| z.descend('文'))
    .unwrap();

assert_eq!(chinese.value(), Some(2));
assert_eq!(chinese.path(), vec!['中', '文']);
```

## Performance Analysis

### Benchmark Results

#### Construction (10,000 terms)

```
ASCII terms:
  DoubleArrayTrie:      3.2ms
  DoubleArrayTrieChar:  3.4ms  (+6%)

Unicode terms (mixed scripts):
  DoubleArrayTrieChar:  3.8ms
```

**Insight**: Construction overhead is minimal (~5-20%).

#### Exact Match (single query)

```
ASCII terms:
  DoubleArrayTrie:      6.6µs
  DoubleArrayTrieChar:  6.9µs  (+5%)

Unicode terms:
  DoubleArrayTrieChar:  7.2µs  (+9%)
```

**Insight**: Query overhead is very small (~5-10%).

#### Fuzzy Search (max distance 2)

```
ASCII terms:
  DoubleArrayTrie:      16.3µs
  DoubleArrayTrieChar:  17.1µs  (+5%)

Unicode terms:
  DoubleArrayTrieChar:  18.4µs  (+13%)
```

**Insight**: Even for fuzzy matching, overhead is acceptable.

### Memory Usage

#### Per-State Memory

```
DoubleArrayTrie:      ~10 bytes/state
DoubleArrayTrieChar:  ~18 bytes/state  (+80%)
```

**Why the increase?**
- `char` is 4 bytes vs `u8` 1 byte
- Edge labels: `Vec<char>` vs `Vec<u8>`
- Approximate 2 edges/state: 8 bytes vs 2 bytes

#### Real-World Examples

**50,000-term English dictionary**:
- DoubleArrayTrie: ~500 KB
- DoubleArrayTrieChar: ~900 KB (+80%)

**20,000-term CJK dictionary**:
- DoubleArrayTrieChar: ~360 KB
- More states due to larger alphabet

### Character Code Distribution Impact

Performance depends on the range of character codes used:

```
Scenario 1: ASCII only (codes 0-127)
  Array size: Minimal
  Performance: Excellent

Scenario 2: Latin + accents (codes 0-255)
  Array size: Small increase
  Performance: Excellent

Scenario 3: CJK (codes 0x4E00-0x9FFF)
  Array size: Larger (high code points)
  Performance: Still good (sparse access)

Scenario 4: Emoji (codes 0x1F300+)
  Array size: Largest
  Performance: Good (cache locality maintained)
```

The BASE/CHECK algorithm adapts well to sparse character sets.

## Byte-Level vs Character-Level

### Decision Matrix

| Factor | DoubleArrayTrie (Byte) | DoubleArrayTrieChar (Char) |
|--------|------------------------|----------------------------|
| **ASCII/Latin-1** | ✅ Perfect | ✅ Works, slight overhead |
| **Accented chars** | ⚠️ Wrong distances | ✅ Correct distances |
| **CJK** | ❌ Meaningless distances | ✅ Correct distances |
| **Emoji** | ❌ Very wrong | ✅ Correct distances |
| **Performance** | ⭐⭐⭐⭐⭐ Fastest | ⭐⭐⭐⭐ ~5% slower |
| **Memory** | ⭐⭐⭐⭐⭐ Smallest | ⭐⭐⭐⭐ ~80% more |
| **Use case** | ASCII-only, speed-critical | Multi-language, correctness |

### When Byte-Level Is Acceptable

Byte-level is fine when:

1. **Pure ASCII**: English text without accents
2. **Binary data**: Matching byte sequences, not human text
3. **Maximum performance**: Microseconds matter more than correctness
4. **Legacy systems**: Must match existing byte-level behavior

### When Character-Level Is Required

Character-level is necessary when:

1. **International**: Any non-ASCII text
2. **User-facing**: Humans expect correct distances
3. **Multi-language**: Dictionary contains diverse scripts
4. **Linguistic correctness**: Academic or NLP applications

### Hybrid Approach

For mixed workloads:

```rust
// ASCII-heavy with occasional Unicode
let ascii_dict = DoubleArrayTrie::from_terms(ascii_terms);
let unicode_dict = DoubleArrayTrieChar::from_terms(unicode_terms);

fn search(query: &str) -> Vec<String> {
    if query.is_ascii() {
        // Fast path: byte-level
        search_byte_dict(&ascii_dict, query)
    } else {
        // Unicode path: character-level
        search_char_dict(&unicode_dict, query)
    }
}
```

## Advanced Topics

### Unicode Normalization

**Problem**: Multiple representations of same character

```rust
let nfc = "café";           // é as U+00E9 (NFC)
let nfd = "cafe\u{0301}";   // e + combining (NFD)

assert_ne!(nfc, nfd);  // Different byte sequences!
```

**Solution**: Normalize before insertion

```rust
use unicode_normalization::UnicodeNormalization;

fn normalize(s: &str) -> String {
    s.nfc().collect()  // Convert to NFC form
}

let dict = DoubleArrayTrieChar::from_terms(
    vec!["café", "cafe\u{0301}"]
        .into_iter()
        .map(normalize)
);

// Now both representations match
assert!(dict.contains(&normalize("café")));
assert!(dict.contains(&normalize("cafe\u{0301}")));
```

### Grapheme Cluster Handling

For true "user-perceived character" handling:

```rust
use unicode_segmentation::UnicodeSegmentation;

// Split into grapheme clusters
let graphemes: Vec<&str> = "🇺🇸".graphemes(true).collect();
// ["🇺🇸"] (flag is 2 code points, 1 grapheme)

let code_points: Vec<char> = "🇺🇸".chars().collect();
// ['🇺', '🇸'] (regional indicators)

// For grapheme-level matching:
// 1. Segment into graphemes
// 2. Treat each grapheme as a "unit"
// 3. Use custom DictionaryNode implementation
```

### Case Folding

For case-insensitive matching:

```rust
let dict = DoubleArrayTrieChar::from_terms(
    vec!["Hello", "WORLD", "CaFé"]
        .into_iter()
        .map(|s| s.to_lowercase())
);

// Query with lowercase
assert!(dict.contains("hello"));
assert!(dict.contains("world"));
assert!(dict.contains("café"));
```

### Collation and Locale-Specific Sorting

For linguistically correct sorting:

```rust
use icu_collator::*;

// Swedish: 'ä' sorts after 'z'
// German: 'ä' sorts as 'ae'

// Use ICU collation for term sorting before construction
let collator = Collator::try_new(&locale!("sv").into(), Default::default()).unwrap();

let mut terms = vec!["ångström", "zebra", "äpple"];
terms.sort_by(|a, b| collator.compare(a, b));

let dict = DoubleArrayTrieChar::from_terms(terms);
```

### Mixed Script Handling

Detect and handle script boundaries:

```rust
use unicode_script::{Script, UnicodeScript};

fn get_script(s: &str) -> Option<Script> {
    s.chars().next().and_then(|c| c.script())
}

// Separate dictionaries per script for better performance
let mut by_script: HashMap<Script, Vec<String>> = HashMap::new();

for term in terms {
    if let Some(script) = get_script(term) {
        by_script.entry(script).or_default().push(term.to_string());
    }
}

let latin_dict = DoubleArrayTrieChar::from_terms(by_script[&Script::Latin]);
let han_dict = DoubleArrayTrieChar::from_terms(by_script[&Script::Han]);
```

## Related Documentation

- [DoubleArrayTrie (byte-level)](double-array-trie.md) - Byte-level variant
- [Dictionary Layer](../README.md) - Overview of all dictionary types
- [Value Storage](../../09-value-storage/README.md) - Term-to-value mappings
- [Zipper Navigation](../../06-zipper-navigation/README.md) - Character-by-character exploration

## References

### Unicode Specifications

1. **Unicode Consortium**. *The Unicode Standard, Version 15.0*
   - 📄 [https://www.unicode.org/versions/Unicode15.0.0/](https://www.unicode.org/versions/Unicode15.0.0/)
   - Official Unicode specification

2. **Unicode Technical Report #15: Unicode Normalization Forms**
   - 📄 [https://www.unicode.org/reports/tr15/](https://www.unicode.org/reports/tr15/)
   - NFC, NFD, NFKC, NFKD normalization

3. **Unicode Technical Standard #10: Unicode Collation Algorithm**
   - 📄 [https://www.unicode.org/reports/tr10/](https://www.unicode.org/reports/tr10/)
   - Locale-specific sorting

### Rust Resources

4. **The Rust Reference: Types - Textual types**
   - 📄 [https://doc.rust-lang.org/reference/types/textual.html](https://doc.rust-lang.org/reference/types/textual.html)
   - Rust's `char` and `str` types

5. **Rust By Example: Strings**
   - 📄 [https://doc.rust-lang.org/rust-by-example/std/str.html](https://doc.rust-lang.org/rust-by-example/std/str.html)
   - UTF-8 handling in Rust

### Libraries

6. **unicode-normalization** crate
   - 📦 [https://crates.io/crates/unicode-normalization](https://crates.io/crates/unicode-normalization)
   - NFC/NFD normalization

7. **unicode-segmentation** crate
   - 📦 [https://crates.io/crates/unicode-segmentation](https://crates.io/crates/unicode-segmentation)
   - Grapheme cluster segmentation

### Academic Papers

8. **Schulz, K. U., & Mihov, S. (2002)**. "Fast String Correction with Levenshtein Automata"
   - *International Journal on Document Analysis and Recognition*, 5(1), 67-85
   - Discusses character-level vs byte-level matching

## Next Steps

- **Byte-Level**: Compare with [DoubleArrayTrie](double-array-trie.md)
- **Values**: Learn about [Value Storage](../../09-value-storage/README.md)
- **Navigation**: Try [Zipper Pattern](../../06-zipper-navigation/README.md)
- **Automata**: Understand [Levenshtein Automata](../../02-automata-layer/README.md)

---

**Navigation**: [← Dictionary Layer](../README.md) | [DoubleArrayTrie (byte-level)](double-array-trie.md) | [Algorithms Home](../../README.md)
