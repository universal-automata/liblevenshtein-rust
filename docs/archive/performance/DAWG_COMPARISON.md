# DAWG Implementation Comparison

## Static vs Dynamic DAWG: Design Philosophy

### Java Static DAWG (Build-Once)

**Philosophy**: Construct entire DAWG upfront, use immutably

```java
// Phase 1: Collection (DAWG not usable yet)
List<String> terms = new ArrayList<>();
terms.add("apple");
terms.add("banana");
terms.add("cherry");

// Phase 2: Construction (requires ALL terms, sorted)
Collections.sort(terms);
DAWG dawg = new DAWGBuilder().build(terms);

// Phase 3: Usage (NOW it works, but immutable)
List<String> results = dawg.query("aple", 2);

// ❌ Cannot modify after construction
// dawg.insert("apricot"); // Not supported!
```

**Key Requirements**:
- ✅ Terms must be sorted before building
- ✅ Complete term list required upfront
- ✅ Perfectly minimal structure guaranteed
- ❌ Cannot modify after construction
- ❌ Rebuilding requires recreating entire structure

### Rust Static DAWG (`DawgDictionary`)

**Philosophy**: Same as Java - immutable perfection

```rust
// Build once from complete term list
let dict = DawgDictionary::from_iter(vec![
    "apple", "banana", "cherry"
]);

// Usable immediately, perfectly minimal
let transducer = Transducer::new(dict, Algorithm::Standard);
let results: Vec<_> = transducer.query("aple", 2).collect();

// ❌ Cannot modify (immutable)
```

**Advantages over Java**:
- ✅ Automatic sorting (no manual sort needed)
- ✅ Memory safety (no GC pauses)
- ✅ Zero-cost abstractions

### Rust Dynamic DAWG (`DynamicDawg`)

**Philosophy**: Immediate usability + optional optimization

```rust
// Phase 1: Start empty - ALREADY USABLE!
let dawg = DynamicDawg::new();
let transducer = Transducer::new(dawg.clone(), Algorithm::Standard);

// Phase 2: Incremental construction - STILL USABLE!
dawg.insert("apple");
let r1: Vec<_> = transducer.query("aple", 2).collect(); // Works!

dawg.insert("banana");
let r2: Vec<_> = transducer.query("banan", 1).collect(); // Works!

// Phase 3: Modification - ALWAYS USABLE!
dawg.remove("apple");
dawg.insert("apricot");
let r3: Vec<_> = transducer.query("apri", 2).collect(); // Works!

// Phase 4: Optimization (optional, but recommended)
dawg.compact(); // NOW it's as minimal as Java's!
```

**Key Features**:
- ✅ Usable immediately (even when empty)
- ✅ Insert/delete anytime
- ✅ `compact()` achieves Java-level minimality
- ✅ Thread-safe modifications
- 🟡 Slightly less space-efficient between compactions

## How `compact()` Achieves Static DAWG Quality

The `compact()` method **recreates** what Java's static builder does:

```rust
pub fn compact(&self) -> usize {
    // 1. Extract all current terms
    let terms = extract_all_terms();

    // 2. Sort them (CRITICAL for minimality!)
    terms.sort();

    // 3. Rebuild from scratch with sorted input
    rebuild_from_sorted(terms);
}
```

This is **identical** to Java's approach:
```java
public static DAWG build(List<String> terms) {
    Collections.sort(terms); // Step 2
    return buildFromSorted(terms); // Step 3
}
```

## Why Sorted Order Matters

DAWG minimization relies on **incremental suffix sharing** during construction:

### Example: Building with Sorted Terms

```
Terms (sorted): ["band", "banana", "bandana"]

Construction:
1. Insert "band"
   b-a-n-d[*]

2. Insert "banana" - shares "ban" prefix
   b-a-n-d[*]
          \
           a-n-a[*]

3. Insert "bandana" - shares "ban" + recognizes "ana" suffix
   b-a-n-d[*]
          \-a-n-a[*]  (shared suffix!)
```

### With Unsorted Terms

```
Terms (unsorted): ["banana", "band", "bandana"]

1. Insert "banana"
   b-a-n-a-n-a[*]

2. Insert "band"
   b-a-n-a-n-a[*]
          \-d[*]

3. Insert "bandana"
   b-a-n-a-n-a[*]
          \-d[*]
           \-a-n-a[*]  (duplicates "ana"!)
```

**Result**: Unsorted insertion creates duplicate suffixes = larger structure!

## Performance Comparison

| Aspect | Static DAWG | DynamicDawg (no compact) | DynamicDawg (after compact) |
|--------|-------------|--------------------------|----------------------------|
| **Construction** | O(n log n) sort + O(n) build | O(mn) incremental | O(n log n) + O(n) |
| **Minimality** | Perfect | Near-minimal | **Perfect** |
| **Space** | Minimal | 1.0x - 1.5x minimal | **Minimal** |
| **Modifications** | ❌ Rebuild required | ✅ O(m) per op | ✅ O(m) per op |
| **Usability** | After complete build | **Immediate** | **Immediate** |

## When to Use Each

### Use Static DAWG (`DawgDictionary`) When:

✅ **Fixed dictionary**
- Word lists that never change
- Embedded systems with ROM dictionaries
- Read-only reference data

✅ **Maximum space efficiency required**
- Memory-constrained devices
- Large dictionaries (millions of terms)
- No tolerance for overhead

✅ **Predictable lifecycle**
- Load once, use many times
- Startup time not critical
- Simple deployment model

**Example**: Mobile app with built-in dictionary

### Use Dynamic DAWG (`DynamicDawg`) When:

✅ **Changing dictionary**
- User-added words
- Live spell checker learning
- Autocomplete with history

✅ **Immediate usability needed**
- Progressive loading
- Streaming data
- Real-time updates

✅ **Batch updates**
- Import/export workflows
- Periodic synchronization
- User sessions

**Example**: IDE with custom dictionary per project

## Migration Path

If you currently use static DAWG but need modifications:

```rust
// Before: Static (rebuild on change)
fn update_dictionary(old_terms: Vec<String>, new_term: String) -> DawgDictionary {
    let mut all_terms = old_terms;
    all_terms.push(new_term);
    DawgDictionary::from_iter(all_terms) // Full rebuild!
}

// After: Dynamic (incremental update)
fn update_dictionary(dawg: &DynamicDawg, new_term: String) {
    dawg.insert(&new_term); // Just add it!
    // Compact periodically, not every time
}
```

## Best Practices Summary

### For Static DAWG:
1. Collect all terms first
2. Optionally pre-sort (for verification)
3. Build once
4. Use immutably

### For Dynamic DAWG:
1. Start early (even empty)
2. Insert/delete as needed
3. Compact after batches
4. Monitor `needs_compaction()`

### Hybrid Approach:
```rust
// Start with static base dictionary
let base_terms = load_standard_dictionary();
let dawg = DynamicDawg::from_iter(base_terms);

// Add user customizations dynamically
dawg.insert("userterm1");
dawg.insert("userterm2");

// Compact before saving
dawg.compact();
save_dictionary(&dawg);
```

## Theoretical Foundation

### Why Sorted Order Enables Minimality

From Schulz & Mihov (2002):

> "For a sorted sequence of words w₁, w₂, ..., wₙ, the minimal DAWG
> can be constructed incrementally in O(n) time by:
> 1. Identifying common prefixes with previous word
> 2. Minimizing the suffix not shared
> 3. Adding the unique suffix"

The key insight: **Lexicographic order ensures maximum prefix reuse**.

Our `compact()` method achieves this by:
1. Extracting current language
2. Sorting (establishes prefix order)
3. Rebuilding incrementally

This is mathematically equivalent to building from scratch with sorted input.

## Conclusion

Both implementations have their place:

- **Static DAWG**: Perfect for immutable, space-critical scenarios
- **Dynamic DAWG**: Perfect for evolving dictionaries
- **`compact()`**: Bridges the gap - dynamic flexibility with static efficiency

The choice depends on your use case, not on implementation quality!
