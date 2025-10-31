# UTF-8 Character-Level Support Implementation

## Overview

This document describes the implementation of UTF-8 character-level support for the liblevenshtein-rust library. The implementation adds character-level variants alongside existing byte-level implementations without breaking backward compatibility.

## Design Goals

1. **Backward Compatibility**: All existing byte-level code continues to work unchanged
2. **Opt-in UTF-8 Support**: Users explicitly choose character-level types when needed
3. **Zero-Cost Abstraction**: Generic implementation with compile-time specialization
4. **Additive Approach**: New types added alongside existing ones, not replacing them

## Problem Statement

The original implementation operated at the byte level:
- Query strings converted to `Vec<u8>` via `into_bytes()`
- Dictionary edges labeled with `u8` values
- Characteristic vector compared byte equality
- Distance functions correctly used `char` (mismatch!)

This caused issues with multi-byte UTF-8 sequences:
- ASCII 'a' (1 byte) → reachable at distance 1 from empty string ✓
- Unicode '¡' (2 bytes) → requires distance 2, should be 1 ❌
- The distance functions already worked at character level, creating inconsistency

## Architecture

### Core Abstraction: CharUnit Trait

**File**: `src/dictionary/char_unit.rs`

```rust
pub trait CharUnit:
    Copy + Clone + Eq + PartialEq + std::hash::Hash + std::fmt::Debug + Send + Sync + 'static
{
    fn from_str(s: &str) -> Vec<Self>;
    fn to_string(units: &[Self]) -> String;
    fn iter_str(s: &str) -> Box<dyn Iterator<Item = Self> + '_>;
}
```

**Implementations**:
- `impl CharUnit for u8` - Byte-level (existing behavior, fastest)
- `impl CharUnit for char` - Character-level (proper Unicode semantics)

### Modified Core Traits

**File**: `src/dictionary/mod.rs`

#### DictionaryNode Trait
```rust
pub trait DictionaryNode: Clone + Send + Sync {
    type Unit: CharUnit;  // ← NEW: Associated type

    fn is_final(&self) -> bool;
    fn transition(&self, label: Self::Unit) -> Option<Self>;  // ← Changed from u8
    fn edges(&self) -> Box<dyn Iterator<Item = (Self::Unit, Self)> + '_>;  // ← Changed
    fn has_edge(&self, label: Self::Unit) -> bool;  // ← Changed
    fn edge_count(&self) -> Option<usize>;
}
```

#### Dictionary Trait
```rust
pub trait Dictionary {
    type Node: DictionaryNode;

    fn root(&self) -> Self::Node;

    fn contains(&self, term: &str) -> bool {
        let mut node = self.root();
        for unit in <Self::Node as DictionaryNode>::Unit::iter_str(term) {  // ← Generic
            match node.transition(unit) {
                Some(next) => node = next,
                None => return false,
            }
        }
        node.is_final()
    }

    // ... rest unchanged
}
```

### Updated Dictionary Implementations

All existing implementations now specify `type Unit = u8`:

**Modified Files**:
- `src/dictionary/double_array_trie.rs` - `impl DictionaryNode for DoubleArrayTrieNode`
- `src/dictionary/dawg.rs` - `impl DictionaryNode for DawgDictionaryNode`
- `src/dictionary/dawg_optimized.rs` - `impl DictionaryNode for OptimizedDawgNodeRef`
- `src/dictionary/dynamic_dawg.rs` - `impl DictionaryNode for DynamicDawgNode`
- `src/dictionary/suffix_automaton.rs` - `impl DictionaryNode for SuffixNodeHandle`
- `src/dictionary/compressed_suffix_automaton.rs` - `impl DictionaryNode for CompressedSuffixNode`
- `src/dictionary/pathmap.rs` - `impl<V> DictionaryNode for PathMapNode<V>`

**Example**:
```rust
impl DictionaryNode for DoubleArrayTrieNode {
    type Unit = u8;  // ← Explicit byte-level

    fn is_final(&self) -> bool { /* ... */ }
    fn transition(&self, label: u8) -> Option<Self> { /* ... */ }
    // ... rest unchanged
}
```

### Generic Intersection and PathNode

**File**: `src/transducer/intersection.rs`

```rust
// PathNode now generic over CharUnit
pub struct PathNode<U: CharUnit> {
    label: U,
    depth: u16,
    parent: Option<Box<PathNode<U>>>,
}

// Intersection uses node's associated Unit type
pub struct Intersection<N: DictionaryNode> {
    pub label: Option<N::Unit>,  // ← Generic
    pub node: N,
    pub state: State,
    pub parent: Option<Box<PathNode<N::Unit>>>,  // ← Generic
}

impl<N: DictionaryNode> Intersection<N> {
    pub fn term(&self) -> String {
        let mut units = Vec::new();
        // Collect labels...
        N::Unit::to_string(&units)  // ← Use trait method
    }
}
```

### Generic Transition Functions

**File**: `src/transducer/transition.rs`

```rust
// Characteristic vector now generic
fn characteristic_vector<'a, U: CharUnit>(
    dict_unit: U,  // ← Generic
    query: &[U],   // ← Generic
    window_size: usize,
    offset: usize,
    buffer: &'a mut [bool; 8],
) -> &'a [bool] {
    let len = window_size.min(8);
    for (i, item) in buffer.iter_mut().enumerate().take(len) {
        let query_idx = offset + i;
        *item = query_idx < query.len() && query[query_idx] == dict_unit;
    }
    &buffer[..len]
}

// State transition now generic
pub fn transition_state_pooled<U: CharUnit>(
    state: &State,
    pool: &mut StatePool,
    dict_unit: U,  // ← Generic
    query: &[U],   // ← Generic
    max_distance: usize,
    algorithm: Algorithm,
    prefix_mode: bool,
) -> Option<State> {
    // ... implementation uses generic U throughout
}
```

### Generic Query Iterators

**File**: `src/transducer/query.rs`

```rust
pub struct QueryIterator<N: DictionaryNode, R: QueryResult = String> {
    pending: VecDeque<Box<Intersection<N>>>,
    query: Vec<N::Unit>,  // ← Uses node's Unit type
    max_distance: usize,
    algorithm: Algorithm,
    finished: bool,
    state_pool: StatePool,
    substring_mode: bool,
    _result_type: PhantomData<R>,
}

impl<N: DictionaryNode, R: QueryResult> QueryIterator<N, R> {
    pub fn with_substring_mode(
        root: N,
        query: String,
        max_distance: usize,
        algorithm: Algorithm,
        substring_mode: bool,
    ) -> Self {
        let query_units = N::Unit::from_str(&query);  // ← Generic conversion
        let initial = initial_state(query_units.len(), max_distance, algorithm);
        // ...
    }
}
```

**Similar updates in**:
- `src/transducer/ordered_query.rs` - OrderedQueryIterator
- `src/transducer/value_filtered_query.rs` - ValueFilteredQueryIterator, ValueSetFilteredQueryIterator

### Public API (Unchanged)

**File**: `src/transducer/mod.rs`

The Transducer API remains unchanged - it works with any Dictionary:

```rust
impl<D: Dictionary> Transducer<D> {
    pub fn query(&self, term: &str, max_distance: usize) -> QueryIterator<D::Node, String> {
        QueryIterator::with_substring_mode(
            self.dictionary.root(),
            term.to_string(),
            max_distance,
            self.algorithm,
            self.dictionary.is_suffix_based(),
        )
    }

    // ... all other methods work generically
}
```

## Implementation Progress

### ✅ Completed

1. **CharUnit Trait** (`src/dictionary/char_unit.rs`)
   - Defined trait with `from_str()`, `to_string()`, `iter_str()`
   - Implemented for `u8` (byte-level)
   - Implemented for `char` (character-level)
   - Comprehensive tests for both implementations

2. **Dictionary Traits** (`src/dictionary/mod.rs`)
   - Added `type Unit: CharUnit` to DictionaryNode
   - Updated all method signatures to use `Self::Unit`
   - Updated `Dictionary::contains()` default implementation

3. **Existing Implementations** (7 files)
   - Added `type Unit = u8` to all DictionaryNode implementations
   - No behavioral changes - fully backward compatible

4. **Generic Intersection** (`src/transducer/intersection.rs`)
   - Made PathNode generic: `PathNode<U: CharUnit>`
   - Updated Intersection to use `N::Unit`
   - Updated term reconstruction to use `N::Unit::to_string()`

5. **Generic Transitions** (`src/transducer/transition.rs`)
   - Made `characteristic_vector<U: CharUnit>()` generic
   - Made `transition_state<U: CharUnit>()` generic
   - Made `transition_state_pooled<U: CharUnit>()` generic

6. **Generic Iterators** (3 files)
   - QueryIterator: query field is `Vec<N::Unit>`
   - OrderedQueryIterator: query field is `Vec<N::Unit>`
   - ValueFilteredQueryIterator: query field is `Vec<N::Unit>`
   - All use `N::Unit::from_str()` for conversion

7. **DAWG Query Helper** (`src/dictionary/dawg_query.rs`)
   - Updated PathNode references to `PathNode<u8>`

8. **Test Fixes**
   - Fixed char_unit tests to use explicit trait qualification
   - Fixed QueryIterator tests to specify result type

9. **Compilation**
   - ✅ Code compiles successfully with `cargo check`

### ⏳ In Progress

10. **Test Validation**
    - About to run full test suite to verify byte-level still works

### 📋 Pending

11. **Character-Level Dictionary Implementations**
    - Create `DoubleArrayTrieChar` (char-based variant)
    - Create `DawgDictionaryChar` (char-based variant)
    - Other char variants as needed

12. **UTF-8 Integration Tests**
    - Test Unicode characters: emoji, CJK, combining chars
    - Verify distance semantics: "" → "¡" should be distance 1
    - Cross-validate with distance functions

13. **Performance Benchmarks**
    - Compare byte vs char performance
    - Measure memory overhead
    - Document trade-offs

14. **Documentation**
    - Usage guide for when to use byte vs char
    - Migration examples
    - API documentation updates

## Files Modified

### Created
- `src/dictionary/char_unit.rs` (169 lines)

### Modified
- `src/dictionary/mod.rs` - Added CharUnit import, made traits generic
- `src/dictionary/double_array_trie.rs` - Added `type Unit = u8`
- `src/dictionary/dawg.rs` - Added `type Unit = u8`
- `src/dictionary/dawg_optimized.rs` - Added `type Unit = u8`
- `src/dictionary/dynamic_dawg.rs` - Added `type Unit = u8`
- `src/dictionary/suffix_automaton.rs` - Added `type Unit = u8`
- `src/dictionary/compressed_suffix_automaton.rs` - Added `type Unit = u8`
- `src/dictionary/pathmap.rs` - Added `type Unit = u8`
- `src/dictionary/dawg_query.rs` - Updated PathNode to `PathNode<u8>`
- `src/transducer/intersection.rs` - Made PathNode and Intersection generic
- `src/transducer/transition.rs` - Made all transition functions generic
- `src/transducer/query.rs` - Made QueryIterator generic over N::Unit
- `src/transducer/ordered_query.rs` - Made OrderedQueryIterator generic over N::Unit
- `src/transducer/value_filtered_query.rs` - Made value iterators generic over N::Unit

## Usage Examples

### Byte-Level (Existing, Unchanged)
```rust
use liblevenshtein::prelude::*;

// Byte-level dictionary (default, fastest)
let dict = DoubleArrayTrie::from_terms(vec!["test", "café"]);
let transducer = Transducer::new(dict, Algorithm::Standard);

// Works as before, but treats multi-byte UTF-8 as multiple units
let results: Vec<_> = transducer.query("test", 2).collect();
```

### Character-Level (Future, When Implemented)
```rust
use liblevenshtein::prelude::*;

// Character-level dictionary (proper Unicode)
let dict = DoubleArrayTrieChar::from_terms(vec!["test", "café", "中文", "🎉"]);
let transducer = Transducer::new(dict, Algorithm::Standard);

// Distance measured in characters, not bytes
// "" → "¡" is distance 1 (one char), not 2 (two bytes)
let results: Vec<_> = transducer.query("café", 2).collect();
```

## Performance Characteristics

### Byte-Level (u8)
- **Memory**: 1 byte per edge label
- **Speed**: Fastest (native machine word operations)
- **Use Case**: ASCII/Latin-1 content, maximum performance

### Character-Level (char)
- **Memory**: 4 bytes per edge label (4x overhead)
- **Speed**: ~10-15% slower (estimated, needs benchmarks)
- **Use Case**: Unicode content, correct semantic distance

## Design Decisions

### Why Associated Type Instead of Generic Parameter?

**Option A (Chosen)**: Associated Type
```rust
trait DictionaryNode {
    type Unit: CharUnit;
    fn transition(&self, label: Self::Unit) -> Option<Self>;
}
```

**Option B (Rejected)**: Generic Parameter
```rust
trait DictionaryNode<U: CharUnit> {
    fn transition(&self, label: U) -> Option<Self>;
}
```

**Rationale**:
- Associated type is more ergonomic: `N::Unit` vs `N::U`
- Unit type is intrinsic to the node, not a choice at use site
- Cleaner type signatures: `QueryIterator<N>` vs `QueryIterator<N, U>`
- Matches Rust idiom (like Iterator::Item)

### Why Not Replace Existing Implementations?

**Chosen**: Additive approach (new types alongside old)

**Alternative**: Modify existing types to be generic

**Rationale**:
- Backward compatibility: existing code continues to work
- Performance: users can keep using fast byte-level for ASCII
- Opt-in: users explicitly choose UTF-8 when needed
- Migration path: can deprecate byte-level later if desired

## Next Steps

1. Run full test suite to ensure byte-level still works
2. Create first char-level dictionary: DoubleArrayTrieChar
3. Add UTF-8 integration tests
4. Validate against failing test cases from TRANSPOSITION_FIX_SUMMARY.md
5. Performance benchmarking
6. Documentation and examples

## Known Limitations

1. **PathMap Backend**: May require special handling for char-level due to &[u8] API
2. **Serialization**: Need to handle char-level dictionaries in serialization
3. **Memory**: 4x overhead for char vs u8 edge labels
4. **Breaking Change for Future**: If we want to make char the default later

## References

- Original bug report: `TRANSPOSITION_FIX_SUMMARY.md` lines 205-208
- Test failures: `tests/test_empty_query.rs`, `tests/debug_unicode_empty_query.rs`
- C++ implementation: Uses template specialization for similar pattern
- Java implementation: Uses factory pattern for polymorphic return types
