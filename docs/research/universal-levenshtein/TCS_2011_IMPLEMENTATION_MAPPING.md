# TCS 2011 Paper Implementation Mapping

**Date**: 2025-11-12
**Paper**: "Deciding Word Neighborhood with Universal Neighborhood Automata" (TCS 2011)
**Authors**: Petar Mitankin, Stoyan Mihov, Klaus U. Schulz
**Related Documents**:
- [TCS_2011_PAPER_ANALYSIS.md](./TCS_2011_PAPER_ANALYSIS.md) - Full paper analysis
- [TCS_2011_LAZY_APPLICABILITY.md](./TCS_2011_LAZY_APPLICABILITY.md) - Lazy applicability analysis

---

## Purpose

This document provides a concrete mapping between theoretical concepts from the TCS 2011 paper and their implementation in both the **lazy** and **universal** Levenshtein automata codebases. Use this as a reference for understanding how theory translates to code.

---

## Quick Navigation

| Paper Concept | Section | Lazy Code | Universal Code |
|---------------|---------|-----------|----------------|
| Bounded Diagonal Property | [§1](#1-bounded-diagonal-property-theorem-82) | ✅ Applied | ✅ Applied |
| Operation Types (t^x, t^y, t^w) | [§2](#2-generalized-operation-types) | ⚠️ Hardcoded | ⚠️ Hardcoded |
| Subsumption (<^χ_s) | [§3](#3-subsumption-relation) | ✅ Implemented | ✅ Implemented |
| State Anti-chain (⊔) | [§4](#4-anti-chain-property--join-operator) | ✅ Implemented | ✅ Implemented |
| Matrix-State Construction | [§5](#5-matrix-state-construction) | ❌ N/A | ✅ Implemented |
| Preprocessing χ[Op,r] | [§6](#6-preprocessing-function-χopr) | ❌ N/A | ✅ Implemented |
| Restricted Substitutions (op^r) | [§7](#7-restricted-substitutions-opr) | 🚧 In Progress | 🚧 In Progress |
| Diagonal Crossing (f_n, m_n) | [§8](#8-diagonal-crossing-f_n-m_n-rm) | ❌ N/A | 🐛 Buggy |
| Characteristic Vector β | [§9](#9-characteristic-vector-β) | ❌ N/A | ✅ Implemented |

**Legend**:
- ✅ Fully implemented
- ⚠️ Partially implemented (hardcoded, not generalized)
- 🚧 Work in progress
- 🐛 Implemented but buggy
- ❌ Not applicable or not implemented

---

## 1. Bounded Diagonal Property (Theorem 8.2)

### Paper Definition (Section 8, Page 2348)

**Theorem 8.2**: The following are equivalent:
1. R[Op,r] has bounded length difference
2. There exists constant c such that every Op instance satisfies c-bounded diagonal property
3. Every zero-weighted type in Υ is length preserving

For Standard Levenshtein (n=2):
- Diagonal bound: c = 2
- Band width: 2c + 1 = 5 diagonals
- Typical state size: ≤ 8 positions (with subsumption)

### Lazy Implementation

**File**: `src/transducer/state.rs:8-48`

```rust
/// # SmallVec Optimization
///
/// Uses SmallVec with inline size of 8 to avoid heap allocations for typical states.
/// This optimization is theoretically justified by the **bounded diagonal property**
/// (Theorem 8.2, Mitankin et al., TCS 2011).
///
/// For Standard Levenshtein with error bound n=2:
/// - Diagonal bound c = 2
/// - Band width = 2c + 1 = 5 diagonals
/// - Typical state size ≤ 8 positions (with subsumption)
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct State {
    positions: SmallVec<[Position; 8]>,  // ← Justified by bounded diagonal
}
```

**Why It Applies**: Lazy automata use word-specific positions `(term_index, num_errors)` which still cluster around the diagonal in the DP matrix. The bounded diagonal property is a property of **Levenshtein distance**, not automaton architecture.

### Universal Implementation

**File**: `src/transducer/universal/state.rs:59-122`

```rust
/// # SmallVec Optimization
///
/// Uses SmallVec with inline size of 8 to avoid heap allocations for typical states.
/// This optimization is theoretically justified by the **bounded diagonal property**
/// (Theorem 8.2, Mitankin et al., TCS 2011).
///
/// For Standard Levenshtein with error bound n=2:
/// - Diagonal bound c = 2
/// - Band width = 2c + 1 = 5 diagonals
/// - Typical state size ≤ 8 positions (with subsumption)
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct UniversalState<V: PositionVariant> {
    positions: SmallVec<[UniversalPosition<V>; 8]>,  // ← Justified by bounded diagonal
    max_distance: u8,
}
```

**Why It Applies**: Universal automata use abstract positions `I + offset#errors` which also satisfy the bounded diagonal property, yielding O(n²) state space independent of word length.

---

## 2. Generalized Operation Types

### Paper Definition (Section 3, Pages 2341-2342)

**Operation Type**: t = ⟨t^x, t^y, t^w⟩

Where:
- `t^x`: Characters consumed from first word (|u|)
- `t^y`: Characters consumed from second word (|v|)
- `t^w`: Operation weight/cost

**Standard Levenshtein Operations**:
```
Match:         ⟨1, 1, 0⟩  (consume both, no cost)
Substitution:  ⟨1, 1, 1⟩  (consume both, cost 1)
Insertion:     ⟨0, 1, 1⟩  (consume v only, cost 1)
Deletion:      ⟨1, 0, 1⟩  (consume u only, cost 1)
```

### Lazy Implementation

**File**: `src/transducer/algorithm.rs:1-23`

```rust
/// Algorithm for computing edit distance
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Algorithm {
    /// Standard Levenshtein distance (operations: match, substitute, insert, delete)
    Standard,

    /// Levenshtein with transposition
    Transposition,

    /// Levenshtein with merge and split
    MergeAndSplit,
}
```

**Status**: ⚠️ **Hardcoded variants** - not generalized to support arbitrary operation types

**Gap**: No representation of `⟨t^x, t^y, t^w⟩` triples. Operations are implicit in the transition logic rather than data-driven.

**Transition Logic** (implicit operations): `src/transducer/lazy.rs:200-350`

```rust
// Match: ⟨1, 1, 0⟩
if query_char == dict_char {
    successor.insert(Position::new(term_index + 1, num_errors), algorithm, query_length);
}

// Operations: ⟨1, 1, 1⟩, ⟨0, 1, 1⟩, ⟨1, 0, 1⟩
if num_errors < max_distance {
    successor.insert(Position::new(term_index + 1, num_errors + 1), algorithm, query_length); // Substitution or Deletion
    successor.insert(Position::new(term_index, num_errors + 1), algorithm, query_length);     // Insertion
    // ... etc
}
```

### Universal Implementation

**File**: `src/transducer/universal/position.rs:1-50`

```rust
pub trait PositionVariant: Clone + Debug + PartialEq + Eq + PartialOrd + Ord {
    // Marker trait for position variants
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct Standard;

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct Transposition;

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct MergeAndSplit;
```

**Status**: ⚠️ **Hardcoded variants** via phantom types

**Gap**: No explicit `⟨t^x, t^y, t^w⟩` representation. Operations encoded implicitly in successor generation logic.

**Successor Logic** (implicit operations): `src/transducer/universal/position.rs:200-400`

```rust
impl<V: PositionVariant> UniversalPosition<V> {
    pub fn successors(&self, bit_vector: &CharacteristicVector, max_distance: u8)
        -> Vec<UniversalPosition<V>>
    {
        // Hardcoded standard operations
        // No generalized operation type system
    }
}
```

### Enhancement Path (Future Work)

**Proposed Design** (applies to both lazy and universal):

```rust
/// Generalized operation type from TCS 2011 Section 3
pub struct OperationType {
    /// Characters consumed from first word (t^x)
    x_consumed: u8,

    /// Characters consumed from second word (t^y)
    y_consumed: u8,

    /// Operation weight/cost (t^w)
    weight: f32,

    /// Optional: Restricted character pairs (op^r)
    restriction: Option<SubstitutionSet>,
}

/// Operation set defining custom edit distance semantics
pub struct OperationSet {
    types: Vec<OperationType>,
}

impl OperationSet {
    /// Standard Levenshtein operations
    pub fn standard() -> Self {
        Self {
            types: vec![
                OperationType { x_consumed: 1, y_consumed: 1, weight: 0.0, restriction: None }, // Match
                OperationType { x_consumed: 1, y_consumed: 1, weight: 1.0, restriction: None }, // Subst
                OperationType { x_consumed: 0, y_consumed: 1, weight: 1.0, restriction: None }, // Insert
                OperationType { x_consumed: 1, y_consumed: 0, weight: 1.0, restriction: None }, // Delete
            ],
        }
    }

    /// Weighted operations (e.g., OCR confidence scores)
    pub fn weighted(weights: &[(u8, u8, f32)]) -> Self { /* ... */ }

    /// Custom operations (e.g., Unicode normalization)
    pub fn custom(types: Vec<OperationType>) -> Self { /* ... */ }
}
```

**Reference**: See `docs/research/universal-levenshtein/TCS_2011_PAPER_ANALYSIS.md` Section 3 for details.

---

## 3. Subsumption Relation (<^χ_s)

### Paper Definition (Implicit in state minimization)

**Subsumption**: Position p₁ subsumes position p₂ if p₁ is "at least as good" as p₂, meaning:
- p₁ has made equal or more progress (offset comparison)
- p₁ has consumed equal or fewer errors
- p₂ is redundant and can be discarded

**Anti-chain Property**: No position in a state subsumes another.

### Lazy Implementation

**File**: `src/transducer/position.rs:80-140`

```rust
impl Position {
    /// Check if this position subsumes another
    ///
    /// Position p1 subsumes p2 if:
    /// - p2 has more errors than p1
    /// - The distance between positions satisfies: |p1.term_index - p2.term_index| ≤ (p2.num_errors - p1.num_errors)
    pub fn subsumes(&self, other: &Position, algorithm: Algorithm, query_length: usize) -> bool {
        // Check error dominance
        if other.num_errors <= self.num_errors {
            return false;
        }

        let error_diff = other.num_errors - self.num_errors;
        let index_diff = (self.term_index as isize - other.term_index as isize).abs() as usize;

        // Subsumption condition: index distance ≤ error difference
        index_diff <= error_diff
    }
}
```

**Usage**: `src/transducer/state.rs:82-100`

```rust
pub fn insert(&mut self, position: Position, algorithm: Algorithm, query_length: usize) {
    // Check if this position is subsumed by an existing one
    for existing in &self.positions {
        if existing.subsumes(&position, algorithm, query_length) {
            return;  // Already covered, discard new position
        }
    }

    // Remove any positions that this new position subsumes
    self.positions.retain(|p| !position.subsumes(p, algorithm, query_length));

    // Insert in sorted position
    self.positions.insert(insert_pos, position);
}
```

**Status**: ✅ **Fully implemented** - Online subsumption during state construction

### Universal Implementation

**File**: `src/transducer/universal/subsumption.rs:1-100`

```rust
/// Check if position p1 subsumes position p2
///
/// From thesis Definition 13 (page 37):
/// p1 <^χ_s p2 ⟺
///   (offset(p1) = offset(p2) ∧ errors(p1) < errors(p2)) ∨
///   (errors(p1) = errors(p2) ∧ offset(p1) < offset(p2))
pub fn subsumes<V: PositionVariant>(
    p1: &UniversalPosition<V>,
    p2: &UniversalPosition<V>,
    max_distance: u8,
) -> bool {
    // Type mismatch: I-type cannot subsume M-type (different domains)
    if p1.is_i_type() != p2.is_i_type() {
        return false;
    }

    // Same offset, fewer errors → p1 subsumes p2
    if p1.offset() == p2.offset() && p1.errors() < p2.errors() {
        return true;
    }

    // Same errors, earlier offset → p1 subsumes p2
    if p1.errors() == p2.errors() && p1.offset() < p2.offset() {
        return true;
    }

    false
}
```

**Usage**: `src/transducer/universal/state.rs:158-176`

```rust
pub fn add_position(&mut self, pos: UniversalPosition<V>) {
    // Check if this position is subsumed by an existing one
    for existing in &self.positions {
        if subsumes(existing, &pos, self.max_distance) {
            return;  // Already covered, discard
        }
    }

    // Remove any positions that this new position subsumes
    self.positions.retain(|p| !subsumes(&pos, p, self.max_distance));

    // Insert in sorted position
    self.positions.insert(insert_pos, pos);
}
```

**Status**: ✅ **Fully implemented** - Online subsumption via ⊔ operator

### Comparison

| Aspect | Lazy | Universal |
|--------|------|-----------|
| **Subsumption Logic** | Distance-based (`\|idx₁ - idx₂\| ≤ err_diff`) | Offset/error comparison |
| **State Maintenance** | Online anti-chain | Online anti-chain (⊔ operator) |
| **Complexity** | O(kn) typical, k << n | O(kn) typical, k << n |
| **Performance** | 3.3× faster than batch | Comparable |

**Key Insight**: Both implementations use **online subsumption** (check during insertion) rather than batch (insert all, then prune). This is a significant optimization validated by benchmarks.

---

## 4. Anti-chain Property & Join Operator (⊔)

### Paper Definition (Definition 15, Page 38)

**Anti-chain Property**: For all positions p₁, p₂ in state Q:
- p₁ ⊀^χ_s p₂ (p₁ does not subsume p₂)
- p₂ ⊀^χ_s p₁ (p₂ does not subsume p₁)

**Join Operator (⊔)**: Subsumption closure when adding position to state:
1. Remove all positions subsumed by new position
2. Add new position if not subsumed by existing positions

### Lazy Implementation

**Implicit via `State::insert()`**: `src/transducer/state.rs:82-100`

```rust
/// Add a position to this state with online subsumption checking.
///
/// Maintains anti-chain property automatically.
pub fn insert(&mut self, position: Position, algorithm: Algorithm, query_length: usize) {
    // Step 1: Check if new position is subsumed (reject if so)
    for existing in &self.positions {
        if existing.subsumes(&position, algorithm, query_length) {
            return;
        }
    }

    // Step 2: Remove positions subsumed by new position
    self.positions.retain(|p| !position.subsumes(p, algorithm, query_length));

    // Step 3: Insert new position (anti-chain maintained)
    self.positions.insert(insert_pos, position);
}
```

**Status**: ✅ Implicit ⊔ operator via insert logic

### Universal Implementation

**Explicit via `UniversalState::add_position()`**: `src/transducer/universal/state.rs:158-176`

```rust
/// Add position, maintaining anti-chain property (⊔ operator)
///
/// Implements the subsumption closure from the thesis:
/// 1. Remove all positions that subsume the new position (worse positions)
/// 2. Add new position if it doesn't subsume any existing position
pub fn add_position(&mut self, pos: UniversalPosition<V>) {
    // Step 1: Check if new position is subsumed
    for existing in &self.positions {
        if subsumes(existing, &pos, self.max_distance) {
            return;
        }
    }

    // Step 2: Remove subsumed positions
    self.positions.retain(|p| !subsumes(&pos, p, self.max_distance));

    // Step 3: Insert new position
    self.positions.insert(insert_pos, pos);
}
```

**Status**: ✅ Explicit ⊔ operator implementation

### Comparison

Both implementations are **functionally identical** — they maintain the anti-chain property via online subsumption. The universal version has explicit documentation referencing the paper's ⊔ operator, while the lazy version achieves the same result with different naming.

---

## 5. Matrix-State Construction

### Paper Definition (Section 9.2, Pages 2350-2352)

**Matrix-State**: Internal representation using three components:
- **I-part**: Non-final positions (I + offset#errors)
- **M-part**: Final positions (M + offset#errors)
- **Extensors**: Additional positions for boundary transitions

**Construction Algorithm** (simplified):
1. Start with initial state {I + 0#0}
2. Apply operations to generate successors
3. Check diagonal crossing with f_n
4. If crossed, apply m_n conversion (I → M)
5. Maintain anti-chain property

### Lazy Implementation

**Status**: ❌ **Not applicable** — Lazy automata don't use matrix-state representation

**Why**: Lazy automata are **word-specific** and use concrete indices:

```rust
pub struct Position {
    term_index: usize,    // Concrete index in query word
    num_errors: usize,    // Error count
    is_special: bool,     // Special flag for transposition/merge-split
}
```

There is no I/M abstraction because the automaton is built for a specific query word at runtime.

### Universal Implementation

**Status**: ✅ **Fully implemented** via `UniversalPosition` enum

**File**: `src/transducer/universal/position.rs:50-100`

```rust
/// Universal position (I-type or M-type)
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum UniversalPosition<V: PositionVariant> {
    /// Non-final position: I + offset#errors
    INonFinal { offset: i8, errors: u8, _phantom: PhantomData<V> },

    /// Final position: M + offset#errors
    MFinal { offset: i8, errors: u8, _phantom: PhantomData<V> },
}

impl<V: PositionVariant> UniversalPosition<V> {
    pub fn new_i(offset: i8, errors: u8, max_distance: u8) -> Result<Self, PositionError> {
        // Validate invariants
        Ok(Self::INonFinal { offset, errors, _phantom: PhantomData })
    }

    pub fn new_m(offset: i8, errors: u8, max_distance: u8) -> Result<Self, PositionError> {
        // Validate invariants
        Ok(Self::MFinal { offset, errors, _phantom: PhantomData })
    }
}
```

**State Construction**: `src/transducer/universal/state.rs:127-134`

```rust
/// Create initial state {I + 0#0}
pub fn initial(max_distance: u8) -> Self {
    let mut state = Self::new(max_distance);
    let initial_pos = UniversalPosition::new_i(0, 0, max_distance)
        .expect("I + 0#0 should always be valid");
    state.positions.push(initial_pos);
    state
}
```

**Why It Works**: Universal automata are **word-agnostic**, using abstract parameters I (start) and M (end) that can be instantiated for any word pair at query time.

---

## 6. Preprocessing Function χ[Op,r]

### Paper Definition (Section 4, Pages 2342-2343)

**Preprocessing Function**: χ[Op,r] computes characteristic information for operations:
- Maps characters to operation applicability
- Encodes which operations can apply at each position
- Used to construct characteristic vectors β(a, w)

**Purpose**: Enables alphabet-independent automaton construction — precompute all character relationships once, then use for any word pair.

### Lazy Implementation

**Status**: ❌ **Not applicable** — Lazy automata don't need preprocessing

**Why**: Lazy automata perform direct character comparison at runtime:

```rust
// Direct comparison, no preprocessing needed
if query_char == dict_char {
    // Match operation
    successor.insert(Position::new(term_index + 1, num_errors), algorithm, query_length);
}
```

This is **word-specific** by design — the automaton is built for a specific query, so there's no need for alphabet-independent encoding.

### Universal Implementation

**Status**: ✅ **Fully implemented** via `CharacteristicVector`

**File**: `src/transducer/universal/bit_vector.rs:1-100`

```rust
/// Characteristic vector β(a, w) encoding character matches
///
/// From thesis page 42: For character a and word w, β(a, w) is a bit vector
/// where bit i is 1 if w[i] = a, 0 otherwise.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CharacteristicVector {
    /// Bit vector: bits[i] = 1 if word[i] matches query character
    bits: SmallVec<[bool; 8]>,
}

impl CharacteristicVector {
    /// Create characteristic vector for character a in word w
    ///
    /// Example: β('b', "abc") = [false, true, false] = "010"
    pub fn new(query_char: char, word: &str) -> Self {
        let bits: SmallVec<[bool; 8]> = word
            .chars()
            .map(|c| c == query_char)
            .collect();

        Self { bits }
    }

    /// Get bit at position i
    pub fn get(&self, index: usize) -> bool {
        self.bits.get(index).copied().unwrap_or(false)
    }
}
```

**Usage in Transitions**: `src/transducer/universal/position.rs:200-300`

```rust
impl<V: PositionVariant> UniversalPosition<V> {
    pub fn successors(&self, bit_vector: &CharacteristicVector, max_distance: u8)
        -> Vec<UniversalPosition<V>>
    {
        // Use bit vector to determine operation applicability
        let match_bit = bit_vector.get(self.position_in_word());

        if match_bit {
            // Match operation applies
            successors.push(/* match successor */);
        }

        // Always consider error operations (independent of character)
        successors.push(/* substitution successor */);
        // ... etc
    }
}
```

**Why It's Needed**: Universal automata must work for **any word pair** without knowing them in advance. Characteristic vectors abstract the character comparison into a precomputable encoding.

---

## 7. Restricted Substitutions (op^r)

### Paper Definition (Section 3.2, Page 2342)

**Restricted Operation**: op = ⟨op^x, op^y, op^r, op^w⟩

Where `op^r ⊆ Σ^{op^x} × Σ^{op^y}` is the allowed replacement relation.

**Examples**:
- **Keyboard proximity**: op^r = {(q,w), (q,a), (w,e), ...}
- **OCR confusion**: op^r = {(O,0), (I,1), (l,I), ...}
- **Phonetic similarity**: op^r = {(f,ph), (c,k), (c,s), ...}

### Lazy Implementation

**Status**: 🚧 **Work in progress** — SubstitutionSet implemented, integration pending

**File**: `src/transducer/substitution_set.rs:1-200`

```rust
/// Set of allowed character substitutions (op^r)
///
/// Maps to the paper's restricted substitution relation: op^r ⊆ Σ × Σ
#[derive(Clone, Debug)]
pub struct SubstitutionSet {
    /// Internal representation (optimized with SmallVec for small sets)
    inner: SubstitutionSetInner,
}

impl SubstitutionSet {
    /// Check if substitution (a, b) is allowed
    pub fn allows(&self, from: char, to: char) -> bool {
        match &self.inner {
            SubstitutionSetInner::Small(vec) => {
                // Linear scan for small sets (≤4 pairs)
                vec.iter().any(|(a, b)| *a == from_byte && *b == to_byte)
            }
            SubstitutionSetInner::Large(set) => {
                // Hash lookup for large sets (>4 pairs)
                set.contains(&(from_byte, to_byte))
            }
        }
    }

    /// Preset: Phonetic substitutions
    pub fn phonetic_basic() -> Self { /* ... */ }

    /// Preset: Keyboard QWERTY proximity
    pub fn keyboard_qwerty() -> Self { /* ... */ }

    /// Preset: OCR confusion sets
    pub fn ocr_friendly() -> Self { /* ... */ }
}
```

**Integration Point** (planned): `src/transducer/lazy.rs:250-300`

```rust
// Planned integration:
if policy.allows_substitution(query_char, dict_char) {
    successor.insert(Position::new(term_index + 1, num_errors + 1), algorithm, query_length);
}
```

**Status**: Data structure complete, transition logic integration pending.

### Universal Implementation

**Status**: 🚧 **Work in progress** — Same `SubstitutionSet` being used

**File**: `src/transducer/universal/substitution_policy.rs:1-50`

```rust
/// Policy for restricting substitution operations
pub trait SubstitutionPolicy: Clone + Debug {
    fn allows_substitution(&self, from: char, to: char) -> bool;
}

/// Unrestricted policy: all substitutions allowed
#[derive(Clone, Debug, Default)]
pub struct Unrestricted;

impl SubstitutionPolicy for Unrestricted {
    fn allows_substitution(&self, _from: char, _to: char) -> bool {
        true  // Always allow
    }
}

/// Restricted policy: only specific substitutions allowed
#[derive(Clone, Debug)]
pub struct Restricted {
    allowed: SubstitutionSet,  // Uses same implementation as lazy
}

impl SubstitutionPolicy for Restricted {
    fn allows_substitution(&self, from: char, to: char) -> bool {
        self.allowed.allows(from, to)
    }
}
```

**Integration Point** (planned): `src/transducer/universal/position.rs:250-300`

```rust
// Planned integration:
fn successors_with_policy<P: SubstitutionPolicy>(
    &self,
    bit_vector: &CharacteristicVector,
    policy: &P,
    max_distance: u8
) -> Vec<UniversalPosition<V>> {
    // Check policy before adding substitution successors
    if policy.allows_substitution(from_char, to_char) {
        successors.push(/* substitution successor */);
    }
}
```

**Status**: Policy trait defined, integration with successor generation pending.

### Comparison

Both implementations share the **same underlying `SubstitutionSet` data structure**, which directly corresponds to the paper's op^r concept. The main difference is:
- **Lazy**: Direct character comparison at transition time
- **Universal**: Policy check via characteristic vector

---

## 8. Diagonal Crossing (f_n, m_n, rm)

### Paper Definition (Section 9.2, Pages 2350-2352)

**Diagonal Crossing Detection**:
- **f_n(p, k)**: Returns `true` if position p has crossed the diagonal at input length k
- **rm(Q)**: Returns rightmost position in state Q
- **m_n(p, k)**: Converts I-type position to M-type when diagonal is crossed

**Purpose**: Determines when to transition from non-final (I) positions to final (M) positions during word processing.

### Lazy Implementation

**Status**: ❌ **Not applicable** — No I/M distinction in lazy automata

**Why**: Lazy automata use concrete indices and determine finality directly:

```rust
pub fn is_final(&self, query_length: usize) -> bool {
    // Final if we've consumed the entire query
    self.term_index >= query_length
}

pub fn infer_distance(&self, query_length: usize) -> Option<usize> {
    let remaining = query_length.saturating_sub(self.term_index);
    Some(self.num_errors + remaining)
}
```

There's no diagonal crossing check because finality is determined by comparing `term_index` with `query_length` directly.

### Universal Implementation

**Status**: 🐛 **Implemented but buggy** — Currently disabled due to premature conversions

**File**: `src/transducer/universal/diagonal.rs:1-200`

```rust
/// Check if diagonal has been crossed (f_n)
///
/// From thesis page 48: f_n(rm(Δ), |x|) checks if rightmost position
/// has crossed the diagonal at input length |x|.
pub fn diagonal_crossed(pos: &UniversalPosition<impl PositionVariant>,
                        input_length: usize,
                        max_distance: u8) -> bool {
    // Implementation based on offset and input_length comparison
    // FIXME: Currently produces false positives in some cases
}

/// Convert position from I-type to M-type (m_n)
///
/// From thesis page 48: m_n(Δ, |x|) converts all positions when
/// diagonal crossing is detected.
pub fn convert_position(pos: &UniversalPosition<impl PositionVariant>,
                        input_length: usize,
                        max_distance: u8) -> Option<UniversalPosition<impl PositionVariant>> {
    match pos {
        UniversalPosition::INonFinal { offset, errors, .. } => {
            // Convert to M-type
            UniversalPosition::new_m(*offset - input_length as i8, *errors, max_distance).ok()
        }
        _ => Some(pos.clone()),  // Already M-type
    }
}

/// Find rightmost position (rm)
pub fn right_most<'a, V: PositionVariant>(
    positions: impl Iterator<Item = &'a UniversalPosition<V>>
) -> Option<UniversalPosition<V>> {
    positions.max_by_key(|p| p.offset()).cloned()
}
```

**Integration in State Transition**: `src/transducer/universal/state.rs:310-360`

```rust
// TODO: Diagonal crossing integration needs fixing
// Currently disabled due to premature conversions

/*
if let Some(rm_pos) = diagonal::right_most(next_state.positions()) {
    if diagonal::diagonal_crossed(&rm_pos, input_length, self.max_distance) {
        // Apply m_n conversion to all positions
        let mut converted_state = Self::new(self.max_distance);
        for pos in &next_state.positions {
            if let Some(converted) = diagonal::convert_position(pos, input_length, self.max_distance) {
                converted_state.add_position(converted);
            }
        }

        if !converted_state.is_empty() {
            next_state = converted_state;
        }
    }
}
*/
```

**Bug Description** (from `TCS_2011_PAPER_ANALYSIS.md` Section 8):
- **Problem**: Diagonal crossing detection triggers premature I→M conversions
- **Root Cause**: Missing explicit `length_diff` (m) tracking in state
- **Consequence**: Violates position invariants, producing invalid conversions
- **Status**: Commented out until proper context (word lengths) available

**Proposed Fix** (from paper Section 9.2):

```rust
pub struct UniversalState<V: PositionVariant> {
    positions: SmallVec<[UniversalPosition<V>; 8]>,
    length_diff: i8,     // NEW: m ∈ [-c, +c] for diagonal tracking
    max_distance: u8,
}
```

With explicit `length_diff`, diagonal crossing can be correctly detected:
- `length_diff = |w| - |x|` (word length difference)
- Crossing occurs when `length_diff` exceeds bounds [-c, +c]

### Comparison

| Aspect | Lazy | Universal |
|--------|------|-----------|
| **Diagonal Crossing** | ❌ Not applicable | 🐛 Implemented but buggy |
| **I/M Conversion** | ❌ Not needed | 🐛 Disabled due to bug |
| **Finality Detection** | ✅ Direct index comparison | 🚧 Requires diagonal check |
| **Status** | Working correctly | Needs fix (see Section 8) |

**Action Required**: Fix diagonal crossing bug in universal implementation (high priority).

---

## 9. Characteristic Vector (β)

### Paper Definition (Section 4, Page 2342)

**Characteristic Vector**: β(a, w) is a bit vector where:
- β(a, w)[i] = 1 if w[i] = a
- β(a, w)[i] = 0 otherwise

**Example**: β('b', "abc") = [0, 1, 0] = "010"

**Purpose**: Abstracts character matching for alphabet-independent automaton construction. Universal automaton uses β instead of direct character comparison.

### Lazy Implementation

**Status**: ❌ **Not needed** — Direct character comparison sufficient

**Why**: Lazy automata are word-specific:

```rust
// Direct comparison at transition time
if query_char == dict_char {
    // Characters match
}
```

No need for bit vector abstraction because we have the actual characters available during transition computation.

### Universal Implementation

**Status**: ✅ **Fully implemented**

**File**: `src/transducer/universal/bit_vector.rs:1-100`

```rust
/// Characteristic vector β(a, w) encoding character matches
///
/// From thesis page 42: For character a and word w, β(a, w) is a bit vector
/// where bit i is 1 if w[i] = a, 0 otherwise.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CharacteristicVector {
    /// Bit vector: bits[i] = 1 if word[i] matches query character
    bits: SmallVec<[bool; 8]>,
}

impl CharacteristicVector {
    /// Create characteristic vector for character a in word w
    ///
    /// Example: β('b', "abc") = [false, true, false] = "010"
    pub fn new(query_char: char, word: &str) -> Self {
        let bits: SmallVec<[bool; 8]> = word
            .chars()
            .map(|c| c == query_char)
            .collect();

        Self { bits }
    }

    /// Get bit at position i
    pub fn get(&self, index: usize) -> bool {
        self.bits.get(index).copied().unwrap_or(false)
    }

    /// Get length of bit vector (word length)
    pub fn len(&self) -> usize {
        self.bits.len()
    }
}
```

**Usage**: Passed to `UniversalPosition::successors()` to determine operation applicability:

```rust
impl<V: PositionVariant> UniversalPosition<V> {
    pub fn successors(&self, bit_vector: &CharacteristicVector, max_distance: u8)
        -> Vec<UniversalPosition<V>>
    {
        let mut successors = Vec::new();

        // Check if match operation applies
        let match_bit = bit_vector.get(self.effective_position());
        if match_bit {
            // Match: ⟨1, 1, 0⟩
            successors.push(self.apply_match());
        }

        // Error operations always apply (independent of bit vector)
        if self.errors() < max_distance {
            successors.push(self.apply_substitution());
            successors.push(self.apply_insertion());
            successors.push(self.apply_deletion());
        }

        successors
    }
}
```

**Why It's Critical**: Universal automaton must work for **any word pair** without knowing them in advance. Characteristic vectors enable this by encoding character relationships in a word-agnostic way.

### Comparison

| Aspect | Lazy | Universal |
|--------|------|-----------|
| **Character Encoding** | Direct comparison | Bit vector (β) |
| **Alphabet Dependence** | Word-specific | Alphabet-independent |
| **Preprocessing** | None needed | Required for each character |
| **Purpose** | Runtime matching | Precomputed matching |

---

## 10. Summary Tables

### Implementation Status by Component

| Component | Lazy Status | Universal Status | Priority |
|-----------|-------------|------------------|----------|
| Bounded Diagonal Property | ✅ Applied | ✅ Applied | Complete |
| Operation Types | ⚠️ Hardcoded | ⚠️ Hardcoded | Medium |
| Subsumption | ✅ Implemented | ✅ Implemented | Complete |
| Anti-chain (⊔) | ✅ Implemented | ✅ Implemented | Complete |
| Matrix-State | ❌ N/A | ✅ Implemented | Complete |
| Preprocessing χ | ❌ N/A | ✅ Implemented | Complete |
| Restricted Substitutions | 🚧 In Progress | 🚧 In Progress | High |
| Diagonal Crossing | ❌ N/A | 🐛 Buggy | Critical |
| Characteristic Vector | ❌ N/A | ✅ Implemented | Complete |

### File Location Reference

#### Lazy Automata

| Concept | File(s) |
|---------|---------|
| State | `src/transducer/state.rs` |
| Position | `src/transducer/position.rs` |
| Transition Logic | `src/transducer/lazy.rs` |
| Algorithm Enum | `src/transducer/algorithm.rs` |
| SubstitutionSet | `src/transducer/substitution_set.rs` |

#### Universal Automata

| Concept | File(s) |
|---------|---------|
| State | `src/transducer/universal/state.rs` |
| Position | `src/transducer/universal/position.rs` |
| Subsumption | `src/transducer/universal/subsumption.rs` |
| Diagonal Crossing | `src/transducer/universal/diagonal.rs` |
| Characteristic Vector | `src/transducer/universal/bit_vector.rs` |
| Substitution Policy | `src/transducer/universal/substitution_policy.rs` |

---

## 11. Recommended Next Steps

Based on the implementation mapping analysis:

### Priority 1: Fix Diagonal Crossing Bug (Critical)
**File**: `src/transducer/universal/state.rs:310-360`
- Add explicit `length_diff` tracking to `UniversalState`
- Fix premature I→M conversions
- Re-enable diagonal crossing logic
- Add comprehensive tests

### Priority 2: Complete Restricted Substitutions (High)
**Files**:
- `src/transducer/lazy.rs` - Integrate `SubstitutionSet` into transition logic
- `src/transducer/universal/position.rs` - Integrate `SubstitutionPolicy` into successor generation
- Add integration tests for all presets

### Priority 3: Design Generalized Operations (Medium)
**New File**: `docs/design/generalized-operations.md`
- Define `OperationType` struct matching paper's ⟨t^x, t^y, t^w⟩
- Design API for custom operation sets
- Plan migration path from hardcoded `Algorithm` enum
- Consider impact on both lazy and universal implementations

### Priority 4: Create Implementation Tests (Medium)
**New Files**: Test files validating paper concepts
- Test bounded diagonal property holds for various n values
- Test subsumption matches paper's definition
- Test characteristic vector encoding matches β definition
- Validate against paper's examples (Section 11)

---

## References

1. **Primary Paper**:
   - Mitankin, P., Mihov, S., Schulz, K.U. (2011). "Deciding Word Neighborhood with Universal Neighborhood Automata". *Theoretical Computer Science*, 410(37-39):2339-2358.

2. **Related Documentation**:
   - [TCS_2011_PAPER_ANALYSIS.md](./TCS_2011_PAPER_ANALYSIS.md) - Full paper analysis
   - [TCS_2011_LAZY_APPLICABILITY.md](./TCS_2011_LAZY_APPLICABILITY.md) - Lazy applicability analysis
   - [THEORETICAL_FOUNDATIONS.md](./THEORETICAL_FOUNDATIONS.md) - Theory overview

3. **Implementation Files**: See Section 10 tables above

---

**Document Version**: 1.0
**Last Updated**: 2025-11-12
**Author**: Claude Code (Anthropic AI Assistant)
**Purpose**: Concrete mapping from TCS 2011 paper to liblevenshtein-rust implementation
