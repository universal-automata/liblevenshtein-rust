# Universal Levenshtein Automata - Implementation Research

**Date**: 2025-11-06
**Status**: Research & Planning Phase

---

## Overview

**Universal Levenshtein Automata** extends the standard Levenshtein distance by allowing **restricted substitutions** - where certain character pairs cannot be substituted for each other. This directory contains research, analysis, and implementation planning for adding restricted substitutions to liblevenshtein-rust.

### What Problem Does It Solve?

Standard Levenshtein distance allows **any** character to be substituted for any other character. In practice, many applications have constraints:

- **Spell checkers**: Only keyboard-adjacent keys should substitute (e.g., 'a'↔'s' plausible, 'a'↔'z' unlikely)
- **OCR correction**: Only visually similar characters should substitute (e.g., '1'↔'I', 'O'↔'0')
- **Phonetic matching**: Only sound-alike characters should substitute (e.g., 'f'↔'ph', 's'↔'c')
- **Handwriting recognition**: Only similar shapes should substitute

### The Solution: Restricted Substitutions

Instead of allowing **all** substitutions, define a set `S ⊆ Σ × Σ` of **allowed** character pairs:

```
Standard Levenshtein:  Can substitute any (a,b)
Restricted (S):        Can substitute (a,b) only if (a,b) ∈ S
```

**Example**:
```
Alphabet: {a, b, c, d, h, k, n, z}
Allowed:  S = {(a,d), (d,a), (h,k), (h,n)}

Query: "hahd"
Dict:  "hand"

✅ Distance = 1  (h→n substitution allowed, because (h,n) ∈ S)

But if (h,n) ∉ S:
❌ Distance > 1  (would require delete 'h' + insert 'n')
```

This **improves precision** by rejecting unrealistic error patterns.

---

## Original Paper

**Title**: "Universal Levenshtein Automata for a Generalization of the Levenshtein Distance"

**Authors**: Petar Mitankin, Stoyan Mihov, Klaus U. Schulz
*(Same authors as your current Levenshtein automata implementation!)*

**Published**: Annuaire de l'Université de Sofia "St. Kliment Ohridski", Tome 99, 2009, pages 5-23

**Location**: `/home/dylon/Papers/Approximate String Matching/Universal Levenshtein Automata for a Generalization of the Levenshtein Distance.pdf`

**Key Contributions**:
1. Extends universal Levenshtein automata to handle restricted substitutions
2. Maintains **deterministic** automaton property
3. Works with additional operations (transposition, merge, split)
4. Provides construction algorithm for universal automaton A_n^∀

---

## Documentation Index

### Analysis Documents
- **[technical-analysis.md](./technical-analysis.md)** - Current codebase analysis, gaps, integration points
- **[use-cases.md](./use-cases.md)** - Practical applications, example substitution sets, real-world scenarios

### Planning Documents
- **[implementation-plan.md](./implementation-plan.md)** - Phase-by-phase implementation (4 phases, 2-4 weeks)
- **[decision-matrix.md](./decision-matrix.md)** - Implementation approach comparison and recommendation
- **[architectural-sketches.md](./architectural-sketches.md)** - Code designs, trait definitions, struct layouts

### Tracking Documents
- **[progress-tracker.md](./progress-tracker.md)** - Task breakdown, status tracking, milestone monitoring

---

## Current Status

**Status**: ⏳ Research Phase - Not Yet Implemented

**Decision**: Pending approval of implementation approach

**Estimated Effort**: 2-4 weeks

**Implementation Phases**:
1. **Phase 1**: Core Restricted Substitutions (1-2 weeks)
2. **Phase 2**: Practical Use Cases (1 week)
3. **Phase 3**: Integration with Existing Algorithms (1 week)
4. **Phase 4**: Optimization (optional, 1 week)

---

## Quick Start

### For Researchers

1. **Understand the concept**:
   - Read this README for overview
   - Read [use-cases.md](./use-cases.md) for practical applications
   - Review the paper for algorithmic details

2. **Assess applicability**:
   - Check if your use case needs restricted substitutions
   - Compare with weighted distance (see [decision-matrix.md](./decision-matrix.md))

3. **Explore current architecture**:
   - Read [technical-analysis.md](./technical-analysis.md) for codebase details
   - Understand current Algorithm enum and transition logic

### For Implementers

1. **Review implementation plan**:
   - Read [implementation-plan.md](./implementation-plan.md) for phase breakdown
   - Check [architectural-sketches.md](./architectural-sketches.md) for code designs

2. **Select approach**:
   - Review [decision-matrix.md](./decision-matrix.md)
   - Consider Option A (New Algorithm Variant) vs Option B (Configuration)

3. **Track progress**:
   - Use [progress-tracker.md](./progress-tracker.md) for task management
   - Update status as tasks complete

---

## Key Concepts

### Restricted Substitutions (Set S)

**Definition** (from paper, Section 2):

The generalized distance `d_L^S(w, x)` is defined as the minimum number of operations to transform `w` into `x`, where:
- **Insert**: Add a character (cost = 1)
- **Delete**: Remove a character (cost = 1)
- **Substitute**: Replace character `a` with `b` **only if** `(a,b) ∈ S` (cost = 1)

When `S = Σ × Σ` (all pairs), this reduces to standard Levenshtein distance.

### Characteristic Vector Extension

**Standard Levenshtein**: Uses characteristic vector χ(a, w[i:j])
- Binary: 1 if character `a` appears at position, 0 otherwise

**Universal with S**: Uses S-characteristic vector χ_s(a, w[i:j])
- Binary: 1 if `(w[i], a) ∈ S` (substitution allowed), 0 otherwise

This is the **key modification** needed in the codebase.

### Universal Automaton A_n^∀

The paper constructs a **universal automaton** `A_n^∀` that:
- Is **independent** of specific query/dictionary words
- Works for **any** error bound `n`
- Maintains **deterministic** property
- Can be combined with transposition, merge, and split operations

---

## What Universal LA Enables

### ✅ Capabilities Added

1. **Keyboard-proximity constraints**
   - QWERTY layout: 'a' can substitute for 's', 'd', 'w', 'q', 'z'
   - AZERTY layout: Different adjacency rules
   - Dvorak layout: Yet another set of constraints

2. **OCR error modeling**
   - Visual similarity: '1' ↔ 'I' ↔ 'l', 'O' ↔ '0', 'S' ↔ '5'
   - Font-specific confusions
   - Context-aware restrictions

3. **Phonetic matching**
   - Sound-alike constraints: 'f' ↔ 'ph', 's' ↔ 'c', 'k' ↔ 'c'
   - Language-specific phonetic rules
   - Syllable-based restrictions

4. **Handwriting recognition**
   - Shape similarity: 'a' ↔ 'o', 'n' ↔ 'm', 'u' ↔ 'v'
   - Context-dependent confusions

5. **Script-based restrictions**
   - Block substitutions between Latin, Cyrillic, Greek scripts
   - Prevent impossible character confusions

6. **Combination with existing operations**
   - Restricted substitutions + Transposition
   - Restricted substitutions + MergeAndSplit

### ❌ Capabilities NOT Added

**Important limitations**:

1. **NOT weighted/variable costs**
   - All allowed operations still cost = 1
   - Restricted substitutions are **binary**: either allowed (cost=1) or blocked (cost=∞)
   - For continuous costs, see weighted Levenshtein distance (different approach)

2. **NOT arbitrary new operation types**
   - Paper covers: substitution, insertion, deletion, transposition, merge, split
   - Other operations would require extending the theory

3. **NOT non-deterministic automata**
   - Maintains determinism (critical for performance)

---

## Comparison: Universal LA vs Alternatives

| Feature | Universal LA | Weighted Distance | Standard LA (Current) |
|---------|-------------|-------------------|----------------------|
| **Restricted substitutions** | ✅ Yes (binary) | ✅ Yes (cost threshold) | ❌ No (all allowed) |
| **Variable operation costs** | ❌ No (uniform=1) | ✅ Yes (continuous) | ❌ No (uniform=1) |
| **Keyboard proximity** | ✅ Built-in | ⚠️ Via cost matrix | ❌ No |
| **OCR modeling** | ✅ Built-in | ⚠️ Via cost matrix | ❌ No |
| **Phonetic rules** | ✅ Built-in | ⚠️ Via cost matrix | ❌ No |
| **Deterministic** | ✅ Yes | ⚠️ Complex | ✅ Yes |
| **Implementation complexity** | 🟡 Moderate | 🔴 High | 🟢 Current |
| **Performance impact** | 🟡 ~10-20% overhead | 🔴 Significant | 🟢 Baseline |

**When to Use Each**:
- **Standard LA** (current): General fuzzy matching, no constraints
- **Universal LA**: Specific error patterns, binary restrictions (keyboard, OCR, phonetic)
- **Weighted Distance**: Continuous cost functions, character-specific weights

---

## Implementation Strategy

### Recommended Approach

**Option B: Configuration-Based** (Recommended)

Add substitution set as **optional configuration** rather than new Algorithm variant:

```rust
pub struct TransducerBuilder {
    algorithm: Algorithm,              // Existing: Standard, Transposition, MergeAndSplit
    substitution_set: Option<SubstitutionSet>,  // NEW: None = all allowed
}
```

**Advantages**:
- Works with all existing algorithms (Standard, Transposition, MergeAndSplit)
- Backward compatible (None = current behavior)
- Clean separation of concerns
- Flexible composition

**Alternative: Option A** (New Variant)

Add as 4th Algorithm variant:

```rust
pub enum Algorithm {
    Standard,
    Transposition,
    MergeAndSplit,
    RestrictedSubstitution,  // NEW
}
```

**Trade-offs**: See [decision-matrix.md](./decision-matrix.md) for detailed comparison.

---

## Key Requirements

### Critical Components Needed

1. ✅ **SubstitutionSet structure**
   - Store allowed character pairs efficiently
   - Fast lookup (HashSet or perfect hashing)
   - Serialization support

2. ✅ **S-characteristic vector**
   - Extend current χ implementation
   - Check `(query_char, dict_char) ∈ S` for substitutions

3. ⚠️ **Modified transition functions**
   - transition.rs: Check substitution validity
   - Respect restricted substitutions in state computation

4. ⚠️ **Adjusted subsumption logic**
   - Paper notes: `d_L^S` may not satisfy triangle inequality
   - May need modified subsumption predicates

5. ✅ **Builder API extensions**
   - `.with_substitution_set(set)` method
   - Predefined sets: keyboard layouts, phonetic rules, OCR rules

6. ✅ **Preset substitution sets**
   - QWERTY keyboard
   - AZERTY keyboard
   - Dvorak keyboard
   - Common phonetic rules
   - OCR visual similarity

---

## Performance Expectations

### Expected Overhead

**Optimistic**: 5-10% slowdown (if substitution set lookups are fast)

**Realistic**: 10-20% slowdown (due to additional checks in transitions)

**Worst-case**: 30% slowdown (if substitution set is large and lookups are slow)

**Mitigation strategies**:
- Use HashSet for O(1) lookup
- Consider perfect hashing for static sets
- Cache lookup results in hot paths
- SIMD-friendly data structures

### When Is Overhead Worth It?

**High value**:
- Spell checkers (keyboard proximity critical)
- OCR systems (visual confusion sets)
- Phonetic search (sound-alike constraints)
- Handwriting recognition (shape similarity)

**Low value**:
- General fuzzy matching (no specific error patterns)
- Very small dictionaries (overhead dominates)
- Ultra-low latency requirements (every nanosecond counts)

---

## Related Documentation

### Library Documentation
- [Algorithm Layer](/docs/algorithms/02-levenshtein-automata/README.md) - Current automata implementation
- [Transducer Module](/src/transducer/mod.rs) - State machines and transitions
- [Position/State Tracking](/src/transducer/position.rs) - How positions are tracked

### Other Research
- [WallBreaker](/docs/research/wallbreaker/README.md) - Pattern splitting for large error bounds
- [GPU Acceleration](/docs/research/comparative-analysis/gpu-acceleration.md) - Performance analysis

### Code Locations
- `/src/transducer/algorithm.rs` - Algorithm enum (Standard, Transposition, MergeAndSplit)
- `/src/transducer/position.rs` - Position structure and subsumption logic
- `/src/transducer/transition.rs` - State transition functions
- `/src/transducer/builder.rs` - API for configuring fuzzy search

---

## Example: Keyboard-Proximity Spell Checker

```rust
use liblevenshtein::prelude::*;

// Define QWERTY keyboard adjacency
let mut qwerty = SubstitutionSet::new();

// Row 1: qwertyuiop
qwerty.add_bidirectional('q', 'w');
qwerty.add_bidirectional('w', 'e');
qwerty.add_bidirectional('w', 'q');
// ... (add all adjacent pairs)

// Row 2: asdfghjkl
qwerty.add_bidirectional('a', 's');
qwerty.add_bidirectional('a', 'w');  // diagonal adjacency
// ... (add all adjacent pairs)

// Build dictionary with restricted substitutions
let dict = TransducerBuilder::new()
    .algorithm(Algorithm::Standard)
    .with_substitution_set(qwerty)
    .build_from_iter(words);

// Query: "tesy" (typo for "test", 'y' adjacent to 't' on keyboard)
let results: Vec<_> = dict.fuzzy_search("tesy", 1).collect();
// ✅ Returns: ["test"] - because 'y'↔'t' is keyboard-adjacent

// Query: "texz" (unlikely typo, 'x' not adjacent to 's')
let results: Vec<_> = dict.fuzzy_search("texz", 1).collect();
// ❌ Returns: [] or distant matches - because 'x'↔'s' not keyboard-adjacent
```

---

## Contact & Discussion

For questions or discussion about Universal Levenshtein Automata:
- Review documentation in this directory
- Check paper for algorithmic details
- Open GitHub issues for implementation questions

---

## License

Documentation follows Apache-2.0 license (same as main library).

---

**Last Updated**: 2025-11-06
**Status**: Research & Planning Phase
**Next Step**: Review documentation, select implementation approach, begin Phase 1
