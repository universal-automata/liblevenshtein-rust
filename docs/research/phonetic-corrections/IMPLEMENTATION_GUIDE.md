# English Phonetic Corrections: Practical Implementation Guide

**Date**: 2025-11-12
**Status**: 📋 **READY FOR IMPLEMENTATION**
**Prerequisite Reading**: [English Phonetic Feasibility Analysis](ENGLISH_PHONETIC_FEASIBILITY.md)
**Related Documents**:
- [Generalized Operations Design](../../design/generalized-operations.md)
- [TCS 2011 Implementation Mapping](../universal-levenshtein/TCS_2011_IMPLEMENTATION_MAPPING.md)

---

## Executive Summary

This guide provides step-by-step instructions for implementing English phonetic correction support in liblevenshtein-rust using the generalized operation framework.

**Target Audience**: Rust developers implementing the phonetic matching feature

**Estimated Effort**:
- Phase 1 (60-70% coverage): 3-5 days
- Phase 2 (75-85% coverage): 2-3 weeks
- Phase 3 (80-85% coverage): 2-3 weeks

**Prerequisites**:
- Generalized operation framework implemented (see [generalized-operations.md](../../design/generalized-operations.md))
- Understanding of universal Levenshtein automata (see [TCS_2011_PAPER_ANALYSIS.md](../universal-levenshtein/TCS_2011_PAPER_ANALYSIS.md))

---

## Table of Contents

1. [Quick Start](#1-quick-start)
2. [Phase 1: Core Phonetic Operations](#2-phase-1-core-phonetic-operations)
3. [Phase 2: Extended Operations](#3-phase-2-extended-operations)
4. [Phase 3: Context Extensions](#4-phase-3-context-extensions)
5. [Testing Strategy](#5-testing-strategy)
6. [Performance Tuning](#6-performance-tuning)
7. [Integration Examples](#7-integration-examples)
8. [Troubleshooting](#8-troubleshooting)

---

## 1. Quick Start

### 1.1 Minimal Working Example

```rust
use liblevenshtein::operation::{OperationSet, OperationSetBuilder, OperationType};
use liblevenshtein::substitution::SubstitutionSet;
use liblevenshtein::transducer::UniversalAutomaton;

// Create basic phonetic operation set
let ops = OperationSetBuilder::new()
    .with_match()

    // Consonant digraphs: ch→ç, sh→$, ph→f, th→+
    .with_operation(OperationType::with_restriction(
        2, 1, 0.15,
        SubstitutionSet::from_pairs(&[
            ("ch", "ç"), ("sh", "$"), ("ph", "f"), ("th", "+"),
        ]),
        "consonant_digraphs",
    ))

    // Vowel digraphs: ea→ë, ee→ë, oa→ö
    .with_operation(OperationType::with_restriction(
        2, 1, 0.15,
        SubstitutionSet::from_pairs(&[
            ("ea", "ë"), ("ee", "ë"), ("oa", "ö"),
        ]),
        "vowel_digraphs",
    ))

    .with_standard_ops()
    .build();

// Create automaton for query
let automaton = UniversalAutomaton::new("telephone", 2, &ops);

// Check matches
assert!(automaton.accepts("tel@fön"));  // Phonetic spelling
assert!(automaton.accepts("telefone")); // Common misspelling
```

### 1.2 File Structure

Create the following files:

```
src/
  transducer/
    operation/
      mod.rs               # Operation module
      phonetic.rs          # NEW: Phonetic operation builders
      context.rs           # NEW (Phase 3): Context patterns

tests/
  phonetic/
    mod.rs                 # Test module
    core_operations.rs     # Phase 1 tests
    extended_operations.rs # Phase 2 tests
    context_operations.rs  # Phase 3 tests

benches/
  phonetic_matcher.rs      # Performance benchmarks

docs/
  research/
    phonetic-corrections/
      ENGLISH_PHONETIC_FEASIBILITY.md  # Already created
      IMPLEMENTATION_GUIDE.md          # This file
```

---

## 2. Phase 1: Core Phonetic Operations

**Goal**: Implement fully modelable rules (60-70% coverage)
**Effort**: 3-5 days
**Files**: `src/transducer/operation/phonetic.rs`

### 2.1 Module Setup

**File**: `src/transducer/operation/phonetic.rs`

```rust
//! Phonetic operation sets for English spelling corrections
//!
//! Based on analysis from https://zompist.com/spell.html
//! See docs/research/phonetic-corrections/ENGLISH_PHONETIC_FEASIBILITY.md

use crate::operation::{OperationSet, OperationSetBuilder, OperationType};
use crate::substitution::SubstitutionSet;

/// Creates a basic phonetic operation set for English
///
/// Coverage: ~60-70% of common phonetic transformations
/// Memory: ~1-8 MB
/// Use cases: Spell checking, fuzzy search, OCR correction
///
/// # Examples
///
/// ```
/// use liblevenshtein::operation::phonetic::phonetic_english_basic;
/// use liblevenshtein::transducer::UniversalAutomaton;
///
/// let ops = phonetic_english_basic();
/// let automaton = UniversalAutomaton::new("telephone", 2, &ops);
///
/// assert!(automaton.accepts("tel@fön"));
/// ```
pub fn phonetic_english_basic() -> OperationSet {
    OperationSetBuilder::new()
        .with_match()
        .with_operation(consonant_digraphs())
        .with_operation(vowel_digraphs())
        .with_operation(vowel_trigraphs())
        .with_operation(silent_e_deletion())
        .with_operation(double_consonant_simplification())
        .with_operation(initial_cluster_reduction())
        .with_operation(y_digraphs())
        .with_standard_ops()
        .build()
}
```

### 2.2 Consonant Digraphs

**Implementation**:

```rust
/// Consonant digraphs: ch→ç, sh→$, ph→f, th→+, qu→kw, wr→r, wh→w
///
/// Coverage: ~25% of English words
/// Examples:
/// - "phone" → "fön" (ph→f)
/// - "church" → "çurç" (ch→ç)
/// - "write" → "rït" (wr→r)
fn consonant_digraphs() -> OperationType {
    OperationType::with_restriction(
        2, 1, 0.15,  // 2 chars → 1 char, low cost (phonetically equivalent)
        SubstitutionSet::from_pairs(&[
            ("ch", "ç"),  // church → çurç
            ("sh", "$"),  // ship → $ip
            ("ph", "f"),  // phone → fön
            ("th", "+"),  // think → +ink
            ("qu", "kw"), // queen → kwën
            ("wr", "r"),  // write → rït
            ("wh", "w"),  // white → wït
            ("rh", "r"),  // rhyme → rïm
        ]),
        "consonant_digraphs",
    )
}
```

**Test**:

**File**: `tests/phonetic/core_operations.rs`

```rust
#[test]
fn test_consonant_digraphs() {
    let ops = phonetic_english_basic();

    // Test ch→ç
    let automaton = UniversalAutomaton::new("church", 2, &ops);
    assert!(automaton.accepts("çurç"));

    // Test ph→f
    let automaton = UniversalAutomaton::new("phone", 2, &ops);
    assert!(automaton.accepts("fön"));

    // Test multiple digraphs
    let automaton = UniversalAutomaton::new("photograph", 2, &ops);
    assert!(automaton.accepts("fötögräf"));
}
```

### 2.3 Vowel Digraphs

**Implementation**:

```rust
/// Vowel digraphs (2→1): ea→ë, ee→ë, ai→ä, oa→ö, etc.
///
/// Coverage: ~40% of multi-syllable words
/// Examples:
/// - "read" → "rëd" (ea→ë)
/// - "boat" → "böt" (oa→ö)
fn vowel_digraphs() -> OperationType {
    OperationType::with_restriction(
        2, 1, 0.15,
        SubstitutionSet::from_pairs(&[
            ("ea", "ë"), ("ee", "ë"),  // eat→ët, bee→bë
            ("ai", "ä"), ("ay", "ä"),  // wait→wät, day→dä
            ("oa", "ö"),                // boat→böt
            ("au", "ò"), ("aw", "ò"),  // caught→kòt, law→lò
            ("ou", "ôw"), ("ow", "ôw"), // loud→lôwd, cow→kôw
            ("oi", "öy"), ("oy", "öy"), // oil→öyl, boy→böy
            ("eu", "ü"), ("ew", "ü"),  // feud→füd, new→nü
            ("ie", "ë"),                // believe→bëlëv (common case)
            ("oo", "u"),                // food→fud
        ]),
        "vowel_digraphs",
    )
}

/// Vowel trigraphs (3→1): eau→ö
///
/// Less common but high-value patterns
fn vowel_trigraphs() -> OperationType {
    OperationType::with_restriction(
        3, 1, 0.2,
        SubstitutionSet::from_pairs(&[
            ("eau", "ö"),  // beauty→büty
            ("eou", "ü"),  // feud variants
        ]),
        "vowel_trigraphs",
    )
}
```

**Test**:

```rust
#[test]
fn test_vowel_digraphs() {
    let ops = phonetic_english_basic();

    // Test ea→ë
    let automaton = UniversalAutomaton::new("read", 2, &ops);
    assert!(automaton.accepts("rëd"));

    // Test multiple digraphs
    let automaton = UniversalAutomaton::new("beautiful", 2, &ops);
    assert!(automaton.accepts("büt@f@l"));
}
```

### 2.4 Silent E Deletion

**Implementation**:

```rust
/// Silent final 'e' deletion
///
/// Note: Without position context, applies to all 'e'
/// Edit distance threshold filters incorrect applications
///
/// Coverage: ~30% of words
/// Examples:
/// - "rate" → "rät" (final e deleted)
/// - "take" → "täk"
fn silent_e_deletion() -> OperationType {
    OperationType::with_restriction(
        1, 0, 0.1,  // Deletion with low cost
        SubstitutionSet::from_chars(&['e']),
        "silent_e",
    )
}
```

**Test**:

```rust
#[test]
fn test_silent_e() {
    let ops = phonetic_english_basic();

    let automaton = UniversalAutomaton::new("rate", 2, &ops);
    assert!(automaton.accepts("rät"));

    let automaton = UniversalAutomaton::new("take", 2, &ops);
    assert!(automaton.accepts("täk"));
}
```

### 2.5 Double Consonant Simplification

**Implementation**:

```rust
/// Double consonant simplification: bb→b, cc→c, etc.
///
/// Coverage: ~20% of words
/// Examples:
/// - "running" → "runing" (nn→n)
/// - "committee" → "comitë" (mm→m, tt→t, ee→ë)
fn double_consonant_simplification() -> OperationType {
    OperationType::with_restriction(
        2, 1, 0.1,
        SubstitutionSet::double_consonants(),
        "geminate_simplification",
    )
}
```

**Helper for SubstitutionSet**:

**File**: `src/substitution.rs` (extend existing)

```rust
impl SubstitutionSet {
    /// Creates a set for all double consonants (bb→b, cc→c, etc.)
    pub fn double_consonants() -> Self {
        const CONSONANTS: &str = "bcdfghjklmnpqrstvwxyz";
        let pairs: Vec<(&str, &str)> = CONSONANTS.chars()
            .map(|c| {
                let double = format!("{}{}", c, c);
                let single = c.to_string();
                // Leak strings to get 'static lifetime (acceptable for const data)
                let double_static: &'static str = Box::leak(double.into_boxed_str());
                let single_static: &'static str = Box::leak(single.into_boxed_str());
                (double_static, single_static)
            })
            .collect();
        SubstitutionSet::from_pairs(&pairs)
    }
}
```

**Test**:

```rust
#[test]
fn test_double_consonants() {
    let ops = phonetic_english_basic();

    let automaton = UniversalAutomaton::new("running", 2, &ops);
    assert!(automaton.accepts("runing"));

    let automaton = UniversalAutomaton::new("committee", 2, &ops);
    assert!(automaton.accepts("comitë"));
}
```

### 2.6 Initial Cluster Reduction

**Implementation**:

```rust
/// Initial consonant cluster reduction: kn→n, gn→n, ps→s, etc.
///
/// Note: Without position context, applies everywhere
/// Acceptable with edit distance threshold
///
/// Coverage: ~5% of words
/// Examples:
/// - "knight" → "nït" (kn→n)
/// - "psychology" → "sïkölöjë" (ps→s)
fn initial_cluster_reduction() -> OperationType {
    OperationType::with_restriction(
        2, 1, 0.15,
        SubstitutionSet::from_pairs(&[
            ("kn", "n"),  // knight→nït
            ("gn", "n"),  // gnat→nât
            ("pn", "n"),  // pneumonia→nümönië
            ("mn", "n"),  // mnemonic→nëmönik
            ("pt", "t"),  // pterodactyl→têrödäktil
            ("ps", "s"),  // psychology→sïkölöjë
        ]),
        "initial_cluster_reduction",
    )
}
```

### 2.7 Y Digraphs

**Implementation**:

```rust
/// Y digraphs: ey→ë, ay→ä, oy→öy
///
/// Coverage: ~10% of words
/// Examples:
/// - "key" → "kë" (ey→ë)
/// - "boy" → "böy" (oy→öy)
fn y_digraphs() -> OperationType {
    OperationType::with_restriction(
        2, 1, 0.15,
        SubstitutionSet::from_pairs(&[
            ("ey", "ë"),  // key→kë
            ("ay", "ä"),  // say→sä
            ("oy", "öy"), // boy→böy
        ]),
        "y_digraphs",
    )
}
```

### 2.8 Module Export

**File**: `src/transducer/operation/mod.rs`

```rust
pub mod phonetic;

// Re-export for convenience
pub use phonetic::{
    phonetic_english_basic,
    // Add more as implemented
};
```

### 2.9 Integration Test

**File**: `tests/phonetic/core_operations.rs`

```rust
use liblevenshtein::operation::phonetic::phonetic_english_basic;
use liblevenshtein::transducer::UniversalAutomaton;

#[test]
fn test_telephone_example() {
    let ops = phonetic_english_basic();
    let automaton = UniversalAutomaton::new("telephone", 2, &ops);

    // Phonetic spelling
    assert!(automaton.accepts("tel@fön"));

    // Common misspelling
    assert!(automaton.accepts("telefone"));
}

#[test]
fn test_beautiful_example() {
    let ops = phonetic_english_basic();
    let automaton = UniversalAutomaton::new("beautiful", 3, &ops);

    assert!(automaton.accepts("büt@f@l"));
}

#[test]
fn test_psychology_example() {
    let ops = phonetic_english_basic();
    let automaton = UniversalAutomaton::new("psychology", 3, &ops);

    assert!(automaton.accepts("sïkölöjë"));
}
```

### 2.10 Benchmark

**File**: `benches/phonetic_matcher.rs`

```rust
use criterion::{black_box, criterion_group, criterion_main, Criterion, BenchmarkId};
use liblevenshtein::operation::phonetic::phonetic_english_basic;
use liblevenshtein::transducer::UniversalAutomaton;

fn bench_phonetic_construction(c: &mut Criterion) {
    let ops = phonetic_english_basic();

    let words = vec![
        ("short", 5),
        ("telephone", 10),
        ("beautiful", 10),
        ("psychology", 15),
        ("extraordinary", 20),
    ];

    for (word, len) in words {
        c.bench_with_input(
            BenchmarkId::new("construct", len),
            &word,
            |b, &word| {
                b.iter(|| {
                    UniversalAutomaton::new(black_box(word), 2, &ops)
                })
            },
        );
    }
}

fn bench_phonetic_matching(c: &mut Criterion) {
    let ops = phonetic_english_basic();
    let automaton = UniversalAutomaton::new("telephone", 2, &ops);

    c.bench_function("match/telephone", |b| {
        b.iter(|| automaton.accepts(black_box("tel@fön")))
    });
}

criterion_group!(benches, bench_phonetic_construction, bench_phonetic_matching);
criterion_main!(benches);
```

**Run benchmarks**:

```bash
RUSTFLAGS="-C target-cpu=native" taskset -c 0 cargo bench --bench phonetic_matcher
```

### 2.11 Phase 1 Checklist

- [ ] Create `src/transducer/operation/phonetic.rs`
- [ ] Implement consonant digraphs
- [ ] Implement vowel digraphs
- [ ] Implement vowel trigraphs
- [ ] Implement silent e deletion
- [ ] Implement double consonant simplification
- [ ] Implement initial cluster reduction
- [ ] Implement y digraphs
- [ ] Add `SubstitutionSet::double_consonants()` helper
- [ ] Create integration tests
- [ ] Create benchmarks
- [ ] Run tests: `cargo test --test phonetic`
- [ ] Run benchmarks: `cargo bench --bench phonetic_matcher`
- [ ] Measure coverage on test corpus (see Section 5.3)
- [ ] Document expected coverage: 60-70%

---

## 3. Phase 2: Extended Operations

**Goal**: Implement partially modelable rules with approximations (75-85% coverage)
**Effort**: 2-3 weeks
**Prerequisite**: Phase 1 complete

### 3.1 Extended Operation Set

**File**: `src/transducer/operation/phonetic.rs`

```rust
/// Creates an extended phonetic operation set for English
///
/// Coverage: ~75-85% of phonetic transformations
/// Memory: ~8-50 MB
/// Includes: Context-encoded patterns, larger operations (d=3,4)
///
/// # Examples
///
/// ```
/// use liblevenshtein::operation::phonetic::phonetic_english_extended;
/// use liblevenshtein::transducer::UniversalAutomaton;
///
/// let ops = phonetic_english_extended();
/// let automaton = UniversalAutomaton::new("daughter", 3, &ops);
///
/// assert!(automaton.accepts("dòt@r"));
/// ```
pub fn phonetic_english_extended() -> OperationSet {
    OperationSetBuilder::new()
        .with_match()

        // Include Phase 1 operations
        .with_operation(consonant_digraphs())
        .with_operation(vowel_digraphs())
        .with_operation(vowel_trigraphs())
        .with_operation(silent_e_deletion())
        .with_operation(double_consonant_simplification())
        .with_operation(initial_cluster_reduction())
        .with_operation(y_digraphs())

        // Phase 2 additions
        .with_operation(velar_softening_contextual())
        .with_operation(vowel_r_coloring())
        .with_operation(vowel_double_r())
        .with_operation(gh_vowel_lengthening())
        .with_operation(gh_before_vowel())
        .with_operation(aught_ought_patterns())
        .with_operation(ough_variants())
        .with_operation(silent_gh())
        .with_operation(tion_sion_endings())

        .with_standard_ops()
        .build()
}
```

### 3.2 Context-Encoded C/G Softening

**Implementation**:

```rust
/// Context-encoded c/g softening
///
/// c→s before e/i/y (cell→sêl)
/// c→k elsewhere (cow→kôw)
/// g→j before e/i/y (gel→jêl)
///
/// Method 2 from feasibility analysis: pre-encode context
fn velar_softening_contextual() -> OperationType {
    OperationType::with_restriction(
        2, 2, 0.25,
        SubstitutionSet::from_pairs(&[
            // Soft c before front vowels
            ("ce", "se"), ("ci", "si"), ("cy", "sy"),

            // Hard c elsewhere
            ("ca", "ka"), ("co", "ko"), ("cu", "ku"),

            // Soft g before front vowels
            ("ge", "je"), ("gi", "ji"), ("gy", "jy"),

            // Note: Hard g is just 'g', handled by match operation
        ]),
        "velar_softening",
    )
}
```

**Test**:

```rust
#[test]
fn test_velar_softening() {
    let ops = phonetic_english_extended();

    // Soft c
    let automaton = UniversalAutomaton::new("ceiling", 3, &ops);
    assert!(automaton.accepts("sëling"));

    // Hard c
    let automaton = UniversalAutomaton::new("cat", 3, &ops);
    assert!(automaton.accepts("kât"));

    // Soft g
    let automaton = UniversalAutomaton::new("gel", 3, &ops);
    assert!(automaton.accepts("jêl"));
}
```

### 3.3 Vowel-R Interactions

**Implementation**:

```rust
/// Vowel + single r coloring
///
/// ar→ôr, er→@r, ir→@r, or→ör, ur→@r
fn vowel_r_coloring() -> OperationType {
    OperationType::with_restriction(
        2, 2, 0.3,
        SubstitutionSet::from_pairs(&[
            ("ar", "ôr"),  // car→kôr
            ("er", "@r"),  // her→h@r
            ("ir", "@r"),  // sir→s@r
            ("or", "ör"),  // for→för
            ("ur", "@r"),  // fur→f@r
        ]),
        "vowel_r_coloring",
    )
}

/// Vowel + double r simplification + coloring
///
/// arr→är, err→är, irr→är, orr→är, urr→är
fn vowel_double_r() -> OperationType {
    OperationType::with_restriction(
        3, 2, 0.3,
        SubstitutionSet::from_pairs(&[
            ("arr", "är"),  // carry→kärë
            ("err", "är"),  // error→är@r
            ("irr", "är"),  // mirror→mir@r
            ("orr", "är"),  // sorry→särë
            ("urr", "är"),  // hurry→härë
        ]),
        "vowel_double_r",
    )
}
```

### 3.4 Complex GH Patterns

**Implementation**:

```rust
/// GH vowel lengthening patterns
///
/// igh→ï (right→rït)
/// eigh→ä (eight→ät)
fn gh_vowel_lengthening() -> OperationType {
    OperationType::with_restriction(
        3, 1, 0.2,
        SubstitutionSet::from_pairs(&[
            ("igh", "ï"),   // right→rït
            ("eigh", "ä"),  // eight→ät
        ]),
        "gh_lengthening",
    )
}

/// GH before vowels: gh→g
///
/// gha→ga, ghe→ge, etc.
fn gh_before_vowel() -> OperationType {
    OperationType::with_restriction(
        3, 2, 0.25,
        SubstitutionSet::from_pairs(&[
            ("gha", "ga"), ("ghe", "ge"), ("ghi", "gi"),
            ("gho", "go"), ("ghu", "gu"),
        ]),
        "gh_before_vowel",
    )
}

/// aught/ought patterns
///
/// aught→òt, ought→òt
fn aught_ought_patterns() -> OperationType {
    OperationType::with_restriction(
        4, 2, 0.25,
        SubstitutionSet::from_pairs(&[
            ("aught", "òt"),  // daughter→dòt@r
            ("ought", "òt"),  // bought→bòt
        ]),
        "aught_ought",
    )
}

/// ough variants
///
/// Multiple pronunciations for "ough"
fn ough_variants() -> OperationType {
    OperationType::with_restriction(
        4, 1, 0.25,
        SubstitutionSet::from_pairs(&[
            ("ough", "ö"),   // dough→dö
            ("ough", "òf"),  // cough→kòf
            ("ough", "ô"),   // through→+rô
            ("ough", "ùf"),  // enough→enùf
        ]),
        "ough_variants",
    )
}

/// Silent gh (often final position)
fn silent_gh() -> OperationType {
    OperationType::with_restriction(
        2, 0, 0.15,
        SubstitutionSet::from_pairs(&[("gh", "")]),
        "silent_gh",
    )
}
```

**Test**:

```rust
#[test]
fn test_gh_patterns() {
    let ops = phonetic_english_extended();

    // igh→ï
    let automaton = UniversalAutomaton::new("right", 3, &ops);
    assert!(automaton.accepts("rït"));

    // aught→òt
    let automaton = UniversalAutomaton::new("daughter", 3, &ops);
    assert!(automaton.accepts("dòt@r"));

    // ough variants (dough)
    let automaton = UniversalAutomaton::new("dough", 3, &ops);
    assert!(automaton.accepts("dö"));
}
```

### 3.5 -tion/-sion Endings

**Implementation**:

```rust
/// -tion/-sion endings
///
/// tion→$@n, sion→$@n
fn tion_sion_endings() -> OperationType {
    OperationType::with_restriction(
        4, 2, 0.2,
        SubstitutionSet::from_pairs(&[
            ("tion", "$@n"),  // nation→nä$@n
            ("sion", "$@n"),  // fusion→fü$@n
        ]),
        "tion_sion",
    )
}
```

### 3.6 Phase 2 Checklist

- [ ] Implement velar softening (context-encoded)
- [ ] Implement vowel-R coloring
- [ ] Implement vowel double-R
- [ ] Implement GH patterns (lengthening, before vowel, aught/ought, ough variants, silent)
- [ ] Implement -tion/-sion endings
- [ ] Write extended integration tests
- [ ] Benchmark memory usage (expect 8-50 MB)
- [ ] Measure coverage (expect 75-85%)
- [ ] Compare performance vs Phase 1

---

## 4. Phase 3: Context Extensions

**Goal**: Add bi-directional context support for lazy automaton (80-85% coverage)
**Effort**: 2-3 weeks
**Prerequisite**: Phase 2 complete

### 4.1 Context Pattern API

**File**: `src/transducer/operation/context.rs`

```rust
//! Context patterns for conditional operations

use std::fmt;

/// Pattern for matching characters in context
#[derive(Clone)]
pub enum ContextPattern {
    /// Match if character satisfies predicate
    Predicate(fn(char) -> bool),

    /// Match if character in set
    CharSet(Vec<char>),

    /// Match any character
    Any,
}

impl ContextPattern {
    /// Create pattern that matches if predicate returns true
    pub fn matches<F>(predicate: fn(char) -> bool) -> Self {
        ContextPattern::Predicate(predicate)
    }

    /// Create pattern that matches characters in string
    pub fn chars(chars: &str) -> Self {
        ContextPattern::CharSet(chars.chars().collect())
    }

    /// Check if pattern matches character
    pub fn matches_char(&self, ch: char) -> bool {
        match self {
            ContextPattern::Predicate(f) => f(ch),
            ContextPattern::CharSet(set) => set.contains(&ch),
            ContextPattern::Any => true,
        }
    }
}

impl fmt::Debug for ContextPattern {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ContextPattern::Predicate(_) => write!(f, "Predicate(<fn>)"),
            ContextPattern::CharSet(chars) => write!(f, "CharSet({:?})", chars),
            ContextPattern::Any => write!(f, "Any"),
        }
    }
}
```

### 4.2 Extend OperationType

**File**: `src/transducer/operation.rs` (modify existing)

```rust
use crate::operation::context::ContextPattern;

pub struct OperationType {
    pub x_consumed: u8,
    pub y_consumed: u8,
    pub weight: f32,
    pub restriction: Option<SubstitutionSet>,
    pub name: &'static str,

    // NEW: Context patterns
    pub left_context: Option<ContextPattern>,
    pub right_context: Option<ContextPattern>,
}

impl OperationType {
    // ... existing methods

    /// Add left context (character before operation)
    pub fn with_left_context(mut self, pattern: ContextPattern) -> Self {
        self.left_context = Some(pattern);
        self
    }

    /// Add right context (character after operation)
    pub fn with_right_context(mut self, pattern: ContextPattern) -> Self {
        self.right_context = Some(pattern);
        self
    }

    /// Check if operation applies in given context
    pub fn applies_in_context(&self, word: &str, pos: usize) -> bool {
        // Check left context
        if let Some(ref left) = self.left_context {
            if pos == 0 {
                return false;  // No left context available
            }
            let prev_char = word.chars().nth(pos - 1).unwrap();
            if !left.matches_char(prev_char) {
                return false;
            }
        }

        // Check right context
        if let Some(ref right) = self.right_context {
            let next_pos = pos + self.x_consumed as usize;
            if next_pos >= word.len() {
                return false;  // No right context available
            }
            let next_char = word.chars().nth(next_pos).unwrap();
            if !right.matches_char(next_char) {
                return false;
            }
        }

        true
    }
}
```

### 4.3 Update Lazy Automaton

**File**: `src/transducer/lazy.rs` (modify transition logic)

```rust
impl State {
    pub fn transition(&self, word: &str, pos: usize, ops: &OperationSet) -> State {
        let mut next_state = State::new();

        for position in &self.positions {
            // Get applicable operations at this position
            let applicable_ops = ops.operations().iter()
                .filter(|op| {
                    // Check if operation applies in context
                    op.applies_in_context(word, pos)
                        && op.applies_to(/* characters */)
                });

            // Apply operations...
        }

        next_state
    }
}
```

### 4.4 Contextual Phonetic Operations

**File**: `src/transducer/operation/phonetic.rs`

```rust
use crate::operation::context::ContextPattern;

/// Creates contextual phonetic operation set (lazy only)
///
/// Coverage: ~80-85% of phonetic transformations
/// Note: Only works with lazy automaton (context-dependent)
pub fn phonetic_english_contextual() -> OperationSet {
    OperationSetBuilder::new()
        .with_match()

        // Include Phase 1 & 2 operations
        // ... (omitted for brevity)

        // Phase 3: Contextual operations
        .with_operation(soft_c_contextual())
        .with_operation(hard_c_default())
        .with_operation(soft_g_contextual())
        .with_operation(x_voicing_contextual())

        .with_standard_ops()
        .build()
}

/// Soft c before front vowels (e, i, y)
fn soft_c_contextual() -> OperationType {
    OperationType::with_restriction(
        1, 1, 0.25,
        SubstitutionSet::from_pairs(&[("c", "s")]),
        "soft_c",
    )
    .with_right_context(ContextPattern::chars("eiy"))
}

/// Hard c (elsewhere, higher cost)
fn hard_c_default() -> OperationType {
    OperationType::with_restriction(
        1, 1, 0.35,
        SubstitutionSet::from_pairs(&[("c", "k")]),
        "hard_c",
    )
    // No context = applies everywhere
}

/// Soft g before front vowels
fn soft_g_contextual() -> OperationType {
    OperationType::with_restriction(
        1, 1, 0.25,
        SubstitutionSet::from_pairs(&[("g", "j")]),
        "soft_g",
    )
    .with_right_context(ContextPattern::chars("eiy"))
}

/// x voicing: x→gz after 'e' before vowel
fn x_voicing_contextual() -> OperationType {
    OperationType::with_restriction(
        1, 2, 0.3,
        SubstitutionSet::from_pairs(&[("x", "gz")]),
        "x_voicing",
    )
    .with_left_context(ContextPattern::chars("e"))
    .with_right_context(ContextPattern::chars("aeiou"))
}
```

### 4.5 Phase 3 Tests

```rust
#[test]
fn test_soft_c_context() {
    let ops = phonetic_english_contextual();

    // Soft c before 'e'
    let automaton = LazyAutomaton::new("cell", 3, &ops);
    assert!(automaton.accepts("sêl"));

    // Hard c before 'a'
    let automaton = LazyAutomaton::new("cat", 3, &ops);
    assert!(automaton.accepts("kât"));
}

#[test]
fn test_x_voicing() {
    let ops = phonetic_english_contextual();

    // x→gz after 'e' before vowel
    let automaton = LazyAutomaton::new("exit", 3, &ops);
    assert!(automaton.accepts("egzit"));

    // x→ks elsewhere
    let automaton = LazyAutomaton::new("fox", 3, &ops);
    assert!(automaton.accepts("fòks"));
}
```

### 4.6 Phase 3 Checklist

- [ ] Implement ContextPattern API
- [ ] Extend OperationType with context fields
- [ ] Update lazy automaton transition logic
- [ ] Implement contextual operations (soft c/g, x voicing)
- [ ] Write contextual tests
- [ ] Benchmark context overhead
- [ ] Compare accuracy: contextual vs pre-encoded
- [ ] Document: Contextual operations only for lazy automaton

---

## 5. Testing Strategy

### 5.1 Unit Tests

Test each operation in isolation:

```rust
#[test]
fn test_consonant_digraph_ch() {
    let op = consonant_digraphs();
    assert_eq!(op.x_consumed, 2);
    assert_eq!(op.y_consumed, 1);
    assert_eq!(op.weight, 0.15);
    assert!(op.restriction.as_ref().unwrap().allows("ch", "ç"));
}
```

### 5.2 Integration Tests

Test complete words:

```rust
#[test]
fn test_common_words() {
    let ops = phonetic_english_extended();

    let test_cases = vec![
        ("telephone", "tel@fön", 2),
        ("beautiful", "büt@f@l", 3),
        ("daughter", "dòt@r", 3),
        ("psychology", "sïkölöjë", 3),
        ("knight", "nït", 2),
    ];

    for (spelling, phonetic, threshold) in test_cases {
        let automaton = UniversalAutomaton::new(spelling, threshold, &ops);
        assert!(
            automaton.accepts(phonetic),
            "Failed: {} → {} (threshold {})",
            spelling, phonetic, threshold
        );
    }
}
```

### 5.3 Coverage Measurement

Create test corpus from CMU Pronouncing Dictionary:

**File**: `tests/phonetic/coverage_test.rs`

```rust
use std::fs::File;
use std::io::{BufRead, BufReader};

#[test]
#[ignore]  // Expensive test
fn measure_coverage() {
    let ops = phonetic_english_extended();

    // Load CMU Pronouncing Dictionary
    let file = File::open("tests/data/cmudict.txt").unwrap();
    let reader = BufReader::new(file);

    let mut total = 0;
    let mut exact_matches = 0;
    let mut close_matches = 0;

    for line in reader.lines() {
        let line = line.unwrap();
        if line.starts_with(";;;") {
            continue;  // Skip comments
        }

        let parts: Vec<&str> = line.split_whitespace().collect();
        if parts.len() < 2 {
            continue;
        }

        let spelling = parts[0].to_lowercase();
        let phonetic = parts[1..].join("");  // Simplified

        let automaton = UniversalAutomaton::new(&spelling, 3, &ops);

        if automaton.accepts(&phonetic) {
            exact_matches += 1;
        } else if automaton.distance(&phonetic) <= 1.5 {
            close_matches += 1;
        }

        total += 1;
    }

    let exact_pct = (exact_matches as f32 / total as f32) * 100.0;
    let close_pct = ((exact_matches + close_matches) as f32 / total as f32) * 100.0;

    println!("Total words: {}", total);
    println!("Exact matches: {} ({:.1}%)", exact_matches, exact_pct);
    println!("Close matches: {} ({:.1}%)", exact_matches + close_matches, close_pct);

    // Assert minimum coverage
    assert!(exact_pct >= 60.0, "Coverage too low: {:.1}%", exact_pct);
}
```

Run:

```bash
cargo test --test coverage_test -- --ignored --nocapture
```

### 5.4 Property-Based Tests

Use `proptest` for fuzzing:

```rust
use proptest::prelude::*;

proptest! {
    #[test]
    fn test_distance_properties(
        word1 in "[a-z]{3,10}",
        word2 in "[a-z]{3,10}",
    ) {
        let ops = phonetic_english_basic();

        // Distance should be symmetric
        let d1 = compute_distance(&word1, &word2, &ops);
        let d2 = compute_distance(&word2, &word1, &ops);
        assert_eq!(d1, d2);

        // Distance to self should be 0
        let d_self = compute_distance(&word1, &word1, &ops);
        assert_eq!(d_self, 0.0);
    }
}
```

---

## 6. Performance Tuning

### 6.1 Profiling

Generate flamegraph:

```bash
RUSTFLAGS="-C target-cpu=native" taskset -c 0 cargo flamegraph \
  --bench phonetic_matcher -- --bench
```

### 6.2 Optimization Checklist

- [ ] Use SmallVec for state positions (already done)
- [ ] Pre-compute SubstitutionSets (cache)
- [ ] Inline hot path functions (#[inline])
- [ ] Reduce allocations in transition logic
- [ ] Benchmark subsumption performance
- [ ] Profile memory usage with d=3, d=4, d=5

### 6.3 Memory Optimization

Monitor state space size:

```rust
#[test]
fn measure_state_space() {
    let ops = phonetic_english_extended();
    let automaton = UniversalAutomaton::new("telephone", 3, &ops);

    println!("Number of states: {}", automaton.state_count());
    println!("Memory usage: {} bytes", automaton.memory_usage());
}
```

---

## 7. Integration Examples

### 7.1 Spell Checker

```rust
use liblevenshtein::operation::phonetic::phonetic_english_extended;
use liblevenshtein::transducer::UniversalAutomaton;

pub struct PhoneticSpellChecker {
    dictionary: Vec<String>,
    operations: OperationSet,
}

impl PhoneticSpellChecker {
    pub fn new(dictionary: Vec<String>) -> Self {
        Self {
            dictionary,
            operations: phonetic_english_extended(),
        }
    }

    pub fn suggest(&self, misspelling: &str, max_distance: u8) -> Vec<String> {
        let automaton = UniversalAutomaton::new(misspelling, max_distance, &self.operations);

        self.dictionary.iter()
            .filter(|word| automaton.accepts(word))
            .cloned()
            .collect()
    }
}

// Usage
let checker = PhoneticSpellChecker::new(load_dictionary());
let suggestions = checker.suggest("telefone", 2);
assert!(suggestions.contains(&"telephone".to_string()));
```

### 7.2 Fuzzy Search

```rust
pub struct PhoneticSearch {
    documents: Vec<Document>,
    operations: OperationSet,
}

impl PhoneticSearch {
    pub fn search(&self, query: &str, threshold: u8) -> Vec<&Document> {
        let automaton = UniversalAutomaton::new(query, threshold, &self.operations);

        self.documents.iter()
            .filter(|doc| {
                doc.words.iter().any(|word| automaton.accepts(word))
            })
            .collect()
    }
}
```

---

## 8. Troubleshooting

### 8.1 Common Issues

**Issue**: Memory usage too high

**Solution**:
- Reduce max_distance (n)
- Reduce max operation size (d)
- Use lazy automaton instead of universal

**Issue**: Coverage lower than expected

**Solution**:
- Add missing operation patterns
- Tune weights (lower = preferred)
- Increase distance threshold

**Issue**: Too many false positives

**Solution**:
- Increase operation weights
- Reduce distance threshold
- Add exception dictionary

**Issue**: Performance too slow

**Solution**:
- Profile with flamegraph
- Optimize subsumption checks
- Cache operation sets
- Use universal automaton for repeated queries

---

## Conclusion

This guide provides a complete implementation roadmap for English phonetic corrections in liblevenshtein-rust. Follow the three phases incrementally, testing and benchmarking at each step.

**Expected Results**:
- Phase 1: 60-70% coverage, 3-5 days
- Phase 2: 75-85% coverage, 2-3 weeks additional
- Phase 3: 80-85% coverage, 2-3 weeks additional

**Total Effort**: 5-7 weeks for full implementation

**Next Steps**:
1. Complete Phase 1
2. Evaluate coverage and performance
3. Decide whether to proceed to Phase 2/3 based on requirements

---

**Document Version**: 1.0
**Last Updated**: 2025-11-12
**Author**: Claude Code (Anthropic AI Assistant)
**Status**: 📋 **READY FOR IMPLEMENTATION**
