# Migration Guide: Lazy/Eager Terminology

## Overview

This document outlines the strategy for transitioning from "Parameterized/Universal" to "Lazy/Eager" terminology while maintaining backward compatibility and easing the transition for existing users.

## Terminology Mapping

| Old Term | New Term | Academic Name | Status |
|----------|----------|---------------|--------|
| Parameterized | Lazy | Schulz & Mihov 2002 | ✅ Active |
| Universal | Eager | Mitankin 2005 | ✅ Active |

## Deprecation Strategy

### Phase 1: Soft Introduction (Current - v0.7.0)

**Goal**: Introduce new terminology without breaking anything.

**Actions**:
1. Add new terminology to documentation
2. Add type aliases with `#[doc(alias)]` attributes
3. Add notes to existing documentation explaining both terms
4. Update examples to show both naming conventions
5. No deprecation warnings yet

**Timeline**: Immediate (v0.6.0 → v0.7.0)

### Phase 2: Dual Support (v0.7.0 - v0.9.0)

**Goal**: Support both terminologies equally, encourage migration.

**Actions**:
1. All public APIs accept both terms
2. Documentation uses new terms primarily, mentions old terms
3. Add migration guide (this document)
4. Blog posts and release notes highlight new terminology
5. Still no deprecation warnings

**Timeline**: 6-12 months (3-6 releases)

### Phase 3: Soft Deprecation (v0.10.0 - v1.0.0)

**Goal**: Signal that old terminology will be removed, but don't break code.

**Actions**:
1. Add `#[deprecated]` attributes to type aliases
2. Deprecation messages reference this migration guide
3. Documentation uses only new terminology
4. Code examples use only new terminology
5. Compiler warnings (but code still works)

**Timeline**: 6-12 months before v1.0.0

### Phase 4: Hard Deprecation (v1.0.0+)

**Goal**: Clean API with only lazy/eager terminology.

**Actions**:
1. Remove type aliases and compatibility shims
2. Breaking change documented in CHANGELOG
3. Migration guide remains for reference
4. Old terminology only in academic references

**Timeline**: v1.0.0 major version bump

---

## Code-Level Deprecation Strategy

### 1. Module-Level Aliases

**Current Structure:**
```
src/
├── transducer/           # "Parameterized" (lazy)
└── transducer/universal/ # "Universal" (eager)
```

**Strategy**: Keep module names unchanged (no filesystem changes), use type aliases and docs.

**Rationale**:
- Changing module paths is disruptive
- Old module names map to academic paper names
- Documentation and type aliases provide new terminology

### 2. Type Aliases with doc(alias)

```rust
// src/transducer/mod.rs

/// Lazy Levenshtein automaton (constructs states on-demand).
///
/// Also known as "Parameterized Levenshtein Automaton" in academic literature.
pub struct Transducer<D: Dictionary, P: SubstitutionPolicy = Unrestricted> {
    // ...
}

// Phase 1-2: Add doc alias for discoverability
#[doc(alias = "ParameterizedTransducer")]
#[doc(alias = "ParameterizedAutomaton")]
// Phase 3: Add deprecation
// #[deprecated(since = "0.10.0", note = "Use `Transducer` directly. The 'parameterized' terminology is being phased out in favor of 'lazy'. See docs/migration/LAZY_EAGER_TERMINOLOGY.md")]
// pub type ParameterizedTransducer<D, P = Unrestricted> = Transducer<D, P>;
```

```rust
// src/transducer/universal/mod.rs

/// Eager Levenshtein automaton (precomputed structure).
///
/// Also known as "Universal Levenshtein Automaton" in academic literature.
pub struct UniversalAutomaton<V: PositionVariant> {
    // ...
}

#[doc(alias = "EagerAutomaton")]
// Phase 1-2: Just documentation aliases
// Phase 3: Add actual type alias with deprecation
// #[deprecated(since = "0.10.0", note = "Use `UniversalAutomaton` directly. Consider the 'eager' terminology for conceptual clarity. See docs/migration/LAZY_EAGER_TERMINOLOGY.md")]
// pub type EagerAutomaton<V> = UniversalAutomaton<V>;
```

### 3. Documentation Strategy

**Phase 1-2 Documentation Pattern:**

```rust
/// Lazy Levenshtein automaton for dictionary queries.
///
/// This automaton constructs states **lazily** (on-demand) during dictionary
/// traversal, minimizing memory usage and construction overhead.
///
/// # Terminology Note
///
/// In academic literature, this is called a "Parameterized Levenshtein Automaton"
/// (Schulz & Mihov, 2002). We use "lazy" terminology to emphasize **when**
/// construction happens (on-demand vs upfront), making the trade-offs more
/// intuitive for developers.
///
/// See [`UniversalAutomaton`] for the "eager" (precomputed) alternative.
```

**Phase 3+ Documentation Pattern:**

```rust
/// Lazy Levenshtein automaton for dictionary queries.
///
/// This automaton constructs states **lazily** (on-demand) during dictionary
/// traversal, minimizing memory usage and construction overhead.
///
/// Formerly called "Parameterized Levenshtein Automaton" in academic literature
/// (Schulz & Mihov, 2002).
```

### 4. Module Documentation

**src/transducer/mod.rs:**

```rust
//! Lazy Levenshtein Automata
//!
//! This module implements lazy (on-demand) construction of Levenshtein automata,
//! also known as Parameterized Levenshtein Automata in academic literature.
//!
//! # Terminology
//!
//! - **Lazy**: States constructed on-demand during queries
//! - **Parameterized**: Academic term from Schulz & Mihov (2002)
//!
//! See [`crate::transducer::universal`] for eager (precomputed) automata.
```

**src/transducer/universal/mod.rs:**

```rust
//! Eager Levenshtein Automata
//!
//! This module implements eager (precomputed) Levenshtein automata,
//! also known as Universal Levenshtein Automata in academic literature.
//!
//! # Terminology
//!
//! - **Eager**: Entire structure precomputed upfront
//! - **Universal**: Academic term from Mitankin (2005)
//!
//! See [`crate::transducer`] for lazy (on-demand) automata.
```

### 5. Example Updates

**Phase 1-2: Show Both**

```rust
// examples/basic_query.rs

//! Basic dictionary query example.
//!
//! This example uses the lazy (parameterized) automaton for efficient
//! dictionary queries.

use liblevenshtein::prelude::*;

fn main() {
    // Create lazy automaton (also called "parameterized")
    let dict = DynamicDawg::from_terms(vec!["apple", "banana", "orange"]);
    let transducer = Transducer::new(dict, Algorithm::Standard);

    // Query
    let results: Vec<_> = transducer.query("aple", 1).collect();
    println!("Matches: {:?}", results);
}
```

**Phase 3+: Use Only New Terms**

```rust
// examples/basic_query.rs

//! Basic dictionary query example using lazy automaton.

use liblevenshtein::prelude::*;

fn main() {
    // Create lazy automaton
    let dict = DynamicDawg::from_terms(vec!["apple", "banana", "orange"]);
    let transducer = Transducer::new(dict, Algorithm::Standard);

    // Query
    let results: Vec<_> = transducer.query("aple", 1).collect();
    println!("Matches: {:?}", results);
}
```

---

## User-Facing Migration

### For Existing Users

**Q: Will my code break?**
A: No. Module names and type names are unchanged. Only documentation terminology is evolving.

**Q: Do I need to change my code?**
A: No immediate changes required. Your code will continue to work through v1.0.0.

**Q: Should I adopt the new terminology?**
A: Yes, when convenient. New terminology is clearer for:
- Understanding when construction happens
- Comparing lazy vs eager trade-offs
- Communicating with new contributors

**Q: What if I'm writing academic papers?**
A: Use original terminology (Parameterized/Universal) and cite:
- Schulz & Mihov (2002) for lazy/parameterized
- Mitankin (2005) for eager/universal

### For New Users

**Recommended**: Learn and use "lazy/eager" terminology.

**Why?**
- More intuitive (when vs what)
- Aligns with common CS concepts
- Clearer documentation

**Academic context**: Documentation notes the academic origins and paper names.

---

## Communication Plan

### Release Notes Template

**v0.7.0:**
```markdown
### Terminology Clarification

We're introducing clearer terminology for our two automaton implementations:

- **Lazy Automata**: On-demand state construction (formerly "Parameterized")
- **Eager Automata**: Precomputed structure (formerly "Universal")

**Why?** The new terms emphasize **when** construction happens, making trade-offs
more intuitive.

**Impact**: Zero. This is documentation-only. Your code works unchanged.

**Migration**: See docs/migration/LAZY_EAGER_TERMINOLOGY.md

**Academic context**: We maintain references to original paper terminology.
```

**v0.10.0:**
```markdown
### Soft Deprecation: Old Terminology

Type aliases for old terminology are now deprecated:
- `ParameterizedTransducer` → use `Transducer` (lazy automaton)
- (If we added) `UniversalTransducer` → use `UniversalAutomaton` (eager automaton)

**Action required**: None yet. Compiler warnings help transition.

**Timeline**: Full removal in v1.0.0 (6+ months away).
```

**v1.0.0:**
```markdown
### Breaking: Terminology Migration Complete

Removed deprecated type aliases:
- `ParameterizedTransducer` (removed)
- Use `Transducer` for lazy automata

**Migration**: See docs/migration/LAZY_EAGER_TERMINOLOGY.md
```

### Blog Post Outline

**Title**: "Clearer Terminology: Lazy vs Eager Levenshtein Automata"

**Sections**:
1. **Why we're changing**: Intuitive naming for developers
2. **What's changing**: Documentation and comments, not code
3. **What's NOT changing**: Module names, type names, APIs
4. **Timeline**: Gradual transition, no surprises
5. **Academic context**: Still reference original papers
6. **For users**: Zero impact, optional adoption

---

## Testing Strategy

### Ensure No Breakage

```rust
// tests/terminology_compatibility.rs

#[test]
fn test_transducer_works_as_lazy_automaton() {
    // New terminology
    let dict = DynamicDawg::from_terms(vec!["test"]);
    let lazy_transducer = Transducer::new(dict, Algorithm::Standard);
    assert_eq!(lazy_transducer.query("test", 0).count(), 1);
}

#[test]
fn test_universal_automaton_works_as_eager() {
    // Academic terminology still works
    let eager = UniversalAutomaton::<Standard>::new(2);
    assert!(eager.accepts("test", "text"));
}

// Phase 3: Test aliases
#[test]
#[allow(deprecated)]
fn test_deprecated_aliases_still_work() {
    // If we add: let _ = ParameterizedTransducer::new(...);
}
```

### Documentation Tests

```rust
/// Example using new terminology.
///
/// ```
/// use liblevenshtein::prelude::*;
///
/// // Lazy automaton
/// let dict = DynamicDawg::from_terms(vec!["test"]);
/// let lazy = Transducer::new(dict, Algorithm::Standard);
/// ```
```

---

## Rollback Plan

**If adoption is poor or confusing:**

1. **Phase 1-2**: Easy rollback - just revert documentation changes
2. **Phase 3**: Remove deprecation warnings, extend dual support
3. **Phase 4**: Delay or cancel based on community feedback

**Success Metrics** (before Phase 3):
- GitHub issues/discussions show positive reception
- Documentation feedback is positive
- No confusion in Stack Overflow or forums
- Blog post comments are supportive

---

## Summary

**Guiding Principles:**
1. **No breaking changes** until v1.0.0
2. **Long transition period** (12-18 months minimum)
3. **Clear communication** at every stage
4. **Respect academic terminology** in appropriate contexts
5. **User choice** - both terms valid during transition

**Key Dates:**
- **v0.7.0** (now): Introduce lazy/eager in docs
- **v0.10.0** (+6 months): Soft deprecation warnings
- **v1.0.0** (+12-18 months): Complete transition

**Community Input:**
- RFC process for major terminology changes
- Gather feedback during Phase 1-2
- Adjust timeline based on adoption

This gradual, respectful approach ensures:
- ✅ No broken code
- ✅ Clear migration path
- ✅ Academic integrity maintained
- ✅ Better onboarding for new users
- ✅ Community buy-in
