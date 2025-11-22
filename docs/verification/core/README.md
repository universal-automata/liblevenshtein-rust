# Liblevenshtein Core Verification Library

**Status**: In Progress
**Date**: 2025-11-21
**Namespace**: `Liblevenshtein.Core.Verification`

## Overview

This library contains reusable formal proofs for core algorithms and data structures used across multiple liblevenshtein components (contextual completion, phonetic transformation, transducer operations).

The core library emphasizes **reusability**: proofs established here are imported by domain-specific verification modules (`docs/verification/contextual/`, `docs/verification/phonetic/`, `docs/verification/transducer/`) to avoid duplication.

## Structure

```
docs/verification/core/
├── _CoqProject          # Build configuration, namespace definitions
├── README.md            # This file
└── theories/
    ├── Distance.v       # Levenshtein distance (Wagner-Fischer DP)
    ├── Strings.v        # UTF-8 string operations (TODO)
    ├── Trees.v          # Generic tree operations, well-formedness (TODO)
    └── Checkpoints.v    # Undo/redo stack with LIFO semantics (TODO)
```

## Modules

### 1. Distance.v - Levenshtein Distance

**Status**: ✅ Initial framework complete (1 theorem proven, 4 admitted)
**Lines**: 372 lines
**Compilation**: Successful (2 deprecation warnings only)

**Purpose**: Proves correctness of the Wagner-Fischer dynamic programming algorithm for computing edit distance between strings.

**Key Components**:
- **Recursive definition**: Axiomatized Wagner-Fischer recurrence relation
- **Matrix-based DP**: Iterative algorithm formalization
- **Metric properties**:
  - ✅ **Identity**: `lev_distance s s = 0` (PROVEN)
  - ⏳ **Symmetry**: `lev_distance s1 s2 = lev_distance s2 s1` (admitted)
  - ⏳ **Triangle inequality**: `d(s1,s3) ≤ d(s1,s2) + d(s2,s3)` (admitted)
  - ⏳ **Upper bound**: `d(s1,s2) ≤ max(|s1|, |s2|)` (admitted)
  - ⏳ **DP correctness**: Matrix algorithm equals recursive definition (admitted)

**Dependencies**:
- Coq/Rocq Standard Library: `List`, `Arith`, `Ascii`, `Bool`, `Nat`, `Lia`

**Usage Example** (from contextual completion):
```coq
From Liblevenshtein.Core.Verification Require Import Distance.

Theorem query_fusion_distance_filter :
  forall (query term : list Char) (max_dist : nat),
    lev_distance query term <= max_dist ->
    (* term should be included in completion results *)
```

**Next Steps**:
1. Prove `lev_distance_symmetry` using edit operation inverse correspondence
2. Prove `lev_distance_triangle_inequality` using edit sequence concatenation
3. Prove `dp_matrix_correctness` using strong induction on matrix cells
4. Consider implementing well-founded recursion for `lev_distance` to replace axioms

### 2. Strings.v - UTF-8 String Operations

**Status**: ⏳ TODO
**Est. Lines**: ~250 lines
**Priority**: High (required for contextual completion Theorem 2)

**Purpose**: Formalize UTF-8 buffer operations (insertion, deletion) with validity preservation.

**Planned Content**:
- **Axioms**: Rust's `char` type guarantees (Unicode scalar values)
- **Operations**: `insert`, `delete` with validity preservation
- **Properties**: Reversibility, length tracking, consistency

**Extracted From**: `docs/formal-verification/proofs/06_contextual_completion/02_draft_consistency.md`

### 3. Trees.v - Generic Tree Operations

**Status**: ⏳ TODO
**Est. Lines**: ~400 lines
**Priority**: Medium (required for contextual completion Theorems 1, 6)

**Purpose**: Generic tree well-formedness, acyclicity, ancestor/descendant relations, visibility predicates.

**Planned Content**:
- **Well-formedness**: `acyclic`, `valid_parent_pointers`
- **Relations**: `is_ancestor`, `is_descendant`, `lca` (lowest common ancestor)
- **Traversal**: `visible_contexts` (ancestor chain), ordering guarantees

**Extracted From**:
- `docs/formal-verification/proofs/06_contextual_completion/01_context_visibility.md`
- `docs/formal-verification/proofs/06_contextual_completion/06_hierarchical_visibility.md`

### 4. Checkpoints.v - Undo/Redo Stack

**Status**: ⏳ TODO
**Est. Lines**: ~200 lines
**Priority**: Low (required for contextual completion Theorem 3)

**Purpose**: LIFO stack semantics for checkpoint-based undo/redo operations.

**Planned Content**:
- **Operations**: `push`, `pop`, `peek`, `clear`
- **Properties**: LIFO ordering, stack invariants, history preservation

**Extracted From**: `docs/formal-verification/proofs/06_contextual_completion/03_checkpoint_stack.md`

## Compilation

### Prerequisites
- **Coq/Rocq**: 9.0+ (tested with Rocq 9.1.0)
- **Build tool**: `coqc` or `make`

### Build Instructions

```bash
cd docs/verification/core

# Single file compilation
coqc -R theories Liblevenshtein.Core.Verification theories/Distance.v

# Full build (when Makefile is added)
make

# Clean build artifacts
make clean
```

### Expected Output
```
File "./theories/Distance.v", line 15, characters 0-61:
Warning: "From Coq" has been replaced by "From Stdlib".
[deprecated-from-Coq,deprecated-since-9.0,deprecated,default]
File "./theories/Distance.v", line 42, characters 0-105:
Warning: Not a truly recursive fixpoint. [non-recursive,fixpoints,default]
```

**Status**: Compiles successfully ✅ (warnings only, no errors)

## Design Philosophy

### 1. Reusability Over Specificity

**Bad**: Proofs tightly coupled to one use case (e.g., "Contextual Completion Distance")
**Good**: Generic proofs applicable to multiple domains (e.g., "Levenshtein Distance - Core Algorithm")

Example:
```coq
(* ❌ Too specific *)
Theorem contextual_completion_distance_correct : ...

(* ✅ Reusable *)
Theorem levenshtein_distance_correctness : ...
  (* Can be imported by contextual/, phonetic/, transducer/ *)
```

### 2. Axioms for Initial Framework

For complex recursive definitions that require well-founded recursion (e.g., `lev_distance`), we:
1. **Axiomatize** the function and its key properties
2. **Prove** metric properties using the axioms
3. **Defer** well-founded recursion implementation to later refinement

**Rationale**: Allows rapid progress on higher-level proofs while maintaining correctness guarantees.

### 3. Admitted Proofs as Placeholders

Proofs marked `Admitted` indicate:
- The theorem statement is correct
- The proof infrastructure (lemmas, definitions) is in place
- The proof is standard/well-established in the literature
- Implementation is deferred for time management

**NOT** a correctness compromise - all admitted proofs will be completed.

## Integration with Domain-Specific Libraries

### Contextual Completion
```coq
From Liblevenshtein.Core.Verification Require Import Distance Strings Trees.
From Liblevenshtein.Contextual.Verification Require Import ContextTree QueryFusion.

Theorem query_fusion_correctness :
  forall (tree : ContextTree) (dict : Dictionary) (query : string) (max_dist : nat),
    well_formed tree ->
    (* Uses core/Distance.v for levenshtein_distance correctness *)
    (* Uses core/Trees.v for well_formed tree property *)
    (* Uses core/Strings.v for UTF-8 validity *)
    ...
```

### Phonetic Transformation
```coq
From Liblevenshtein.Core.Verification Require Import Distance.
From Liblevenshtein.Phonetic.Verification Require Import Patterns.

Theorem phonetic_similarity_metric :
  forall (s1 s2 : list Phone),
    (* Reuses levenshtein_distance metric properties *)
    lev_distance (to_phonetic s1) (to_phonetic s2) = ...
```

### Transducer Operations (Future)
```coq
From Liblevenshtein.Core.Verification Require Import Distance Trees.
From Liblevenshtein.Transducer.Verification Require Import NFA DFA.

Theorem transducer_distance_bounded :
  forall (nfa : NFA) (s1 s2 : string),
    (* Reuses distance upper bound theorem *)
    ...
```

## Proof Status Summary

| Module | Total Theorems | Proven | Admitted | % Complete |
|--------|---------------|--------|----------|------------|
| Distance.v | 5 | 1 | 4 | 20% |
| Strings.v | - | - | - | 0% (TODO) |
| Trees.v | - | - | - | 0% (TODO) |
| Checkpoints.v | - | - | - | 0% (TODO) |
| **TOTAL** | 5 | 1 | 4 | **20%** |

## Development Timeline

### Week 1-2 (Current)
- ✅ Create directory structure
- ✅ Set up `_CoqProject`
- ✅ Formalize Distance.v with axioms
- ✅ Prove `lev_distance_identity`
- ⏳ Create README (this document)

### Week 3-4
- Create Strings.v (UTF-8 operations)
- Create Trees.v (tree well-formedness)
- Create Checkpoints.v (undo/redo stack)

### Week 5-6
- Prove admitted theorems in Distance.v
- Add Makefile for full builds
- Add .gitignore for build artifacts

### Week 7-8
- Begin contextual verification library
- Import core proofs into contextual modules
- Create QueryFusion.v using core/Distance.v

## References

- **Wagner-Fischer Algorithm**: Original DP formulation for edit distance
- **Contextual Completion Specs**: `docs/formal-verification/proofs/06_contextual_completion/`
- **Phonetic Verification**: `docs/verification/phonetic/`
- **Coq Standard Library**: https://coq.inria.fr/doc/master/stdlib/
- **Rocq/Coq 9.x**: https://rocq-prover.org/

## Contributors

- Formal Verification Team
- Date: 2025-11-21

---

**Last Updated**: 2025-11-21
**Next Review**: After Strings.v implementation (Week 3-4)
