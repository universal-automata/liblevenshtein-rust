# Position Skipping Proof - Modular Organization

This directory contains the modular decomposition of the position skipping optimization proof for phonetic rewrite rules.

## Quick Start

### Building All Modules

```bash
# Generate Makefile from _CoqProject
coq_makefile -f _CoqProject -o Makefile

# Compile all modules in parallel
make -j$(nproc)

# Clean build artifacts
make clean
```

### Building Individual Modules

Compile modules in dependency order:

```bash
# Layer 1: Base types
coqc Auxiliary/Types.v

# Layer 2: Core library
coqc Auxiliary/Lib.v

# Layer 3: Core operations
coqc Core/Rules.v

# Layer 4: Pattern helpers and Invariants base
coqc Patterns/PatternHelpers.v
coqc Invariants/SearchInvariant.v

# Layer 5: Advanced invariants
coqc Invariants/AlgoState.v
coqc Invariants/NoMatch.v

# Layer 6: Pattern overlap (Axiom 2)
coqc Patterns/PatternOverlap.v

# Layer 7: Main proof
coqc Position_Skipping_Proof.v
```

## Module Structure

```
theories/
├── Position_Skipping_Proof.v    Main entry point (569 lines)
├── Auxiliary/
│   ├── Types.v                  Type definitions (169 lines)
│   └── Lib.v                    Core library (969 lines)
├── Core/
│   └── Rules.v                  Rule operations (105 lines)
├── Invariants/
│   ├── SearchInvariant.v        Search invariant (314 lines)
│   ├── NoMatch.v                No-match preservation (381 lines)
│   └── AlgoState.v              Algorithm state (222 lines)
└── Patterns/
    ├── PatternHelpers.v         Pattern lemmas (472 lines)
    └── PatternOverlap.v         Axiom 2 - FULLY PROVEN (506 lines)
```

## Module Descriptions

### Position_Skipping_Proof.v
**Main entry point** - Ties all modules together

Key theorems:
- `position_skip_safe_for_local_contexts` - Main correctness theorem
- `position_skipping_conditionally_safe` - Conditional safety
- `final_position_can_change` - Counterexample

### Auxiliary/Types.v
**Foundational types** - Type definitions and predicates

Defines:
- `wf_rule` - Well-formedness
- `position_dependent_context` - Context classification
- `SearchInvariant`, `AlgoState` - State predicates

### Auxiliary/Lib.v
**Core library** - 969 lines of reusable lemmas

Provides:
- List manipulation lemmas
- String structure preservation
- Context helper lemmas
- `find_first_match` properties

### Core/Rules.v
**Rule operations** - Core transformation operations

Key lemmas:
- `apply_rule_at_region_structure` - Regional preservation
- `apply_rule_at_preserves_prefix` - Prefix preservation
- `can_apply_at_beyond_length` - Bounds checking

### Invariants/SearchInvariant.v
**Search invariant** - Properties of search state

Establishes:
- Initialization lemmas
- Maintenance lemmas
- Establishment lemmas

### Invariants/NoMatch.v
**No-match preservation** - Axiom 1 and supporting theorems

Key theorem:
- `single_rule_no_match_preserved` (Axiom 1) - FULLY PROVEN

### Invariants/AlgoState.v
**Algorithm state** - Execution state model

Key theorem:
- `algo_state_maintains_invariant` - State preservation

### Patterns/PatternHelpers.v
**Pattern helpers** - Pattern matching analysis

Provides:
- `pattern_matches_at_has_mismatch`
- `pattern_has_leftmost_mismatch`
- Phone classification lemmas

### Patterns/PatternOverlap.v
**Axiom 2** - Pattern overlap preservation (FULLY PROVEN)

Crown jewel theorems:
- `leftmost_mismatch_before_transformation` - 172-line proof
- `pattern_overlap_preservation` - Complete Axiom 2

## Proof Status

**100% COMPLETE** - All theorems proven with Qed

| Theorem | Status | Module |
|---------|--------|--------|
| Axiom 1: `single_rule_no_match_preserved` | ✅ PROVEN | NoMatch.v |
| Axiom 2: `pattern_overlap_preservation` | ✅ PROVEN | PatternOverlap.v |
| Main: `position_skip_safe_for_local_contexts` | ✅ PROVEN | Position_Skipping_Proof.v |
| Conditional: `position_skipping_conditionally_safe` | ✅ PROVEN | Position_Skipping_Proof.v |
| Counterexample: `final_position_can_change` | ✅ PROVEN | Position_Skipping_Proof.v |

## Dependencies

Each module's dependencies are explicit via `Require Import` statements:

```
Position_Skipping_Proof.v → [All modules]
Patterns.PatternOverlap → PatternHelpers, Core.Rules, Auxiliary.*
Invariants.NoMatch → PatternHelpers, Core.Rules, Auxiliary.*
Invariants.AlgoState → Core.Rules, Auxiliary.*
Invariants.SearchInvariant → Core.Rules, Auxiliary.*
Patterns.PatternHelpers → Auxiliary.*
Core.Rules → Auxiliary.*
Auxiliary.Lib → Auxiliary.Types
Auxiliary.Types → (stdlib only)
```

## Extraction

To extract verified OCaml code:

```coq
Require Import Liblevenshtein.Phonetic.Verification.Position_Skipping_Proof.

Extraction "position_skipping.ml"
  apply_rules_seq
  apply_rules_seq_opt
  can_apply_at
  position_dependent_context.
```

## Documentation

- `MODULAR_DECOMPOSITION.md` - Detailed module breakdown and statistics
- `README.md` - This file
- Individual module headers contain comprehensive documentation

## Contact

Part of the liblevenshtein-rust verification project.

For questions about the proof structure or modules, refer to the inline documentation in each `.v` file.
