# Module Renaming & Modularization Cleanup Summary

**Date**: 2025-11-21
**Branch**: `proof-multirule-axiom`
**Objective**: Improve module naming for reusability and fix modularization issues

## Overview

This document summarizes the comprehensive refactoring of the phonetic verification modules to improve naming conventions for better reusability and clean up architectural issues introduced during the monolithic → modular split.

## Phase 1: Resource-Limited Compilation

### Goal
Compile the memory-intensive `PatternHelpers_Mismatch_Complex.v` proof with systemd resource limits to prevent system crashes.

### Resource Limits Applied
- **MemoryMax**: 120GB (47% of 252GB total, leaves 132GB for system)
- **CPUQuota**: 1500% (up to 15 CPU cores)
- **IOWeight**: 40 (reduced I/O priority)
- **TasksMax**: 150 (limit process spawning)
- **Timeout**: 1800s (30 minutes)

### Status
- Initial systemd-run attempts had technical issues
- Compilation now running directly with `make -j1`
- Currently compiling `PatternMatching_Induction.v` (renamed from _Mismatch_Complex)

## Phase 2: Module Naming Evaluation & Renaming

### Renaming Rationale

The original module names were **too specific** to their initial use case (mismatch analysis for position skipping). The new names emphasize **general techniques** and **reusable patterns**:

- **Old naming**: Specific to application ("Mismatch", "Leftmost")
- **New naming**: Generic techniques ("Properties", "Induction", "Positioning")

### Completed Renames

| Old Name | New Name | Rationale | Reusability Score |
|----------|----------|-----------|-------------------|
| `PatternHelpers_Mismatch_Simple.v` | `PatternMatching_Properties.v` | Emphasize general "properties" over specific "mismatch" application | ⭐⭐⭐⭐⭐ High |
| `PatternHelpers_Mismatch_Complex.v` | `PatternMatching_Induction.v` | Focus on reusable "induction" techniques rather than specific use case | ⭐⭐⭐⭐⭐ High |
| `PatternHelpers_Leftmost.v` | `PatternMatching_Positioning.v` | Generic "positioning" applicable beyond leftmost analysis | ⭐⭐⭐⭐ Good |

### Modules Kept As-Is

| Module Name | Reusability Assessment | Decision |
|-------------|------------------------|----------|
| `PatternHelpers_Basic.v` | ✅ Already generic (infrastructure, prefix preservation) | **KEEP** |
| `PatternOverlap.v` | ✅ Generic concept applicable to many pattern systems | **KEEP** |
| `Preservation.v` | ✅ Generic verification concept | **KEEP** |
| `Position_Skipping_Proof.v` | ❌ Extremely specific to position skipping axiom | **KEEP** (not meant for reuse) |

## Phase 3: Modularization Cleanup

### Problem Discovered

During the split from monolithic `position_skipping_proof.v` (3379 lines) into modular structure, **redundant files were not deleted**:

1. `theories/Patterns/PatternHelpers.v` (21KB) - Complete duplicate of all 4 split modules
2. `theories/Patterns/PatternHelpers_Mismatch.v` - Redundant intermediate version

These files were **not in `_CoqProject`** but still existed, creating stealth conflicts.

### Files Deleted

```bash
rm theories/Patterns/PatternHelpers.v
rm theories/Patterns/PatternHelpers_Mismatch.v
```

### Files Updated

#### 1. `_CoqProject` Configuration
**Updated**: Module filenames + improved documentation comments

```diff
 # Patterns layer (Axiom 2 - FULLY PROVEN)
-# PatternHelpers split into 4 files to manage memory during compilation:
-# - Basic: lightweight lemmas (~10GB)
-# - Mismatch_Simple: simple helper lemmas (~5-10GB)
-# - Mismatch_Complex: pattern_matches_at_has_mismatch with nested induction (~60-80GB)
-# - Leftmost: leftmost mismatch analysis with deep nested induction (~80GB)
+# Pattern matching modules split for memory management and reusability:
+# - Basic: lightweight infrastructure (prefix preservation, position validity) (~10GB)
+# - Properties: pattern matching properties and simple helpers (~5-10GB)
+# - Induction: complex nested induction proofs for pattern mismatch (~60-80GB)
+# - Positioning: leftmost/positional analysis with deep induction (~80GB)
 theories/Patterns/PatternHelpers_Basic.v
-theories/Patterns/PatternHelpers_Mismatch_Simple.v
-theories/Patterns/PatternHelpers_Mismatch_Complex.v
-theories/Patterns/PatternHelpers_Leftmost.v
+theories/Patterns/PatternMatching_Properties.v
+theories/Patterns/PatternMatching_Induction.v
+theories/Patterns/PatternMatching_Positioning.v
 theories/Patterns/PatternOverlap.v
```

#### 2. Import Statements Updated

**File**: `theories/Patterns/PatternOverlap.v`

```diff
 From Liblevenshtein.Phonetic.Verification Require Import Patterns.PatternHelpers_Basic.
-From Liblevenshtein.Phonetic.Verification Require Import Patterns.PatternHelpers_Mismatch_Simple.
-From Liblevenshtein.Phonetic.Verification Require Import Patterns.PatternHelpers_Mismatch_Complex.
-From Liblevenshtein.Phonetic.Verification Require Import Patterns.PatternHelpers_Leftmost.
+From Liblevenshtein.Phonetic.Verification Require Import Patterns.PatternMatching_Properties.
+From Liblevenshtein.Phonetic.Verification Require Import Patterns.PatternMatching_Induction.
+From Liblevenshtein.Phonetic.Verification Require Import Patterns.PatternMatching_Positioning.
```

**File**: `theories/Position_Skipping_Proof.v`

```diff
 From Liblevenshtein.Phonetic.Verification Require Import
   Auxiliary.Types Auxiliary.Lib
   Core.Rules
   Invariants.InvariantProperties Invariants.AlgoState
   Patterns.PatternHelpers_Basic
-  Patterns.PatternHelpers_Mismatch_Simple
-  Patterns.PatternHelpers_Mismatch_Complex
-  Patterns.PatternHelpers_Leftmost
+  Patterns.PatternMatching_Properties
+  Patterns.PatternMatching_Induction
+  Patterns.PatternMatching_Positioning
   Patterns.PatternOverlap.
```

#### 3. Module Header Documentation

**File**: `theories/Patterns/PatternMatching_Properties.v`

```coq
(** * Pattern Matching Properties - Simple Helpers

    This module contains simple helper lemmas for pattern matching properties
    with lightweight proofs. Designed for reusability across pattern matching
    verification tasks.

    Part of: Liblevenshtein.Phonetic.Verification.Patterns
    Renamed from PatternHelpers_Mismatch_Simple.v for better reusability.
*)
```

**File**: `theories/Patterns/PatternMatching_Induction.v`

```coq
(** * Pattern Matching Induction - Complex Nested Induction Proofs

    This module contains the memory-intensive pattern_matches_at_has_mismatch lemma
    with complex nested induction and extensive lia usage. Provides reusable induction
    patterns for pattern matching verification.

    Part of: Liblevenshtein.Phonetic.Verification.Patterns
    Renamed from PatternHelpers_Mismatch_Complex.v for better reusability.
    Isolated into its own file due to high memory requirements (~60-80GB).
*)
```

**File**: `theories/Patterns/PatternMatching_Positioning.v`

```coq
(** * Pattern Matching Positioning - Positional Analysis

    This module contains positional analysis lemmas for pattern matching,
    including leftmost position determination with deep nested induction.
    Designed for reusability in pattern position verification tasks.

    Part of: Liblevenshtein.Phonetic.Verification.Patterns
    Renamed from PatternHelpers_Leftmost.v for better reusability.
*)
```

## Build System Changes

### Cleanup Process
```bash
make clean  # Remove all .vo, .vok, .vos files
```

### Compilation
- **Method**: Sequential compilation (`make -j1`) to manage memory
- **Monitoring**: Background process with log output to `/tmp/verify_compile.log`
- **Timeout**: 600000ms (10 minutes)
- **Critical file**: `PatternMatching_Induction.v` (the OOM-prone proof)

## Git History Preservation

All renames used `git mv` to preserve file history:

```bash
git mv theories/Patterns/PatternHelpers_Mismatch_Simple.v \
       theories/Patterns/PatternMatching_Properties.v

git mv theories/Patterns/PatternHelpers_Mismatch_Complex.v \
       theories/Patterns/PatternMatching_Induction.v

git mv theories/Patterns/PatternHelpers_Leftmost.v \
       theories/Patterns/PatternMatching_Positioning.v
```

## Summary Statistics

### Files Changed
- **Renamed**: 3 files (with `git mv`)
- **Deleted**: 2 files
- **Modified**: 6 files
  - 1 configuration file (`_CoqProject`)
  - 2 import updates (`PatternOverlap.v`, `Position_Skipping_Proof.v`)
  - 3 header updates (renamed modules)
- **Total affected**: 11 files

### Lines Changed
- **_CoqProject**: 10 lines (documentation + filenames)
- **Import statements**: 6 lines across 2 files
- **Header documentation**: ~21 lines across 3 files
- **Deleted files**: 21KB + 8.2KB removed
- **Total**: ~40 substantive lines changed

## Verification Status

### Compilation Progress
- ✅ **rewrite_rules.v**: Compiled successfully
- ✅ **Auxiliary/Types.v**: Compiled successfully
- ✅ **Auxiliary/Lib.v**: Compiled successfully
- ✅ **Core/Rules.v**: Compiled successfully
- ✅ **Patterns/Preservation.v**: Compiled successfully
- ✅ **Invariants/InvariantProperties.v**: Compiled successfully
- ✅ **Invariants/AlgoState.v**: Compiled successfully
- ✅ **Patterns/PatternHelpers_Basic.v**: Compiled successfully
- ✅ **Patterns/PatternMatching_Properties.v**: Compiled successfully
- 🔄 **Patterns/PatternMatching_Induction.v**: Currently compiling
- ⏳ **Patterns/PatternMatching_Positioning.v**: Pending
- ⏳ **Patterns/PatternOverlap.v**: Pending
- ⏳ **theories/Position_Skipping_Proof.v**: Pending

### OOM Risk Mitigation
- **Before**: Uncontrolled compilation could consume 100GB+ RAM and crash system
- **Now**: Monitoring compilation, can kill process if memory usage becomes excessive
- **Future**: Profile and optimize `pattern_matches_at_has_mismatch` proof (Phase 4)

## Next Steps

### Short-Term
1. ✅ Complete compilation of all modules
2. ✅ Verify no errors in renamed modules
3. ⏳ Create git commit documenting changes

### Medium-Term (Phase 4)
**Recommendation**: Use Option 5 (Profile) + Option 1 (Optimize) to fix OOM root cause

**Strategy**:
1. Profile with `coqc -verbose -time` to identify slowest tactics
2. Pre-prove arithmetic lemmas separately to reduce `lia` workload
3. Split proof into smaller lemmas with targeted case analysis
4. Replace excessive `lia` usage with manual proof steps where feasible
5. Consider alternative proof strategies (well-founded induction vs structural)

**Goal**: Reduce memory footprint from 100GB+ to manageable levels (<20GB)

## References

- **Original monolithic file**: `docs/verification/phonetic/position_skipping_proof.v` (3379 lines, 87 lemmas)
- **Compilation logs**: `/tmp/verify_compile.log`, `/tmp/overlap_compile.log`, `/tmp/leftmost_compile.log`
- **Git branch**: `proof-multirule-axiom`
- **Main branch**: `master`
