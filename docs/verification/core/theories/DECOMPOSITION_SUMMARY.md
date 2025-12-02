# Modular Decomposition Summary

**Last Updated:** 2025-12-01
**Status:** ✅ **COMPLETE** - All modules compile successfully with Rocq Prover 9.1.0. No Admitted lemmas remain.

## Overview

This directory contains the modular decomposition of the Levenshtein distance proofs. The original monolithic files have been decomposed into smaller, focused modules organized by functionality.

## Original Files (Backed Up)

- `Distance.v.bak` (8,541 lines) - Original monolithic Levenshtein distance proofs
- `TraceLowerBound.v.bak` (2,195 lines) - Original monolithic trace lower bound proofs

## Module Structure

### Tier 1: Foundation
- `Core/Definitions.v` - Basic definitions (Char, String, min3, subst_cost, Trace, Matrix)

### Tier 2: Core Algorithm
- `Core/LevDistance.v` - Levenshtein distance function with termination proof
- `Core/MinLemmas.v` - Lemmas about min3 function

### Tier 3: Metric Properties
- `Core/MetricProperties.v` - Metric space properties (identity, symmetry, upper bound)

### Tier 4: Trace Infrastructure
- `Trace/TraceBasics.v` - Trace type, validity predicates, basic operations
- `Trace/TouchedPositions.v` - touched_in_A, touched_in_B projections
- `Trace/TraceCost.v` - trace_cost function and cost lemmas
- `Trace/TraceComposition.v` - compose_trace operation

### Tier 5: Cardinality & Witnesses
- `Cardinality/NoDupInclusion.v` - NoDup inclusion lemmas
- `Cardinality/NoDupPreservation.v` - NoDup preservation under trace operations

### Tier 6: Triangle Support
- `Triangle/SubstCostTriangle.v` - Substitution cost triangle inequality

### Tier 7: Composition
- `Composition/WitnessLemmas.v` - Witness construction lemmas
- `Composition/CompositionNoDup.v` - NoDup preservation for composed traces
- `Composition/CompositionValidity.v` - Validity preservation for composed traces
- `Composition/CostBounds.v` - Cost bounds for trace composition

### Tier 8: Optimal Trace
- `OptimalTrace/Construction.v` - optimal_trace_pair construction via DP backtracking
- `OptimalTrace/Validity.v` - Validity proof for optimal traces
- `OptimalTrace/CostEquality.v` - trace_cost(optimal_trace) = lev_distance

### Tier 9: Main Theorems
- `Triangle/TriangleInequality.v` - Triangle inequality via trace composition
- `MainTheorems.v` - Consolidated exports of all main theorems

### Tier 10: DP Matrix
- `DPMatrix/MatrixOps.v` - Matrix initialization and update operations
- `DPMatrix/SnocLemmas.v` - Suffix (snoc) lemmas for lev_distance
- `DPMatrix/Correctness.v` - Wagner-Fischer DP matrix correctness

### LowerBound Modules (from TraceLowerBound.v)
- `LowerBound/Definitions.v` - Trace types and basic definitions
- `LowerBound/HasPredicates.v` - has_A1, has_B1, has_pair_11 predicates
- `LowerBound/ShiftTrace11.v` - shift_trace_11 operation
- `LowerBound/ShiftTraceA.v` - shift_trace_A operation
- `LowerBound/ShiftTraceB.v` - shift_trace_B operation
- `LowerBound/BoundHelpers.v` - Validity bound helpers
- `LowerBound/PigeonholeBounds.v` - Pigeonhole principle bounds
- `LowerBound/NoDupPreservation.v` - NoDup preservation under shifts
- `LowerBound/ShiftTrace11Lemmas.v` - shift_trace_11 validity and NoDup
- `LowerBound/MonotonicityLemmas.v` - Monotonicity preservation
- `LowerBound/TraceCostFold.v` - trace_cost_fold and change_cost decomposition
- `LowerBound/MainTheorem.v` - Main trace_cost_lower_bound theorem

## Build Instructions

```bash
# Generate Makefile
coq_makefile -f _CoqProject -o Makefile

# Build all modules (using systemd resource limits for stability)
systemd-run --user --scope -p MemoryMax=126G -p CPUQuota=1800% make -j1

# Or simple build
make -j4
```

## Key Theorems

### 1. Metric Space Properties (`MainTheorems.v`)
- **levenshtein_is_metric**: Levenshtein distance satisfies all metric axioms
  - Non-negativity: d(A,B) >= 0
  - Identity: d(A,B) = 0 <-> A = B
  - Symmetry: d(A,B) = d(B,A)
  - Triangle Inequality: d(A,C) <= d(A,B) + d(B,C)

### 2. Triangle Inequality (`Triangle/TriangleInequality.v`)
- **lev_distance_triangle_inequality**: Proven via trace composition
  - d(A,C) = min{cost(T) | T: A->C}
  - <= cost(T1 o T2) for optimal T1: A->B, T2: B->C
  - <= cost(T1) + cost(T2)
  - = d(A,B) + d(B,C)

### 3. Optimal Trace (`OptimalTrace/CostEquality.v`)
- **optimal_trace_cost**: trace_cost(optimal_trace A B) = lev_distance A B
- **optimal_trace_valid**: optimal_trace produces valid traces

### 4. DP Correctness (`DPMatrix/Correctness.v`)
- **dp_matrix_correctness**: Wagner-Fischer matrix cells equal recursive distance
- **levenshtein_distance_correctness**: Full algorithm produces correct result

### 5. Trace Lower Bound (`LowerBound/MainTheorem.v`)
- **trace_cost_lower_bound**: Any valid trace has cost >= lev_distance

## Admitted Lemmas

**Status as of 2025-12-01:** ✅ **ALL PROOFS COMPLETE - NO ADMITTED LEMMAS REMAIN**

All modular proofs are now fully proven with `Qed`. The decomposition from Distance.v.bak and TraceLowerBound.v.bak is complete.

### Completed Proofs:

1. **trace_cost_lower_bound_internal** (`Triangle/TriangleInequality.v`)
   - ✅ Fully proven via bridge lemmas to LowerBound module
   - Uses `is_valid_trace_aux_implies_monotonic` from TraceBasics.v
   - Connects Core's `is_valid_trace` to LowerBound's `trace_cost_lower_bound`

2. **trace_composition_cost_bound** (`Composition/CostBounds.v`)
   - ✅ Fully proven - cost(T1 ∘ T2) ≤ cost(T1) + cost(T2)
   - Extracted from Distance.v.bak (lines 6785-6874)
   - All ~500 lines of helper lemmas extracted and proven:
     - `witness_to_T1_injective`, `witness_to_T2_injective` - injectivity proofs
     - `map_injective_on_list_NoDup` - NoDup preservation under injective maps
     - `fold_left_triangle_bound`, `fold_left_sum_map_eq` - fold_left infrastructure
     - `change_cost_compose_bound` - change cost triangle inequality
     - `trace_composition_delete_insert_bound` - delete/insert cost bounds
     - `composition_size_pigeonhole` - pigeonhole principle for composition
     - `NoDup_incl_exclusion` (NoDupInclusion.v) - inclusion-exclusion principle

## Module Count

- **Total modules:** 31
- **Core/:** 4 modules
- **Trace/:** 4 modules
- **Cardinality/:** 2 modules
- **Triangle/:** 2 modules
- **Composition/:** 4 modules
- **OptimalTrace/:** 3 modules
- **DPMatrix/:** 3 modules
- **LowerBound/:** 12 modules
- **Main:** 1 module (MainTheorems.v)

## Dependency Graph (Tiers)

```
Tier 1: Core/Definitions
    |
Tier 2: Core/LevDistance, Core/MinLemmas
    |
Tier 3: Core/MetricProperties
    |
Tier 4: Trace/TraceBasics, TouchedPositions, TraceCost, TraceComposition
    |
Tier 5: Cardinality/NoDupInclusion, NoDupPreservation
    |
Tier 6: Triangle/SubstCostTriangle
    |
Tier 7: Composition/WitnessLemmas, CompositionNoDup, CompositionValidity, CostBounds
    |
Tier 8: OptimalTrace/Construction, Validity, CostEquality
    |
Tier 9: Triangle/TriangleInequality, MainTheorems
    |
Tier 10: DPMatrix/MatrixOps, SnocLemmas, Correctness
    |
LowerBound/* (parallel track)
```
