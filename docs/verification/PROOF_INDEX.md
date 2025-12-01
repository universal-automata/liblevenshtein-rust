# Levenshtein Verification Proof Index

**Generated:** 2025-12-01
**Status:** All theorems proven with Qed (except 1 admitted semantic gap)

## Quick Statistics

| Category | Core | Phonetic | Total |
|----------|------|----------|-------|
| Modules | 21 | 14 | 35 |
| Theorems | 4 | 4 | 8 |
| Lemmas | ~200 | ~95 | ~295 |
| Definitions | ~40 | ~15 | ~55 |
| Axioms | 0 | 2 | 2 |

---

## 1. Main Theorems (Top-Level Results)

### Core Verification - Levenshtein Distance Properties

| Theorem | Location | Description |
|---------|----------|-------------|
| **trace_cost_lower_bound** | `LowerBound/MainTheorem.v:42` | Any valid trace with NoDup and monotonicity has cost >= lev_distance. The fundamental lower bound theorem. |
| **lev_distance_identity** | `Core/MetricProperties.v:21` | d(A, A) = 0. A string has zero distance to itself. |
| **lev_distance_symmetry** | `Core/MetricProperties.v:41` | d(A, B) = d(B, A). Edit distance is symmetric. |
| **lev_distance_upper_bound** | `Core/MetricProperties.v:92` | d(A, B) <= max(\|A\|, \|B\|). Distance bounded by longer string. |

### Phonetic Verification - Position Skipping Optimization

| Theorem | Location | Description |
|---------|----------|-------------|
| **position_skipping_conditionally_safe** | `Position_Skipping_Proof.v:518` | Position skipping is safe for restricted rule sets with position-independent contexts. |
| **position_skip_safe_for_local_contexts** | `Position_Skipping_Proof.v:365` | Position skipping preserves semantics when contexts don't depend on absolute position. |
| **apply_rules_seq_opt_terminates** | `Core/Rules.v:75` | The optimized algorithm always terminates with sufficient fuel. |
| **pattern_overlap_preservation** | `Patterns/PatternOverlap.v` | When a pattern overlaps a transformation region and fails to match originally, it fails after transformation. (612-line proof) |

---

## 2. Supporting Theorems & Key Lemmas

### Tier 1: Metric Space Foundations

| Name | Type | Location | Description |
|------|------|----------|-------------|
| lev_distance_length_diff_lower | Lemma | `Core/MetricProperties.v:199` | Distance is at least the difference in lengths |
| abs_diff_succ_bound | Lemma | `Core/MetricProperties.v:155` | Bound on abs_diff with successor |

### Tier 2: Algorithm Correctness

| Name | Type | Location | Description |
|------|------|----------|-------------|
| lev_distance_unfold | Lemma | `Core/LevDistance.v:61` | Unfolding lemma matching recursive definition |
| lev_distance_empty_left | Lemma | `Core/LevDistance.v:81` | Base case: distance from empty string on left |
| lev_distance_empty_right | Lemma | `Core/LevDistance.v:89` | Base case: distance from empty string on right |
| lev_distance_cons | Lemma | `Core/LevDistance.v:98` | Recursive case for cons patterns |
| lev_distance_nil_nil | Lemma | `LowerBound/Definitions.v:22` | Base: empty to empty is 0 |
| lev_distance_nil_l | Lemma | `LowerBound/Definitions.v:25` | Base: empty to any on left |
| lev_distance_nil_r | Lemma | `LowerBound/Definitions.v:28` | Base: any to empty on right |
| lev_distance_cons_cons | Lemma | `LowerBound/Definitions.v:31` | Cons case for both strings |

### Tier 3: Min Function Properties

| Name | Type | Location | Description |
|------|------|----------|-------------|
| min3_lower_bound | Lemma | `Core/MinLemmas.v:19` | min3 returns value <= all inputs |
| min3_comm_12 | Lemma | `Core/MinLemmas.v:37` | min3 commutative in first two args |
| subst_cost_eq | Lemma | `Core/MinLemmas.v:78` | subst_cost is 0 for identical chars |
| subst_cost_neq | Lemma | `Core/MinLemmas.v:93` | subst_cost is 1 for different chars |
| subst_cost_bound | Lemma | `Core/MinLemmas.v:107` | subst_cost bounded by 1 |

### Tier 4: Trace Validity

| Name | Type | Location | Description |
|------|------|----------|-------------|
| is_valid_trace_aux_implies_monotonic | Lemma | `Trace/TraceBasics.v:126` | BRIDGE: is_valid_trace_aux implies monotonicity |
| is_valid_trace_implies_NoDup | Lemma | `Trace/TraceBasics.v:225` | Valid traces have NoDup |
| is_valid_trace_implies_monotonic | Lemma | `Trace/TraceBasics.v:237` | Valid traces are monotonic |
| compatible_pairs_monotonic_helper | Lemma | `Trace/TraceBasics.v:55` | Compatible pairs enforce order |
| forallb_compatible_monotonic | Lemma | `Trace/TraceBasics.v:73` | forallb compatible implies monotonicity |

### Tier 5: Touched Positions

| Name | Type | Location | Description |
|------|------|----------|-------------|
| touched_in_A_length | Lemma | `Trace/TouchedPositions.v:36` | Length of touched_in_A equals trace length |
| touched_in_B_length | Lemma | `Trace/TouchedPositions.v:47` | Length of touched_in_B equals trace length |
| In_touched_in_A_exists_pair | Lemma | `Trace/TouchedPositions.v:58` | If i in touched_in_A, exists j with (i,j) in T |
| In_pair_implies_touched_A | Lemma | `Trace/TouchedPositions.v:84` | If (i,j) in T, then i in touched_in_A |
| In_pair_implies_touched_B | Lemma | `Trace/TouchedPositions.v:97` | If (i,j) in T, then j in touched_in_B |

### Tier 6: Cardinality & NoDup

| Name | Type | Location | Description |
|------|------|----------|-------------|
| NoDup_split | Lemma | `Cardinality/NoDupInclusion.v:18` | Split list with NoDup at element |
| incl_length_NoDup | Lemma | `Cardinality/NoDupInclusion.v:50` | Inclusion with NoDup implies length ordering |
| NoDup_list_inter | Lemma | `Cardinality/NoDupInclusion.v:132` | NoDup preserved by list_inter |
| list_inter_length_bound | Lemma | `Cardinality/NoDupInclusion.v:143` | Length of intersection is bounded |

### Tier 7: Has Predicates

| Name | Type | Location | Description |
|------|------|----------|-------------|
| monotonicity_eliminates_cross_matching | Lemma | `LowerBound/HasPredicates.v:33` | Monotonicity eliminates cross-matching |
| monotonic_cross_matching_impossible | Lemma | `LowerBound/HasPredicates.v:98` | Cross-matching impossible with monotonicity |
| touched_in_A_1_implies_pair | Lemma | `LowerBound/HasPredicates.v:53` | Extract (1, j) from touched_in_A containing 1 |
| valid_trace_indices_ge1 | Lemma | `LowerBound/HasPredicates.v:79` | Pairs in valid trace have indices >= 1 |

### Tier 8: Shift Operations

| Name | Type | Location | Description |
|------|------|----------|-------------|
| shift_trace_11_length | Lemma | `LowerBound/ShiftTrace11Lemmas.v:21` | Length of shift_trace_11 when (1,1) present |
| shift_trace_A_length_no_A1 | Lemma | `LowerBound/ShiftTraceA.v:46` | shift_trace_A preserves length when has_A1=false |
| shift_trace_B_length_no_B1 | Lemma | `LowerBound/ShiftTraceB.v:39` | shift_trace_B preserves length when has_B1=false |
| shift_trace_11_valid | Lemma | `LowerBound/ShiftTrace11Lemmas.v:86` | Validity of shift_trace_11 |
| shift_trace_A_valid | Lemma | `LowerBound/ShiftTraceA.v:156` | Validity of shift_trace_A |
| shift_trace_B_valid | Lemma | `LowerBound/ShiftTraceB.v:104` | Validity of shift_trace_B |

### Tier 9: NoDup Preservation

| Name | Type | Location | Description |
|------|------|----------|-------------|
| shift_trace_A_NoDup_A | Lemma | `LowerBound/NoDupPreservation.v:95` | NoDup preserved for A under shift_trace_A |
| shift_trace_B_NoDup_B | Lemma | `LowerBound/NoDupPreservation.v:184` | NoDup preserved for B under shift_trace_B |
| shift_trace_11_NoDup_A | Lemma | `LowerBound/ShiftTrace11Lemmas.v:266` | NoDup preserved for shift_trace_11 on A |
| shift_trace_11_NoDup_B | Lemma | `LowerBound/ShiftTrace11Lemmas.v:306` | NoDup preserved for shift_trace_11 on B |

### Tier 10: Monotonicity Preservation

| Name | Type | Location | Description |
|------|------|----------|-------------|
| shift_trace_A_monotonic | Lemma | `LowerBound/MonotonicityLemmas.v:89` | Monotonicity preserved for shift_trace_A |
| shift_trace_B_monotonic | Lemma | `LowerBound/MonotonicityLemmas.v:106` | Monotonicity preserved for shift_trace_B |
| shift_trace_11_monotonic | Lemma | `LowerBound/MonotonicityLemmas.v:123` | Monotonicity preserved for shift_trace_11 |

### Tier 11: Pigeonhole Bounds

| Name | Type | Location | Description |
|------|------|----------|-------------|
| NoDup_length_le_range | Lemma | `LowerBound/PigeonholeBounds.v:116` | Pigeonhole: NoDup list in [a,b] has length <= b-a+1 |
| NoDup_A_bound | Lemma | `LowerBound/PigeonholeBounds.v:135` | NoDup + validity + no A1 implies \|T\| <= \|s1'\| |
| NoDup_B_bound | Lemma | `LowerBound/PigeonholeBounds.v:160` | NoDup + validity + no B1 implies \|T\| <= \|s2'\| |

### Tier 12: Cost Analysis

| Name | Type | Location | Description |
|------|------|----------|-------------|
| trace_cost_fold_cons | Lemma | `LowerBound/TraceCostFold.v:29` | Accumulator property for fold_left |
| trace_cost_fold_shift_all_ge2 | Lemma | `LowerBound/TraceCostFold.v:50` | Cost equality after shift when indices >= 2 |
| change_cost_shift_11 | Lemma | `LowerBound/TraceCostFold.v:79` | Cost decomposition for shift_trace_11 |
| change_cost_shift_A | Lemma | `LowerBound/ShiftTraceA.v:142` | Cost equality for shift_trace_A |
| change_cost_shift_B | Lemma | `LowerBound/ShiftTraceB.v:90` | Cost equality for shift_trace_B |

---

## 3. Core Definitions

### Foundation Types

| Name | Type | Location | Description |
|------|------|----------|-------------|
| Char | Definition | `Core/Definitions.v:18` | Characters as Coq's ascii type |
| Matrix | Definition | `Core/Definitions.v:24` | DP matrix: nested list for 2D array |
| Trace | Definition | `Trace/TraceBasics.v:20` | List of pairs (i, j) representing alignment |
| SearchInvariant | Inductive | `Auxiliary/Types.v:82` | Execution state of sequential search |
| AlgoState | Inductive | `Auxiliary/Types.v:95` | Execution state of search algorithm |

### Core Functions

| Name | Type | Location | Description |
|------|------|----------|-------------|
| min3 | Definition | `Core/Definitions.v:29` | Minimum of three natural numbers |
| subst_cost | Definition | `Core/Definitions.v:41` | Substitution cost: 0 if match, 1 otherwise |
| lev_distance_pair | Function | `Core/LevDistance.v:36` | Levenshtein distance with well-founded recursion |
| lev_distance | Definition | `Core/LevDistance.v:55` | Wrapper with standard signature |
| optimal_trace_pair | Function | `OptimalTrace/Construction.v:28` | Optimal trace via DP backtracking |

### Trace Operations

| Name | Type | Location | Description |
|------|------|----------|-------------|
| touched_in_A | Definition | `Trace/TouchedPositions.v:20` | Positions in A touched by trace |
| touched_in_B | Definition | `Trace/TouchedPositions.v:27` | Positions in B touched by trace |
| trace_cost | Definition | `Trace/TraceCost.v:22` | Cost according to Wagner-Fischer |
| valid_pair | Definition | `Trace/TraceBasics.v:25` | Check if pair valid for lengths |
| trace_monotonic | Definition | `Trace/TraceBasics.v:48` | Trace preserves order |

### Shift Operations

| Name | Type | Location | Description |
|------|------|----------|-------------|
| shift_trace_11 | Definition | `LowerBound/ShiftTrace11.v:20` | Filter out (1,1) and shift indices |
| shift_trace_A | Definition | `LowerBound/ShiftTraceA.v:28` | Filter pairs with i>1 and shift |
| shift_trace_B | Definition | `LowerBound/ShiftTraceB.v:21` | Filter pairs with j>1 and shift |

### Predicates

| Name | Type | Location | Description |
|------|------|----------|-------------|
| has_pair_11 | Definition | `LowerBound/HasPredicates.v:19` | Check if (1,1) in trace |
| has_A1 | Definition | `LowerBound/HasPredicates.v:23` | Check if 1 in touched_in_A |
| has_B1 | Definition | `LowerBound/HasPredicates.v:27` | Check if 1 in touched_in_B |
| simple_valid_trace | Definition | `LowerBound/Definitions.v:66` | Simple validity check |
| can_apply_at | Definition | `Auxiliary/Types.v:20` | Check if rule can apply at position |
| no_rules_match_before | Definition | `Auxiliary/Types.v:31` | No rules match before position |

---

## 4. Phonetic Verification - Supporting Lemmas

### Find First Match Lemmas

| Name | Type | Location | Description |
|------|------|----------|-------------|
| find_first_match_from_lower_bound | Lemma | `Auxiliary/Lib.v:44` | Search only from start_pos onward |
| find_first_match_some_implies_can_apply | Lemma | `Auxiliary/Lib.v:287` | Some result implies can_apply_at true |
| find_first_match_is_first | Lemma | `Auxiliary/Lib.v:376` | Found position has no earlier match |
| find_first_match_from_skip_one | Lemma | `Position_Skipping_Proof.v:42` | Skip single non-matching position |
| find_first_match_from_skip_range | Lemma | `Position_Skipping_Proof.v:55` | Skip range of non-matching positions |

### Context Preservation

| Name | Type | Location | Description |
|------|------|----------|-------------|
| apply_rule_at_preserves_prefix | Lemma | `Patterns/PatternHelpers_Basic.v:19` | Preserves phones before match position |
| initial_context_preserved | Lemma | `Patterns/PatternHelpers_Basic.v:71` | Initial context preserved at earlier positions |
| before_vowel_context_preserved | Lemma | `Patterns/PatternHelpers_Basic.v:85` | BeforeVowel context preserved |
| after_consonant_context_preserved | Lemma | `Patterns/PatternHelpers_Basic.v:138` | AfterConsonant context preserved |

### Pattern Matching

| Name | Type | Location | Description |
|------|------|----------|-------------|
| pattern_matches_at_has_mismatch | Lemma | `Patterns/PatternMatching_Induction.v:25` | False match implies mismatch position exists |
| pattern_has_leftmost_mismatch | Lemma | `Patterns/PatternMatching_Positioning.v:25` | Mismatch has leftmost (first) position |
| leftmost_mismatch_before_transformation | Lemma | `Patterns/PatternOverlap.v:44` | Leftmost mismatch before transformation |

### Invariant Maintenance

| Name | Type | Location | Description |
|------|------|----------|-------------|
| algo_state_maintains_invariant | Theorem | `Invariants/AlgoState.v:61` | AlgoState maintains no_rules_match_before |
| search_invariant_init | Lemma | `Invariants/InvariantProperties.v:125` | Search invariant holds at position 0 |
| search_invariant_step_all_rules | Lemma | `Invariants/InvariantProperties.v:179` | Invariant extends when all rules don't match |
| no_rules_match_before_first_match_preserved | Theorem | `Position_Skipping_Proof.v:111` | Multi-rule invariant for position-independent contexts |

---

## 5. Axioms & Semantic Gaps

| Name | Status | Location | Description |
|------|--------|----------|-------------|
| rule_id_unique | Axiom | `Auxiliary/Types.v:127` | rule_id uniquely identifies rules in Zompist phonetic system. Closed-world semantics for finite rule set. |
| find_first_match_in_algorithm_implies_no_earlier_matches | Axiom | `Auxiliary/Types.v:142` | If find_first_match finds position for rule, no rules matched before. Semantic bridge. |
| find_first_match_implies_algo_state | Admitted | `Invariants/AlgoState.v:100` | SEMANTIC GAP: Connects find_first_match result to AlgoState existence. |

---

## 6. Module-by-Module Reference

### Core Theories (`docs/verification/core/theories/`)

#### Core/
- `Definitions.v` - Base types: Char, Matrix, min3, subst_cost
- `LevDistance.v` - Main lev_distance function with well-founded recursion
- `MinLemmas.v` - Properties of min3 and subst_cost
- `MetricProperties.v` - Metric space: identity, symmetry, upper bound

#### Trace/
- `TraceBasics.v` - Trace type, validity, monotonicity
- `TouchedPositions.v` - touched_in_A, touched_in_B projections
- `TraceCost.v` - trace_cost function and bounds

#### Cardinality/
- `NoDupInclusion.v` - NoDup lemmas, list_inter, cardinality bounds

#### OptimalTrace/
- `Construction.v` - optimal_trace_pair construction via DP

#### LowerBound/ (12 modules)
- `Definitions.v` - Trace types and base lemmas
- `HasPredicates.v` - has_A1, has_B1, has_pair_11
- `ShiftTrace11.v` - shift_trace_11 operation
- `ShiftTraceA.v` - shift_trace_A operation
- `ShiftTraceB.v` - shift_trace_B operation
- `BoundHelpers.v` - Validity bound helpers
- `PigeonholeBounds.v` - Pigeonhole principle bounds
- `NoDupPreservation.v` - NoDup preservation under shifts
- `ShiftTrace11Lemmas.v` - shift_trace_11 validity and NoDup
- `MonotonicityLemmas.v` - Monotonicity preservation
- `TraceCostFold.v` - trace_cost_fold and cost decomposition
- `MainTheorem.v` - **trace_cost_lower_bound theorem**

### Phonetic Theories (`docs/verification/phonetic/theories/`)

#### Auxiliary/
- `Types.v` - can_apply_at, SearchInvariant, AlgoState, axioms
- `Lib.v` - find_first_match_from, arithmetic helpers, search lemmas

#### Core/
- `Rules.v` - apply_rules_seq_opt, termination theorem

#### Invariants/
- `AlgoState.v` - algo_state_maintains_invariant
- `InvariantProperties.v` - Invariant initialization and stepping
- `NoMatch.v` - No-match preservation lemmas
- `SearchInvariant.v` - SearchInvariant lemmas

#### Patterns/
- `PatternHelpers_Basic.v` - Prefix preservation, context preservation
- `PatternMatching_Properties.v` - Pattern matching properties
- `PatternMatching_Induction.v` - Nested induction for mismatch
- `PatternMatching_Positioning.v` - Leftmost mismatch analysis
- `PatternOverlap.v` - **pattern_overlap_preservation theorem**
- `Preservation.v` - Context preservation definitions

#### Main Entry Point
- `Position_Skipping_Proof.v` - **position_skipping_conditionally_safe theorem**

---

## 7. Dependency Graph (Simplified)

```
                     trace_cost_lower_bound
                              |
            +-----------------+------------------+
            |                 |                  |
    change_cost_shift_*   NoDup_*_bound    shift_trace_*_monotonic
            |                 |                  |
    trace_cost_fold     pigeonhole         shift_trace_*_valid
            |                 |                  |
        subst_cost      touched_in_*       trace_monotonic
            |                 |                  |
         min3              Trace            valid_pair
            |                 |                  |
          Char          list (nat*nat)         nat
```

```
              position_skipping_conditionally_safe
                              |
            +-----------------+------------------+
            |                 |                  |
    no_rules_match_*   pattern_overlap_*   apply_rules_seq_opt
            |                 |                  |
    search_invariant    leftmost_mismatch   find_first_match_from
            |                 |                  |
    algo_state          context_preserved    can_apply_at
            |                 |                  |
    AlgoState           apply_rule_at       RewriteRule
```
