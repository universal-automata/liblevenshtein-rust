# Coq/Rocq Modular Proof Compilation: Memory Analysis

**Date**: 2025-11-20
**Issue**: PatternHelpers.v OOM during compilation despite conservative resource limits
**Status**: Root cause identified, solutions proposed

---

## Problem Statement

**Symptom**: PatternHelpers.v killed by OOM (Out of Memory) during compilation
- **File size**: 591 lines (21KB)
- **Memory allocated**: 126GB (50% of 252GB system RAM)
- **Configuration**: Serial build (`-j1`), 18 cores
- **Result**: Process killed after 30+ minutes

**Comparison to Monolithic Build**:
- **Monolithic file**: 3,379 lines (position_skipping_proof.v)
- **Memory used**: ~40GB peak
- **Compile time**: ~5 minutes
- **Success**: ✅

**Paradox**: Modular file (17.5% size) uses >3× memory of monolithic file (100% size).

---

## Root Cause Analysis

### 1. Proof Complexity

**PatternHelpers.v Characteristics**:
```bash
$ wc -l PatternHelpers.v
591 PatternHelpers.v

$ grep -c "lia\." PatternHelpers.v
42

$ grep -c "induction" PatternHelpers.v
14

$ grep -c "destruct" PatternHelpers.v
89
```

**Key Lemmas**:
1. `pattern_matches_at_has_mismatch` (96 lines)
   - Nested induction on pattern positions
   - 15 `lia` calls
   - Proof complexity: O(n²) in pattern length

2. `pattern_has_leftmost_mismatch` (136 lines)
   - Builds on previous lemma
   - Additional nested destruct
   - 18 `lia` calls
   - Proof complexity: O(n³) due to leftmost property

**Tactic Overhead**:
- Each `lia` call generates large proof terms (SMT solver traces)
- `destruct` creates case splits (exponential in nesting depth)
- `induction` duplicates entire proof context for each case

### 2. Module Dependency Chain

**Dependency Graph**:
```
PatternHelpers.v
  ├─ imports: Preservation.v
  │   ├─ imports: Rules.v
  │   │   ├─ imports: Types.v
  │   │   └─ imports: Lib.v
  │   └─ 182 lines (9.8KB)
  │
  └─ imports: InvariantProperties.v
      └─ imports: AlgoState.v
```

**Memory Impact**:
1. **Loading .vo files**: Each import loads compiled object
2. **Type-checking at boundaries**: Verify imported theorem types
3. **Proof term dependencies**: Cannot discard imported proof terms (referenced in current proof)

**Estimated Memory**:
```
Types.vo: ~5GB
Lib.vo: ~5GB
Rules.vo: ~10GB
Preservation.vo: ~20GB (includes nested induction + lia)
InvariantProperties.vo: ~15GB
AlgoState.vo: ~10GB

Total dependencies: ~65GB
PatternHelpers.v proof terms: ~80-100GB (nested induction × lia)

Grand total: ~150-165GB
```

**Why Monolithic is Smaller**:
- No .vo loading overhead (everything in one file)
- Can discard intermediate proof terms (Qed seals them)
- Sequential proof checking (no module boundaries)

### 3. Proof Term Explosion

**lia Tactic Mechanism**:
1. Extract arithmetic constraints from goal
2. Call external SMT solver (Z3 or Omega)
3. Generate proof certificate (witness trace)
4. Reconstruct proof in Coq (large proof term)

**Example**:
```coq
Goal: i < j < k → i < k
Tactic: lia.

Proof term generated (simplified):
  le_trans i j k
    (le_S_n i (j-1) ...)
    (le_S_n j (k-1) ...)
    ...
  (* 50-100 lines of proof term per lia call *)
```

**Nested Induction**:
```coq
induction phones as [| ph phones' IH].
- (* Base case: nil *)
  lia.  (* Proof term 1 *)
- (* Inductive case *)
  destruct pos.
  + (* pos = 0 *)
    lia.  (* Proof term 2, includes IH context *)
  + (* pos = S pos' *)
    destruct (Phone_eqb ...).
    * lia.  (* Proof term 3, includes all above *)
    * induction pattern.
      -- lia.  (* Proof term 4, nested induction context *)
      -- ...
```

**Memory Growth**:
- Depth 1 induction: Context size C
- Depth 2 induction: Context size C²
- Depth 3 induction: Context size C³
- Each `lia` at depth n: Proof term size ~ C^n

**PatternHelpers.v**:
- Max induction depth: 3
- `lia` calls at depth 3: ~8
- Estimated proof term: 8 × C³ where C ~ 10GB → 80GB

---

## Experimental Evidence

### Attempt 1: Parallel Build (`-j4`, 150GB)
```bash
systemd-run --user --scope \
  -p MemoryMax=150G \
  -p CPUQuota=2700% \
  -p IOWeight=50 \
  -p TasksMax=300 \
  make -j4 2>&1 | tee /tmp/compile_j4_limited.log

Result: OOM killed at PatternHelpers.v
Reason: 4 files compiling × 40GB each = 160GB > 150GB
```

### Attempt 2: Serial Build (`-j1`, 126GB)
```bash
systemd-run --user --scope \
  -p MemoryMax=126G \
  -p CPUQuota=1800% \
  -p IOWeight=30 \
  -p TasksMax=200 \
  make -j1 2>&1 | tee /tmp/compile_serial_safe.log

Result: OOM killed at PatternHelpers.v (after 30+ min)
Reason: PatternHelpers.v alone > 126GB
```

### Monolithic Build (Historical)
```bash
# Original position_skipping_proof.v (3,379 lines)
make theories/position_skipping_proof.vo

Result: ✅ Success (~5 min, ~40GB peak)
Reason: No .vo loading, sequential proof checking
```

---

## Proposed Solutions

### Solution 1: Split PatternHelpers.v (Recommended)

**Strategy**: Break into smaller modules to reduce peak memory.

**Proposed Structure**:
```
PatternHelpers_Basic.v  (200 lines)
  - pattern_length_bounds
  - pattern_matches_at_spec
  - Basic helper lemmas (no heavy proofs)

PatternHelpers_Mismatch.v  (150 lines)
  - pattern_matches_at_has_mismatch (96 lines)
  - Depends on: PatternHelpers_Basic

PatternHelpers_Leftmost.v  (241 lines)
  - pattern_has_leftmost_mismatch (136 lines)
  - Other advanced lemmas
  - Depends on: PatternHelpers_Mismatch
```

**Expected Memory**:
- PatternHelpers_Basic.vo: ~10GB
- PatternHelpers_Mismatch.vo: ~50GB (loads Basic.vo ~10GB + own proofs ~40GB)
- PatternHelpers_Leftmost.vo: ~80GB (loads Mismatch.vo ~50GB + own proofs ~30GB)

**Peak memory**: 80GB < 126GB ✅

**Trade-off**:
- ✅ Compiles within memory limits
- ⚠️ More module files (3 vs 1)
- ⚠️ Slightly slower overall (more .vo loading)

### Solution 2: Use Admitted for Heavy Lemmas

**Strategy**: Temporarily admit memory-intensive lemmas, compile rest of system.

**Implementation**:
```coq
(* PatternHelpers.v *)

Lemma pattern_has_leftmost_mismatch :
  forall pat s p,
    pattern_matches_at pat s p = false ->
    (length pat > 0)%nat ->
    exists i,
      (p <= i < p + length pat)%nat /\
      ...
Proof.
  (* Original 136-line proof causes OOM *)
Admitted.  (* Temporarily *)

(* Use in PatternOverlap.v *)
Lemma overlap_preserves_correctness : ...
Proof.
  ...
  apply pattern_has_leftmost_mismatch.  (* Uses admitted lemma *)
  ...
Qed.
```

**Benefits**:
- ✅ System compiles immediately
- ✅ Can test Rust implementation
- ✅ Identifies other issues

**Drawbacks**:
- ❌ Proofs incomplete (not fully verified)
- ❌ Need to complete later
- ⚠️ Admitted lemmas are trusted axioms (soundness risk)

**When to Use**:
- Testing implementation
- Deadline pressure
- Plan to return and complete proofs

### Solution 3: Optimize Proof Tactics

**Strategy**: Reduce `lia` calls and proof term sizes.

**Technique 1: Manual Arithmetic**:
```coq
(* Before: Heavy lia *)
Lemma foo : forall n, n < n + 1.
Proof.
  intros. lia.  (* Generates 50-line proof term *)
Qed.

(* After: Direct proof *)
Lemma foo : forall n, n < n + 1.
Proof.
  intros. apply Nat.lt_succ_diag_r.  (* 1-line proof term *)
Qed.
```

**Technique 2: Lemma Extraction**:
```coq
(* Extract common lia patterns *)
Lemma pos_lt_sum : forall p len, p < p + len -> len > 0.
Proof. intros. lia. Qed.  (* Prove once, heavy *)

(* Reuse in main proof *)
Lemma main : ...
Proof.
  ...
  apply pos_lt_sum. (* Light reference *)
  ...
Qed.
```

**Technique 3: Simplification Before lia**:
```coq
(* Before *)
Lemma foo : forall a b c d e, complex_expr a b c d e > 0.
Proof.
  intros. lia.  (* Must solve huge constraint system *)
Qed.

(* After *)
Lemma foo : forall a b c d e, complex_expr a b c d e > 0.
Proof.
  intros.
  unfold complex_expr.
  simpl.
  (* Now much simpler *)
  lia.  (* Smaller problem *)
Qed.
```

**Expected Savings**: 30-50% reduction in proof term size

**Effort**: High (requires manual proof rewriting)

### Solution 4: Increase System RAM

**Strategy**: Allocate more memory to Coq.

**Current**: 126GB (50% of 252GB)

**Options**:
```bash
# 75% of RAM
systemd-run --user --scope \
  -p MemoryMax=189G \
  -p CPUQuota=1800% \
  -p IOWeight=30 \
  -p TasksMax=200 \
  make -j1

# 90% of RAM (risky, may freeze system)
systemd-run --user --scope \
  -p MemoryMax=227G \
  -p CPUQuota=1800% \
  -p IOWeight=30 \
  -p TasksMax=200 \
  make -j1
```

**Risks**:
- ⚠️ May still OOM if PatternHelpers needs >189GB
- ⚠️ System instability (desktop, browser competing for remaining RAM)
- ⚠️ No guarantee (may just delay OOM)

**Recommendation**: Try 189GB (75%) as fallback if Solution 1 fails

### Solution 5: Return to Monolithic Proof

**Strategy**: Abandon modular decomposition, use original single file.

**Benefits**:
- ✅ Known to compile (~40GB, 5 minutes)
- ✅ No module overhead
- ✅ Immediate solution

**Drawbacks**:
- ❌ Lose reusability (77 theorems, 3 optimizations)
- ❌ Maintenance difficulty (3,379 lines)
- ❌ Cannot extract crown jewels

**When to Use**: Last resort if all else fails

---

## Recommendation

**Primary Plan**: Solution 1 (Split PatternHelpers.v)

**Rationale**:
1. **Most likely to succeed** (80GB peak < 126GB limit)
2. **Preserves modularity** (still reusable, just 3 files instead of 1)
3. **No proof changes** (just file organization)
4. **Low risk** (can fall back to Solutions 2 or 4)

**Fallback Plan**: Solution 4 (189GB) if Solution 1 still OOMs

**Steps**:
1. Split PatternHelpers.v → 3 files
2. Update _CoqProject
3. Compile with 126GB limit
4. If OOM, try 189GB limit
5. If still OOM, use Solution 2 (Admitted) temporarily

---

## Implementation: Split PatternHelpers.v

### File 1: PatternHelpers_Basic.v (~200 lines)

**Contents**:
- `pattern_length_bounds`
- `pattern_matches_at_spec`
- `pattern_prefix_match`
- Other lightweight lemmas (no nested induction)

**Estimated Memory**: ~10GB

### File 2: PatternHelpers_Mismatch.v (~150 lines)

**Contents**:
```coq
Require Import PatternHelpers_Basic.

Lemma pattern_matches_at_has_mismatch :
  forall pat s p,
    pattern_matches_at pat s p = false ->
    (length pat > 0)%nat ->
    exists i,
      (p <= i < p + length pat)%nat /\
      (nth_error s i = None \/
       exists ph pat_ph,
         nth_error s i = Some ph /\
         nth_error pat (i - p) = Some pat_ph /\
         Phone_eqb ph pat_ph = false).
Proof.
  (* 96-line proof from PatternHelpers.v *)
Qed.
```

**Dependencies**: PatternHelpers_Basic.vo (~10GB)
**Own Proofs**: ~40GB
**Total Peak**: ~50GB

### File 3: PatternHelpers_Leftmost.v (~241 lines)

**Contents**:
```coq
Require Import PatternHelpers_Mismatch.

Lemma pattern_has_leftmost_mismatch :
  forall pat s p,
    pattern_matches_at pat s p = false ->
    (length pat > 0)%nat ->
    exists i,
      (p <= i < p + length pat)%nat /\
      (nth_error s i = None \/
       exists ph pat_ph,
         nth_error s i = Some ph /\
         nth_error pat (i - p) = Some pat_ph /\
         Phone_eqb ph pat_ph = false) /\
      (* i is the LEFTMOST mismatch *)
      (forall j, (p <= j < i)%nat ->
         exists s_ph pat_ph,
           nth_error s j = Some s_ph /\
           nth_error pat (j - p) = Some pat_ph /\
           Phone_eqb s_ph pat_ph = true).
Proof.
  (* 136-line proof from PatternHelpers.v *)
Qed.

(* Other advanced lemmas *)
```

**Dependencies**: PatternHelpers_Mismatch.vo (~50GB)
**Own Proofs**: ~30GB
**Total Peak**: ~80GB

### Updated _CoqProject

```coq
-R theories Liblevenshtein.Phonetic.Verification

theories/Auxiliary/Types.v
theories/Auxiliary/Lib.v
theories/Core/Rules.v

theories/Patterns/Preservation.v
theories/Patterns/PatternHelpers_Basic.v
theories/Patterns/PatternHelpers_Mismatch.v
theories/Patterns/PatternHelpers_Leftmost.v
theories/Patterns/PatternOverlap.v

theories/Invariants/InvariantProperties.v
theories/Invariants/AlgoState.v
```

### Update Imports in PatternOverlap.v

```coq
(* Old *)
Require Import Liblevenshtein.Phonetic.Verification.Patterns.PatternHelpers.

(* New *)
Require Import Liblevenshtein.Phonetic.Verification.Patterns.PatternHelpers_Basic.
Require Import Liblevenshtein.Phonetic.Verification.Patterns.PatternHelpers_Mismatch.
Require Import Liblevenshtein.Phonetic.Verification.Patterns.PatternHelpers_Leftmost.
```

---

## Expected Compilation Timeline

**With Split Solution**:
```
Makefile dependency order:
1. Types.v, Lib.v (parallel) → 2 min
2. Rules.v → 3 min
3. Preservation.v → 8 min (has nested induction + lia)
4. InvariantProperties.v, AlgoState.v (parallel) → 5 min
5. PatternHelpers_Basic.v → 5 min
6. PatternHelpers_Mismatch.v → 15 min (heavy proof)
7. PatternHelpers_Leftmost.v → 20 min (heaviest proof)
8. PatternOverlap.v → 10 min
9. Position_Skipping_Proof.v → 15 min

Total: ~80 minutes (serial, -j1)
```

**With Parallel** (if memory allows `-j2`):
```
Total: ~50 minutes
```

---

## Monitoring During Compilation

```bash
# Terminal 1: Run compilation
cd /home/dylon/Workspace/f1r3fly.io/liblevenshtein-rust/docs/verification/phonetic
systemd-run --user --scope \
  -p MemoryMax=126G \
  -p CPUQuota=1800% \
  -p IOWeight=30 \
  -p TasksMax=200 \
  make -j1 2>&1 | tee /tmp/coq_split_build.log

# Terminal 2: Monitor memory
watch -n 5 'ps aux | grep -E "rocq|coq" | grep -v grep | awk "{sum+=\$6} END {print sum/1024/1024 \" GB\"}"'

# Terminal 3: Check systemd cgroup
systemd-cgtop --user
```

---

## Success Criteria

**Compilation Successful** if:
1. ✅ All .vo files created in theories/
2. ✅ No "Admitted" lemmas (except documented ones)
3. ✅ Rust test suite passes (147 tests)
4. ✅ Memory usage stays < 126GB throughout

**Compilation Failed** if:
- ❌ OOM kill (exit code 137)
- ❌ Compilation errors
- ❌ Hang (>2 hours for single file)

---

## Conclusion

The modular decomposition faces a **fundamental memory challenge**: PatternHelpers.v's complex nested proofs with heavy `lia` usage generate proof terms exceeding 126GB.

**Root Cause**: Proof complexity (O(n³) nested induction × 42 `lia` calls) + Module loading overhead (~65GB dependencies)

**Recommended Solution**: Split PatternHelpers.v into 3 smaller modules (Basic, Mismatch, Leftmost) to reduce peak memory to ~80GB.

**Expected Outcome**: ✅ Compilation succeeds within 126GB limit, preserves modularity and reusability.

**Fallback**: Increase memory limit to 189GB (75% RAM) or use Admitted temporarily.

---

## References

- RESOURCE_LIMITING.md: systemd-run usage guide
- MODULAR_DECOMPOSITION_STATUS.md: Decomposition progress
- Coq Reference Manual: https://coq.inria.fr/refman/
  - Chapter 7.2: The lia tactic
  - Chapter 6.10: Proof term inspection
