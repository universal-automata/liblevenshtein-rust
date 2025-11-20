# Production Rules Analysis for Axiom 2 Completion

**Date**: 2025-11-19
**Purpose**: Analyze all 13 production rules to prove pattern overlap preservation
**Goal**: Replace admit at position_skipping_proof.v:2114

## Executive Summary

The Rust implementation uses **13 production rules** (not the full 56 Zompist rules):
- **8 orthography rules** (weight = 0.0) - exact transformations
- **3 phonetic rules** (weight = 0.15) - approximate transformations
- **2 test rules** (weight = 0.0) - for non-commutativity testing

**Total rule pairs to analyze**: 13 × 13 = **169 pairs**

## Complete Rule Enumeration

### Orthography Rules (8 rules, weight=0.0)

#### Rule 1: ch → ç (digraph)
- **ID**: 1
- **Pattern**: `[Consonant('c'), Consonant('h')]` (length 2)
- **Replacement**: `[Digraph('c', 'h')]` (length 1)
- **Context**: `Anywhere`
- **Type**: Contraction (2→1)
- **Example**: "church" → "çurç"

#### Rule 2: sh → $ (digraph)
- **ID**: 2
- **Pattern**: `[Consonant('s'), Consonant('h')]` (length 2)
- **Replacement**: `[Digraph('s', 'h')]` (length 1)
- **Context**: `Anywhere`
- **Type**: Contraction (2→1)
- **Example**: "ship" → "$ip"

#### Rule 3: ph → f
- **ID**: 3
- **Pattern**: `[Consonant('p'), Consonant('h')]` (length 2)
- **Replacement**: `[Consonant('f')]` (length 1)
- **Context**: `Anywhere`
- **Type**: Contraction (2→1)
- **Example**: "phone" → "fone"

#### Rule 20: c → s / _[ie]
- **ID**: 20
- **Pattern**: `[Consonant('c')]` (length 1)
- **Replacement**: `[Consonant('s')]` (length 1)
- **Context**: `BeforeVowel(['e', 'i'])`
- **Type**: Substitution (1→1)
- **Example**: "city" → "sity"

#### Rule 21: c → k (elsewhere)
- **ID**: 21
- **Pattern**: `[Consonant('c')]` (length 1)
- **Replacement**: `[Consonant('k')]` (length 1)
- **Context**: `Anywhere`
- **Type**: Substitution (1→1)
- **Example**: "cat" → "kat"

#### Rule 22: g → j / _[ie]
- **ID**: 22
- **Pattern**: `[Consonant('g')]` (length 1)
- **Replacement**: `[Consonant('j')]` (length 1)
- **Context**: `BeforeVowel(['e', 'i'])`
- **Type**: Substitution (1→1)
- **Example**: "gem" → "jem"

#### Rule 33: e → ∅ / _# (silent final e)
- **ID**: 33
- **Pattern**: `[Vowel('e')]` (length 1)
- **Replacement**: `[Silent]` (length 1)
- **Context**: `Final`
- **Type**: Deletion (1→Silent)
- **Example**: "code" → "cod∅"

#### Rule 34: gh → ∅ (silent gh)
- **ID**: 34
- **Pattern**: `[Consonant('g'), Consonant('h')]` (length 2)
- **Replacement**: `[Silent]` (length 1)
- **Context**: `Anywhere`
- **Type**: Deletion (2→Silent)
- **Example**: "night" → "nit"

### Phonetic Rules (3 rules, weight=0.15)

#### Rule 100: th → t (phonetic)
- **ID**: 100
- **Pattern**: `[Consonant('t'), Consonant('h')]` (length 2)
- **Replacement**: `[Consonant('t')]` (length 1)
- **Context**: `Anywhere`
- **Type**: Contraction (2→1)
- **Example**: "math" → "mat"

#### Rule 101: qu → kw (phonetic)
- **ID**: 101
- **Pattern**: `[Consonant('q'), Consonant('u')]` (length 2)
- **Replacement**: `[Consonant('k'), Consonant('w')]` (length 2)
- **Context**: `Anywhere`
- **Type**: Substitution (2→2)
- **Example**: "quick" → "kwik"

#### Rule 102: kw → qu (phonetic reverse)
- **ID**: 102
- **Pattern**: `[Consonant('k'), Consonant('w')]` (length 2)
- **Replacement**: `[Consonant('q'), Consonant('u')]` (length 2)
- **Context**: `Anywhere`
- **Type**: Substitution (2→2)
- **Example**: "hawk" → "hauq"

### Test Rules (2 rules, weight=0.0)

#### Rule 200: x → yy (expansion test)
- **ID**: 200
- **Pattern**: `[Consonant('x')]` (length 1)
- **Replacement**: `[Consonant('y'), Consonant('y')]` (length 2)
- **Context**: `Anywhere`
- **Type**: Expansion (1→2)
- **Example**: "box" → "boyy"

#### Rule 201: y → z (transformation test)
- **ID**: 201
- **Pattern**: `[Consonant('y')]` (length 1)
- **Replacement**: `[Consonant('z')]` (length 1)
- **Context**: `Anywhere`
- **Type**: Substitution (1→1)
- **Example**: "yes" → "zes"

## Rule Classification

### By Transformation Type

**Contractions (5 rules)**: Pattern longer than replacement
- Rule 1: ch → ç (2→1)
- Rule 2: sh → $ (2→1)
- Rule 3: ph → f (2→1)
- Rule 34: gh → ∅ (2→1)
- Rule 100: th → t (2→1)

**Substitutions (6 rules)**: Same length
- Rule 20: c → s (1→1)
- Rule 21: c → k (1→1)
- Rule 22: g → j (1→1)
- Rule 33: e → ∅ (1→1, Silent counts as 1)
- Rule 101: qu → kw (2→2)
- Rule 102: kw → qu (2→2)

**Expansions (1 rule)**: Replacement longer than pattern
- Rule 200: x → yy (1→2)

### By Context Type

**Position-Independent (12 rules)**: Safe for overlap preservation
- `Anywhere` (9 rules): 1, 2, 3, 21, 34, 100, 101, 102, 200, 201
- `BeforeVowel` (2 rules): 20, 22

**Position-Dependent (1 rule)**: Requires special handling
- `Final` (1 rule): 33

### By Pattern Length

**Single-phone patterns (5 rules)**:
- Rules 20, 21, 22, 33, 200, 201

**Two-phone patterns (6 rules)**:
- Rules 1, 2, 3, 34, 100, 101, 102

## Pattern Overlap Safety Analysis

### Core Question

For Axiom 2, we need to prove that for any two rules `r_applied` and `r`:

> If `r` doesn't match at position `p < pos` in string `s`, and `r_applied` is applied at `pos` where `p < pos < p + length(pattern r)`, then `r` still doesn't match at `p` in the result `s'`.

### Key Observation

For position-independent contexts, the critical case is when:
1. Leftmost mismatch `i_left` is at position `i_left >= pos`
2. The transformation might "fix" the mismatch

**This requires**: `replacement(r_applied)` cannot accidentally match `pattern(r)` in the overlap region.

## Rule Pair Analysis Strategy

### Step 1: Trivially Safe Pairs

**Case 1.1: Disjoint patterns** (no overlapping phones)
- Pattern phones are completely different
- Example: Rule 1 (ch) vs Rule 3 (ph) - no 'c' or 'h' in 'ph' pattern

**Case 1.2: Context disjoint**
- Contexts can never both be true
- Example: `BeforeVowel(['e','i'])` vs `Final` - mutually exclusive

**Case 1.3: Deletion rules as r_applied**
- If `r_applied` produces `Silent`, it cannot match non-Silent patterns
- Rules 33, 34 produce Silent

### Step 2: Structural Analysis

**Case 2.1: Replacement too short to match pattern**
- If `length(replacement r_applied) < length(pattern r)`, cannot match
- Example: Rule 3 (ph→f, len 1) cannot match Rule 1 pattern (ch, len 2)

**Case 2.2: No phone overlap in replacement and pattern**
- Replacement phones don't appear in pattern
- Example: Rule 3 replacement [f] cannot match Rule 1 pattern [c,h]

### Step 3: Specific Pair Checking

For remaining pairs, check computationally:
- Does `replacement(r_applied)` contain subsequence matching `pattern(r)`?

## Detailed Pair Classification

### Trivially Safe Pairs (automatic)

#### All deletion pairs (26 pairs):
- (r_applied ∈ {33, 34}) × (all rules) - Silent cannot match Consonant/Vowel patterns

#### All Digraph rules vs non-Digraph-matching patterns (25+ pairs):
- Rule 1,2 produce Digraphs, which are single phones
- Cannot match multi-consonant patterns

### Requires Checking (remaining ~110 pairs)

Will use computational decision procedure in Coq.

## Next Steps

1. ✅ **Enumerate all 13 rules** (completed above)
2. ⏳ **Build 13×13 pair matrix** (169 pairs)
3. ⏳ **Classify each pair**:
   - Trivially safe (deletion, length mismatch, disjoint patterns)
   - Requires computational check
4. ⏳ **Create Coq decision procedure**:
   ```coq
   Fixpoint check_pair_safe (r1 r2: RewriteRule) : bool :=
     (* Check if r1's replacement can match r2's pattern *)
   ```
5. ⏳ **Prove correctness**:
   ```coq
   Lemma check_pair_safe_correct:
     forall r1 r2,
       check_pair_safe r1 r2 = true ->
       (* Then replacement r1 cannot match pattern r2 in overlap *)
   ```
6. ⏳ **Compute for all pairs**:
   ```coq
   Definition all_production_rules_safe :=
     forallb (fun '(r1, r2) => check_pair_safe r1 r2)
             (list_prod production_rules production_rules).

   Compute all_production_rules_safe. (* Should reduce to 'true' *)
   ```
7. ⏳ **Apply to resolve admit**

## File References

- **Source**: `/home/dylon/Workspace/f1r3fly.io/liblevenshtein-rust/src/phonetic/rules.rs`
- **Verification**: `/home/dylon/Workspace/f1r3fly.io/liblevenshtein-rust/docs/verification/phonetic/position_skipping_proof.v:2114`
- **Zompist reference**: `/home/dylon/Workspace/f1r3fly.io/liblevenshtein-rust/docs/verification/phonetic/zompist_rules.v`

---

**Status**: Step 1 complete - all 13 rules documented
**Next**: Build and classify 169-pair interaction matrix
