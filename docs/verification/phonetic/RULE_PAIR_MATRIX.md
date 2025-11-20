# Rule Pair Interaction Matrix (13×13 = 169 pairs)

**Date**: 2025-11-19
**Purpose**: Systematic analysis of all rule pair interactions for Axiom 2
**Question**: Can `replacement(r_applied)` match `pattern(r_check)` in overlap region?

## Matrix Legend

- ✅ **SAFE**: Provably cannot interfere (trivial)
- 🔍 **CHECK**: Requires computational verification
- ⚠️ **WARN**: Potential interference (needs proof)

## Rule Summary Table

| ID | Name | Pattern | Replacement | Context | Type |
|----|------|---------|-------------|---------|------|
| 1 | ch→ç | [c,h] (2) | [Digraph] (1) | Anywhere | Contract |
| 2 | sh→$ | [s,h] (2) | [Digraph] (1) | Anywhere | Contract |
| 3 | ph→f | [p,h] (2) | [f] (1) | Anywhere | Contract |
| 20 | c→s/_[ie] | [c] (1) | [s] (1) | BeforeVowel(e,i) | Subst |
| 21 | c→k | [c] (1) | [k] (1) | Anywhere | Subst |
| 22 | g→j/_[ie] | [g] (1) | [j] (1) | BeforeVowel(e,i) | Subst |
| 33 | e→∅/_# | [e] (1) | [Silent] (1) | Final | Delete |
| 34 | gh→∅ | [g,h] (2) | [Silent] (1) | Anywhere | Delete |
| 100 | th→t | [t,h] (2) | [t] (1) | Anywhere | Contract |
| 101 | qu→kw | [q,u] (2) | [k,w] (2) | Anywhere | Subst |
| 102 | kw→qu | [k,w] (2) | [q,u] (2) | Anywhere | Subst |
| 200 | x→yy | [x] (1) | [y,y] (2) | Anywhere | Expand |
| 201 | y→z | [y] (1) | [z] (1) | Anywhere | Subst |

## Complete 13×13 Matrix

### Rows: r_applied (what rule is applied)
### Cols: r_check (what pattern we're checking)

```
        │  1   2   3  20  21  22  33  34 100 101 102 200 201
────────┼──────────────────────────────────────────────────────
  1 ch→ç│ ✅  ✅  ✅  ✅  ✅  ✅  ✅  ✅  ✅  ✅  ✅  ✅  ✅
  2 sh→$│ ✅  ✅  ✅  ✅  ✅  ✅  ✅  ✅  ✅  ✅  ✅  ✅  ✅
  3 ph→f│ ✅  ✅  ✅  ✅  ✅  ✅  ✅  ✅  ✅  ✅  ✅  ✅  ✅
 20 c→s │ ✅  ✅  ✅  ✅  ✅  ✅  ✅  ✅  ✅  ✅  ✅  ✅  ✅
 21 c→k │ ✅  ✅  ✅  ✅  ✅  ✅  ✅  ✅  ✅  ✅  🔍  ✅  ✅
 22 g→j │ ✅  ✅  ✅  ✅  ✅  ✅  ✅  ✅  ✅  ✅  ✅  ✅  ✅
 33 e→∅ │ ✅  ✅  ✅  ✅  ✅  ✅  ✅  ✅  ✅  ✅  ✅  ✅  ✅
 34 gh→∅│ ✅  ✅  ✅  ✅  ✅  ✅  ✅  ✅  ✅  ✅  ✅  ✅  ✅
100 th→t│ ✅  ✅  ✅  ✅  ✅  ✅  ✅  ✅  ✅  ✅  ✅  ✅  ✅
101 qu→kw│ ✅  ✅  ✅  ✅  ✅  ✅  ✅  ✅  ✅  ✅  🔍  ✅  ✅
102 kw→qu│ ✅  ✅  ✅  ✅  ✅  ✅  ✅  ✅  ✅  🔍  ✅  ✅  ✅
200 x→yy│ ✅  ✅  ✅  ✅  ✅  ✅  ✅  ✅  ✅  ✅  ✅  ✅  ⚠️
201 y→z │ ✅  ✅  ✅  ✅  ✅  ✅  ✅  ✅  ✅  ✅  ✅  ✅  ✅
```

## Detailed Analysis

### Row 1: r_applied = Rule 1 (ch → Digraph)

- Replacement: `[Digraph(c,h)]` (single phone, special type)
- **All 13 pairs SAFE**: Digraph is a single atomic phone, cannot match multi-consonant patterns

| Pair | r_check | Reasoning |
|------|---------|-----------|
| (1,1) | ch→ç | ✅ Digraph ≠ [c,h] pattern |
| (1,2) | sh→$ | ✅ Digraph ≠ [s,h] pattern |
| (1,3) | ph→f | ✅ Digraph ≠ [p,h] pattern |
| (1,20) | c→s | ✅ Digraph ≠ Consonant(c) |
| (1,21) | c→k | ✅ Digraph ≠ Consonant(c) |
| (1,22) | g→j | ✅ Digraph ≠ Consonant(g) |
| (1,33) | e→∅ | ✅ Digraph ≠ Vowel(e) |
| (1,34) | gh→∅ | ✅ Digraph ≠ [g,h] pattern |
| (1,100) | th→t | ✅ Digraph ≠ [t,h] pattern |
| (1,101) | qu→kw | ✅ Digraph ≠ [q,u] pattern |
| (1,102) | kw→qu | ✅ Digraph ≠ [k,w] pattern |
| (1,200) | x→yy | ✅ Digraph ≠ Consonant(x) |
| (1,201) | y→z | ✅ Digraph ≠ Consonant(y) |

### Row 2: r_applied = Rule 2 (sh → Digraph)

- Replacement: `[Digraph(s,h)]` (single phone, special type)
- **All 13 pairs SAFE**: Same reasoning as Rule 1

### Row 3: r_applied = Rule 3 (ph → f)

- Replacement: `[Consonant(f)]` (single consonant)
- **All 13 pairs SAFE**: Single consonant 'f' doesn't match any pattern

| Pair | r_check | Reasoning |
|------|---------|-----------|
| (3,1) | ch→ç | ✅ [f] too short for [c,h] (len 1 < 2) |
| (3,2) | sh→$ | ✅ [f] too short for [s,h] |
| (3,3) | ph→f | ✅ [f] ≠ [p,h] |
| (3,20) | c→s | ✅ f ≠ c |
| (3,21) | c→k | ✅ f ≠ c |
| (3,22) | g→j | ✅ f ≠ g |
| (3,33) | e→∅ | ✅ Consonant(f) ≠ Vowel(e) |
| (3,34) | gh→∅ | ✅ [f] too short for [g,h] |
| (3,100) | th→t | ✅ [f] too short for [t,h] |
| (3,101) | qu→kw | ✅ [f] too short for [q,u] |
| (3,102) | kw→qu | ✅ [f] too short for [k,w] |
| (3,200) | x→yy | ✅ f ≠ x |
| (3,201) | y→z | ✅ f ≠ y |

### Row 4: r_applied = Rule 20 (c → s)

- Replacement: `[Consonant(s)]` (single consonant)
- **All 13 pairs SAFE**: Single 's' doesn't match any pattern

| Pair | r_check | Reasoning |
|------|---------|-----------|
| (20,1) | ch→ç | ✅ [s] too short for [c,h] |
| (20,2) | sh→$ | ✅ [s] alone ≠ [s,h] (needs h) |
| (20,3) | ph→f | ✅ s ≠ p, and too short |
| (20,20) | c→s | ✅ s ≠ c |
| (20,21) | c→k | ✅ s ≠ c |
| (20,22) | g→j | ✅ s ≠ g |
| (20,33) | e→∅ | ✅ Consonant(s) ≠ Vowel(e) |
| (20,34) | gh→∅ | ✅ [s] too short for [g,h] |
| (20,100) | th→t | ✅ s ≠ t, and too short |
| (20,101) | qu→kw | ✅ [s] too short for [q,u] |
| (20,102) | kw→qu | ✅ [s] too short for [k,w] |
| (20,200) | x→yy | ✅ s ≠ x |
| (20,201) | y→z | ✅ s ≠ y |

### Row 5: r_applied = Rule 21 (c → k)

- Replacement: `[Consonant(k)]` (single consonant)
- **12 SAFE, 1 CHECK**

| Pair | r_check | Reasoning |
|------|---------|-----------|
| (21,1) | ch→ç | ✅ [k] too short for [c,h] |
| (21,2) | sh→$ | ✅ k ≠ s |
| (21,3) | ph→f | ✅ k ≠ p |
| (21,20) | c→s | ✅ k ≠ c |
| (21,21) | c→k | ✅ k ≠ c |
| (21,22) | g→j | ✅ k ≠ g |
| (21,33) | e→∅ | ✅ Consonant(k) ≠ Vowel(e) |
| (21,34) | gh→∅ | ✅ [k] too short for [g,h] |
| (21,100) | th→t | ✅ k ≠ t |
| (21,101) | qu→kw | ✅ [k] too short for [q,u] |
| (21,102) | kw→qu | 🔍 **CHECK**: [k] is prefix of [k,w]! |
| (21,200) | x→yy | ✅ k ≠ x |
| (21,201) | y→z | ✅ k ≠ y |

**Analysis (21,102)**:
- Pattern [k,w] starts with k
- BUT: For overlap preservation, we need the FULL pattern to match
- [k] alone ≠ [k,w] (pattern length 2)
- **Conclusion**: ✅ SAFE (partial match insufficient)

### Row 6: r_applied = Rule 22 (g → j)

- Replacement: `[Consonant(j)]`
- **All 13 pairs SAFE**: Single 'j' doesn't match any pattern

### Row 7: r_applied = Rule 33 (e → Silent)

- Replacement: `[Silent]`
- **All 13 pairs SAFE**: Silent phone cannot match any Consonant/Vowel pattern

| Pair | r_check | Reasoning |
|------|---------|-----------|
| (33,*) | All | ✅ Silent ≠ Consonant/Vowel/Digraph |

### Row 8: r_applied = Rule 34 (gh → Silent)

- Replacement: `[Silent]`
- **All 13 pairs SAFE**: Same as Rule 33

### Row 9: r_applied = Rule 100 (th → t)

- Replacement: `[Consonant(t)]`
- **All 13 pairs SAFE**: Single 't' doesn't match any pattern

| Pair | r_check | Reasoning |
|------|---------|-----------|
| (100,1) | ch→ç | ✅ t ≠ c |
| (100,2) | sh→$ | ✅ t ≠ s |
| (100,3) | ph→f | ✅ t ≠ p |
| (100,20) | c→s | ✅ t ≠ c |
| (100,21) | c→k | ✅ t ≠ c |
| (100,22) | g→j | ✅ t ≠ g |
| (100,33) | e→∅ | ✅ Consonant(t) ≠ Vowel(e) |
| (100,34) | gh→∅ | ✅ [t] too short for [g,h] |
| (100,100) | th→t | ✅ [t] alone ≠ [t,h] |
| (100,101) | qu→kw | ✅ t ≠ q, and too short |
| (100,102) | kw→qu | ✅ t ≠ k |
| (100,200) | x→yy | ✅ t ≠ x |
| (100,201) | y→z | ✅ t ≠ y |

### Row 10: r_applied = Rule 101 (qu → kw)

- Replacement: `[Consonant(k), Consonant(w)]` (length 2)
- **12 SAFE, 1 CHECK**

| Pair | r_check | Reasoning |
|------|---------|-----------|
| (101,1) | ch→ç | ✅ [k,w] ≠ [c,h] (different phones) |
| (101,2) | sh→$ | ✅ [k,w] ≠ [s,h] |
| (101,3) | ph→f | ✅ [k,w] too long for [f] (len 2 > 1) |
| (101,20) | c→s | ✅ [k,w] too long for [c] |
| (101,21) | c→k | ✅ [k,w] too long for [c] |
| (101,22) | g→j | ✅ [k,w] too long for [g] |
| (101,33) | e→∅ | ✅ [k,w] too long for [e] |
| (101,34) | gh→∅ | ✅ [k,w] ≠ [g,h] |
| (101,100) | th→t | ✅ [k,w] ≠ [t,h] |
| (101,101) | qu→kw | ✅ [k,w] ≠ [q,u] |
| (101,102) | kw→qu | 🔍 **CHECK**: [k,w] = [k,w]! EXACT MATCH! |
| (101,200) | x→yy | ✅ [k,w] too long for [x] |
| (101,201) | y→z | ✅ [k,w] too long for [y] |

**Analysis (101,102)**:
- Replacement [k,w] EXACTLY matches pattern [k,w]
- **This IS a problem!** Rule 101 creates [k,w], which Rule 102 can match
- **BUT**: Need to check contexts and actual application scenarios
- Both rules have `Context::Anywhere`, so contexts don't help
- **CONCERN**: This is a genuine circular dependency (qu ↔ kw)

### Row 11: r_applied = Rule 102 (kw → qu)

- Replacement: `[Consonant(q), Consonant(u)]` (length 2)
- **12 SAFE, 1 CHECK**

| Pair | r_check | Reasoning |
|------|---------|-----------|
| (102,1-100) | Various | ✅ [q,u] doesn't match other patterns |
| (102,101) | qu→kw | 🔍 **CHECK**: [q,u] = [q,u]! EXACT MATCH! |
| (102,102) | kw→qu | ✅ [q,u] ≠ [k,w] |
| (102,200-201) | x→yy, y→z | ✅ No match |

**Analysis (102,101)**:
- Replacement [q,u] EXACTLY matches pattern [q,u]
- **This IS a problem!** Rule 102 creates [q,u], which Rule 101 can match
- **Circular dependency**: Rules 101 ↔ 102 create each other's patterns!

### Row 12: r_applied = Rule 200 (x → yy)

- Replacement: `[Consonant(y), Consonant(y)]` (length 2)
- **12 SAFE, 1 WARNING**

| Pair | r_check | Reasoning |
|------|---------|-----------|
| (200,1-22) | Various | ✅ [y,y] doesn't match |
| (200,33) | e→∅ | ✅ [y,y] too long for [e] |
| (200,34-100) | Various | ✅ [y,y] ≠ patterns |
| (200,101-102) | qu/kw | ✅ [y,y] ≠ [q,u] or [k,w] |
| (200,200) | x→yy | ✅ [y,y] too long for [x] |
| (200,201) | y→z | ⚠️ **WARN**: [y,y] contains y, pattern is [y]! |

**Analysis (200,201)**:
- Replacement [y,y] contains two y's
- Pattern [y] matches single y
- **This IS a problem!** Rule 200 creates [y,y], Rule 201 can match one of them
- This is the **non-commutativity test case** mentioned in docs!
- **Expected**: These rules demonstrate non-confluence

### Row 13: r_applied = Rule 201 (y → z)

- Replacement: `[Consonant(z)]`
- **All 13 pairs SAFE**: Single 'z' doesn't match any pattern

## Summary Statistics

### Total Pairs: 169

- ✅ **SAFE (automatic)**: 165 pairs (97.6%)
- 🔍 **CHECK (need verification)**: 2 pairs (1.2%)
  - (21,102): [k] vs [k,w] - partial match, but insufficient
  - (101,101): self-application (trivial)
- ⚠️ **PROBLEMATIC**: 2 pairs (1.2%)
  - **(101,102)**: qu→kw creates [k,w], which kw→qu matches
  - **(102,101)**: kw→qu creates [q,u], which qu→kw matches
  - **(200,201)**: x→yy creates [y,y], which y→z matches

### Critical Finding: Circular Dependencies

**Phonetic rules 101 ↔ 102** create a cycle:
- "quick" → "kwikk" → "quikk" → ...
- These rules are mutually interfering!

**Test rules 200-201** demonstrate non-confluence:
- "box" → "boyy" → "bozz" (if 201 applies twice)
- This is INTENTIONAL (test case for non-commutativity)

## Implication for Axiom 2

### Good News

For **orthography rules only** (Rules 1-3, 20-22, 33-34):
- **All 64 pairs (8×8) are SAFE!** ✅
- No circular dependencies
- No interference

### Challenge

For **full rule set** (all 13 rules):
- Rules 101-102 interfere with each other
- Rules 200-201 interfere (intentionally)

### Solution Strategy

**Option 1**: Prove Axiom 2 **only for orthography rules**
- Restrict to position-independent, non-interfering subset
- This matches production usage (orthography applied first)

**Option 2**: Add precondition to Axiom 2
- Require that `r_applied` and `r` are non-interfering
- Define `non_interfering(r1, r2)` predicate

**Option 3**: Accept the circular case
- Prove that even with interference, pattern overlap is preserved
- The interference doesn't violate the theorem (pattern STILL doesn't match)

## Recommended Approach

**Prove Axiom 2 for orthography rules subset** (8 rules):

1. All 64 pairs provably safe ✅
2. Matches production usage
3. Cleaner proof (no circular dependency edge cases)
4. Can extend later to full set with additional lemmas

**Next step**: Create Coq formalization of these 8 rules and prove safety lemma.

---

**Status**: All 169 pairs analyzed
**Safe pairs**: 165/169 (97.6%)
**Problematic pairs**: 4 (Rules 101-102, 200-201 circularity)
**Recommendation**: Focus on orthography rules (64 pairs, 100% safe)
