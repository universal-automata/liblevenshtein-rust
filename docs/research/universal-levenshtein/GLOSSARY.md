# Universal Levenshtein Automata - Glossary

**Document Status**: Complete notation reference
**Source**: Universal Levenshtein Automata - Building and Properties (2005)
**Last Updated**: 2025-11-11

---

## Purpose

This glossary provides a comprehensive reference for all mathematical notation, symbols, functions, and terminology used in the Universal Levenshtein Automata thesis and documentation.

**Related Documents**:
- [PAPER_SUMMARY.md](./PAPER_SUMMARY.md) - Full chapter-by-chapter analysis
- [README.md](./README.md) - Overview and quick start
- [ALGORITHMS.md](./ALGORITHMS.md) - Implementation algorithms
- [Core Paper Glossary](../levenshtein-automata/glossary.md) - Fixed-word automata notation

---

## Quick Reference

### Most Important Symbols

| Symbol | Meaning | Page |
|--------|---------|------|
| χ | Metasymbol: ε (standard), t (transposition), ms (merge/split) | 3 |
| d^χ_L(v, w) | Levenshtein distance between v and w | 3-5 |
| i#e | Fixed-word position: position i, error count e | 9 |
| I + i#e | Universal non-final position | 30 |
| M + i#e | Universal final position | 33 |
| A^∀,χ_n | Universal Levenshtein automaton | 30 |
| h_n(w, x) | Bit vector encoding of word pair | 51 |
| β(x, w) | Characteristic vector | 17 |
| ≤^χ_s | Subsumption relation | 18 |
| ⊔A | Subsumption closure | 21 |

---

## Notation by Category

### 1. Metasymbols and Variants

#### χ (Chi) - Distance Variant Metasymbol
**Definition**: χ ∈ {ε, t, ms}
- **χ = ε** (or χ = ²): Standard Levenshtein distance
- **χ = t**: Levenshtein distance with transposition
- **χ = ms**: Levenshtein distance with merge and split

**Usage**: Throughout the thesis as a placeholder for any of the three variants

**Example**: d^χ_L means d²_L, d^t_L, or d^ms_L depending on context

---

### 2. Distance Functions

#### d²_L : Σ* × Σ* → ℕ
**Standard Levenshtein Distance** (Page 3)

Minimum cost to transform v into w using:
- Deletion (cost 1)
- Insertion (cost 1)
- Substitution (cost 1)

**Properties**:
- d²_L(v, w) = 0 ⇔ v = w
- d²_L(v, w) = d²_L(w, v) (symmetric)

#### d^t_L : Σ* × Σ* → ℕ
**Levenshtein Distance with Transposition** (Page 4)

Standard operations plus:
- Transposition of adjacent characters (cost 1)

**⚠️ WARNING**: Does NOT satisfy triangle inequality!
- Not a proper metric
- Example: d^t_L(abcd, abdc) + d^t_L(abdc, bdac) < d^t_L(abcd, bdac)

#### d^ms_L : Σ* × Σ* → ℕ
**Levenshtein Distance with Merge/Split** (Page 5)

Standard operations plus:
- Merge: Two characters → one character (cost 1)
- Split: One character → two characters (cost 1)

#### d^χ_L : Σ* × Σ* → ℕ
**Generic notation** for any of the above three distances

---

### 3. Language and Sets

#### L^χ_Lev(n, w) : 𝒫(Σ*)
**Levenshtein Language** (Page 6)

```
L^χ_Lev(n, w) = {v | d^χ_L(v, w) ≤ n}
```

The set of all words within distance n from w.

#### R^χ(n, w) : 𝒫(Σ*)
**Extension Function** (Page 7)

Recursive decomposition of L^χ_Lev(n, w):
- For χ = ε: Includes insertion, deletion, substitution, match terms
- For χ = t: Adds transposition term
- For χ = ms: Adds merge and split terms

**Key Property**: L^χ_Lev(n, w) = R^χ(n, w)

---

### 4. Position Notation (Fixed-Word)

#### i#e
**Standard Position** (Page 9)

Compact notation for ⟨⟨i, 0⟩, e⟩

- **i**: Position in word w (0 ≤ i ≤ |w|)
- **e**: Error count consumed (0 ≤ e ≤ n)

**Language**: L(i#e) = L^χ_Lev(n - e, w_{i+1}...w_p)

#### i#e_t
**Transposition Position** (Page 10)

Compact notation for ⟨⟨i, 1⟩, e⟩

Used when detecting transposition of w_{i+1} and w_{i+2}

#### i#e_s
**Merge/Split Position** (Page 10)

Compact notation for ⟨⟨i, 2⟩, e⟩

Used when processing merge or split operations

---

### 5. Position Notation (Universal)

#### I + i#e
**Universal Non-Final Standard Position** (Page 29)

Compact notation for ⟨⟨λI.I+i, 0⟩, e⟩

- **I**: Parameter (to be substituted with 0 for word start)
- **i**: Relative offset (-n ≤ i ≤ n)
- **e**: Error count (0 ≤ e ≤ n)

**Constraint**: |i| ≤ e

#### It + i#e
**Universal Non-Final Transposition Position** (Page 31)

Compact notation for ⟨⟨λI.I+i, 1⟩, e⟩

#### Is + i#e
**Universal Non-Final Split Position** (Page 32)

Compact notation for ⟨⟨λI.I+i, 2⟩, e⟩

#### M + i#e
**Universal Final Standard Position** (Page 33)

Compact notation for ⟨⟨λM.M+i, 3⟩, e⟩

- **M**: Parameter (to be substituted with |w| for word end)
- **i**: Relative offset (-2n ≤ i ≤ 0)
- **e**: Error count (0 ≤ e ≤ n)

**Constraint**: e ≥ -i - n

#### Mt + i#e
**Universal Final Transposition Position** (Page 34)

Compact notation for ⟨⟨λM.M+i, 4⟩, e⟩

#### Ms + i#e
**Universal Final Split Position** (Page 35)

Compact notation for ⟨⟨λM.M+i, 5⟩, e⟩

---

### 6. Automata

#### A^ND,χ_n(w)
**Nondeterministic Levenshtein Automaton** (Page 9)

```
A^ND,χ_n(w) = ⟨Σ, Q^ND,χ_n, I^ND,χ, F^ND,χ_n*, δ^ND,χ_n⟩
```

- **Alphabet**: Σ ∪ {ε}
- **States**: Positions i#e (and i#e_t, i#e_s for t, ms)
- **Language**: L^χ_Lev(n, w)

#### A^D,χ_n(w)
**Deterministic Levenshtein Automaton** (Page 23)

```
A^D,χ_n(w) = ⟨Σ, Q^D,χ_n, I^D,χ, F^D,χ_n, δ^D,χ_n⟩
```

- **Alphabet**: Σ
- **States**: Sets of positions (anti-chains under subsumption)
- **Language**: L^χ_Lev(n, w)

#### A^∀,χ_n
**Universal Levenshtein Automaton** (Page 30)

```
A^∀,χ_n = ⟨Σ^∀_n, Q^∀,χ_n, I^∀,χ, F^∀,χ_n, δ^∀,χ_n⟩
```

- **Alphabet**: Σ^∀_n = {x ∈ {0,1}⁺ | |x| ≤ 2n + 2}
- **States**: Sets of universal positions
- **Language**: {h_n(w, x) | d^χ_L(w, x) ≤ n}

---

### 7. State Sets

#### Q^ND,χ_n
**NFA State Set** (Page 9)

For χ = ε: {i#e | 0 ≤ i ≤ p ∧ 0 ≤ e ≤ n}

Plus transposition/split states for t, ms variants.

#### Q^D,χ_n
**DFA State Set** (Page 23)

Sets of positions that are:
1. Anti-chains under ≤^χ_s (no position subsumes another)
2. Have a common base position

#### I^χ_s
**Universal Non-Final Position Set** (Page 30-32)

All valid I-type positions for variant χ.

For χ = ε: {I + t#k | |t| ≤ k ∧ -n ≤ t ≤ n ∧ 0 ≤ k ≤ n}

#### M^χ_s
**Universal Final Position Set** (Page 33-35)

All valid M-type positions for variant χ.

For χ = ε: {M + t#k | k ≥ -t - n ∧ -2n ≤ t ≤ 0 ∧ 0 ≤ k ≤ n}

#### I^χ_states
**Universal Non-Final States** (Page 38)

```
I^χ_states = {Q | Q ⊆ I^χ_s ∧ ∀q₁,q₂ ∈ Q (q₁ ⊀^χ_s q₂)} \ {∅}
```

Anti-chains of non-final positions.

#### M^χ_states
**Universal Final States** (Page 38)

```
M^χ_states = {Q | Q ⊆ M^χ_s ∧ anti-chain ∧ valid constraints} \ {∅}
```

Anti-chains of final positions with additional constraints.

---

### 8. Transition Functions

#### δ^ND,χ_n : Q^ND,χ_n × (Σ ∪ {ε}) → 𝒫(Q^ND,χ_n)
**NFA Transition** (Page 9-10)

Standard NFA transitions with ε-transitions for insertions.

#### δ^ND,χ_n* : Q^ND,χ_n × Σ* → 𝒫(Q^ND,χ_n)
**Extended NFA Transition** (Page 11)

Handles sequences with ε-closure.

#### δ^D,χ_e : Q^ND,χ × {0,1}* → 𝒫(Q^ND,χ)
**Elementary Transition Function** (Page 14-16)

Given position and bit vector, compute reachable positions.

#### δ^D,χ_n : Q^D,χ_n × Σ → Q^D,χ_n
**DFA Transition** (Page 23)

```
δ^D,χ_n(M, x) = ⊔_{π∈M} δ^D,χ_e(π, x)
```

Apply elementary transitions and subsumption closure.

#### δ^∀,χ_e : (I^χ_s ∪ M^χ_s) × Σ^∀_n → 𝒫(I^χ_s ∪ M^χ_s)
**Universal Elementary Transition** (Page 46)

Extract relevant subvector, apply δ^D,χ_e, convert back to universal positions.

#### δ^∀,χ_n : Q^∀,χ_n × Σ^∀_n → Q^∀,χ_n
**Universal Transition** (Page 48)

```
δ^∀,χ_n(Q, x) = {
    Δ           if f_n(rm(Δ), |x|) = false
    m_n(Δ, |x|) if f_n(rm(Δ), |x|) = true
}
where Δ = ⊔_{q∈Q} δ^∀,χ_e(q, x)
```

Includes diagonal crossing check and I/M conversion.

---

### 9. Helper Functions

#### w[π] : Relevant Subword
**Definition** (Page 17): For position π = i#e, returns w_{i+1}...w_{i+k} where k = min(n - e + 1, p - i)

#### β(x, w) : Characteristic Vector
**Definition** (Page 17): β : Σ × Σ* → {0,1}*

```
β(x, w₁w₂...w_p) = b₁b₂...b_p where b_i = (1 if x = w_i else 0)
```

**Example**: β('a', "banana") = "101010"

#### s_n(w, i) : Relevant Subword for Position
**Definition** (Page 51): Returns window around position i

```
s_n(w, i) = w_{i-n}...w_{min(|w|, i+n+1)}
```

With padding: w_{-n+1} = ... = w_0 = $

#### h_n(w, x) : Bit Vector Encoding
**Definition** (Page 51): Encodes word pair (w, x) as bit vector sequence

```
h_n(w, x₁...x_t) = β(x₁, s_n(w,1))...β(x_t, s_n(w,t))
```

**Key Property**: x ∈ L^χ_Lev(n, w) ⇔ h_n(w, x) ∈ L(A^∀,χ_n)

#### r_n : Relevant Subvector
**Definition** (Page 39): Extracts relevant portion of bit vector for a universal position

For I + i#e: Extract from position (n + i + 1)
For M + i#e: Extract from position (k + i + 1) where k = |input|

#### m_n : I/M Conversion
**Definition** (Page 42): Converts between non-final and final positions

```
m_n(I + i#e, k) = M + (i + n + 1 - k)#e
m_n(M + i#e, k) = I + (i - n - 1 + k)#e
```

#### f_n : Diagonal Check
**Definition** (Page 43): Checks if position crossed diagonal

For I + i#e: f_n(S, k) = true if k ≤ 2n + 1 ∧ e ≤ i + 2n + 1 - k
For M + i#e: f_n(S, k) = true if e > i + n

#### rm : Right-Most Element
**Definition** (Page 45): Returns position with maximum (e - i) in a state

```
rm(A) = position with max(e - i)
```

#### ▽_a : Allowed Lengths
**Definition** (Page 47): Returns valid input lengths for a state

For {I#0}: {k | n ≤ k ≤ 2n + 2}
For other states: Computed based on right-most element

---

### 10. Subsumption Relations

#### ≤^χ_s : Subsumption Relation
**Definition** (Page 18-19): Partial order on positions

**For χ = ε**:
```
i#e ≤^ε_s j#f ⇔ f > e ∧ |j - i| ≤ f - e
```

**Intuition**: Position j#f subsumes i#e if j#f has enough extra errors to "cover" the position difference.

**For universal positions** (Page 36-37):
```
I + i#e ≤^χ_s I + j#f ⇔ i#e ≤^χ_s j#f
M + i#e ≤^χ_s M + j#f ⇔ i#e ≤^χ_s j#f
```

**Properties**:
- Reflexive: π ≤^χ_s π
- Antisymmetric: π₁ ≤^χ_s π₂ ∧ π₂ ≤^χ_s π₁ ⇒ π₁ = π₂
- Transitive: π₁ ≤^χ_s π₂ ∧ π₂ ≤^χ_s π₃ ⇒ π₁ ≤^χ_s π₃

#### <^χ_s : Strict Subsumption
**Definition**: π₁ <^χ_s π₂ ⇔ π₁ ≤^χ_s π₂ ∧ π₁ ≠ π₂

#### ⊔A : Subsumption Closure
**Definition** (Page 21, 47): Removes subsumed elements

```
⊔A = {π | π ∈ ⋃A ∧ ¬∃π' ∈ ⋃A (π' <^χ_s π)}
```

Returns maximal elements (anti-chain).

---

### 11. Conversion Functions

#### I^χ : 𝒫(Q^ND,χ) → 𝒫(P^χ)
**Concrete to Universal (Non-Final)** (Page 44)

```
I^ε(A) = {I + (i - 1)#e | i#e ∈ A}
```

Shifts positions by -1 and adds I parameter.

#### M^χ : 𝒫(Q^ND,χ) → 𝒫(P^χ)
**Concrete to Universal (Final)** (Page 44)

```
M^ε(A) = {M + i#e | i#e ∈ A}
```

Adds M parameter without shift.

#### d : (I^χ_s ∪ M^χ_s) × ℕ → Q^ND,χ
**Universal to Concrete** (Page 52)

```
d(I + i#e, z) = (z + i)#e
d(M + i#e, z) = (z + i)#e
```

Substitutes parameter (I or M) with concrete value z.

---

### 12. Special Notation

#### ↪ : Suffix Operator
**Definition** (Page 4): x₁...xₖ ↪ t removes first t characters

```
x₁...xₖ ↪ t = {
    ε                if t ≥ k
    x_{t+1}...xₖ    otherwise
}
```

#### < : Prefix Relation
**Definition** (Page 4): c < d means c is a prefix of d

#### μz[A] : Minimum
**Definition** (Page 14): The least z such that property A holds

#### ! : Definedness
**Definition**: !x means x is defined (not ¬!)

#### ¬! : Undefinedness
**Definition**: ¬!x means x is undefined

#### def= : Definition
**Definition**: x def= y means x is defined to equal y

---

### 13. Set Notation

#### Σ
**Alphabet**: Finite set of symbols

#### Σ*
**All words**: Set of all finite sequences over Σ (including empty word ε)

#### Σ⁺
**Non-empty words**: Σ* \ {ε}

#### ε
**Empty word**: Word of length 0

#### |w|
**Word length**: Number of characters in w

#### 𝒫(A)
**Power set**: Set of all subsets of A

#### ℕ
**Natural numbers**: {0, 1, 2, ...}

#### ℕ⁺
**Positive integers**: {1, 2, 3, ...}

#### ℤ
**Integers**: {..., -2, -1, 0, 1, 2, ...}

---

### 14. Automaton Components

#### Q
**States**: Set of states

#### I
**Initial state**: Starting state (usually {0#0} or {I#0})

#### F
**Final states**: Accepting states

#### δ
**Transition function**: Maps (state, symbol) to states

#### L(A)
**Language of automaton**: Set of words accepted by A

#### L(π)
**Language of state**: Set of words accepted starting from state π

---

### 15. Complexity Notation

#### O(f(n))
**Big-O**: Upper bound on growth rate

**Examples in thesis**:
- States: O(n²)
- Construction: O(n² · 2^{2n})

---

## Cross-Reference by Section

### Section 1: Introduction
- d^t_L triangle inequality violation warning

### Section 2: Distance Definitions (Pages 3-8)
- d²_L, d^t_L, d^ms_L
- ↪, <, L^χ_Lev, R^χ

### Section 3: Nondeterministic Automata (Pages 8-13)
- i#e, i#e_t, i#e_s
- A^ND,χ_n(w), δ^ND,χ_n, Clε

### Section 4: Deterministic Automata (Pages 13-28)
- δ^D,χ_e, β, w[π]
- ≤^χ_s, ⊔, A^D,χ_n(w)

### Section 5: Universal Automata (Pages 28-48)
- I + i#e, M + i#e, It, Is, Mt, Ms
- A^∀,χ_n, r_n, m_n, f_n, rm, ▽_a
- h_n, s_n, I^χ, M^χ, d

### Section 6: Building (Pages 48-59)
- Construction algorithms (see ALGORITHMS.md)

### Section 7: Minimality (Pages 59-72)
- Proofs using subsumption properties

### Section 8: Properties (Pages 72-77)
- Additional theorems and properties

---

## Usage Tips

### For Reading the Paper
1. Start with χ = ε (standard) before tackling transposition/merge-split
2. Understand fixed-word automata (Sections 3-4) before universal (Section 5)
3. Remember: d^t_L violates triangle inequality (affects subsumption logic)
4. Universal positions use parameters (I, M) that get substituted with concrete values (0, |w|)

### For Implementation
1. Implement subsumption (≤^χ_s, ⊔) correctly - critical for correctness
2. Bit vector encoding (β, h_n) must be efficient
3. Diagonal crossing (f_n, m_n) handles I/M conversion
4. Test against fixed-word automata for validation

### For Debugging
1. Check subsumption closure: No position should subsume another in a state
2. Verify diagonal crossing: f_n determines when to apply m_n
3. Validate bit vectors: h_n encoding must match characteristic vectors
4. Compare with fixed-word: Use Proposition 19 correspondence

---

## Common Confusions

### 1. Position Notation
**Fixed**: i#e (concrete position i in specific word w)
**Universal**: I + i#e (parametric, i is offset from I)

### 2. I vs M
**I-type**: Non-final states (before reaching end of word)
**M-type**: Final states (at or past end of word)

Conversion happens when crossing diagonal (detected by f_n).

### 3. Subsumption Direction
i#e ≤^χ_s j#f means j#f **subsumes** i#e (j#f recognizes more words)

In state sets, we keep only maximal elements (not subsumed by others).

### 4. Bit Vector Encoding
h_n(w, x) produces a **sequence** of bit vectors (one per character of x)
Each bit vector encodes matches with a window around that position in w

### 5. Triangle Inequality
Only d^t_L violates it! d²_L and d^ms_L may satisfy it (not proven in thesis).

---

## Quick Lookup Table

| To find... | Look for... |
|------------|-------------|
| Distance definition | Section 2, d^χ_L |
| Fixed-word position | Section 3, i#e |
| Universal position | Section 5, I + i#e, M + i#e |
| Subsumption | Section 4, ≤^χ_s |
| Bit encoding | Section 5, h_n, β |
| Conversion I↔M | Section 5, m_n |
| Diagonal check | Section 5, f_n |
| Transition function | δ^ND,χ_n, δ^D,χ_n, δ^∀,χ_n |
| Construction algorithm | Section 6, Build_Automaton |
| Correctness proof | Section 5, Proposition 19 |
| Minimality proof | Section 7 |

---

**End of Glossary**

**Last Updated**: 2025-11-11
**Notation Count**: 50+ symbols and functions
**Cross-referenced**: All sections covered
