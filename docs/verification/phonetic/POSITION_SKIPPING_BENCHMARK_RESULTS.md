# Position Skipping Optimization: Benchmark Results

**Date**: 2025-11-30
**Optimization**: Conditional Position Skipping for Phonetic Rewrite Rules
**Formal Verification**: `docs/verification/phonetic/position_skipping_proof.v`

## Scientific Methodology

### Hypothesis

- **H₀ (Null)**: Position skipping provides no statistically significant performance improvement
- **H₁ (Alternative)**: Position skipping provides measurable performance improvement when rules don't use `Context::Final`

### Experimental Setup

- **CPU**: Intel Xeon E5-2699 v3 @ 2.30GHz (pinned to core 0 via `taskset -c 0`)
- **Compiler Flags**: `RUSTFLAGS="-C target-cpu=native"`
- **Statistical Method**: Criterion with 100 samples per test
- **Rule Set**: `phonetic_rules()` - computationally expensive rule set (no `Context::Final`)

## Results: `phonetic_position_skipping_comparison`

### Performance Comparison Table

| Input Size | Standard (apply_rules_seq) | Optimized (apply_rules_seq_opt) | Speedup |
|------------|---------------------------|--------------------------------|---------|
| 10 chars   | 156.47 ns                 | 164.85 ns                      | 0.95× (5% overhead) |
| 25 chars   | 730.79 µs                 | 178.92 µs                      | **4.08×** |
| 50 chars   | 2.43 ms                   | 1.24 ms                        | **1.96×** |
| 100 chars  | 8.72 ms                   | 1.31 ms                        | **6.65×** |
| 200 chars  | 29.29 ms                  | 2.25 ms                        | **13.0×** |
| 500 chars  | 173.54 ms                 | 6.51 ms                        | **26.6×** |

### Observations

1. **Small inputs (10 chars)**: Slight overhead (~5%) due to position tracking cost
2. **Medium inputs (25-50 chars)**: Significant speedups begin (2-4×)
3. **Large inputs (100+ chars)**: Dramatic speedups (6.6× to 26.6×)
4. **Speedup scaling**: Approximately O(n) speedup factor with input length

### Complexity Analysis

| Implementation | Time Complexity | Space Complexity |
|----------------|-----------------|------------------|
| Standard       | O(n² × r)       | O(n)             |
| Optimized      | O(n × r)        | O(n)             |

Where:
- `n` = input string length
- `r` = number of rules

The optimization eliminates redundant re-scanning from position 0 after each rule application.

## Hypothesis Verdict

**H₁ CONFIRMED**: Position skipping provides statistically significant performance improvement for inputs ≥25 characters when rules don't use `Context::Final`.

### Key Findings

1. **Break-even point**: ~15-20 characters (below this, overhead > benefit)
2. **Maximum observed speedup**: **26.6×** for 500-character inputs
3. **Speedup trend**: Linear growth with input size (confirming O(n) improvement)
4. **`auto_opt` behavior**: Correctly detects safe rules and applies optimization

## Formal Correctness Guarantee

The optimization is proven correct in Coq/Rocq:
- **Theorem**: `position_skipping_conditionally_safe` (`position_skipping_proof.v:1850`)
- **Precondition**: `¬ has_final_context(rules)` (no rules use `Context::Final`)
- **Guarantee**: `apply_rules_seq_opt(rules, s) = apply_rules_seq(rules, s)`

Counter-example for unsafe case (`position_skipping_proof.v:3424-3444`):
- Original: `[a,b,c]` (length 3), position 2 is NOT final
- After shortening: `[a,b]` (length 2), position 2 IS now final
- A rule with `Final` context might match at a position previously skipped

## Implementation Details

### API Functions

```rust
// Byte-level (u8)
pub fn apply_rules_seq(rules: &[RewriteRule], s: &[Phone], fuel: usize) -> Option<Vec<Phone>>;
pub fn apply_rules_seq_optimized(rules: &[RewriteRule], s: &[Phone], fuel: usize) -> Option<Vec<Phone>>;
#[deprecated] pub fn apply_rules_seq_opt(...);  // Now just calls apply_rules_seq
pub fn has_position_dependent_rules(rules: &[RewriteRule]) -> bool;

// Character-level (char)
pub fn apply_rules_seq_char(rules: &[RewriteRuleChar], s: &[PhoneChar], fuel: usize) -> Option<Vec<PhoneChar>>;
pub fn apply_rules_seq_optimized_char(rules: &[RewriteRuleChar], s: &[PhoneChar], fuel: usize) -> Option<Vec<PhoneChar>>;
#[deprecated] pub fn apply_rules_seq_opt_char(...);  // Now just calls apply_rules_seq_char
pub fn has_position_dependent_rules_char(rules: &[RewriteRuleChar]) -> bool;
```

### API Semantics

| Function | Behavior | Recommended Use |
|----------|----------|-----------------|
| `apply_rules_seq` | Standard implementation - starts search from position 0 after each rule application | **Default** - all typical workloads |
| `apply_rules_seq_optimized` | Position skipping - starts search from last match position (caller must verify no `Context::Final` rules) | **Opt-in** - long repetitive strings (100+ chars) |
| `apply_rules_seq_opt` | **Deprecated** - now delegates to `apply_rules_seq` | Migrate to `apply_rules_seq` |
| `has_position_dependent_rules` | Returns `true` if any rule uses `Context::Final` | Safety check before using optimized version |

## Files Modified

- `src/phonetic/types.rs`: Added `Context::is_position_dependent()` method
- `src/phonetic/application.rs`: Added optimized functions and safety check
- `src/phonetic/mod.rs`: Exported new API functions
- `benches/phonetic_position_skip_benchmark.rs`: Comparison benchmark suite

---

## Results: English Dictionary Word Benchmark (Session 2)

**Date**: 2025-11-30
**Purpose**: Validate optimization effectiveness on real-world English words

### Hypothesis

- **H₂ (Null)**: Position skipping provides no benefit for English dictionary words (avg 5 chars, below break-even)
- **H₃ (Alternative)**: Long words (15+ chars) or concatenated phrases show measurable improvement

### Experimental Setup

- **Data Source**: `/usr/share/dict/words` (system dictionary)
- **Word Categories**: Short (3-5 chars), Medium (6-10), Long (11-15), Very Long (16+)
- **Sample Sizes**: 100/100/50/25 words per category
- **Rules**: `phonetic_rules()` (same as synthetic benchmarks)

### Dictionary Words Results

| Category | Avg Length | Standard (µs) | Optimized (µs) | Speedup |
|----------|------------|---------------|----------------|---------|
| Short (3-5)   | 4 chars  | 9.04          | 9.13           | **0.99×** (1% overhead) |
| Medium (6-10) | 7 chars  | 14.53         | 14.92          | **0.97×** (3% overhead) |
| Long (11-15)  | 11 chars | 10.19         | 11.97          | **0.85×** (15% overhead) |
| Very Long (16+)| 16 chars| 7.21          | 7.43           | **0.97×** (3% overhead) |

### Compound Phrases Results

| Phrase Length | Standard (ns) | Optimized (ns) | Speedup |
|---------------|---------------|----------------|---------|
| 20 chars      | 292.60        | 302.28         | **0.97×** (3% overhead) |
| 25 chars      | 332.11        | 376.43         | **0.88×** (13% overhead) |
| 30 chars      | 463.31        | 487.07         | **0.95×** (5% overhead) |
| 40 chars      | 569.55        | 591.15         | **0.96×** (4% overhead) |
| 50 chars      | 577.57        | 616.48         | **0.94×** (6% overhead) |

### Hypothesis Verdict

**H₂ CONFIRMED**: Position skipping provides NO benefit for real English words.

The optimized version is consistently **slower** across all categories:
- Dictionary words: 1-15% overhead
- Compound phrases (20-50 chars): 3-13% overhead

### Critical Analysis: Why Synthetic vs Real Results Differ

| Factor | Synthetic Inputs | Real English Words |
|--------|------------------|-------------------|
| **Character distribution** | Repetitive (`"a".repeat(500)`) | Varied (natural language) |
| **Rule match density** | High (many patterns match) | Low (few patterns match) |
| **Position skip benefit** | Large (many positions skipped) | Minimal (few matches to skip past) |
| **Tracking overhead** | Amortized by large gains | Dominates (no gains to offset) |

### Key Insight

The position skipping optimization's O(n² × r) → O(n × r) improvement only manifests when:
1. Rules match **frequently** throughout the string
2. String length is **very long** (100+ chars) with repetitive patterns

For natural language text:
- Rules match infrequently
- The overhead of position tracking exceeds any benefit
- The standard implementation is faster

### Recommendation Update

Based on these findings, `apply_rules_seq_optimized` should:
1. **Skip optimization for strings < 100 chars** (natural language threshold)
2. **Consider rule match density**, not just rule safety
3. **Default to standard implementation** for dictionary lookups

---

## Conclusion

The position skipping optimization provides substantial performance improvements (up to 26.6×) **for synthetic repetitive strings** while maintaining formal correctness through Coq proofs.

**IMPORTANT**: For real English dictionary words and phrases (3-50 chars), the optimization provides **NO benefit** and introduces 1-15% overhead. The `apply_rules_seq_optimized` function should only be used for:
- Very long strings (100+ chars)
- Strings with high rule match density (repetitive patterns)
- Processing bulk text (documents, paragraphs)

For spell-checking individual words, use the standard `apply_rules_seq` function.

---

## API Recommendations (v0.8.0+)

Based on the benchmark results, the following API changes were made in v0.8.0:

### Summary

| Function | Status | When to Use |
|----------|--------|-------------|
| `apply_rules_seq` | **Recommended** | Default choice for all typical workloads |
| `apply_rules_seq_optimized` | **Opt-in** | Long repetitive strings (100+ chars) with high rule match density |
| `apply_rules_seq_opt` | **Deprecated** | Migrate to `apply_rules_seq` |

### Migration Guide

**Before (v0.7.x)**:
```rust
// Auto-detected optimization (could cause overhead for typical words)
let result = apply_rules_seq_opt(&rules, &input, fuel);
```

**After (v0.8.0+)**:
```rust
// Standard implementation (recommended for most use cases)
let result = apply_rules_seq(&rules, &input, fuel);

// OR: Explicit opt-in to optimization (for long repetitive strings only)
if !has_position_dependent_rules(&rules) && input.len() > 100 {
    let result = apply_rules_seq_optimized(&rules, &input, fuel);
}
```

### Decision Tree

```
Is input length > 100 chars?
├── NO → Use apply_rules_seq
└── YES → Does input have repetitive patterns with high rule match density?
          ├── NO → Use apply_rules_seq
          └── YES → Does rule set use Context::Final?
                    ├── YES → Use apply_rules_seq (optimization unsafe)
                    └── NO → Use apply_rules_seq_optimized (up to 26.6× speedup)
```

### Rationale

The position skipping optimization was originally auto-applied via `apply_rules_seq_opt` when deemed safe. However, benchmarks revealed:

1. **Synthetic repetitive strings**: Up to 26.6× speedup for 500-char inputs
2. **Real English words**: 1-15% **overhead** (no benefit, tracking cost dominates)

The auto-detection was based on rule safety (`Context::Final`), but this missed the crucial factor: **rule match density**. Natural language text has low match density, making the optimization counterproductive.

The new API design makes the standard implementation the default and requires explicit opt-in for the optimization, ensuring users only pay the tracking cost when they expect to benefit from it.
