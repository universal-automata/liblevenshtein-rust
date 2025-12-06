# Data Flow Through the Correction Stack

This document describes the complete data flow through the three-tier correction
WFST architecture, from input to ranked corrections.

**Sources**:
- liblevenshtein: `/home/dylon/Workspace/f1r3fly.io/liblevenshtein-rust/`
- MORK: `/home/dylon/Workspace/f1r3fly.io/MORK/`
- MeTTaTron: `/home/dylon/Workspace/f1r3fly.io/MeTTa-Compiler/`

---

## Table of Contents

1. [Overview](#overview)
2. [Input Processing](#input-processing)
3. [Tier 1 to Tier 2 Transition](#tier-1-to-tier-2-transition)
4. [Tier 2 to Tier 3 Transition](#tier-2-to-tier-3-transition)
5. [Weight Composition](#weight-composition)
6. [Output Ranking](#output-ranking)
7. [End-to-End Example](#end-to-end-example)

---

## Overview

Data flows through the correction stack with progressive refinement:

```
┌─────────────────────────────────────────────────────────────────┐
│                    Complete Data Flow                            │
├─────────────────────────────────────────────────────────────────┤
│                                                                  │
│  INPUT                                                          │
│  ┌─────────────────────────────────────────────────────────────┐│
│  │  Raw input (text, phonemes, code)                           ││
│  │  Context (surrounding text, AST location, type environment) ││
│  └──────────────────────────┬──────────────────────────────────┘│
│                             │                                    │
│                             ▼                                    │
│  TIER 1: LEXICAL           ─────────────────────────────────────│
│  ┌─────────────────────────────────────────────────────────────┐│
│  │  Input:  Error token + context window                       ││
│  │  Output: CandidateLattice<Tropical>                         ││
│  │  Data:   [(candidate, edit_distance), ...]                  ││
│  │  Size:   ~100-1000 candidates                               ││
│  └──────────────────────────┬──────────────────────────────────┘│
│                             │                                    │
│                             ▼                                    │
│  TIER 2: SYNTACTIC         ─────────────────────────────────────│
│  ┌─────────────────────────────────────────────────────────────┐│
│  │  Input:  CandidateLattice + Grammar                         ││
│  │  Output: FilteredLattice<Tropical>                          ││
│  │  Data:   [(candidate, edit_dist * parse_prob), ...]         ││
│  │  Size:   ~10-100 candidates                                  ││
│  └──────────────────────────┬──────────────────────────────────┘│
│                             │                                    │
│                             ▼                                    │
│  TIER 3: SEMANTIC          ─────────────────────────────────────│
│  ┌─────────────────────────────────────────────────────────────┐│
│  │  Input:  FilteredLattice + Type Environment                 ││
│  │  Output: TypedCorrections                                   ││
│  │  Data:   [(candidate, combined_score, type_info), ...]      ││
│  │  Size:   ~1-10 candidates                                    ││
│  └──────────────────────────┬──────────────────────────────────┘│
│                             │                                    │
│                             ▼                                    │
│  OUTPUT                                                          │
│  ┌─────────────────────────────────────────────────────────────┐│
│  │  Ranked corrections with confidence scores                   ││
│  │  Type information and error explanations                     ││
│  └─────────────────────────────────────────────────────────────┘│
│                                                                  │
└─────────────────────────────────────────────────────────────────┘
```

---

## Input Processing

### Written Text

```rust
/// Process written text input
pub fn process_written_text(
    text: &str,
    error_span: Range<usize>,
    context: &TextContext,
) -> CorrectionInput {
    // Extract error token
    let error_token = &text[error_span.clone()];

    // Extract context window (e.g., ±5 tokens)
    let context_window = context.window_around(error_span, 5);

    CorrectionInput {
        error_token: error_token.to_string(),
        context_window,
        input_type: InputType::Written,
    }
}
```

### Spoken Language (ASR)

```rust
/// Process ASR lattice input
pub fn process_asr_lattice(
    phoneme_lattice: &PhonemeLattice,
    context: &SpeechContext,
) -> CorrectionInput {
    // Convert phoneme lattice to character candidates
    let char_candidates = phoneme_lattice
        .best_paths(10)
        .map(|path| phonemes_to_text(&path))
        .collect();

    CorrectionInput {
        candidates: char_candidates,
        context_window: context.surrounding_utterances(),
        input_type: InputType::Spoken,
    }
}
```

### Programming Language Code

```rust
/// Process code with syntax errors
pub fn process_code_error(
    code: &str,
    error: &SyntaxError,
    ast: &PartialAst,
) -> CorrectionInput {
    // Extract error region
    let error_span = error.span();
    let error_token = &code[error_span.clone()];

    // Get AST context
    let ast_context = ast.context_at(error_span.start);

    // Get type environment at error location
    let type_env = ast.type_environment_at(error_span.start);

    CorrectionInput {
        error_token: error_token.to_string(),
        ast_context,
        type_env,
        input_type: InputType::Code,
    }
}
```

---

## Tier 1 to Tier 2 Transition

### Lattice Structure

```rust
/// Candidate lattice produced by Tier 1
pub struct CandidateLattice<W: Semiring> {
    /// Entry node (before error)
    entry: NodeId,
    /// Exit node (after error)
    exit: NodeId,
    /// Candidate edges
    edges: Vec<LatticeEdge<W>>,
}

/// Edge in the lattice
pub struct LatticeEdge<W: Semiring> {
    pub from: NodeId,
    pub to: NodeId,
    pub candidate: Vec<u8>,
    pub weight: W,
    /// Source of candidate (edit distance, phonetic, etc.)
    pub source: CandidateSource,
}
```

### Transition Processing

```rust
/// Transition from Tier 1 to Tier 2
pub fn tier1_to_tier2<W: Semiring>(
    input: &CorrectionInput,
    config: &Tier1Config,
) -> CandidateLattice<W> {
    // Step 1: Generate edit distance candidates
    let edit_candidates = generate_edit_candidates(
        &input.error_token,
        &config.dictionary,
        config.max_distance,
    );

    // Step 2: Generate phonetic candidates
    let phonetic_candidates = generate_phonetic_candidates(
        &input.error_token,
        &config.phonetic_rules,
    );

    // Step 3: Merge and deduplicate
    let all_candidates = merge_candidates(
        edit_candidates,
        phonetic_candidates,
        &config.merge_strategy,
    );

    // Step 4: Build lattice
    build_lattice(all_candidates)
}

/// Generate candidates via edit distance
fn generate_edit_candidates<W: Semiring>(
    query: &str,
    dictionary: &impl FuzzySource,
    max_distance: u8,
) -> Vec<(Vec<u8>, W)> {
    dictionary.fuzzy_lookup(query.as_bytes(), max_distance)
        .map(|(candidate, distance)| {
            let weight = W::from_f64(distance as f64);
            (candidate, weight)
        })
        .collect()
}
```

### Data Format

```
Tier 1 Output Format:
{
  "lattice": {
    "entry": 0,
    "exit": 1,
    "edges": [
      {"from": 0, "to": 1, "candidate": "the", "weight": 1.0, "source": "edit"},
      {"from": 0, "to": 1, "candidate": "tea", "weight": 1.0, "source": "edit"},
      {"from": 0, "to": 1, "candidate": "tee", "weight": 2.0, "source": "edit"},
      {"from": 0, "to": 1, "candidate": "tea", "weight": 0.5, "source": "phonetic"},
      ...
    ]
  },
  "context": {
    "before": ["was", "sitting", "on"],
    "after": ["mat"]
  }
}
```

---

## Tier 2 to Tier 3 Transition

### Grammar Filtering

```rust
/// Transition from Tier 2 to Tier 3
pub fn tier2_to_tier3<W: Semiring>(
    lattice: &CandidateLattice<W>,
    grammar: &Grammar,
    context: &SyntaxContext,
) -> FilteredLattice<W> {
    // Step 1: Parse lattice against grammar
    let parse_results = lattice_parser.parse(lattice, grammar)?;

    // Step 2: Filter invalid parses
    let valid_edges: Vec<_> = lattice.edges()
        .filter(|edge| parse_results.is_valid(&edge.candidate))
        .map(|edge| {
            // Combine edit weight with parse probability
            let parse_prob = parse_results.probability(&edge.candidate);
            let combined = edge.weight.mul(&W::from_f64(-parse_prob.ln()));
            LatticeEdge {
                weight: combined,
                ..edge.clone()
            }
        })
        .collect();

    // Step 3: Build filtered lattice with parse info
    FilteredLattice {
        lattice: CandidateLattice::from_edges(valid_edges),
        parse_trees: parse_results.trees,
        context: context.clone(),
    }
}
```

### Context-Aware Filtering

```rust
/// Filter based on syntactic context
fn filter_by_context(
    candidates: &[LatticeEdge<W>],
    context: &SyntaxContext,
    grammar: &Grammar,
) -> Vec<LatticeEdge<W>> {
    candidates.iter()
        .filter(|edge| {
            // Check if candidate is valid in context
            let expected_categories = grammar.expected_at(context.position());
            let candidate_categories = grammar.categories_of(&edge.candidate);

            candidate_categories.iter()
                .any(|cat| expected_categories.contains(cat))
        })
        .cloned()
        .collect()
}
```

### Data Format

```
Tier 2 Output Format:
{
  "filtered_lattice": {
    "entry": 0,
    "exit": 1,
    "edges": [
      {
        "from": 0,
        "to": 1,
        "candidate": "the",
        "weight": 1.5,  // edit_dist + parse_weight
        "parse_category": "Det"
      },
      {
        "from": 0,
        "to": 1,
        "candidate": "tea",
        "weight": 2.0,
        "parse_category": "N"
      }
    ]
  },
  "parse_context": {
    "expected": ["Det", "N"],
    "position": "NP head"
  }
}
```

---

## Tier 2 to Tier 3 Transition

### Type Checking Pipeline

```rust
/// Transition from Tier 2 to Tier 3
pub fn tier2_to_tier3_semantic<W: Semiring>(
    filtered: &FilteredLattice<W>,
    type_env: &TypeEnvironment,
    checker: &TypeChecker,
) -> TypedCorrections<W> {
    let mut typed_corrections = Vec::new();

    for edge in filtered.lattice.edges() {
        // Convert to MeTTa term for type checking
        let term = bytes_to_metta_term(&edge.candidate)?;

        // Check against expected type from context
        let expected_type = type_env.expected_at(filtered.context.position);

        match checker.check_type(&term, &expected_type) {
            Ok(type_result) => {
                // Combine weights
                let type_weight = W::from_f64(type_result.confidence);
                let combined = edge.weight.mul(&type_weight);

                typed_corrections.push(TypedCorrection {
                    candidate: edge.candidate.clone(),
                    weight: combined,
                    inferred_type: type_result.inferred_type,
                    behavioral_properties: type_result.properties,
                });
            }
            Err(type_error) => {
                // Optionally store error for diagnostics
                continue;
            }
        }
    }

    TypedCorrections { corrections: typed_corrections }
}
```

---

## Weight Composition

### Semiring Composition

```rust
/// Compose weights from all tiers
pub fn compose_weights<W: Semiring>(
    tier1_weight: W,  // Edit distance
    tier2_weight: W,  // Parse probability
    tier3_weight: W,  // Type confidence
    config: &WeightConfig,
) -> W {
    // Apply tier-specific scaling
    let w1 = tier1_weight.scale(config.lexical_scale);
    let w2 = tier2_weight.scale(config.syntactic_scale);
    let w3 = tier3_weight.scale(config.semantic_scale);

    // Compose: in tropical semiring, this is addition
    w1.mul(&w2).mul(&w3)
}
```

### Weight Configuration

```rust
/// Configuration for weight composition
pub struct WeightConfig {
    /// Scale for lexical (edit distance) weights
    pub lexical_scale: f64,
    /// Scale for syntactic (parse) weights
    pub syntactic_scale: f64,
    /// Scale for semantic (type) weights
    pub semantic_scale: f64,
    /// Normalization method
    pub normalization: Normalization,
}

impl Default for WeightConfig {
    fn default() -> Self {
        Self {
            lexical_scale: 1.0,
            syntactic_scale: 0.5,  // Parse probs often very small
            semantic_scale: 0.3,
            normalization: Normalization::LogSpace,
        }
    }
}
```

---

## Output Ranking

### Final Ranking Algorithm

```rust
/// Produce ranked corrections from typed candidates
pub fn rank_corrections<W: Semiring + Ord>(
    typed: &TypedCorrections<W>,
    config: &RankingConfig,
) -> Vec<RankedCorrection> {
    let mut ranked: Vec<_> = typed.corrections.iter()
        .map(|tc| {
            let score = compute_final_score(&tc.weight, config);
            RankedCorrection {
                correction: String::from_utf8_lossy(&tc.candidate).to_string(),
                score,
                type_info: tc.inferred_type.clone(),
                properties: tc.behavioral_properties.clone(),
            }
        })
        .collect();

    // Sort by score (lower is better in tropical semiring)
    ranked.sort_by(|a, b| a.score.partial_cmp(&b.score).unwrap());

    // Return top-k
    ranked.truncate(config.top_k);
    ranked
}

/// Compute final score with all adjustments
fn compute_final_score<W: Semiring>(weight: &W, config: &RankingConfig) -> f64 {
    let mut score = weight.to_f64();

    // Apply length penalty
    score += config.length_penalty * (1.0 / (1.0 + score));

    // Apply diversity bonus (if similar to previous suggestions)
    // ...

    score
}
```

### Output Format

```rust
/// Final correction output
pub struct RankedCorrection {
    /// The corrected text
    pub correction: String,
    /// Combined score (lower = better)
    pub score: f64,
    /// Inferred type information
    pub type_info: Option<Type>,
    /// Verified behavioral properties
    pub properties: Vec<BehavioralProperty>,
}

/// Behavioral property verified by type checker
pub enum BehavioralProperty {
    Terminates,
    Safe,
    NamespaceIsolated(String),
    Bisimilar(String),
}
```

---

## End-to-End Example

### Example: Code Correction

```rust
// Input: "let x: Int = teh_value;"
//                      ^^^^^^^^^ error

// Tier 1: Lexical candidates
let tier1_candidates = [
    ("the_value", 1),   // edit distance 1
    ("new_value", 2),   // edit distance 2
    ("tea_value", 1),   // edit distance 1
    ("ten_value", 1),   // edit distance 1
    // ... ~50 more candidates
];

// Tier 2: Syntactic filtering
let tier2_candidates = [
    ("the_value", 1.0 + 0.1),   // valid identifier
    ("new_value", 2.0 + 0.2),   // valid identifier
    // tea_value, ten_value filtered if not in scope
    // ~10 candidates remain
];

// Tier 3: Semantic type checking
// Context: expecting Int type
let tier3_candidates = [
    ("the_value", 1.1, Type::Int, []),  // matches expected Int
    // new_value filtered: has type String
    // ~3 candidates remain
];

// Output
[
    RankedCorrection {
        correction: "the_value",
        score: 1.1,
        type_info: Some(Type::Int),
        properties: vec![],
    }
]
```

### Complete Pipeline Code

```rust
/// Complete correction pipeline
pub fn correct<W: Semiring + Ord>(
    input: &CorrectionInput,
    resources: &CorrectionResources,
    config: &CorrectionConfig,
) -> Result<Vec<RankedCorrection>, CorrectionError> {
    // Tier 1: Lexical
    let lexical_lattice = tier1_lexical(
        &input,
        &resources.dictionary,
        &config.tier1,
    )?;

    // Tier 2: Syntactic
    let syntactic_lattice = tier2_syntactic(
        &lexical_lattice,
        &resources.grammar,
        &input.syntax_context,
        &config.tier2,
    )?;

    // Tier 3: Semantic
    let typed_corrections = tier3_semantic(
        &syntactic_lattice,
        &resources.type_checker,
        &input.type_env,
        &config.tier3,
    )?;

    // Rank and return
    let ranked = rank_corrections(&typed_corrections, &config.ranking);

    Ok(ranked)
}
```

---

## Summary

The data flow through the correction stack:

1. **Input**: Raw text/phonemes/code + context
2. **Tier 1 → Tier 2**: Candidate lattice with edit distances
3. **Tier 2 → Tier 3**: Filtered lattice with parse weights
4. **Output**: Ranked corrections with combined scores

Key data structures:
- `CandidateLattice<W>`: Weighted graph of candidates
- `FilteredLattice<W>`: Syntactically valid subset
- `TypedCorrections<W>`: Semantically verified candidates
- `RankedCorrection`: Final output with score and type info

Weight composition uses semiring algebra for consistent propagation across tiers.

---

## References

- See [01-architecture-overview.md](./01-architecture-overview.md) for architecture
- See [02-tier1-lexical-correction.md](./02-tier1-lexical-correction.md) for Tier 1
- See [03-tier2-syntactic-validation.md](./03-tier2-syntactic-validation.md) for Tier 2
- See [04-tier3-semantic-type-checking.md](./04-tier3-semantic-type-checking.md) for Tier 3
- See [bibliography.md](../reference/bibliography.md) for complete references
