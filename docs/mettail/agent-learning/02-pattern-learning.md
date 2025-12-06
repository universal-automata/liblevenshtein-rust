# Pattern Learning

## Overview

The pattern learning layer extracts recurring error patterns from user feedback, clusters
similar patterns, and generalizes them into reusable correction rules. This enables the
system to learn common mistakes and automatically correct them without requiring manual
rule creation.

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                    PATTERN LEARNING ARCHITECTURE                             │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                              │
│  FeedbackStore (PathMap)                                                     │
│  (Negative feedback: rejections, modifications)                              │
│      │                                                                       │
│      ▼                                                                       │
│  ┌───────────────────────────────────────────────────────────────────────┐  │
│  │                    PATTERN EXTRACTION                                  │  │
│  │  ┌─────────────────────────────────────────────────────────────────┐  │  │
│  │  │ Input: (original, proposed, user_modified)                      │  │  │
│  │  │                                                                 │  │  │
│  │  │  ┌──────────────┐  ┌──────────────┐  ┌──────────────┐          │  │  │
│  │  │  │ Token-Level  │  │ N-Gram       │  │ Phonetic     │          │  │  │
│  │  │  │ Extraction   │  │ Extraction   │  │ Extraction   │          │  │  │
│  │  │  │              │  │              │  │              │          │  │  │
│  │  │  │ "teh" → "the"│  │ "would of"   │  │ /ðɛr/ →     │          │  │  │
│  │  │  │              │  │  → "would    │  │  "their" or │          │  │  │
│  │  │  │              │  │      have"   │  │  "there"    │          │  │  │
│  │  │  └──────┬───────┘  └──────┬───────┘  └──────┬───────┘          │  │  │
│  │  │         │                 │                 │                   │  │  │
│  │  │         └─────────────────┼─────────────────┘                   │  │  │
│  │  │                           ▼                                     │  │  │
│  │  │              ┌─────────────────────────┐                       │  │  │
│  │  │              │   Candidate Patterns    │                       │  │  │
│  │  │              └────────────┬────────────┘                       │  │  │
│  │  └───────────────────────────┼─────────────────────────────────────┘  │  │
│  └──────────────────────────────┼────────────────────────────────────────┘  │
│                                 │                                           │
│                                 ▼                                           │
│  ┌───────────────────────────────────────────────────────────────────────┐  │
│  │                    PATTERN CLUSTERING                                  │  │
│  │  ┌─────────────────────────────────────────────────────────────────┐  │  │
│  │  │  ┌──────────────┐  ┌──────────────┐  ┌──────────────┐          │  │  │
│  │  │  │ Similarity   │  │ Frequency    │  │ Error Type   │          │  │  │
│  │  │  │ Grouping     │  │ Analysis     │  │ Classification│         │  │  │
│  │  │  │              │  │              │  │              │          │  │  │
│  │  │  │ Similar      │  │ Patterns     │  │ Typo vs      │          │  │  │
│  │  │  │ errors →     │  │ appearing    │  │ grammar vs   │          │  │  │
│  │  │  │ same cluster │  │ frequently   │  │ semantic     │          │  │  │
│  │  │  └──────┬───────┘  └──────┬───────┘  └──────┬───────┘          │  │  │
│  │  │         │                 │                 │                   │  │  │
│  │  │         └─────────────────┼─────────────────┘                   │  │  │
│  │  │                           ▼                                     │  │  │
│  │  │              ┌─────────────────────────┐                       │  │  │
│  │  │              │    Pattern Clusters     │                       │  │  │
│  │  │              └────────────┬────────────┘                       │  │  │
│  │  └───────────────────────────┼─────────────────────────────────────┘  │  │
│  └──────────────────────────────┼────────────────────────────────────────┘  │
│                                 │                                           │
│                                 ▼                                           │
│  ┌───────────────────────────────────────────────────────────────────────┐  │
│  │                    PATTERN GENERALIZATION                              │  │
│  │  ┌─────────────────────────────────────────────────────────────────┐  │  │
│  │  │  ┌──────────────┐  ┌──────────────┐  ┌──────────────┐          │  │  │
│  │  │  │ Abstraction  │  │ Rule         │  │ Confidence   │          │  │  │
│  │  │  │              │  │ Synthesis    │  │ Estimation   │          │  │  │
│  │  │  │              │  │              │  │              │          │  │  │
│  │  │  │ Find common  │  │ Generate     │  │ Calculate    │          │  │  │
│  │  │  │ structure    │  │ reusable     │  │ pattern      │          │  │  │
│  │  │  │ across       │  │ rules        │  │ reliability  │          │  │  │
│  │  │  │ instances    │  │              │  │              │          │  │  │
│  │  │  └──────┬───────┘  └──────┬───────┘  └──────┬───────┘          │  │  │
│  │  │         │                 │                 │                   │  │  │
│  │  │         └─────────────────┼─────────────────┘                   │  │  │
│  │  │                           ▼                                     │  │  │
│  │  │              ┌─────────────────────────┐                       │  │  │
│  │  │              │   Learned Patterns      │                       │  │  │
│  │  │              └────────────┬────────────┘                       │  │  │
│  │  └───────────────────────────┼─────────────────────────────────────┘  │  │
│  └──────────────────────────────┼────────────────────────────────────────┘  │
│                                 │                                           │
│                                 ▼                                           │
│  ┌───────────────────────────────────────────────────────────────────────┐  │
│  │                    PATTERN STORE (PathMap)                            │  │
│  └───────────────────────────────────────────────────────────────────────┘  │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
```

---

## Pattern Types

### 1. Token-Level Patterns

Token patterns capture word-to-word replacements:

| Type | Example | Pattern |
|------|---------|---------|
| **Typo** | "teh" → "the" | `TokenReplace("teh", "the")` |
| **Transposition** | "recieve" → "receive" | `TokenReplace("recieve", "receive")` |
| **Doubling** | "occured" → "occurred" | `TokenReplace("occured", "occurred")` |
| **Missing char** | "definately" → "definitely" | `TokenReplace("definately", "definitely")` |

### 2. N-Gram Patterns (Context-Sensitive)

N-gram patterns capture corrections that depend on surrounding context:

| Type | Context | Error | Correction |
|------|---------|-------|------------|
| **Homophone confusion** | "They went _" | "their" | "there" |
| **Grammar** | "would _" | "of" | "have" |
| **Agreement** | "The team _" | "are" | "is" |
| **Collocation** | "make a _" | "decide" | "decision" |

### 3. Phonetic Patterns

Phonetic patterns capture sound-based confusions:

| Sound | Variants | Example |
|-------|----------|---------|
| **/ðɛr/** | there, their, they're | "There going to the store" → "They're..." |
| **/tu/** | to, too, two | "I want too go" → "I want to go" |
| **/aɪt/** | -ight, -ite | "lite" → "light" |

### 4. Morphological Patterns

Morphological patterns capture systematic suffix/prefix errors:

| Pattern | Examples |
|---------|----------|
| **-tion/-sion confusion** | "extention" → "extension" |
| **-ible/-able confusion** | "accessable" → "accessible" |
| **-ment/-ness confusion** | "developness" → "development" |
| **un-/in- prefix** | "unresponsible" → "irresponsible" |

### 5. Regex Patterns

Regex patterns capture complex structural patterns:

```rust
// Double negatives
Regex { pattern: r"(can|could|would|should)n't\s+not", replacement: "$1n't" }

// Run-on sentences (simplified)
Regex { pattern: r"(\w)\s+,\s+(\w)", replacement: "$1, $2" }
```

---

## Core Data Structures

### Pattern Specification

```rust
/// Specification of an error pattern
#[derive(Clone, Debug, Serialize, Deserialize, PartialEq)]
pub enum PatternSpec {
    /// Exact token replacement
    TokenReplace {
        /// The error token
        error: String,
        /// The correction
        correction: String,
        /// Case sensitivity
        case_sensitive: bool,
    },

    /// Context-sensitive n-gram pattern
    NGram {
        /// Tokens that must appear before (empty = any)
        left_context: Vec<ContextMatcher>,
        /// The error token(s)
        error: Vec<String>,
        /// Tokens that must appear after (empty = any)
        right_context: Vec<ContextMatcher>,
        /// The correction
        correction: Vec<String>,
    },

    /// Phonetic similarity pattern
    Phonetic {
        /// Phonemes representing the sound
        phonemes: Vec<Phoneme>,
        /// Possible correct spellings
        corrections: Vec<(String, f64)>,  // (correction, base_probability)
        /// Context hints for disambiguation
        context_hints: Vec<ContextHint>,
    },

    /// Morphological pattern (suffix/prefix rules)
    Morphological {
        /// Error suffix/prefix pattern
        error_affix: AffixPattern,
        /// Correction suffix/prefix
        correction_affix: String,
        /// Part of speech constraint (if any)
        pos_constraint: Option<PartOfSpeech>,
    },

    /// Regular expression pattern
    Regex {
        /// Regex pattern to match
        pattern: String,
        /// Replacement string (can use capture groups)
        replacement: String,
        /// Maximum number of replacements per text
        max_replacements: Option<usize>,
    },
}

/// Context matcher for n-gram patterns
#[derive(Clone, Debug, Serialize, Deserialize, PartialEq)]
pub enum ContextMatcher {
    /// Exact token match
    Exact(String),
    /// Any of these tokens
    OneOf(Vec<String>),
    /// Any token (wildcard)
    Any,
    /// Beginning of sentence
    StartOfSentence,
    /// End of sentence
    EndOfSentence,
    /// Part of speech constraint
    POS(PartOfSpeech),
}

/// Context hint for phonetic disambiguation
#[derive(Clone, Debug, Serialize, Deserialize, PartialEq)]
pub struct ContextHint {
    /// Words that suggest this correction
    indicator_words: Vec<String>,
    /// The correction this hint suggests
    suggested_correction: String,
    /// Confidence boost when hint matches
    confidence_boost: f64,
}

/// Affix pattern for morphological rules
#[derive(Clone, Debug, Serialize, Deserialize, PartialEq)]
pub struct AffixPattern {
    /// Prefix pattern (if any)
    prefix: Option<String>,
    /// Suffix pattern (if any)
    suffix: Option<String>,
    /// Minimum stem length
    min_stem_length: usize,
}
```

### Learned Pattern

```rust
/// A learned pattern with statistics
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct LearnedPattern {
    /// Unique pattern identifier
    pub pattern_id: PatternId,

    /// The pattern specification
    pub spec: PatternSpec,

    /// Learning statistics
    pub stats: PatternStats,

    /// Confidence score (0.0 to 1.0)
    pub confidence: f64,

    /// When the pattern was created
    pub created_at: Timestamp,

    /// When the pattern was last updated
    pub updated_at: Timestamp,

    /// Source of the pattern
    pub source: PatternSource,

    /// User scope (user-specific or global)
    pub scope: PatternScope,
}

/// Pattern learning statistics
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct PatternStats {
    /// Number of times pattern matched
    pub match_count: u64,

    /// Number of times correction was accepted
    pub accept_count: u64,

    /// Number of times correction was rejected
    pub reject_count: u64,

    /// Number of times correction was modified
    pub modify_count: u64,

    /// Acceptance rate (accept / total_feedback)
    pub acceptance_rate: f64,

    /// First seen timestamp
    pub first_seen: Timestamp,

    /// Last seen timestamp
    pub last_seen: Timestamp,

    /// Average confidence of matches
    pub avg_match_confidence: f64,
}

/// Source of a pattern
#[derive(Clone, Debug, Serialize, Deserialize, PartialEq)]
pub enum PatternSource {
    /// Extracted from user feedback
    Feedback { feedback_ids: Vec<FeedbackId> },
    /// Built-in pattern
    BuiltIn,
    /// Imported from external source
    Imported { source: String },
    /// Generalized from multiple patterns
    Generalized { source_patterns: Vec<PatternId> },
}

/// Scope of a pattern
#[derive(Clone, Debug, Serialize, Deserialize, PartialEq)]
pub enum PatternScope {
    /// Applies to all users
    Global,
    /// Applies to a specific user
    User(UserId),
    /// Applies to a specific domain
    Domain(Domain),
}
```

---

## Pattern Extraction

### Token Pattern Extraction

```rust
/// Extracts token-level patterns from feedback
pub struct TokenPatternExtractor {
    /// Minimum frequency before pattern is considered
    min_frequency: u64,

    /// Maximum edit distance for similar patterns
    max_edit_distance: u8,
}

impl TokenPatternExtractor {
    /// Extract token patterns from a feedback item
    pub fn extract(&self, feedback: &Feedback) -> Vec<CandidatePattern> {
        let mut candidates = Vec::new();

        match &feedback.response {
            FeedbackResponse::Reject(_) => {
                // User rejected: the proposed correction was wrong
                // This means original → proposed was incorrect
                // We can learn: DON'T do original → proposed in this context
                candidates.push(CandidatePattern::NegativeExample {
                    original: feedback.correction.original.clone(),
                    wrong_correction: feedback.correction.proposed.clone(),
                    context: feedback.correction.context.clone(),
                });
            }

            FeedbackResponse::Modify(m) => {
                // User modified: they provided the correct answer
                // Learn: original → user_modified
                if m.modified_text != feedback.correction.original {
                    candidates.push(CandidatePattern::PositiveExample {
                        error: feedback.correction.original.clone(),
                        correction: m.modified_text.clone(),
                        context: feedback.correction.context.clone(),
                    });
                }

                // Also learn what NOT to do: original → proposed
                if m.modified_text != feedback.correction.proposed {
                    candidates.push(CandidatePattern::NegativeExample {
                        original: feedback.correction.original.clone(),
                        wrong_correction: feedback.correction.proposed.clone(),
                        context: feedback.correction.context.clone(),
                    });
                }
            }

            _ => {}
        }

        // Tokenize and extract word-level patterns
        self.extract_word_patterns(&candidates)
    }

    fn extract_word_patterns(
        &self,
        candidates: &[CandidatePattern],
    ) -> Vec<CandidatePattern> {
        let mut word_patterns = Vec::new();

        for candidate in candidates {
            match candidate {
                CandidatePattern::PositiveExample { error, correction, context } => {
                    // Tokenize both strings
                    let error_tokens: Vec<&str> = error.split_whitespace().collect();
                    let correction_tokens: Vec<&str> = correction.split_whitespace().collect();

                    // Find token-level differences
                    let diffs = self.diff_tokens(&error_tokens, &correction_tokens);

                    for diff in diffs {
                        if let TokenDiff::Replace(err, corr) = diff {
                            word_patterns.push(CandidatePattern::TokenPattern {
                                error: err.to_string(),
                                correction: corr.to_string(),
                                frequency: 1,
                            });
                        }
                    }
                }
                _ => {}
            }
        }

        word_patterns
    }

    fn diff_tokens<'a>(
        &self,
        error: &[&'a str],
        correction: &[&'a str],
    ) -> Vec<TokenDiff<'a>> {
        // Use LCS or similar algorithm to find minimal differences
        // Simplified implementation
        let mut diffs = Vec::new();

        // Simple case: same length, compare position by position
        if error.len() == correction.len() {
            for (e, c) in error.iter().zip(correction.iter()) {
                if e != c {
                    diffs.push(TokenDiff::Replace(e, c));
                }
            }
        }
        // More complex cases would use full diff algorithm

        diffs
    }
}

/// Candidate pattern from extraction
#[derive(Clone, Debug)]
pub enum CandidatePattern {
    /// A positive example (error → correction)
    PositiveExample {
        error: String,
        correction: String,
        context: CorrectionContext,
    },

    /// A negative example (original → wrong_correction should NOT be done)
    NegativeExample {
        original: String,
        wrong_correction: String,
        context: CorrectionContext,
    },

    /// A token-level pattern
    TokenPattern {
        error: String,
        correction: String,
        frequency: u64,
    },
}

/// Token difference type
enum TokenDiff<'a> {
    Replace(&'a str, &'a str),
    Insert(&'a str),
    Delete(&'a str),
}
```

### N-Gram Pattern Extraction

```rust
/// Extracts context-sensitive n-gram patterns
pub struct NGramPatternExtractor {
    /// N-gram sizes to consider
    ngram_sizes: Vec<usize>,

    /// Minimum frequency for pattern consideration
    min_frequency: u64,
}

impl NGramPatternExtractor {
    /// Extract n-gram patterns from feedback
    pub fn extract(&self, feedback: &Feedback) -> Vec<CandidatePattern> {
        let mut candidates = Vec::new();

        if let FeedbackResponse::Modify(m) = &feedback.response {
            // Get surrounding context
            let left_ctx = &feedback.correction.context.left_context;
            let right_ctx = &feedback.correction.context.right_context;

            // Tokenize context
            let left_tokens: Vec<&str> = left_ctx.split_whitespace().collect();
            let right_tokens: Vec<&str> = right_ctx.split_whitespace().collect();

            // Extract n-grams of various sizes
            for n in &self.ngram_sizes {
                let left_ngram = self.get_suffix(&left_tokens, *n);
                let right_ngram = self.get_prefix(&right_tokens, *n);

                candidates.push(CandidatePattern::NGramPattern {
                    left_context: left_ngram,
                    error: vec![feedback.correction.original.clone()],
                    right_context: right_ngram,
                    correction: vec![m.modified_text.clone()],
                });
            }
        }

        candidates
    }

    fn get_suffix(&self, tokens: &[&str], n: usize) -> Vec<String> {
        let start = tokens.len().saturating_sub(n);
        tokens[start..].iter().map(|s| s.to_string()).collect()
    }

    fn get_prefix(&self, tokens: &[&str], n: usize) -> Vec<String> {
        let end = n.min(tokens.len());
        tokens[..end].iter().map(|s| s.to_string()).collect()
    }
}
```

### Phonetic Pattern Extraction

```rust
/// Extracts phonetic patterns from feedback
pub struct PhoneticPatternExtractor {
    /// Phonetic encoder (Metaphone, Soundex, etc.)
    encoder: PhoneticEncoder,

    /// Minimum similarity for phonetic match
    min_similarity: f64,
}

impl PhoneticPatternExtractor {
    /// Extract phonetic patterns
    pub fn extract(&self, feedback: &Feedback) -> Vec<CandidatePattern> {
        let mut candidates = Vec::new();

        if let FeedbackResponse::Modify(m) = &feedback.response {
            let original = &feedback.correction.original;
            let modified = &m.modified_text;

            // Check if phonetically similar
            let orig_phonetic = self.encoder.encode(original);
            let mod_phonetic = self.encoder.encode(modified);

            let similarity = self.phonetic_similarity(&orig_phonetic, &mod_phonetic);

            if similarity >= self.min_similarity && original != modified {
                candidates.push(CandidatePattern::PhoneticPattern {
                    phonemes: orig_phonetic,
                    variants: vec![
                        (original.clone(), 0.5),
                        (modified.clone(), 0.5),
                    ],
                    context: feedback.correction.context.clone(),
                });
            }
        }

        candidates
    }

    fn phonetic_similarity(&self, a: &[Phoneme], b: &[Phoneme]) -> f64 {
        if a == b {
            return 1.0;
        }

        // Calculate similarity based on shared phonemes
        let shared = a.iter().filter(|p| b.contains(p)).count();
        let total = a.len().max(b.len());

        if total == 0 { 1.0 } else { shared as f64 / total as f64 }
    }
}
```

---

## Pattern Clustering

```rust
/// Clusters similar patterns together
pub struct PatternClusterer {
    /// Similarity threshold for clustering
    similarity_threshold: f64,

    /// Minimum cluster size to keep
    min_cluster_size: usize,
}

impl PatternClusterer {
    /// Cluster candidate patterns by similarity
    pub fn cluster(&self, patterns: Vec<CandidatePattern>) -> Vec<PatternCluster> {
        let mut clusters: Vec<PatternCluster> = Vec::new();

        for pattern in patterns {
            // Find best matching cluster
            let best_cluster = clusters.iter_mut()
                .enumerate()
                .filter_map(|(i, c)| {
                    let sim = self.pattern_similarity(&pattern, &c.representative);
                    if sim >= self.similarity_threshold {
                        Some((i, sim))
                    } else {
                        None
                    }
                })
                .max_by(|(_, a), (_, b)| a.partial_cmp(b).unwrap());

            match best_cluster {
                Some((idx, _)) => {
                    // Add to existing cluster
                    clusters[idx].members.push(pattern);
                    clusters[idx].update_stats();
                }
                None => {
                    // Create new cluster
                    clusters.push(PatternCluster::new(pattern));
                }
            }
        }

        // Filter out small clusters
        clusters.into_iter()
            .filter(|c| c.members.len() >= self.min_cluster_size)
            .collect()
    }

    fn pattern_similarity(
        &self,
        a: &CandidatePattern,
        b: &CandidatePattern,
    ) -> f64 {
        match (a, b) {
            (
                CandidatePattern::TokenPattern { error: e1, correction: c1, .. },
                CandidatePattern::TokenPattern { error: e2, correction: c2, .. },
            ) => {
                // Similarity based on edit distance
                let error_sim = 1.0 - normalized_edit_distance(e1, e2);
                let correction_sim = 1.0 - normalized_edit_distance(c1, c2);
                (error_sim + correction_sim) / 2.0
            }

            (
                CandidatePattern::PhoneticPattern { phonemes: p1, .. },
                CandidatePattern::PhoneticPattern { phonemes: p2, .. },
            ) => {
                // Similarity based on phonetic similarity
                if p1 == p2 { 1.0 } else { 0.5 }
            }

            _ => 0.0,  // Different pattern types don't cluster together
        }
    }
}

/// A cluster of similar patterns
#[derive(Clone, Debug)]
pub struct PatternCluster {
    /// Representative pattern for this cluster
    pub representative: CandidatePattern,

    /// All patterns in this cluster
    pub members: Vec<CandidatePattern>,

    /// Total frequency of patterns in cluster
    pub total_frequency: u64,

    /// Error type classification
    pub error_type: ErrorType,
}

impl PatternCluster {
    fn new(pattern: CandidatePattern) -> Self {
        Self {
            representative: pattern.clone(),
            members: vec![pattern],
            total_frequency: 1,
            error_type: ErrorType::Unknown,
        }
    }

    fn update_stats(&mut self) {
        self.total_frequency = self.members.iter()
            .filter_map(|p| match p {
                CandidatePattern::TokenPattern { frequency, .. } => Some(*frequency),
                _ => Some(1),
            })
            .sum();

        // Update representative to most common pattern
        // (simplified: just keep first)
    }
}

/// Error type classification
#[derive(Clone, Debug, PartialEq)]
pub enum ErrorType {
    Typo,           // Keyboard error
    Spelling,       // Doesn't know correct spelling
    Grammar,        // Grammatical error
    Homophone,      // Sound-alike confusion
    Semantic,       // Wrong word choice
    Unknown,
}
```

---

## Pattern Generalization

```rust
/// Generalizes clusters into reusable patterns
pub struct PatternGeneralizer {
    /// Minimum confidence for a generalized pattern
    min_confidence: f64,

    /// Minimum support (occurrences) for a pattern
    min_support: u64,
}

impl PatternGeneralizer {
    /// Generalize a cluster into a learned pattern
    pub fn generalize(&self, cluster: &PatternCluster) -> Option<LearnedPattern> {
        if cluster.total_frequency < self.min_support {
            return None;
        }

        let spec = self.synthesize_pattern_spec(cluster)?;
        let confidence = self.estimate_confidence(cluster);

        if confidence < self.min_confidence {
            return None;
        }

        Some(LearnedPattern {
            pattern_id: PatternId::new(),
            spec,
            stats: PatternStats {
                match_count: cluster.total_frequency,
                accept_count: cluster.total_frequency,  // Approximation
                reject_count: 0,
                modify_count: 0,
                acceptance_rate: 1.0,
                first_seen: Timestamp::now(),
                last_seen: Timestamp::now(),
                avg_match_confidence: confidence,
            },
            confidence,
            created_at: Timestamp::now(),
            updated_at: Timestamp::now(),
            source: PatternSource::Generalized {
                source_patterns: vec![],  // Would be filled with actual pattern IDs
            },
            scope: PatternScope::Global,
        })
    }

    fn synthesize_pattern_spec(&self, cluster: &PatternCluster) -> Option<PatternSpec> {
        // Find common structure across all patterns in cluster
        match &cluster.representative {
            CandidatePattern::TokenPattern { error, correction, .. } => {
                // Check if all members have same error/correction
                let all_same = cluster.members.iter().all(|p| {
                    matches!(p, CandidatePattern::TokenPattern { error: e, correction: c, .. }
                        if e == error && c == correction)
                });

                if all_same {
                    Some(PatternSpec::TokenReplace {
                        error: error.clone(),
                        correction: correction.clone(),
                        case_sensitive: !self.has_case_variations(cluster),
                    })
                } else {
                    // Try to find regex pattern
                    self.synthesize_regex_pattern(cluster)
                }
            }

            CandidatePattern::NGramPattern { left_context, error, right_context, correction } => {
                Some(PatternSpec::NGram {
                    left_context: left_context.iter()
                        .map(|t| ContextMatcher::Exact(t.clone()))
                        .collect(),
                    error: error.clone(),
                    right_context: right_context.iter()
                        .map(|t| ContextMatcher::Exact(t.clone()))
                        .collect(),
                    correction: correction.clone(),
                })
            }

            CandidatePattern::PhoneticPattern { phonemes, variants, .. } => {
                Some(PatternSpec::Phonetic {
                    phonemes: phonemes.clone(),
                    corrections: variants.clone(),
                    context_hints: vec![],  // Would be extracted from context
                })
            }

            _ => None,
        }
    }

    fn estimate_confidence(&self, cluster: &PatternCluster) -> f64 {
        let frequency_factor = (cluster.total_frequency as f64).ln() / 10.0;
        let consistency_factor = self.cluster_consistency(cluster);

        (frequency_factor * consistency_factor).clamp(0.0, 1.0)
    }

    fn cluster_consistency(&self, cluster: &PatternCluster) -> f64 {
        // How consistent are the patterns in this cluster?
        // Higher consistency = higher confidence
        if cluster.members.len() <= 1 {
            return 0.5;  // Single member: medium confidence
        }

        // Check how similar all members are to the representative
        let similarities: Vec<f64> = cluster.members.iter()
            .map(|p| {
                // Simplified: just check if same type
                match (&cluster.representative, p) {
                    (CandidatePattern::TokenPattern { .. }, CandidatePattern::TokenPattern { .. }) => 1.0,
                    _ => 0.0,
                }
            })
            .collect();

        let avg_sim = similarities.iter().sum::<f64>() / similarities.len() as f64;
        avg_sim
    }

    fn has_case_variations(&self, cluster: &PatternCluster) -> bool {
        // Check if cluster has patterns with different cases
        let mut seen_lower = false;
        let mut seen_upper = false;
        let mut seen_mixed = false;

        for member in &cluster.members {
            if let CandidatePattern::TokenPattern { error, .. } = member {
                if error.chars().all(|c| c.is_lowercase()) {
                    seen_lower = true;
                } else if error.chars().all(|c| c.is_uppercase()) {
                    seen_upper = true;
                } else {
                    seen_mixed = true;
                }
            }
        }

        (seen_lower as u8 + seen_upper as u8 + seen_mixed as u8) > 1
    }

    fn synthesize_regex_pattern(&self, _cluster: &PatternCluster) -> Option<PatternSpec> {
        // Complex: would analyze patterns to find common regex
        // For now, return None
        None
    }
}
```

---

## Pattern Application

```rust
/// Applies learned patterns during correction
pub struct PatternApplicator {
    /// Loaded patterns
    patterns: Vec<LearnedPattern>,

    /// Minimum confidence to apply pattern
    min_confidence: f64,
}

impl PatternApplicator {
    /// Check if any patterns match the input
    pub fn find_matches(&self, input: &str, context: &CorrectionContext) -> Vec<PatternMatch> {
        let mut matches = Vec::new();

        for pattern in &self.patterns {
            if pattern.confidence < self.min_confidence {
                continue;
            }

            if let Some(m) = self.try_match(&pattern.spec, input, context) {
                matches.push(PatternMatch {
                    pattern_id: pattern.pattern_id.clone(),
                    correction: m.correction,
                    confidence: pattern.confidence * m.match_quality,
                    span: m.span,
                });
            }
        }

        // Sort by confidence
        matches.sort_by(|a, b| b.confidence.partial_cmp(&a.confidence).unwrap());
        matches
    }

    fn try_match(
        &self,
        spec: &PatternSpec,
        input: &str,
        context: &CorrectionContext,
    ) -> Option<MatchResult> {
        match spec {
            PatternSpec::TokenReplace { error, correction, case_sensitive } => {
                let input_cmp = if *case_sensitive { input.to_string() } else { input.to_lowercase() };
                let error_cmp = if *case_sensitive { error.clone() } else { error.to_lowercase() };

                if input_cmp == error_cmp {
                    // Preserve case if not case-sensitive
                    let final_correction = if !*case_sensitive && input.chars().next()?.is_uppercase() {
                        let mut chars: Vec<char> = correction.chars().collect();
                        if let Some(c) = chars.first_mut() {
                            *c = c.to_uppercase().next()?;
                        }
                        chars.into_iter().collect()
                    } else {
                        correction.clone()
                    };

                    Some(MatchResult {
                        correction: final_correction,
                        match_quality: 1.0,
                        span: 0..input.len(),
                    })
                } else {
                    None
                }
            }

            PatternSpec::NGram { left_context, error, right_context, correction } => {
                // Check context matches
                let left_matches = self.context_matches(&context.left_context, left_context);
                let right_matches = self.context_matches(&context.right_context, right_context);

                if !left_matches || !right_matches {
                    return None;
                }

                // Check error matches
                let input_tokens: Vec<&str> = input.split_whitespace().collect();
                if input_tokens != error.iter().map(|s| s.as_str()).collect::<Vec<_>>() {
                    return None;
                }

                Some(MatchResult {
                    correction: correction.join(" "),
                    match_quality: 0.9,  // Slightly lower for context-dependent
                    span: 0..input.len(),
                })
            }

            PatternSpec::Phonetic { phonemes, corrections, context_hints } => {
                // Encode input phonetically
                let encoder = PhoneticEncoder::default();
                let input_phonemes = encoder.encode(input);

                if input_phonemes == *phonemes {
                    // Find best correction based on context
                    let best = self.select_phonetic_correction(
                        corrections,
                        context_hints,
                        context,
                    );

                    Some(MatchResult {
                        correction: best.0,
                        match_quality: best.1,
                        span: 0..input.len(),
                    })
                } else {
                    None
                }
            }

            PatternSpec::Regex { pattern, replacement, max_replacements } => {
                let re = regex::Regex::new(pattern).ok()?;

                if re.is_match(input) {
                    let corrected = match max_replacements {
                        Some(n) => re.replacen(input, *n, replacement).to_string(),
                        None => re.replace_all(input, replacement).to_string(),
                    };

                    if corrected != input {
                        Some(MatchResult {
                            correction: corrected,
                            match_quality: 0.8,  // Lower for regex
                            span: 0..input.len(),
                        })
                    } else {
                        None
                    }
                } else {
                    None
                }
            }

            PatternSpec::Morphological { error_affix, correction_affix, pos_constraint } => {
                // Check affix match
                let matches_affix = match &error_affix.suffix {
                    Some(suffix) => input.ends_with(suffix),
                    None => true,
                } && match &error_affix.prefix {
                    Some(prefix) => input.starts_with(prefix),
                    None => true,
                };

                if !matches_affix {
                    return None;
                }

                // Extract stem and apply correction
                let stem = self.extract_stem(input, error_affix);
                if stem.len() < error_affix.min_stem_length {
                    return None;
                }

                let corrected = format!("{}{}", stem, correction_affix);

                Some(MatchResult {
                    correction: corrected,
                    match_quality: 0.85,
                    span: 0..input.len(),
                })
            }
        }
    }

    fn context_matches(&self, actual: &str, expected: &[ContextMatcher]) -> bool {
        if expected.is_empty() {
            return true;
        }

        let tokens: Vec<&str> = actual.split_whitespace().collect();

        for (i, matcher) in expected.iter().enumerate() {
            let token = tokens.get(tokens.len().saturating_sub(expected.len()) + i);

            let matches = match (matcher, token) {
                (ContextMatcher::Any, _) => true,
                (ContextMatcher::Exact(e), Some(t)) => e == *t,
                (ContextMatcher::OneOf(options), Some(t)) => options.iter().any(|o| o == *t),
                (ContextMatcher::StartOfSentence, None) => i == 0,
                (ContextMatcher::EndOfSentence, None) => i == expected.len() - 1,
                (ContextMatcher::POS(_), _) => true,  // Would need POS tagger
                _ => false,
            };

            if !matches {
                return false;
            }
        }

        true
    }

    fn select_phonetic_correction(
        &self,
        corrections: &[(String, f64)],
        hints: &[ContextHint],
        context: &CorrectionContext,
    ) -> (String, f64) {
        // Check context hints
        let full_context = format!("{} {} {}", context.left_context, "", context.right_context);

        for hint in hints {
            if hint.indicator_words.iter().any(|w| full_context.contains(w)) {
                if let Some((_, base_prob)) = corrections.iter()
                    .find(|(c, _)| c == &hint.suggested_correction)
                {
                    return (hint.suggested_correction.clone(), base_prob + hint.confidence_boost);
                }
            }
        }

        // Return highest probability correction
        corrections.iter()
            .max_by(|(_, a), (_, b)| a.partial_cmp(b).unwrap())
            .map(|(c, p)| (c.clone(), *p))
            .unwrap_or_else(|| ("".to_string(), 0.0))
    }

    fn extract_stem(&self, word: &str, affix: &AffixPattern) -> String {
        let mut stem = word.to_string();

        if let Some(suffix) = &affix.suffix {
            if stem.ends_with(suffix) {
                stem = stem[..stem.len() - suffix.len()].to_string();
            }
        }

        if let Some(prefix) = &affix.prefix {
            if stem.starts_with(prefix) {
                stem = stem[prefix.len()..].to_string();
            }
        }

        stem
    }
}

/// Result of a pattern match
struct MatchResult {
    correction: String,
    match_quality: f64,
    span: std::ops::Range<usize>,
}

/// A pattern match for external use
#[derive(Clone, Debug)]
pub struct PatternMatch {
    pub pattern_id: PatternId,
    pub correction: String,
    pub confidence: f64,
    pub span: std::ops::Range<usize>,
}
```

---

## PathMap Storage Schema

```
PathMap Key Structure (Patterns):
=================================

/learning/pattern/{pattern_id}/
    spec/
        type -> token_replace|ngram|phonetic|morphological|regex
        ; Type-specific fields
        ; For token_replace:
        error -> error string
        correction -> correction string
        case_sensitive -> bool
        ; For ngram:
        left_context/ -> [context_matcher, ...]
        error/ -> [error_tokens, ...]
        right_context/ -> [context_matcher, ...]
        correction/ -> [correction_tokens, ...]
        ; For phonetic:
        phonemes/ -> [phoneme, ...]
        corrections/ -> [(correction, probability), ...]
        context_hints/ -> [hint, ...]
        ; For morphological:
        error_affix/
            prefix -> optional string
            suffix -> optional string
            min_stem_length -> int
        correction_affix -> string
        pos_constraint -> optional pos
        ; For regex:
        pattern -> regex string
        replacement -> replacement string
        max_replacements -> optional int

    stats/
        match_count -> u64
        accept_count -> u64
        reject_count -> u64
        modify_count -> u64
        acceptance_rate -> float
        first_seen -> timestamp
        last_seen -> timestamp
        avg_match_confidence -> float

    confidence -> float
    created_at -> timestamp
    updated_at -> timestamp

    source/
        type -> feedback|builtin|imported|generalized
        ; For feedback:
        feedback_ids/ -> [feedback_id, ...]
        ; For imported:
        source_name -> string
        ; For generalized:
        source_patterns/ -> [pattern_id, ...]

    scope/
        type -> global|user|domain
        ; For user:
        user_id -> user identifier
        ; For domain:
        domain -> domain name

/learning/pattern_index/
    /by_error/{error_hash}/
        {pattern_id} -> true
    /by_type/{pattern_type}/
        {pattern_id} -> true
    /by_scope/{scope_type}/{scope_value}/
        {pattern_id} -> true
    /by_confidence/
        {confidence_bucket}/{pattern_id} -> confidence
```

---

## MeTTa Predicates

### Pattern Specification Predicates

```metta
; Pattern types
(: PatternSpec Type)
(: LearnedPattern Type)

; Pattern constructors
(: token-pattern (-> String String Bool PatternSpec))
(: ngram-pattern (-> (List ContextMatcher) (List String) (List ContextMatcher) (List String) PatternSpec))
(: phonetic-pattern (-> (List Phoneme) (List (Pair String Float)) PatternSpec))
(: morph-pattern (-> AffixPattern String PatternSpec))
(: regex-pattern (-> String String PatternSpec))

; Context matchers
(: ctx-exact (-> String ContextMatcher))
(: ctx-one-of (-> (List String) ContextMatcher))
(: ctx-any ContextMatcher)
(: ctx-start-of-sentence ContextMatcher)
(: ctx-end-of-sentence ContextMatcher)
```

### Pattern Learning Predicates

```metta
; Pattern extraction
(: extract-token-patterns (-> Feedback (List CandidatePattern)))
(: extract-ngram-patterns (-> Feedback (List CandidatePattern)))
(: extract-phonetic-patterns (-> Feedback (List CandidatePattern)))

; Pattern clustering
(: cluster-patterns (-> (List CandidatePattern) Float (List PatternCluster)))
(: cluster-similarity (-> CandidatePattern CandidatePattern Float))

; Pattern generalization
(: generalize-cluster (-> PatternCluster (Maybe LearnedPattern)))
(: estimate-confidence (-> PatternCluster Float))
(: synthesize-spec (-> PatternCluster (Maybe PatternSpec)))
```

### Pattern Application Predicates

```metta
; Pattern matching
(: pattern-matches (-> PatternSpec String CorrectionContext Bool))
(: apply-pattern (-> PatternSpec String CorrectionContext (Maybe String)))
(: find-pattern-matches (-> String CorrectionContext (List PatternMatch)))

; Pattern statistics
(: pattern-confidence (-> LearnedPattern Float))
(: pattern-acceptance-rate (-> LearnedPattern Float))
(: update-pattern-stats (-> LearnedPattern Feedback LearnedPattern))
```

### Pattern Management Predicates

```metta
; Storage operations
(: store-pattern (-> LearnedPattern (Result () Error)))
(: load-pattern (-> PatternId (Result LearnedPattern Error)))
(: delete-pattern (-> PatternId (Result () Error)))

; Query operations
(: patterns-for-error (-> String (List LearnedPattern)))
(: patterns-by-type (-> PatternType (List LearnedPattern)))
(: patterns-by-confidence (-> Float Float (List LearnedPattern)))
(: user-patterns (-> UserId (List LearnedPattern)))
```

---

## Integration with Correction Pipeline

```
┌─────────────────────────────────────────────────────────────────────────────┐
│            PATTERN LEARNING IN CORRECTION PIPELINE                           │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                              │
│  User Input: "I would of gone"                                              │
│      │                                                                       │
│      ▼                                                                       │
│  ┌───────────────────────────────────────────────────────────────────────┐  │
│  │                    TIER 1: LEXICAL CORRECTION                         │  │
│  │                                                                       │  │
│  │  Standard Dictionary + liblevenshtein                                 │  │
│  │      ↓                                                                │  │
│  │  ┌─────────────────────────────────────────┐                         │  │
│  │  │ LEARNED PATTERNS (Token-Level)          │                         │  │
│  │  │                                         │                         │  │
│  │  │ Check: "of" in "would of" context       │                         │  │
│  │  │ Match: NGram("would", "of", *, "have")  │ ← Learned from feedback │  │
│  │  │ Correction: "would have"                │                         │  │
│  │  └─────────────────────────────────────────┘                         │  │
│  │                                                                       │  │
│  └───────────────────────────────────────────────────────────────────────┘  │
│      │                                                                       │
│      ▼                                                                       │
│  ┌───────────────────────────────────────────────────────────────────────┐  │
│  │                    TIER 2: SYNTACTIC VALIDATION                       │  │
│  │                                                                       │  │
│  │  Grammar Rules + CFG                                                  │  │
│  │      ↓                                                                │  │
│  │  ┌─────────────────────────────────────────┐                         │  │
│  │  │ LEARNED PATTERNS (Grammar-Level)        │                         │  │
│  │  │                                         │                         │  │
│  │  │ No additional patterns for this input   │                         │  │
│  │  └─────────────────────────────────────────┘                         │  │
│  │                                                                       │  │
│  └───────────────────────────────────────────────────────────────────────┘  │
│      │                                                                       │
│      ▼                                                                       │
│  Correction: "I would have gone"                                            │
│      │                                                                       │
│      ▼                                                                       │
│  User Accepts ───────────────────────────────────────────────────────────┐  │
│                                                                          │  │
│                                                                          │  │
│  (Later, different input: "I could of went")                            │  │
│      │                                                                   │  │
│      ▼                                                                   │  │
│  Pattern Matcher finds:                                                  │  │
│    - NGram("could", "of", *, "have") matches!                           │  │
│    - Correction: "I could have went"                                    │  │
│                                                                          │  │
│  User Modifies to: "I could have gone"                                  │  │
│      │                                                                   │  │
│      ▼                                                                   │  │
│  ┌───────────────────────────────────────────────────────────────────┐  │  │
│  │                 NEW PATTERN LEARNED                                │  │  │
│  │                                                                    │  │  │
│  │  NGram("could/would/should", "have", *, "gone" not "went")        │  │  │
│  │                                                                    │  │  │
│  │  (Generalized from multiple examples)                             │  │  │
│  └───────────────────────────────────────────────────────────────────┘  │  │
│                                                                          │  │
└──────────────────────────────────────────────────────────────────────────────┘
```

---

## Related Documentation

- [README](./README.md) - Agent learning overview
- [Feedback Collection](./01-feedback-collection.md) - Input to pattern learning
- [User Preferences](./03-user-preferences.md) - User-specific patterns
- [Online Learning](./04-online-learning.md) - Pattern weight updates
