# Output Postprocessing

This document details the response postprocessing pipeline that validates LLM output
for coherence, factual accuracy, and consistency before delivery to the user.

**Sources**:
- Plan: Part V - Dialogue Context and LLM Agent Correction Extension
- Dialogue Layer: `../dialogue/`
- Correction WFST: `../correction-wfst/`
- PathMap: `/home/dylon/Workspace/f1r3fly.io/PathMap/`
- MORK: `/home/dylon/Workspace/f1r3fly.io/MORK/`

---

## Table of Contents

1. [Overview](#overview)
2. [Pipeline Architecture](#pipeline-architecture)
3. [Coherence Checking](#coherence-checking)
4. [Fact Validation](#fact-validation)
5. [Response Correction](#response-correction)
6. [Confidence Scoring](#confidence-scoring)
7. [Handling Recommendations](#handling-recommendations)
8. [Implementation](#implementation)
9. [MeTTa Predicates](#metta-predicates)
10. [PathMap Schema](#pathmap-schema)

---

## Overview

The Response Postprocessor validates LLM output through multiple checks before
delivery to the user:

1. **Coherence Checking** - Validates response against dialogue context
2. **Fact Validation** - Verifies claims against knowledge base
3. **Hallucination Detection** - Identifies fabricated content (detailed in 03)
4. **Response Correction** - Applies fixes or flags issues
5. **Confidence Scoring** - Computes overall reliability score

```
┌─────────────────────────────────────────────────────────────────────────┐
│                   RESPONSE POSTPROCESSING PIPELINE                       │
│                                                                          │
│  LLM Response                                                            │
│       │                                                                  │
│       ▼                                                                  │
│  ┌────────────────────────────────────────────────────────────────────┐ │
│  │ STAGE 1: COHERENCE CHECKING                                        │ │
│  │  ┌─────────────┐  ┌─────────────┐  ┌─────────────┐                │ │
│  │  │    QUD      │→ │   Topic     │→ │   Entity    │                │ │
│  │  │  Relevance  │  │ Consistency │  │ Consistency │                │ │
│  │  └─────────────┘  └─────────────┘  └─────────────┘                │ │
│  └───────────────────────────┬────────────────────────────────────────┘ │
│                              ▼                                           │
│  ┌────────────────────────────────────────────────────────────────────┐ │
│  │ STAGE 2: FACT VALIDATION                                           │ │
│  │  ┌─────────────┐  ┌─────────────┐  ┌─────────────┐                │ │
│  │  │   Claim     │→ │   KB        │→ │  Dialogue   │                │ │
│  │  │ Extraction  │  │   Lookup    │  │   History   │                │ │
│  │  └─────────────┘  └─────────────┘  └─────────────┘                │ │
│  └───────────────────────────┬────────────────────────────────────────┘ │
│                              ▼                                           │
│  ┌────────────────────────────────────────────────────────────────────┐ │
│  │ STAGE 3: HALLUCINATION DETECTION                                   │ │
│  │  ┌─────────────┐  ┌─────────────┐  ┌─────────────┐                │ │
│  │  │ Fabricated  │→ │  Nonexistent│→ │Inconsistent │                │ │
│  │  │   Facts     │  │  Entities   │  │   Claims    │                │ │
│  │  └─────────────┘  └─────────────┘  └─────────────┘                │ │
│  └───────────────────────────┬────────────────────────────────────────┘ │
│                              ▼                                           │
│  ┌────────────────────────────────────────────────────────────────────┐ │
│  │ STAGE 4: RESPONSE CORRECTION                                       │ │
│  │  ┌─────────────┐  ┌─────────────┐  ┌─────────────┐                │ │
│  │  │  Grammar    │→ │   Factual   │→ │  Annotation │                │ │
│  │  │  Correction │  │ Correction  │  │   Insertion │                │ │
│  │  └─────────────┘  └─────────────┘  └─────────────┘                │ │
│  └───────────────────────────┬────────────────────────────────────────┘ │
│                              ▼                                           │
│  ┌────────────────────────────────────────────────────────────────────┐ │
│  │ STAGE 5: CONFIDENCE SCORING & RECOMMENDATION                       │ │
│  │  ┌─────────────┐  ┌─────────────┐  ┌─────────────┐                │ │
│  │  │   Score     │→ │  Threshold  │→ │  Decision   │                │ │
│  │  │ Aggregation │  │   Check     │  │   Making    │                │ │
│  │  └─────────────┘  └─────────────┘  └─────────────┘                │ │
│  └───────────────────────────┬────────────────────────────────────────┘ │
│                              ▼                                           │
│                   Postprocessed Response                                 │
│                                                                          │
└─────────────────────────────────────────────────────────────────────────┘
```

---

## Pipeline Architecture

### Core Components

```rust
/// Main response postprocessing pipeline
pub struct ResponsePostprocessor {
    /// Coherence checking system
    coherence_checker: CoherenceChecker,

    /// Fact validation system
    fact_validator: FactValidator,

    /// Hallucination detection system
    hallucination_detector: HallucinationDetector,

    /// Response correction system
    response_corrector: ResponseCorrector,

    /// Confidence scoring system
    confidence_scorer: ConfidenceScorer,

    /// Configuration
    config: PostprocessorConfig,
}

/// Postprocessor configuration
pub struct PostprocessorConfig {
    /// Minimum acceptable coherence score
    pub min_coherence_score: f64,

    /// Minimum acceptable factual accuracy
    pub min_factual_score: f64,

    /// Hallucination confidence threshold for flagging
    pub hallucination_threshold: f64,

    /// Whether to auto-correct or just flag
    pub auto_correct: bool,

    /// Maximum corrections to apply
    pub max_corrections: usize,

    /// Response handling thresholds
    pub handling_thresholds: HandlingThresholds,
}

/// Thresholds for handling decisions
pub struct HandlingThresholds {
    /// Above this: Accept
    pub accept_threshold: f64,

    /// Below accept, above this: Accept with flags
    pub flag_threshold: f64,

    /// Below flag, above this: Correct and deliver
    pub correct_threshold: f64,

    /// Below correct, above this: Regenerate
    pub regenerate_threshold: f64,

    /// Below regenerate: Human review
    // (implicit)
}

impl Default for HandlingThresholds {
    fn default() -> Self {
        Self {
            accept_threshold: 0.90,
            flag_threshold: 0.75,
            correct_threshold: 0.50,
            regenerate_threshold: 0.30,
        }
    }
}
```

### Pipeline Execution

```rust
impl ResponsePostprocessor {
    /// Process LLM response through full postprocessing pipeline
    pub fn postprocess(
        &self,
        response: &str,
        dialogue_state: &DialogueState,
        knowledge_base: &KnowledgeBase,
        original_query: &str,
    ) -> Result<PostprocessedResponse, PostprocessingError> {
        // Stage 1: Coherence Checking
        let coherence = self.coherence_checker.check(
            response,
            dialogue_state,
            original_query,
        )?;

        // Stage 2: Fact Validation
        let factual = self.fact_validator.validate(
            response,
            knowledge_base,
            dialogue_state,
        )?;

        // Stage 3: Hallucination Detection
        let hallucinations = self.hallucination_detector.detect(
            response,
            dialogue_state,
            knowledge_base,
        )?;

        // Stage 4: Response Correction (if enabled)
        let corrected = if self.config.auto_correct {
            Some(self.response_corrector.correct(
                response,
                &coherence,
                &factual,
                &hallucinations,
            )?)
        } else {
            None
        };

        // Stage 5: Confidence Scoring & Recommendation
        let confidence = self.confidence_scorer.score(
            &coherence,
            &factual,
            &hallucinations,
        );

        let recommendation = self.determine_recommendation(
            confidence,
            &coherence,
            &factual,
            &hallucinations,
        );

        // Extract new entities mentioned in response
        let new_entities = self.extract_new_entities(
            response,
            dialogue_state,
        )?;

        Ok(PostprocessedResponse {
            original: response.to_string(),
            corrected,
            coherence,
            factual_validation: factual,
            hallucination_flags: hallucinations,
            new_entities,
            confidence,
            recommendation,
        })
    }
}
```

---

## Coherence Checking

Coherence checking validates that the LLM response makes sense in the dialogue context.

### Coherence Dimensions

```
┌────────────────────────────────────────────────────────────────────────┐
│                     COHERENCE CHECKING DIMENSIONS                       │
├────────────────────────────────────────────────────────────────────────┤
│                                                                         │
│  ┌───────────────────────────────────────────────────────────────────┐ │
│  │ 1. QUD (Question Under Discussion) RELEVANCE                      │ │
│  │                                                                   │ │
│  │ Does the response address what was asked?                         │ │
│  │                                                                   │ │
│  │ User asked: "What time is the meeting with John?"                 │ │
│  │                                                                   │ │
│  │ ✓ Good: "The meeting with John is at 2pm on Monday."              │ │
│  │ ✗ Bad:  "John is a great colleague who works in Engineering."    │ │
│  │                                                                   │ │
│  │ Check: Does response contain answer to QUD?                       │ │
│  │ Score: 1.0 if directly answers, 0.5 if partially, 0.0 if unrelated│ │
│  └───────────────────────────────────────────────────────────────────┘ │
│                                                                         │
│  ┌───────────────────────────────────────────────────────────────────┐ │
│  │ 2. TOPIC CONSISTENCY                                              │ │
│  │                                                                   │ │
│  │ Does the response stay on topic?                                  │ │
│  │                                                                   │ │
│  │ Dialogue topic: Meeting scheduling                                │ │
│  │                                                                   │ │
│  │ ✓ Good: "I've scheduled the meeting for 2pm. Should I send       │ │
│  │         calendar invites to the attendees?"                       │ │
│  │ ✗ Bad:  "By the way, have you tried the new restaurant downtown? │ │
│  │         The food is amazing."                                     │ │
│  │                                                                   │ │
│  │ Check: Topic overlap with current topic graph                     │ │
│  │ Score: Keyword overlap + semantic similarity                      │ │
│  └───────────────────────────────────────────────────────────────────┘ │
│                                                                         │
│  ┌───────────────────────────────────────────────────────────────────┐ │
│  │ 3. ENTITY CONSISTENCY                                             │ │
│  │                                                                   │ │
│  │ Are entity references correct?                                    │ │
│  │                                                                   │ │
│  │ Known: John Smith (colleague, Engineering)                        │ │
│  │                                                                   │ │
│  │ ✓ Good: "John Smith from Engineering confirmed his attendance."   │ │
│  │ ✗ Bad:  "John Smith from Marketing will present the budget."     │ │
│  │                (Wrong department)                                 │ │
│  │                                                                   │ │
│  │ Check: Entity attributes match known information                  │ │
│  │ Score: Fraction of correct entity references                      │ │
│  └───────────────────────────────────────────────────────────────────┘ │
│                                                                         │
│  ┌───────────────────────────────────────────────────────────────────┐ │
│  │ 4. DISCOURSE COHERENCE                                            │ │
│  │                                                                   │ │
│  │ Does the response flow logically from the conversation?           │ │
│  │                                                                   │ │
│  │ Previous: User asked to schedule meeting                          │ │
│  │ Expected: Confirmation or clarification                           │ │
│  │                                                                   │ │
│  │ ✓ Good: "I've scheduled the meeting. Is there anything else?"    │ │
│  │ ✗ Bad:  "Why did you cancel the meeting?"                        │ │
│  │         (Contradicts expected discourse flow)                     │ │
│  │                                                                   │ │
│  │ Check: Expected speech act given dialogue history                 │ │
│  │ Score: Match with expected discourse patterns                     │ │
│  └───────────────────────────────────────────────────────────────────┘ │
│                                                                         │
│  ┌───────────────────────────────────────────────────────────────────┐ │
│  │ 5. PRONOUN/REFERENCE CONSISTENCY                                  │ │
│  │                                                                   │ │
│  │ Are pronouns and references clear and consistent?                 │ │
│  │                                                                   │ │
│  │ Context: Discussing John (male) and Sarah (female)                │ │
│  │                                                                   │ │
│  │ ✓ Good: "He (John) will present first, then she (Sarah) will..."  │ │
│  │ ✗ Bad:  "She will present the budget." (Ambiguous - who?)        │ │
│  │                                                                   │ │
│  │ Check: Pronouns resolve unambiguously in context                  │ │
│  │ Score: Fraction of resolvable references                          │ │
│  └───────────────────────────────────────────────────────────────────┘ │
│                                                                         │
└────────────────────────────────────────────────────────────────────────┘
```

### Coherence Checker Implementation

```rust
/// Coherence checking system
pub struct CoherenceChecker {
    /// QUD relevance analyzer
    qud_analyzer: QUDAnalyzer,

    /// Topic consistency analyzer
    topic_analyzer: TopicAnalyzer,

    /// Entity consistency analyzer
    entity_analyzer: EntityAnalyzer,

    /// Discourse coherence analyzer
    discourse_analyzer: DiscourseAnalyzer,

    /// Reference consistency analyzer
    reference_analyzer: ReferenceAnalyzer,

    /// Configuration
    config: CoherenceConfig,
}

/// Coherence check result
pub struct CoherenceResult {
    /// Overall coherence score (0.0 - 1.0)
    pub score: f64,

    /// QUD relevance score and details
    pub qud_relevance: QUDRelevanceResult,

    /// Topic consistency score and details
    pub topic_consistency: TopicConsistencyResult,

    /// Entity consistency score and details
    pub entity_consistency: EntityConsistencyResult,

    /// Discourse coherence score and details
    pub discourse_coherence: DiscourseCoherenceResult,

    /// Reference consistency score and details
    pub reference_consistency: ReferenceConsistencyResult,

    /// Aggregated issues found
    pub issues: Vec<CoherenceIssue>,
}

/// Individual coherence issue
pub struct CoherenceIssue {
    /// Issue type
    pub issue_type: CoherenceIssueType,

    /// Location in response (if applicable)
    pub span: Option<Range<usize>>,

    /// Description of the issue
    pub description: String,

    /// Severity (0.0 = minor, 1.0 = critical)
    pub severity: f64,

    /// Suggested fix (if available)
    pub suggestion: Option<String>,
}

/// Types of coherence issues
pub enum CoherenceIssueType {
    QUDNotAddressed,
    QUDPartiallyAddressed,
    TopicDrift,
    TopicUnrelated,
    EntityMismatch,
    EntityUnknown,
    DiscourseBreak,
    UnexpectedSpeechAct,
    AmbiguousReference,
    InconsistentPronoun,
}

impl CoherenceChecker {
    /// Check response coherence against dialogue context
    pub fn check(
        &self,
        response: &str,
        dialogue_state: &DialogueState,
        original_query: &str,
    ) -> Result<CoherenceResult, CoherenceError> {
        let mut issues = Vec::new();

        // 1. QUD Relevance
        let qud_relevance = self.qud_analyzer.analyze(
            response,
            original_query,
            dialogue_state.get_qud_stack()?,
        )?;
        issues.extend(qud_relevance.issues.clone());

        // 2. Topic Consistency
        let topic_consistency = self.topic_analyzer.analyze(
            response,
            &dialogue_state.topic_graph,
        )?;
        issues.extend(topic_consistency.issues.clone());

        // 3. Entity Consistency
        let entity_consistency = self.entity_analyzer.analyze(
            response,
            &dialogue_state.entity_registry,
        )?;
        issues.extend(entity_consistency.issues.clone());

        // 4. Discourse Coherence
        let discourse_coherence = self.discourse_analyzer.analyze(
            response,
            &dialogue_state.turns,
        )?;
        issues.extend(discourse_coherence.issues.clone());

        // 5. Reference Consistency
        let reference_consistency = self.reference_analyzer.analyze(
            response,
            dialogue_state,
        )?;
        issues.extend(reference_consistency.issues.clone());

        // Calculate overall score
        let score = self.calculate_overall_score(
            &qud_relevance,
            &topic_consistency,
            &entity_consistency,
            &discourse_coherence,
            &reference_consistency,
        );

        Ok(CoherenceResult {
            score,
            qud_relevance,
            topic_consistency,
            entity_consistency,
            discourse_coherence,
            reference_consistency,
            issues,
        })
    }

    /// Calculate weighted overall coherence score
    fn calculate_overall_score(
        &self,
        qud: &QUDRelevanceResult,
        topic: &TopicConsistencyResult,
        entity: &EntityConsistencyResult,
        discourse: &DiscourseCoherenceResult,
        reference: &ReferenceConsistencyResult,
    ) -> f64 {
        let weights = &self.config.weights;

        weights.qud * qud.score
            + weights.topic * topic.score
            + weights.entity * entity.score
            + weights.discourse * discourse.score
            + weights.reference * reference.score
    }
}

/// QUD Relevance Analyzer
pub struct QUDAnalyzer {
    /// Semantic similarity model
    similarity_model: SemanticSimilarityModel,

    /// Question type classifier
    question_classifier: QuestionClassifier,
}

impl QUDAnalyzer {
    /// Analyze whether response addresses the QUD
    pub fn analyze(
        &self,
        response: &str,
        query: &str,
        qud_stack: &[QUD],
    ) -> Result<QUDRelevanceResult, CoherenceError> {
        let mut issues = Vec::new();

        // Classify the question type
        let question_type = self.question_classifier.classify(query)?;

        // Check if response contains expected answer elements
        let answer_coverage = match question_type {
            QuestionType::YesNo => self.check_yes_no_answer(response, query)?,
            QuestionType::Wh { wh_word } => {
                self.check_wh_answer(response, query, &wh_word)?
            }
            QuestionType::How => self.check_how_answer(response, query)?,
            QuestionType::Alternative => {
                self.check_alternative_answer(response, query)?
            }
            QuestionType::Statement => {
                self.check_statement_relevance(response, query)?
            }
        };

        // Check semantic relevance
        let semantic_relevance = self.similarity_model.similarity(response, query)?;

        // Determine score
        let score = (answer_coverage * 0.6 + semantic_relevance * 0.4).clamp(0.0, 1.0);

        if score < 0.3 {
            issues.push(CoherenceIssue {
                issue_type: CoherenceIssueType::QUDNotAddressed,
                span: None,
                description: format!(
                    "Response does not address the question: '{}'",
                    query
                ),
                severity: 1.0,
                suggestion: None,
            });
        } else if score < 0.7 {
            issues.push(CoherenceIssue {
                issue_type: CoherenceIssueType::QUDPartiallyAddressed,
                span: None,
                description: "Response partially addresses the question".to_string(),
                severity: 0.5,
                suggestion: None,
            });
        }

        Ok(QUDRelevanceResult {
            score,
            question_type,
            answer_coverage,
            semantic_relevance,
            addresses_qud: score >= 0.5,
            issues,
        })
    }

    /// Check if response contains yes/no answer
    fn check_yes_no_answer(
        &self,
        response: &str,
        _query: &str,
    ) -> Result<f64, CoherenceError> {
        let response_lower = response.to_lowercase();

        // Direct yes/no
        if response_lower.starts_with("yes") || response_lower.contains("yes,") {
            return Ok(1.0);
        }
        if response_lower.starts_with("no") || response_lower.contains("no,") {
            return Ok(1.0);
        }

        // Indirect affirmation/negation
        let affirmative_markers = ["certainly", "absolutely", "definitely", "correct"];
        let negative_markers = ["unfortunately", "i'm afraid", "cannot", "don't"];

        for marker in &affirmative_markers {
            if response_lower.contains(marker) {
                return Ok(0.9);
            }
        }

        for marker in &negative_markers {
            if response_lower.contains(marker) {
                return Ok(0.9);
            }
        }

        // No clear yes/no
        Ok(0.3)
    }

    /// Check if response contains Wh-answer
    fn check_wh_answer(
        &self,
        response: &str,
        _query: &str,
        wh_word: &str,
    ) -> Result<f64, CoherenceError> {
        match wh_word {
            "what" | "which" => {
                // Should contain a noun phrase answer
                // Simplified: check for capitalized nouns or quoted text
                if response.chars().any(|c| c.is_uppercase()) {
                    Ok(0.8)
                } else {
                    Ok(0.4)
                }
            }
            "who" | "whom" => {
                // Should contain person reference
                // Simplified: check for capitalized names
                let has_name = response.split_whitespace()
                    .any(|w| w.chars().next().map(|c| c.is_uppercase()).unwrap_or(false));
                if has_name {
                    Ok(0.9)
                } else {
                    Ok(0.3)
                }
            }
            "where" => {
                // Should contain location
                let location_markers = ["at", "in", "on", "near", "to"];
                if location_markers.iter().any(|m| response.to_lowercase().contains(m)) {
                    Ok(0.8)
                } else {
                    Ok(0.3)
                }
            }
            "when" => {
                // Should contain time reference
                let time_patterns = ["at", "on", "in", "tomorrow", "yesterday",
                                      "today", "pm", "am", "o'clock"];
                if time_patterns.iter().any(|p| response.to_lowercase().contains(p)) {
                    Ok(0.9)
                } else {
                    Ok(0.3)
                }
            }
            "why" => {
                // Should contain reason/explanation
                let reason_markers = ["because", "since", "due to", "as", "the reason"];
                if reason_markers.iter().any(|m| response.to_lowercase().contains(m)) {
                    Ok(0.9)
                } else {
                    Ok(0.4)
                }
            }
            _ => Ok(0.5),
        }
    }
}
```

---

## Fact Validation

Fact validation verifies claims in the LLM response against the knowledge base.

### Validation Process

```
Response: "John Smith's email is john.s@company.org. He joined the
          company in 2019 and works in the Marketing department."
     │
     ▼
┌────────────────────────────────────────────────────────────────────────┐
│ STEP 1: CLAIM EXTRACTION                                               │
│                                                                        │
│ Extract verifiable claims:                                             │
│   ┌─────────────────────────────────────────────────────────────────┐ │
│   │ Claim ID │ Type       │ Subject    │ Predicate    │ Object     │ │
│   │----------|------------|------------|--------------|------------|│ │
│   │ C1       │ Attribute  │ John Smith │ email        │ john.s@... │ │
│   │ C2       │ Attribute  │ John Smith │ join_date    │ 2019       │ │
│   │ C3       │ Attribute  │ John Smith │ department   │ Marketing  │ │
│   └─────────────────────────────────────────────────────────────────┘ │
└────────────────────────────────────────────────────────────────────────┘
     │
     ▼
┌────────────────────────────────────────────────────────────────────────┐
│ STEP 2: KNOWLEDGE BASE LOOKUP                                          │
│                                                                        │
│ Query KB for John Smith (EntityId: E42):                               │
│   ┌─────────────────────────────────────────────────────────────────┐ │
│   │ Attribute  │ KB Value                    │ Confidence           │ │
│   │------------|-----------------------------|--------------------- │ │
│   │ email      │ john.smith@company.com      │ 1.0 (verified)      │ │
│   │ join_date  │ 2020                        │ 0.95 (HR record)    │ │
│   │ department │ Engineering                 │ 1.0 (verified)      │ │
│   └─────────────────────────────────────────────────────────────────┘ │
└────────────────────────────────────────────────────────────────────────┘
     │
     ▼
┌────────────────────────────────────────────────────────────────────────┐
│ STEP 3: CLAIM VERIFICATION                                             │
│                                                                        │
│ Compare claims against KB:                                             │
│   ┌─────────────────────────────────────────────────────────────────┐ │
│   │ Claim │ Response Value │ KB Value          │ Status            │ │
│   │-------|----------------|-------------------|-------------------│ │
│   │ C1    │ john.s@...     │ john.smith@...    │ ✗ CONTRADICTED   │ │
│   │ C2    │ 2019           │ 2020              │ ✗ CONTRADICTED   │ │
│   │ C3    │ Marketing      │ Engineering       │ ✗ CONTRADICTED   │ │
│   └─────────────────────────────────────────────────────────────────┘ │
│                                                                        │
│ Summary: 0/3 claims verified, 3/3 contradicted                        │
└────────────────────────────────────────────────────────────────────────┘
     │
     ▼
┌────────────────────────────────────────────────────────────────────────┐
│ STEP 4: DIALOGUE HISTORY CHECK                                         │
│                                                                        │
│ Check if claims contradict earlier conversation:                       │
│                                                                        │
│ Turn T-3: "John works in Engineering."                                │
│ Turn T-5: "I joined in 2020, same year as John."                      │
│                                                                        │
│ Additional contradictions found:                                       │
│   - C2 contradicts Turn T-5 (user said John joined in 2020)           │
│   - C3 contradicts Turn T-3 (user said John in Engineering)           │
└────────────────────────────────────────────────────────────────────────┘
```

### Fact Validator Implementation

```rust
/// Fact validation system
pub struct FactValidator {
    /// Claim extractor
    claim_extractor: ClaimExtractor,

    /// Knowledge base interface
    knowledge_base: Arc<RwLock<KnowledgeBase>>,

    /// Dialogue history checker
    history_checker: HistoryChecker,

    /// Configuration
    config: FactValidatorConfig,
}

/// Fact validation result
pub struct FactualValidationResult {
    /// Overall factual accuracy score (0.0 - 1.0)
    pub score: f64,

    /// Claims extracted from response
    pub claims: Vec<Claim>,

    /// Validation results per claim
    pub claim_validations: Vec<ClaimValidation>,

    /// Summary statistics
    pub stats: ValidationStats,
}

/// Validation statistics
pub struct ValidationStats {
    /// Total claims extracted
    pub claims_checked: usize,

    /// Claims verified as correct
    pub claims_verified: usize,

    /// Claims contradicted by KB
    pub claims_contradicted: usize,

    /// Claims not found in KB
    pub claims_unverifiable: usize,

    /// Claims contradicting dialogue history
    pub claims_history_conflict: usize,
}

/// Individual claim
pub struct Claim {
    /// Claim identifier
    pub id: ClaimId,

    /// Claim type
    pub claim_type: ClaimType,

    /// Subject entity
    pub subject: String,

    /// Predicate/relation
    pub predicate: String,

    /// Object/value
    pub object: String,

    /// Location in response
    pub span: Range<usize>,

    /// Extraction confidence
    pub confidence: f64,
}

/// Claim validation result
pub struct ClaimValidation {
    /// The claim being validated
    pub claim: Claim,

    /// Validation status
    pub status: ValidationStatus,

    /// KB evidence (if found)
    pub kb_evidence: Option<KBEvidence>,

    /// History evidence (if conflict found)
    pub history_evidence: Option<HistoryEvidence>,

    /// Correction suggestion (if contradicted)
    pub suggestion: Option<String>,
}

/// Validation status
pub enum ValidationStatus {
    /// Claim matches KB
    Verified { confidence: f64 },

    /// Claim contradicts KB
    Contradicted { kb_value: String, confidence: f64 },

    /// Claim not found in KB
    Unverifiable,

    /// Claim contradicts dialogue history
    HistoryConflict { conflicting_turn: TurnId },

    /// Unable to validate
    Error { reason: String },
}

impl FactValidator {
    /// Validate facts in response
    pub fn validate(
        &self,
        response: &str,
        knowledge_base: &KnowledgeBase,
        dialogue_state: &DialogueState,
    ) -> Result<FactualValidationResult, FactValidationError> {
        // Step 1: Extract claims
        let claims = self.claim_extractor.extract(response)?;

        // Step 2 & 3: Validate each claim
        let mut claim_validations = Vec::new();
        for claim in &claims {
            let validation = self.validate_claim(claim, knowledge_base, dialogue_state)?;
            claim_validations.push(validation);
        }

        // Calculate statistics
        let stats = self.calculate_stats(&claim_validations);

        // Calculate overall score
        let score = if stats.claims_checked == 0 {
            1.0  // No claims to validate = neutral
        } else {
            stats.claims_verified as f64 / stats.claims_checked as f64
        };

        Ok(FactualValidationResult {
            score,
            claims,
            claim_validations,
            stats,
        })
    }

    /// Validate a single claim
    fn validate_claim(
        &self,
        claim: &Claim,
        knowledge_base: &KnowledgeBase,
        dialogue_state: &DialogueState,
    ) -> Result<ClaimValidation, FactValidationError> {
        // Try KB lookup first
        let kb_result = self.lookup_in_kb(claim, knowledge_base)?;

        match kb_result {
            Some(evidence) => {
                if evidence.matches {
                    Ok(ClaimValidation {
                        claim: claim.clone(),
                        status: ValidationStatus::Verified {
                            confidence: evidence.confidence,
                        },
                        kb_evidence: Some(evidence),
                        history_evidence: None,
                        suggestion: None,
                    })
                } else {
                    Ok(ClaimValidation {
                        claim: claim.clone(),
                        status: ValidationStatus::Contradicted {
                            kb_value: evidence.kb_value.clone(),
                            confidence: evidence.confidence,
                        },
                        kb_evidence: Some(evidence.clone()),
                        history_evidence: None,
                        suggestion: Some(format!(
                            "Replace '{}' with '{}'",
                            claim.object, evidence.kb_value
                        )),
                    })
                }
            }
            None => {
                // Check dialogue history
                let history_result = self.history_checker.check(claim, dialogue_state)?;

                if let Some(conflict) = history_result {
                    Ok(ClaimValidation {
                        claim: claim.clone(),
                        status: ValidationStatus::HistoryConflict {
                            conflicting_turn: conflict.turn_id,
                        },
                        kb_evidence: None,
                        history_evidence: Some(conflict),
                        suggestion: None,
                    })
                } else {
                    Ok(ClaimValidation {
                        claim: claim.clone(),
                        status: ValidationStatus::Unverifiable,
                        kb_evidence: None,
                        history_evidence: None,
                        suggestion: None,
                    })
                }
            }
        }
    }

    /// Look up claim in knowledge base
    fn lookup_in_kb(
        &self,
        claim: &Claim,
        knowledge_base: &KnowledgeBase,
    ) -> Result<Option<KBEvidence>, FactValidationError> {
        // Find entity by subject
        let entity = knowledge_base.find_entity(&claim.subject)?;

        if let Some(entity) = entity {
            // Look up attribute
            let attribute = entity.get_attribute(&claim.predicate)?;

            if let Some(attr_value) = attribute {
                // Compare values
                let matches = self.compare_values(&claim.object, &attr_value.value);

                return Ok(Some(KBEvidence {
                    entity_id: entity.id,
                    attribute: claim.predicate.clone(),
                    kb_value: attr_value.value.clone(),
                    claimed_value: claim.object.clone(),
                    matches,
                    confidence: attr_value.confidence,
                }));
            }
        }

        Ok(None)
    }

    /// Compare claimed value with KB value
    fn compare_values(&self, claimed: &str, kb_value: &str) -> bool {
        // Exact match
        if claimed.eq_ignore_ascii_case(kb_value) {
            return true;
        }

        // Normalize and compare
        let claimed_normalized = self.normalize_value(claimed);
        let kb_normalized = self.normalize_value(kb_value);

        if claimed_normalized == kb_normalized {
            return true;
        }

        // Fuzzy match for minor variations
        let distance = edit_distance(&claimed_normalized, &kb_normalized);
        let max_len = claimed_normalized.len().max(kb_normalized.len());

        if max_len > 0 && distance as f64 / max_len as f64 < 0.1 {
            return true;
        }

        false
    }
}
```

---

## Response Correction

Response correction applies fixes to issues identified in earlier stages.

### Correction Types

```rust
/// Response correction system
pub struct ResponseCorrector {
    /// Grammar corrector (three-tier WFST)
    grammar_corrector: CorrectionEngine,

    /// Factual corrector
    factual_corrector: FactualCorrector,

    /// Annotation inserter
    annotation_inserter: AnnotationInserter,

    /// Configuration
    config: ResponseCorrectorConfig,
}

/// Types of response corrections
pub enum ResponseCorrectionType {
    /// Grammar/spelling correction
    Grammar {
        original: String,
        corrected: String,
    },

    /// Factual correction (replace incorrect fact)
    Factual {
        original: String,
        corrected: String,
        source: String,
    },

    /// Add annotation/flag without changing text
    Annotation {
        span: Range<usize>,
        annotation_type: AnnotationType,
        message: String,
    },

    /// Remove content (usually for severe issues)
    Removal {
        span: Range<usize>,
        reason: String,
    },
}

/// Annotation types for flagging
pub enum AnnotationType {
    /// Unverified claim
    Unverified,

    /// Potentially incorrect
    Uncertain,

    /// Hallucination warning
    PossibleHallucination,

    /// Information from external source
    ExternalSource,

    /// User should verify
    NeedsVerification,
}

impl ResponseCorrector {
    /// Apply corrections to response
    pub fn correct(
        &self,
        response: &str,
        coherence: &CoherenceResult,
        factual: &FactualValidationResult,
        hallucinations: &[HallucinationFlag],
    ) -> Result<CorrectedResponse, CorrectionError> {
        let mut corrections = Vec::new();
        let mut current = response.to_string();

        // 1. Apply grammar corrections
        let grammar_result = self.grammar_corrector.correct(&current)?;
        for correction in grammar_result.corrections {
            corrections.push(ResponseCorrection {
                correction_type: ResponseCorrectionType::Grammar {
                    original: correction.original.clone(),
                    corrected: correction.corrected.clone(),
                },
                span: correction.original_span.clone(),
                confidence: correction.confidence,
            });
        }
        current = grammar_result.corrected_text;

        // 2. Apply factual corrections
        for validation in &factual.claim_validations {
            if let ValidationStatus::Contradicted { kb_value, confidence } = &validation.status {
                if *confidence >= self.config.factual_correction_threshold {
                    if let Some(suggestion) = &validation.suggestion {
                        corrections.push(ResponseCorrection {
                            correction_type: ResponseCorrectionType::Factual {
                                original: validation.claim.object.clone(),
                                corrected: kb_value.clone(),
                                source: "Knowledge Base".to_string(),
                            },
                            span: validation.claim.span.clone(),
                            confidence: *confidence,
                        });

                        // Apply the correction
                        current = self.apply_text_correction(
                            &current,
                            &validation.claim.span,
                            kb_value,
                        )?;
                    }
                }
            }
        }

        // 3. Add annotations for hallucinations
        for flag in hallucinations {
            if flag.confidence >= self.config.hallucination_annotation_threshold {
                corrections.push(ResponseCorrection {
                    correction_type: ResponseCorrectionType::Annotation {
                        span: flag.span.clone(),
                        annotation_type: AnnotationType::PossibleHallucination,
                        message: format!(
                            "Potential hallucination: {}",
                            flag.hallucination_type
                        ),
                    },
                    span: flag.span.clone(),
                    confidence: flag.confidence,
                });
            }
        }

        // 4. Add annotations for unverifiable claims
        for validation in &factual.claim_validations {
            if let ValidationStatus::Unverifiable = validation.status {
                corrections.push(ResponseCorrection {
                    correction_type: ResponseCorrectionType::Annotation {
                        span: validation.claim.span.clone(),
                        annotation_type: AnnotationType::Unverified,
                        message: "Claim could not be verified".to_string(),
                    },
                    span: validation.claim.span.clone(),
                    confidence: 0.5,
                });
            }
        }

        // Generate annotated version
        let annotated = self.annotation_inserter.insert(
            &current,
            &corrections,
        )?;

        Ok(CorrectedResponse {
            original: response.to_string(),
            corrected: current,
            annotated,
            corrections,
        })
    }
}
```

---

## Confidence Scoring

Confidence scoring aggregates results from all checks into an overall score.

### Scoring Model

```rust
/// Confidence scoring system
pub struct ConfidenceScorer {
    /// Weights for different factors
    weights: ConfidenceWeights,

    /// Configuration
    config: ConfidenceScorerConfig,
}

/// Weights for confidence calculation
pub struct ConfidenceWeights {
    /// Weight for coherence score
    pub coherence: f64,

    /// Weight for factual accuracy
    pub factual: f64,

    /// Weight for hallucination absence
    pub hallucination: f64,

    /// Weight for entity consistency
    pub entity: f64,
}

impl Default for ConfidenceWeights {
    fn default() -> Self {
        Self {
            coherence: 0.25,
            factual: 0.35,
            hallucination: 0.30,
            entity: 0.10,
        }
    }
}

impl ConfidenceScorer {
    /// Calculate overall confidence score
    pub fn score(
        &self,
        coherence: &CoherenceResult,
        factual: &FactualValidationResult,
        hallucinations: &[HallucinationFlag],
    ) -> f64 {
        // Coherence component
        let coherence_score = coherence.score;

        // Factual component
        let factual_score = factual.score;

        // Hallucination component (inverse - fewer hallucinations = higher score)
        let hallucination_score = self.calculate_hallucination_score(hallucinations);

        // Entity component
        let entity_score = coherence.entity_consistency.score;

        // Weighted average
        let raw_score = self.weights.coherence * coherence_score
            + self.weights.factual * factual_score
            + self.weights.hallucination * hallucination_score
            + self.weights.entity * entity_score;

        // Apply severity penalties
        let penalty = self.calculate_severity_penalty(
            coherence,
            factual,
            hallucinations,
        );

        (raw_score - penalty).clamp(0.0, 1.0)
    }

    /// Calculate hallucination score (inverse)
    fn calculate_hallucination_score(&self, hallucinations: &[HallucinationFlag]) -> f64 {
        if hallucinations.is_empty() {
            return 1.0;
        }

        // Weight by confidence and severity
        let total_severity: f64 = hallucinations
            .iter()
            .map(|h| h.confidence * self.get_hallucination_severity(&h.hallucination_type))
            .sum();

        // Normalize and invert
        let normalized = (total_severity / hallucinations.len() as f64).min(1.0);
        1.0 - normalized
    }

    /// Get severity weight for hallucination type
    fn get_hallucination_severity(&self, hall_type: &HallucinationType) -> f64 {
        match hall_type {
            HallucinationType::FabricatedFact => 1.0,
            HallucinationType::NonexistentEntity => 0.9,
            HallucinationType::WrongAttribute => 0.8,
            HallucinationType::ContradictsFact => 1.0,
            HallucinationType::ContradictsPrior => 0.85,
            HallucinationType::UnsupportedClaim => 0.5,
            HallucinationType::TemporalError => 0.7,
            HallucinationType::LogicalInconsistency => 0.6,
        }
    }

    /// Calculate penalty for severe issues
    fn calculate_severity_penalty(
        &self,
        coherence: &CoherenceResult,
        factual: &FactualValidationResult,
        hallucinations: &[HallucinationFlag],
    ) -> f64 {
        let mut penalty = 0.0;

        // Critical coherence issues
        for issue in &coherence.issues {
            if issue.severity > 0.8 {
                penalty += 0.1;
            }
        }

        // High-confidence contradictions
        for validation in &factual.claim_validations {
            if let ValidationStatus::Contradicted { confidence, .. } = &validation.status {
                if *confidence > 0.9 {
                    penalty += 0.15;
                }
            }
        }

        // High-confidence hallucinations
        for hall in hallucinations {
            if hall.confidence > 0.85 {
                penalty += 0.1;
            }
        }

        penalty.min(0.5)  // Cap penalty at 50%
    }
}
```

---

## Handling Recommendations

Based on confidence score, the system recommends how to handle the response.

### Decision Tree

```
┌────────────────────────────────────────────────────────────────────────┐
│                    RESPONSE HANDLING DECISION TREE                      │
├────────────────────────────────────────────────────────────────────────┤
│                                                                         │
│  Confidence Score                                                       │
│        │                                                                │
│        ▼                                                                │
│  ┌─────────────────────────────────────────────────────────────────┐   │
│  │            ≥ 0.90                                               │   │
│  │                                                                 │   │
│  │   ACCEPT                                                        │   │
│  │   Deliver response as-is                                        │   │
│  │   No modifications needed                                       │   │
│  └─────────────────────────────────────────────────────────────────┘   │
│        │                                                                │
│        ▼ < 0.90                                                         │
│  ┌─────────────────────────────────────────────────────────────────┐   │
│  │            ≥ 0.75                                               │   │
│  │                                                                 │   │
│  │   ACCEPT WITH FLAGS                                             │   │
│  │   Deliver response with annotations                             │   │
│  │   Flag uncertain/unverified parts                               │   │
│  │                                                                 │   │
│  │   Example: "John's email is john@co.com [unverified]"          │   │
│  └─────────────────────────────────────────────────────────────────┘   │
│        │                                                                │
│        ▼ < 0.75                                                         │
│  ┌─────────────────────────────────────────────────────────────────┐   │
│  │            ≥ 0.50                                               │   │
│  │                                                                 │   │
│  │   CORRECT AND DELIVER                                           │   │
│  │   Apply factual corrections                                     │   │
│  │   Fix identified issues                                         │   │
│  │   Deliver corrected version                                     │   │
│  │                                                                 │   │
│  │   Example: "john@co.com" → "john.smith@company.com"            │   │
│  └─────────────────────────────────────────────────────────────────┘   │
│        │                                                                │
│        ▼ < 0.50                                                         │
│  ┌─────────────────────────────────────────────────────────────────┐   │
│  │            ≥ 0.30                                               │   │
│  │                                                                 │   │
│  │   REGENERATE                                                    │   │
│  │   Request new response from LLM                                 │   │
│  │   Provide guidance based on issues                              │   │
│  │                                                                 │   │
│  │   Guidance: "Verify John's email address. Check that           │   │
│  │   department matches Engineering, not Marketing."               │   │
│  └─────────────────────────────────────────────────────────────────┘   │
│        │                                                                │
│        ▼ < 0.30                                                         │
│  ┌─────────────────────────────────────────────────────────────────┐   │
│  │                                                                 │   │
│  │   HUMAN REVIEW                                                  │   │
│  │   Escalate to human operator                                    │   │
│  │   Response too unreliable for automatic handling               │   │
│  │                                                                 │   │
│  │   Reason: "Multiple high-confidence hallucinations detected.   │   │
│  │   Response contradicts 3 known facts and dialogue history."    │   │
│  └─────────────────────────────────────────────────────────────────┘   │
│                                                                         │
└────────────────────────────────────────────────────────────────────────┘
```

### Recommendation Implementation

```rust
impl ResponsePostprocessor {
    /// Determine handling recommendation
    fn determine_recommendation(
        &self,
        confidence: f64,
        coherence: &CoherenceResult,
        factual: &FactualValidationResult,
        hallucinations: &[HallucinationFlag],
    ) -> ResponseRecommendation {
        let thresholds = &self.config.handling_thresholds;

        if confidence >= thresholds.accept_threshold {
            ResponseRecommendation::Accept
        } else if confidence >= thresholds.flag_threshold {
            // Collect spans to flag
            let mut flags = Vec::new();

            // Flag unverified claims
            for validation in &factual.claim_validations {
                if matches!(validation.status, ValidationStatus::Unverifiable) {
                    flags.push(validation.claim.span.clone());
                }
            }

            // Flag low-confidence hallucinations
            for hall in hallucinations {
                if hall.confidence >= 0.5 && hall.confidence < 0.8 {
                    flags.push(hall.span.clone());
                }
            }

            let severity = if flags.len() > 3 {
                Severity::Medium
            } else {
                Severity::Low
            };

            ResponseRecommendation::AcceptWithFlags { flags, severity }
        } else if confidence >= thresholds.correct_threshold {
            // Collect corrections to apply
            let mut corrections = Vec::new();

            // Add factual corrections
            for validation in &factual.claim_validations {
                if let ValidationStatus::Contradicted { kb_value, .. } = &validation.status {
                    corrections.push(ResponseCorrection {
                        correction_type: ResponseCorrectionType::Factual {
                            original: validation.claim.object.clone(),
                            corrected: kb_value.clone(),
                            source: "Knowledge Base".to_string(),
                        },
                        span: validation.claim.span.clone(),
                        confidence: 0.9,
                    });
                }
            }

            ResponseRecommendation::CorrectAndDeliver { corrections }
        } else if confidence >= thresholds.regenerate_threshold {
            // Generate guidance for regeneration
            let guidance = self.generate_regeneration_guidance(
                coherence,
                factual,
                hallucinations,
            );

            ResponseRecommendation::Regenerate { guidance }
        } else {
            // Generate reason for human review
            let reason = self.generate_human_review_reason(
                confidence,
                coherence,
                factual,
                hallucinations,
            );

            ResponseRecommendation::HumanReview { reason }
        }
    }

    /// Generate guidance for LLM regeneration
    fn generate_regeneration_guidance(
        &self,
        coherence: &CoherenceResult,
        factual: &FactualValidationResult,
        hallucinations: &[HallucinationFlag],
    ) -> String {
        let mut guidance_parts = Vec::new();

        // Address QUD issues
        if !coherence.qud_relevance.addresses_qud {
            guidance_parts.push(
                "Please directly address the user's question.".to_string()
            );
        }

        // Address factual issues
        for validation in &factual.claim_validations {
            if let ValidationStatus::Contradicted { kb_value, .. } = &validation.status {
                guidance_parts.push(format!(
                    "For {}'s {}, the correct value is '{}'.",
                    validation.claim.subject,
                    validation.claim.predicate,
                    kb_value
                ));
            }
        }

        // Address hallucinations
        for hall in hallucinations.iter().filter(|h| h.confidence >= 0.7) {
            guidance_parts.push(format!(
                "Please verify or remove: '{}'.",
                hall.content
            ));
        }

        guidance_parts.join(" ")
    }

    /// Generate reason for human review
    fn generate_human_review_reason(
        &self,
        confidence: f64,
        coherence: &CoherenceResult,
        factual: &FactualValidationResult,
        hallucinations: &[HallucinationFlag],
    ) -> String {
        let mut reasons = Vec::new();

        reasons.push(format!(
            "Overall confidence too low: {:.0}%",
            confidence * 100.0
        ));

        if coherence.score < 0.4 {
            reasons.push(format!(
                "Severe coherence issues ({} problems found)",
                coherence.issues.len()
            ));
        }

        if factual.stats.claims_contradicted > 0 {
            reasons.push(format!(
                "{} factual contradictions detected",
                factual.stats.claims_contradicted
            ));
        }

        let high_conf_halls: Vec<_> = hallucinations
            .iter()
            .filter(|h| h.confidence >= 0.8)
            .collect();

        if !high_conf_halls.is_empty() {
            reasons.push(format!(
                "{} high-confidence hallucinations",
                high_conf_halls.len()
            ));
        }

        reasons.join(". ")
    }
}
```

---

## Implementation

### Full Pipeline Example

```rust
/// Example: Full postprocessing pipeline execution
pub async fn postprocess_llm_response(
    llm_response: &str,
    session: &Session,
    original_query: &str,
) -> Result<PostprocessedResponse, Error> {
    // Initialize pipeline
    let postprocessor = ResponsePostprocessor::new(
        session.coherence_checker.clone(),
        session.fact_validator.clone(),
        session.hallucination_detector.clone(),
        session.response_corrector.clone(),
        session.confidence_scorer.clone(),
        PostprocessorConfig::default(),
    );

    // Get current dialogue state
    let dialogue_state = session.dialogue_state.read().await;

    // Get knowledge base
    let knowledge_base = session.knowledge_base.read().await;

    // Run postprocessing
    let result = postprocessor.postprocess(
        llm_response,
        &dialogue_state,
        &knowledge_base,
        original_query,
    )?;

    // Log postprocessing metrics
    tracing::info!(
        confidence = result.confidence,
        coherence = result.coherence.score,
        factual = result.factual_validation.score,
        hallucinations = result.hallucination_flags.len(),
        recommendation = ?result.recommendation,
        "Response postprocessing complete"
    );

    // Handle based on recommendation
    match &result.recommendation {
        ResponseRecommendation::Accept => {
            tracing::debug!("Response accepted");
        }
        ResponseRecommendation::AcceptWithFlags { flags, severity } => {
            tracing::info!(
                flags = flags.len(),
                ?severity,
                "Response accepted with flags"
            );
        }
        ResponseRecommendation::CorrectAndDeliver { corrections } => {
            tracing::info!(
                corrections = corrections.len(),
                "Response corrected before delivery"
            );
        }
        ResponseRecommendation::Regenerate { guidance } => {
            tracing::warn!(
                guidance = %guidance,
                "Requesting response regeneration"
            );
        }
        ResponseRecommendation::HumanReview { reason } => {
            tracing::error!(
                reason = %reason,
                "Response escalated for human review"
            );
        }
    }

    Ok(result)
}
```

---

## MeTTa Predicates

```metta
; Core postprocessing predicates
(: postprocess-response (-> String DialogueState KnowledgeBase String PostprocessedResponse))
(: check-coherence (-> String DialogueState String CoherenceResult))
(: validate-facts (-> String KnowledgeBase DialogueState FactualValidationResult))
(: correct-response (-> String CoherenceResult FactualValidationResult (List HallucinationFlag) CorrectedResponse))
(: score-confidence (-> CoherenceResult FactualValidationResult (List HallucinationFlag) Float))
(: determine-recommendation (-> Float CoherenceResult FactualValidationResult (List HallucinationFlag) ResponseRecommendation))

; Coherence checking predicates
(: check-qud-relevance (-> String String (List QUD) QUDRelevanceResult))
(: check-topic-consistency (-> String TopicGraph TopicConsistencyResult))
(: check-entity-consistency (-> String EntityRegistry EntityConsistencyResult))
(: check-discourse-coherence (-> String (List Turn) DiscourseCoherenceResult))
(: check-reference-consistency (-> String DialogueState ReferenceConsistencyResult))

; Fact validation predicates
(: extract-claims (-> String (List Claim)))
(: lookup-claim-in-kb (-> Claim KnowledgeBase (Maybe KBEvidence)))
(: check-claim-in-history (-> Claim DialogueState (Maybe HistoryEvidence)))
(: validate-claim (-> Claim KnowledgeBase DialogueState ClaimValidation))

; Correction predicates
(: apply-grammar-correction (-> String CorrectedResponse))
(: apply-factual-correction (-> String (List ClaimValidation) CorrectedResponse))
(: insert-annotations (-> String (List ResponseCorrection) String))

; Confidence predicates
(: calculate-coherence-weight (-> CoherenceResult Float))
(: calculate-factual-weight (-> FactualValidationResult Float))
(: calculate-hallucination-weight (-> (List HallucinationFlag) Float))
(: apply-severity-penalty (-> CoherenceResult FactualValidationResult (List HallucinationFlag) Float))

; Recommendation predicates
(: should-accept (-> Float Bool))
(: should-flag (-> Float Bool))
(: should-correct (-> Float Bool))
(: should-regenerate (-> Float Bool))
(: generate-guidance (-> CoherenceResult FactualValidationResult (List HallucinationFlag) String))
```

---

## PathMap Schema

```
PathMap Key Structure:
=======================

/postprocessing/{session_id}/{turn_id}/
    /input/
        llm_response        → Raw LLM response
        query               → Original user query

    /coherence/
        score               → Overall coherence score
        /qud/
            score           → QUD relevance score
            addresses_qud   → Boolean
            question_type   → Question type classification
        /topic/
            score           → Topic consistency score
            drift_detected  → Boolean
        /entity/
            score           → Entity consistency score
            mismatches      → Count of mismatches
        /discourse/
            score           → Discourse coherence score
        /reference/
            score           → Reference consistency score
        /issues/
            count           → Number of issues
            /{issue_idx}/   → Issue details

    /factual/
        score               → Factual accuracy score
        claims_checked      → Number of claims
        claims_verified     → Number verified
        claims_contradicted → Number contradicted
        claims_unverifiable → Number unverifiable
        /claims/
            /{claim_idx}/
                type        → Claim type
                subject     → Subject entity
                predicate   → Predicate/relation
                object      → Object/value
                status      → Validation status
                kb_value    → KB value (if found)
                suggestion  → Correction suggestion

    /hallucinations/
        count               → Number of flags
        /{flag_idx}/
            span_start      → Start position
            span_end        → End position
            content         → Flagged content
            type            → Hallucination type
            confidence      → Detection confidence
            suggestion      → Correction suggestion

    /correction/
        applied             → Whether corrections applied
        correction_count    → Number of corrections
        /corrections/
            /{correction_idx}/
                type        → Correction type
                original    → Original text
                corrected   → Corrected text
                confidence  → Correction confidence

    /result/
        confidence          → Overall confidence score
        recommendation      → Handling recommendation
        corrected_response  → Corrected response (if any)
        annotated_response  → Annotated response
        new_entities_count  → New entities found
```

---

## Related Documentation

- [LLM Integration Overview](./README.md) - Layer architecture
- [Prompt Preprocessing](./01-prompt-preprocessing.md) - Input preparation
- [Hallucination Detection](./03-hallucination-detection.md) - Detection algorithms
- [Context Injection](./04-context-injection.md) - RAG and history
- [Dialogue Context](../dialogue/README.md) - Turn and entity tracking
- [Discourse Semantics](../dialogue/01-discourse-semantics.md) - Coherence relations

---

## References

- Ji, Z. et al. (2023). "Survey of Hallucination in Natural Language Generation"
- Maynez, J. et al. (2020). "On Faithfulness and Factuality in Abstractive Summarization"
- Kryscinski, W. et al. (2020). "Evaluating the Factual Consistency of Abstractive Text"
- Rashkin, H. et al. (2021). "Measuring Attribution in Natural Language Generation Models"
- Durmus, E. et al. (2020). "FEQA: A Question Answering Evaluation Framework"
