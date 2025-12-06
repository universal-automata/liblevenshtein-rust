# Hallucination Detection

This document details the hallucination detection system that identifies fabricated
facts, nonexistent entities, and unsupported claims in LLM-generated responses.

**Sources**:
- Plan: Part V - Dialogue Context and LLM Agent Correction Extension
- Dialogue Layer: `../dialogue/`
- PathMap: `/home/dylon/Workspace/f1r3fly.io/PathMap/`
- MORK: `/home/dylon/Workspace/f1r3fly.io/MORK/`

---

## Table of Contents

1. [Overview](#overview)
2. [Hallucination Taxonomy](#hallucination-taxonomy)
3. [Detection Architecture](#detection-architecture)
4. [Detection Methods](#detection-methods)
5. [Confidence Scoring](#confidence-scoring)
6. [Mitigation Strategies](#mitigation-strategies)
7. [Implementation](#implementation)
8. [MeTTa Predicates](#metta-predicates)
9. [PathMap Schema](#pathmap-schema)

---

## Overview

Hallucination detection identifies content that the LLM has fabricated rather than
generated based on factual knowledge or context. This is critical for maintaining
trust and accuracy in conversational AI agents.

### What is a Hallucination?

A hallucination occurs when an LLM generates content that:
- **Is factually incorrect** - contradicts known facts
- **Refers to nonexistent entities** - makes up people, places, events
- **Claims unsupported assertions** - states things without basis
- **Contradicts the conversation** - conflicts with prior dialogue
- **Exhibits logical inconsistency** - contains internal contradictions

```
┌─────────────────────────────────────────────────────────────────────────┐
│                    HALLUCINATION DETECTION OVERVIEW                      │
│                                                                          │
│  LLM Response                                                            │
│       │                                                                  │
│       ▼                                                                  │
│  ┌────────────────────────────────────────────────────────────────────┐ │
│  │ DETECTION PIPELINE                                                 │ │
│  │                                                                    │ │
│  │  ┌─────────────────────────────────────────────────────────────┐  │ │
│  │  │ 1. Segment Response                                         │  │ │
│  │  │    Split into analyzable claims and statements              │  │ │
│  │  └─────────────────────────────────────────────────────────────┘  │ │
│  │                         │                                         │ │
│  │                         ▼                                         │ │
│  │  ┌─────────────────────────────────────────────────────────────┐  │ │
│  │  │ 2. Apply Detection Methods                                  │  │ │
│  │  │    • KB Verification    • Entity Existence                 │  │ │
│  │  │    • History Check      • Consistency Analysis             │  │ │
│  │  │    • Self-Contradiction • Uncertainty Signals              │  │ │
│  │  └─────────────────────────────────────────────────────────────┘  │ │
│  │                         │                                         │ │
│  │                         ▼                                         │ │
│  │  ┌─────────────────────────────────────────────────────────────┐  │ │
│  │  │ 3. Score and Aggregate                                      │  │ │
│  │  │    Calculate confidence for each potential hallucination    │  │ │
│  │  └─────────────────────────────────────────────────────────────┘  │ │
│  │                         │                                         │ │
│  │                         ▼                                         │ │
│  │  ┌─────────────────────────────────────────────────────────────┐  │ │
│  │  │ 4. Generate Flags                                           │  │ │
│  │  │    Create actionable hallucination flags                    │  │ │
│  │  └─────────────────────────────────────────────────────────────┘  │ │
│  │                                                                    │ │
│  └───────────────────────────────────────────────────────────────────┘ │
│                              │                                          │
│                              ▼                                          │
│                  List<HallucinationFlag>                                │
│                                                                          │
└─────────────────────────────────────────────────────────────────────────┘
```

---

## Hallucination Taxonomy

### Types of Hallucinations

```
┌─────────────────────────────────────────────────────────────────────────┐
│                      HALLUCINATION TAXONOMY                              │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                          │
│  ┌────────────────────────────────────────────────────────────────────┐ │
│  │ TYPE 1: FABRICATED FACTS                                           │ │
│  │ ━━━━━━━━━━━━━━━━━━━━━━━━━                                          │ │
│  │                                                                    │ │
│  │ Making up factual claims that don't exist in knowledge base        │ │
│  │                                                                    │ │
│  │ Example: "The company was founded in 1847 by James Roberts."       │ │
│  │          (When no such founding date or founder exists in KB)      │ │
│  │                                                                    │ │
│  │ Severity: HIGH                                                     │ │
│  │ Detection: KB lookup, fact verification                            │ │
│  └────────────────────────────────────────────────────────────────────┘ │
│                                                                          │
│  ┌────────────────────────────────────────────────────────────────────┐ │
│  │ TYPE 2: NONEXISTENT ENTITIES                                       │ │
│  │ ━━━━━━━━━━━━━━━━━━━━━━━━━━━                                        │ │
│  │                                                                    │ │
│  │ Referencing people, places, or things that don't exist             │ │
│  │                                                                    │ │
│  │ Example: "You should contact Sarah from the Analytics team."       │ │
│  │          (When no Sarah exists in Analytics)                       │ │
│  │                                                                    │ │
│  │ Severity: HIGH                                                     │ │
│  │ Detection: Entity registry lookup, name verification               │ │
│  └────────────────────────────────────────────────────────────────────┘ │
│                                                                          │
│  ┌────────────────────────────────────────────────────────────────────┐ │
│  │ TYPE 3: WRONG ATTRIBUTES                                           │ │
│  │ ━━━━━━━━━━━━━━━━━━━━━━━━━                                          │ │
│  │                                                                    │ │
│  │ Correct entity with incorrect attributes                           │ │
│  │                                                                    │ │
│  │ Example: "John Smith works in the Marketing department."           │ │
│  │          (When John actually works in Engineering)                 │ │
│  │                                                                    │ │
│  │ Severity: MEDIUM-HIGH                                              │ │
│  │ Detection: Attribute verification against KB                       │ │
│  └────────────────────────────────────────────────────────────────────┘ │
│                                                                          │
│  ┌────────────────────────────────────────────────────────────────────┐ │
│  │ TYPE 4: CONTRADICTS KNOWN FACTS                                    │ │
│  │ ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━                                      │ │
│  │                                                                    │ │
│  │ Statement directly contradicts verified knowledge                  │ │
│  │                                                                    │ │
│  │ Example: "The meeting is scheduled for Tuesday."                   │ │
│  │          (When KB shows meeting is on Wednesday)                   │ │
│  │                                                                    │ │
│  │ Severity: HIGH                                                     │ │
│  │ Detection: Direct KB contradiction check                           │ │
│  └────────────────────────────────────────────────────────────────────┘ │
│                                                                          │
│  ┌────────────────────────────────────────────────────────────────────┐ │
│  │ TYPE 5: CONTRADICTS PRIOR DIALOGUE                                 │ │
│  │ ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━                                  │ │
│  │                                                                    │ │
│  │ Statement contradicts something established earlier in conversation │ │
│  │                                                                    │ │
│  │ Example: Turn 3: "I'll book the meeting for Monday."               │ │
│  │          Turn 7: "As I mentioned, the meeting is on Friday."       │ │
│  │                                                                    │ │
│  │ Severity: MEDIUM-HIGH                                              │ │
│  │ Detection: Dialogue history contradiction analysis                 │ │
│  └────────────────────────────────────────────────────────────────────┘ │
│                                                                          │
│  ┌────────────────────────────────────────────────────────────────────┐ │
│  │ TYPE 6: UNSUPPORTED CLAIMS                                         │ │
│  │ ━━━━━━━━━━━━━━━━━━━━━━━━━                                          │ │
│  │                                                                    │ │
│  │ Making assertions without factual basis                            │ │
│  │                                                                    │ │
│  │ Example: "Studies show that this approach increases productivity   │ │
│  │          by 40%." (No source, no studies in KB)                    │ │
│  │                                                                    │ │
│  │ Severity: MEDIUM                                                   │ │
│  │ Detection: Source verification, evidence check                     │ │
│  └────────────────────────────────────────────────────────────────────┘ │
│                                                                          │
│  ┌────────────────────────────────────────────────────────────────────┐ │
│  │ TYPE 7: TEMPORAL ERRORS                                            │ │
│  │ ━━━━━━━━━━━━━━━━━━━━━━━━━                                          │ │
│  │                                                                    │ │
│  │ Incorrect temporal relationships or impossible timelines           │ │
│  │                                                                    │ │
│  │ Example: "The project was completed before it started."            │ │
│  │          "The event happened last year in 2026."                   │ │
│  │                                                                    │ │
│  │ Severity: MEDIUM                                                   │ │
│  │ Detection: Temporal consistency analysis                           │ │
│  └────────────────────────────────────────────────────────────────────┘ │
│                                                                          │
│  ┌────────────────────────────────────────────────────────────────────┐ │
│  │ TYPE 8: LOGICAL INCONSISTENCY                                      │ │
│  │ ━━━━━━━━━━━━━━━━━━━━━━━━━━━                                        │ │
│  │                                                                    │ │
│  │ Self-contradictory statements within the same response             │ │
│  │                                                                    │ │
│  │ Example: "The system is both running and not running."             │ │
│  │          "All items were shipped, except for the 3 that weren't."  │ │
│  │                                                                    │ │
│  │ Severity: MEDIUM                                                   │ │
│  │ Detection: Logical consistency analysis                            │ │
│  └────────────────────────────────────────────────────────────────────┘ │
│                                                                          │
└─────────────────────────────────────────────────────────────────────────┘
```

### Rust Type Definition

```rust
/// Types of hallucination
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum HallucinationType {
    /// Made-up fact not in knowledge base
    FabricatedFact,

    /// Reference to non-existent entity
    NonexistentEntity,

    /// Incorrect attribute of known entity
    WrongAttribute,

    /// Contradicts known fact in KB
    ContradictsFact,

    /// Contradicts earlier dialogue turn
    ContradictsPrior,

    /// Claim without supporting evidence
    UnsupportedClaim,

    /// Temporal inconsistency
    TemporalError,

    /// Logical inconsistency within response
    LogicalInconsistency,
}

impl HallucinationType {
    /// Get base severity for this hallucination type
    pub fn base_severity(&self) -> f64 {
        match self {
            Self::FabricatedFact => 0.95,
            Self::NonexistentEntity => 0.90,
            Self::WrongAttribute => 0.75,
            Self::ContradictsFact => 0.95,
            Self::ContradictsPrior => 0.80,
            Self::UnsupportedClaim => 0.50,
            Self::TemporalError => 0.65,
            Self::LogicalInconsistency => 0.60,
        }
    }

    /// Description for user-facing messages
    pub fn description(&self) -> &str {
        match self {
            Self::FabricatedFact => "This fact could not be verified",
            Self::NonexistentEntity => "This entity could not be found",
            Self::WrongAttribute => "This attribute appears incorrect",
            Self::ContradictsFact => "This contradicts known information",
            Self::ContradictsPrior => "This contradicts earlier in the conversation",
            Self::UnsupportedClaim => "This claim has no supporting evidence",
            Self::TemporalError => "The timeline appears incorrect",
            Self::LogicalInconsistency => "This contains a logical contradiction",
        }
    }
}
```

---

## Detection Architecture

### Core Components

```rust
/// Main hallucination detection system
pub struct HallucinationDetector {
    /// Fabricated fact detector
    fact_detector: FabricatedFactDetector,

    /// Entity existence checker
    entity_checker: EntityExistenceChecker,

    /// Attribute verifier
    attribute_verifier: AttributeVerifier,

    /// KB contradiction detector
    kb_contradiction_detector: KBContradictionDetector,

    /// Dialogue history contradiction detector
    history_contradiction_detector: HistoryContradictionDetector,

    /// Unsupported claim detector
    claim_detector: UnsupportedClaimDetector,

    /// Temporal consistency checker
    temporal_checker: TemporalConsistencyChecker,

    /// Logical consistency checker
    logical_checker: LogicalConsistencyChecker,

    /// Configuration
    config: HallucinationDetectorConfig,
}

/// Detection configuration
pub struct HallucinationDetectorConfig {
    /// Minimum confidence to flag as hallucination
    pub detection_threshold: f64,

    /// Enable each detector type
    pub enabled_detectors: EnabledDetectors,

    /// Weight for each detector in combined scoring
    pub detector_weights: DetectorWeights,

    /// Maximum claims to analyze per response
    pub max_claims: usize,
}

/// Flags for which detectors to enable
pub struct EnabledDetectors {
    pub fabricated_facts: bool,
    pub nonexistent_entities: bool,
    pub wrong_attributes: bool,
    pub kb_contradictions: bool,
    pub history_contradictions: bool,
    pub unsupported_claims: bool,
    pub temporal_errors: bool,
    pub logical_inconsistencies: bool,
}

impl Default for EnabledDetectors {
    fn default() -> Self {
        Self {
            fabricated_facts: true,
            nonexistent_entities: true,
            wrong_attributes: true,
            kb_contradictions: true,
            history_contradictions: true,
            unsupported_claims: true,
            temporal_errors: true,
            logical_inconsistencies: true,
        }
    }
}
```

### Detection Pipeline

```rust
impl HallucinationDetector {
    /// Detect hallucinations in LLM response
    pub fn detect(
        &self,
        response: &str,
        dialogue_state: &DialogueState,
        knowledge_base: &KnowledgeBase,
    ) -> Result<Vec<HallucinationFlag>, HallucinationError> {
        let mut all_flags = Vec::new();

        // Segment response into analyzable units
        let segments = self.segment_response(response)?;

        // Run each enabled detector
        if self.config.enabled_detectors.fabricated_facts {
            let flags = self.fact_detector.detect(&segments, knowledge_base)?;
            all_flags.extend(flags);
        }

        if self.config.enabled_detectors.nonexistent_entities {
            let flags = self.entity_checker.detect(&segments, dialogue_state, knowledge_base)?;
            all_flags.extend(flags);
        }

        if self.config.enabled_detectors.wrong_attributes {
            let flags = self.attribute_verifier.detect(&segments, knowledge_base)?;
            all_flags.extend(flags);
        }

        if self.config.enabled_detectors.kb_contradictions {
            let flags = self.kb_contradiction_detector.detect(&segments, knowledge_base)?;
            all_flags.extend(flags);
        }

        if self.config.enabled_detectors.history_contradictions {
            let flags = self.history_contradiction_detector.detect(&segments, dialogue_state)?;
            all_flags.extend(flags);
        }

        if self.config.enabled_detectors.unsupported_claims {
            let flags = self.claim_detector.detect(&segments, knowledge_base)?;
            all_flags.extend(flags);
        }

        if self.config.enabled_detectors.temporal_errors {
            let flags = self.temporal_checker.detect(&segments)?;
            all_flags.extend(flags);
        }

        if self.config.enabled_detectors.logical_inconsistencies {
            let flags = self.logical_checker.detect(&segments)?;
            all_flags.extend(flags);
        }

        // Deduplicate overlapping flags
        let deduped = self.deduplicate_flags(all_flags);

        // Filter by threshold
        let filtered: Vec<_> = deduped
            .into_iter()
            .filter(|f| f.confidence >= self.config.detection_threshold)
            .collect();

        Ok(filtered)
    }

    /// Segment response into analyzable units
    fn segment_response(&self, response: &str) -> Result<Vec<ResponseSegment>, HallucinationError> {
        let mut segments = Vec::new();

        // Split by sentences
        let sentences = self.split_sentences(response);

        for (idx, sentence) in sentences.iter().enumerate() {
            // Extract claims from sentence
            let claims = self.extract_claims(sentence)?;

            // Extract entity mentions
            let entities = self.extract_entities(sentence)?;

            // Extract temporal references
            let temporals = self.extract_temporals(sentence)?;

            segments.push(ResponseSegment {
                index: idx,
                text: sentence.text.clone(),
                span: sentence.span.clone(),
                claims,
                entities,
                temporals,
            });
        }

        Ok(segments)
    }
}
```

---

## Detection Methods

### Method 1: Fabricated Fact Detection

```rust
/// Detector for fabricated facts
pub struct FabricatedFactDetector {
    /// Claim extractor
    claim_extractor: ClaimExtractor,

    /// Knowledge base interface
    kb: Arc<RwLock<KnowledgeBase>>,
}

impl FabricatedFactDetector {
    /// Detect fabricated facts in segments
    pub fn detect(
        &self,
        segments: &[ResponseSegment],
        knowledge_base: &KnowledgeBase,
    ) -> Result<Vec<HallucinationFlag>, HallucinationError> {
        let mut flags = Vec::new();

        for segment in segments {
            for claim in &segment.claims {
                // Check if claim subject exists
                let subject_exists = knowledge_base.entity_exists(&claim.subject)?;

                if !subject_exists {
                    // Making claims about nonexistent subject
                    flags.push(HallucinationFlag {
                        span: claim.span.clone(),
                        content: claim.to_string(),
                        hallucination_type: HallucinationType::FabricatedFact,
                        confidence: 0.85,
                        suggestion: Some(format!(
                            "Could not verify: '{}'",
                            claim.subject
                        )),
                        evidence: Some("Subject entity not found in knowledge base".to_string()),
                    });
                    continue;
                }

                // Check if predicate is valid for subject
                let entity = knowledge_base.get_entity(&claim.subject)?;
                if let Some(entity) = entity {
                    let has_attribute = entity.has_attribute(&claim.predicate);

                    if !has_attribute {
                        // Claiming attribute that doesn't exist
                        let confidence = self.calculate_fabrication_confidence(
                            &claim,
                            &entity,
                        );

                        if confidence >= 0.5 {
                            flags.push(HallucinationFlag {
                                span: claim.span.clone(),
                                content: claim.to_string(),
                                hallucination_type: HallucinationType::FabricatedFact,
                                confidence,
                                suggestion: Some(format!(
                                    "No '{}' attribute found for '{}'",
                                    claim.predicate, claim.subject
                                )),
                                evidence: Some(format!(
                                    "Known attributes: {}",
                                    entity.attribute_names().join(", ")
                                )),
                            });
                        }
                    }
                }
            }
        }

        Ok(flags)
    }

    /// Calculate confidence that a claim is fabricated
    fn calculate_fabrication_confidence(
        &self,
        claim: &Claim,
        entity: &Entity,
    ) -> f64 {
        let mut confidence = 0.6;  // Base confidence

        // Higher confidence if entity is well-documented
        if entity.attribute_count() > 10 {
            confidence += 0.15;
        }

        // Higher confidence if predicate is common but missing
        let common_predicates = ["email", "phone", "department", "title", "location"];
        if common_predicates.contains(&claim.predicate.as_str()) {
            confidence += 0.1;
        }

        // Lower confidence if predicate is uncommon
        if entity.similar_attributes(&claim.predicate).is_empty() {
            confidence -= 0.1;
        }

        confidence.clamp(0.0, 1.0)
    }
}
```

### Method 2: Entity Existence Checking

```rust
/// Detector for references to nonexistent entities
pub struct EntityExistenceChecker {
    /// Named entity recognizer
    ner: NERModel,

    /// Entity resolution system
    resolver: EntityResolver,
}

impl EntityExistenceChecker {
    /// Detect references to nonexistent entities
    pub fn detect(
        &self,
        segments: &[ResponseSegment],
        dialogue_state: &DialogueState,
        knowledge_base: &KnowledgeBase,
    ) -> Result<Vec<HallucinationFlag>, HallucinationError> {
        let mut flags = Vec::new();

        for segment in segments {
            for entity_mention in &segment.entities {
                // Skip pronouns (handled by coreference)
                if entity_mention.mention_type == MentionType::Pronoun {
                    continue;
                }

                // Try to resolve in dialogue context
                let resolved = self.resolver.resolve_mention(
                    entity_mention,
                    dialogue_state,
                )?;

                if resolved.is_none() {
                    // Try knowledge base
                    let kb_match = knowledge_base.find_entity(&entity_mention.surface)?;

                    if kb_match.is_none() {
                        // Entity not found anywhere
                        let confidence = self.calculate_nonexistence_confidence(
                            entity_mention,
                            dialogue_state,
                        );

                        if confidence >= 0.5 {
                            flags.push(HallucinationFlag {
                                span: entity_mention.span.clone(),
                                content: entity_mention.surface.clone(),
                                hallucination_type: HallucinationType::NonexistentEntity,
                                confidence,
                                suggestion: Some(format!(
                                    "Could not find entity: '{}'",
                                    entity_mention.surface
                                )),
                                evidence: Some(
                                    "Not found in dialogue history or knowledge base".to_string()
                                ),
                            });
                        }
                    }
                }
            }
        }

        Ok(flags)
    }

    /// Calculate confidence that entity doesn't exist
    fn calculate_nonexistence_confidence(
        &self,
        mention: &EntityMention,
        dialogue_state: &DialogueState,
    ) -> f64 {
        let mut confidence = 0.7;  // Base confidence

        // Higher confidence for specific entity types
        match mention.mention_type {
            MentionType::ProperName => confidence += 0.15,
            MentionType::DefiniteDesc => confidence += 0.05,
            _ => {}
        }

        // Lower confidence if similar entities exist
        let similar = dialogue_state
            .entity_registry
            .find_similar(&mention.surface, 0.8);

        if !similar.is_empty() {
            // Might be a typo rather than hallucination
            confidence -= 0.2;
        }

        // Lower confidence for generic names
        let generic_names = ["the team", "the manager", "someone", "a person"];
        if generic_names.iter().any(|n| mention.surface.to_lowercase().contains(n)) {
            confidence -= 0.3;
        }

        confidence.clamp(0.0, 1.0)
    }
}
```

### Method 3: Dialogue History Contradiction Detection

```rust
/// Detector for contradictions with prior dialogue
pub struct HistoryContradictionDetector {
    /// Semantic similarity model
    similarity_model: SemanticSimilarityModel,

    /// Contradiction classifier
    contradiction_classifier: ContradictionClassifier,
}

impl HistoryContradictionDetector {
    /// Detect contradictions with dialogue history
    pub fn detect(
        &self,
        segments: &[ResponseSegment],
        dialogue_state: &DialogueState,
    ) -> Result<Vec<HallucinationFlag>, HallucinationError> {
        let mut flags = Vec::new();

        // Get recent turns
        let recent_turns: Vec<_> = dialogue_state
            .turns
            .iter()
            .rev()
            .take(10)
            .collect();

        for segment in segments {
            for claim in &segment.claims {
                // Find potentially related prior claims
                let related = self.find_related_claims(claim, &recent_turns)?;

                for (prior_claim, turn_id, similarity) in related {
                    // Check for contradiction
                    let contradiction = self.contradiction_classifier.classify(
                        &claim.to_string(),
                        &prior_claim.to_string(),
                    )?;

                    if contradiction.is_contradiction && contradiction.confidence >= 0.6 {
                        flags.push(HallucinationFlag {
                            span: claim.span.clone(),
                            content: claim.to_string(),
                            hallucination_type: HallucinationType::ContradictsPrior,
                            confidence: contradiction.confidence * similarity,
                            suggestion: Some(format!(
                                "This contradicts a previous statement"
                            )),
                            evidence: Some(format!(
                                "Earlier: '{}' (Turn {})",
                                prior_claim.to_string(),
                                turn_id
                            )),
                        });
                    }
                }
            }
        }

        Ok(flags)
    }

    /// Find claims related to the current claim in history
    fn find_related_claims(
        &self,
        claim: &Claim,
        turns: &[&Turn],
    ) -> Result<Vec<(Claim, TurnId, f64)>, HallucinationError> {
        let mut related = Vec::new();

        let claim_embedding = self.similarity_model.embed(&claim.to_string())?;

        for turn in turns {
            // Extract claims from turn
            let turn_claims = self.extract_claims_from_turn(turn)?;

            for prior_claim in turn_claims {
                let prior_embedding = self.similarity_model.embed(&prior_claim.to_string())?;
                let similarity = cosine_similarity(&claim_embedding, &prior_embedding);

                // High similarity suggests related claims
                if similarity >= 0.7 {
                    related.push((prior_claim, turn.turn_id, similarity));
                }
            }
        }

        // Sort by similarity
        related.sort_by(|a, b| b.2.partial_cmp(&a.2).unwrap());

        Ok(related)
    }
}

/// Contradiction classification result
pub struct ContradictionResult {
    /// Whether the statements contradict
    pub is_contradiction: bool,

    /// Confidence in the classification
    pub confidence: f64,

    /// Type of contradiction (if any)
    pub contradiction_type: Option<ContradictionType>,
}

/// Types of contradictions
pub enum ContradictionType {
    /// Direct negation
    DirectNegation,

    /// Incompatible values
    IncompatibleValues,

    /// Temporal impossibility
    TemporalImpossibility,

    /// Logical impossibility
    LogicalImpossibility,
}
```

### Method 4: Temporal Consistency Checking

```rust
/// Detector for temporal errors
pub struct TemporalConsistencyChecker {
    /// Temporal expression extractor
    temporal_extractor: TemporalExtractor,

    /// Current date reference
    current_date: DateTime<Utc>,
}

impl TemporalConsistencyChecker {
    /// Detect temporal errors in segments
    pub fn detect(
        &self,
        segments: &[ResponseSegment],
    ) -> Result<Vec<HallucinationFlag>, HallucinationError> {
        let mut flags = Vec::new();

        // Collect all temporal expressions
        let mut all_temporals = Vec::new();
        for segment in segments {
            for temporal in &segment.temporals {
                all_temporals.push((temporal, segment.span.clone()));
            }
        }

        // Check individual temporal expressions
        for (temporal, span) in &all_temporals {
            // Check for future dates referenced as past
            if let Some(date) = temporal.resolved_date {
                if date > self.current_date && temporal.tense == Tense::Past {
                    flags.push(HallucinationFlag {
                        span: span.clone(),
                        content: temporal.surface.clone(),
                        hallucination_type: HallucinationType::TemporalError,
                        confidence: 0.85,
                        suggestion: Some(format!(
                            "{} is in the future but referenced in past tense",
                            date.format("%Y-%m-%d")
                        )),
                        evidence: Some(format!(
                            "Current date: {}",
                            self.current_date.format("%Y-%m-%d")
                        )),
                    });
                }
            }

            // Check for impossible years
            if let Some(year) = temporal.year {
                if year > self.current_date.year() as i32 + 10 {
                    flags.push(HallucinationFlag {
                        span: span.clone(),
                        content: temporal.surface.clone(),
                        hallucination_type: HallucinationType::TemporalError,
                        confidence: 0.90,
                        suggestion: Some(format!("Year {} seems too far in the future", year)),
                        evidence: None,
                    });
                }
            }
        }

        // Check temporal ordering between events
        let ordering_issues = self.check_temporal_ordering(&all_temporals)?;
        flags.extend(ordering_issues);

        Ok(flags)
    }

    /// Check that temporal ordering is consistent
    fn check_temporal_ordering(
        &self,
        temporals: &[(&TemporalExpression, Range<usize>)],
    ) -> Result<Vec<HallucinationFlag>, HallucinationError> {
        let mut flags = Vec::new();

        // Look for "before" / "after" inconsistencies
        for i in 0..temporals.len() {
            for j in (i + 1)..temporals.len() {
                let (temp_i, span_i) = &temporals[i];
                let (temp_j, span_j) = &temporals[j];

                if let (Some(date_i), Some(date_j)) = (temp_i.resolved_date, temp_j.resolved_date) {
                    // Check for "before" claims that are actually after
                    if temp_i.relation == Some(TemporalRelation::Before) {
                        if date_i > date_j {
                            flags.push(HallucinationFlag {
                                span: span_i.clone(),
                                content: format!("{} before {}", temp_i.surface, temp_j.surface),
                                hallucination_type: HallucinationType::TemporalError,
                                confidence: 0.80,
                                suggestion: Some("Temporal ordering is inconsistent".to_string()),
                                evidence: Some(format!(
                                    "{} is actually after {}",
                                    date_i.format("%Y-%m-%d"),
                                    date_j.format("%Y-%m-%d")
                                )),
                            });
                        }
                    }
                }
            }
        }

        Ok(flags)
    }
}
```

### Method 5: Logical Consistency Checking

```rust
/// Detector for logical inconsistencies
pub struct LogicalConsistencyChecker {
    /// Statement parser
    statement_parser: StatementParser,

    /// Logical inference engine
    inference_engine: LogicalInferenceEngine,
}

impl LogicalConsistencyChecker {
    /// Detect logical inconsistencies within response
    pub fn detect(
        &self,
        segments: &[ResponseSegment],
    ) -> Result<Vec<HallucinationFlag>, HallucinationError> {
        let mut flags = Vec::new();

        // Parse all statements into logical form
        let mut statements = Vec::new();
        for segment in segments {
            let parsed = self.statement_parser.parse(&segment.text)?;
            statements.extend(parsed);
        }

        // Check for direct contradictions
        for i in 0..statements.len() {
            for j in (i + 1)..statements.len() {
                let contradiction = self.check_contradiction(&statements[i], &statements[j])?;

                if let Some(contradiction) = contradiction {
                    flags.push(HallucinationFlag {
                        span: statements[i].span.start..statements[j].span.end,
                        content: format!(
                            "'{}' vs '{}'",
                            statements[i].surface,
                            statements[j].surface
                        ),
                        hallucination_type: HallucinationType::LogicalInconsistency,
                        confidence: contradiction.confidence,
                        suggestion: Some("These statements contradict each other".to_string()),
                        evidence: Some(contradiction.explanation),
                    });
                }
            }
        }

        // Check for semantic contradictions
        let semantic_issues = self.check_semantic_contradictions(&statements)?;
        flags.extend(semantic_issues);

        Ok(flags)
    }

    /// Check if two statements contradict each other
    fn check_contradiction(
        &self,
        stmt1: &LogicalStatement,
        stmt2: &LogicalStatement,
    ) -> Result<Option<Contradiction>, HallucinationError> {
        // Direct negation: P and ¬P
        if stmt1.is_negation_of(stmt2) {
            return Ok(Some(Contradiction {
                confidence: 0.95,
                explanation: "Direct logical negation".to_string(),
            }));
        }

        // Incompatible predicates
        if stmt1.subject == stmt2.subject && stmt1.predicate == stmt2.predicate {
            if stmt1.object != stmt2.object && !stmt1.object.compatible_with(&stmt2.object) {
                return Ok(Some(Contradiction {
                    confidence: 0.85,
                    explanation: format!(
                        "{} cannot be both {} and {}",
                        stmt1.subject, stmt1.object, stmt2.object
                    ),
                }));
            }
        }

        // Exclusive category membership
        if self.are_mutually_exclusive(&stmt1.category, &stmt2.category) {
            return Ok(Some(Contradiction {
                confidence: 0.80,
                explanation: format!(
                    "{} and {} are mutually exclusive categories",
                    stmt1.category, stmt2.category
                ),
            }));
        }

        Ok(None)
    }

    /// Check for semantic contradictions using world knowledge
    fn check_semantic_contradictions(
        &self,
        statements: &[LogicalStatement],
    ) -> Result<Vec<HallucinationFlag>, HallucinationError> {
        let mut flags = Vec::new();

        for stmt in statements {
            // Check for impossible properties
            let impossible = self.check_impossible_properties(stmt)?;
            if let Some(issue) = impossible {
                flags.push(HallucinationFlag {
                    span: stmt.span.clone(),
                    content: stmt.surface.clone(),
                    hallucination_type: HallucinationType::LogicalInconsistency,
                    confidence: issue.confidence,
                    suggestion: Some(issue.explanation.clone()),
                    evidence: None,
                });
            }

            // Check for contradictory quantifiers
            // "All X" and "No X" in same scope
            if stmt.has_universal_quantifier() {
                for other in statements {
                    if other.has_existential_negation_of(&stmt.subject) {
                        flags.push(HallucinationFlag {
                            span: stmt.span.start..other.span.end,
                            content: format!("{} vs {}", stmt.surface, other.surface),
                            hallucination_type: HallucinationType::LogicalInconsistency,
                            confidence: 0.85,
                            suggestion: Some(
                                "Universal and existential claims conflict".to_string()
                            ),
                            evidence: None,
                        });
                    }
                }
            }
        }

        Ok(flags)
    }
}
```

---

## Confidence Scoring

### Multi-Factor Confidence

```rust
/// Confidence scoring for hallucination flags
pub struct HallucinationConfidenceScorer {
    /// Weights for different evidence types
    weights: EvidenceWeights,
}

/// Weights for evidence types
pub struct EvidenceWeights {
    /// Weight for KB evidence
    pub kb_evidence: f64,

    /// Weight for dialogue history evidence
    pub history_evidence: f64,

    /// Weight for linguistic signals
    pub linguistic_signals: f64,

    /// Weight for consistency with prior flags
    pub consistency: f64,
}

impl Default for EvidenceWeights {
    fn default() -> Self {
        Self {
            kb_evidence: 0.35,
            history_evidence: 0.25,
            linguistic_signals: 0.20,
            consistency: 0.20,
        }
    }
}

impl HallucinationConfidenceScorer {
    /// Calculate refined confidence for a hallucination flag
    pub fn score(
        &self,
        flag: &HallucinationFlag,
        kb_evidence: Option<&KBEvidence>,
        history_evidence: Option<&HistoryEvidence>,
        linguistic_signals: &[LinguisticSignal],
        other_flags: &[HallucinationFlag],
    ) -> f64 {
        let mut score = flag.hallucination_type.base_severity();

        // Adjust for KB evidence
        if let Some(kb) = kb_evidence {
            let kb_factor = if kb.contradicts {
                1.0 + (0.3 * kb.confidence)  // Boost for KB contradiction
            } else if kb.unverifiable {
                1.0  // Neutral
            } else {
                0.5  // KB supports, reduce confidence in hallucination
            };
            score *= self.weights.kb_evidence * kb_factor + (1.0 - self.weights.kb_evidence);
        }

        // Adjust for history evidence
        if let Some(history) = history_evidence {
            let history_factor = if history.contradicts {
                1.0 + (0.25 * history.confidence)
            } else {
                0.7
            };
            score *= self.weights.history_evidence * history_factor
                + (1.0 - self.weights.history_evidence);
        }

        // Adjust for linguistic signals
        let linguistic_factor = self.calculate_linguistic_factor(linguistic_signals);
        score *= self.weights.linguistic_signals * linguistic_factor
            + (1.0 - self.weights.linguistic_signals);

        // Adjust for consistency with other flags
        let consistency_factor = self.calculate_consistency_factor(flag, other_flags);
        score *= self.weights.consistency * consistency_factor + (1.0 - self.weights.consistency);

        score.clamp(0.0, 1.0)
    }

    /// Calculate factor from linguistic signals
    fn calculate_linguistic_factor(&self, signals: &[LinguisticSignal]) -> f64 {
        if signals.is_empty() {
            return 1.0;
        }

        let mut factor = 1.0;

        for signal in signals {
            match signal {
                // Hedging reduces confidence in hallucination
                LinguisticSignal::Hedging { strength } => {
                    factor *= 1.0 - (0.3 * strength);
                }

                // Overconfidence increases confidence in hallucination
                LinguisticSignal::Overconfidence { strength } => {
                    factor *= 1.0 + (0.2 * strength);
                }

                // Vagueness is neutral
                LinguisticSignal::Vagueness { .. } => {}

                // Self-correction reduces confidence
                LinguisticSignal::SelfCorrection => {
                    factor *= 0.8;
                }

                // Certainty markers on false claims increase confidence
                LinguisticSignal::CertaintyMarker => {
                    factor *= 1.15;
                }
            }
        }

        factor
    }

    /// Calculate factor from consistency with other flags
    fn calculate_consistency_factor(
        &self,
        flag: &HallucinationFlag,
        other_flags: &[HallucinationFlag],
    ) -> f64 {
        if other_flags.is_empty() {
            return 1.0;
        }

        // Multiple related hallucinations suggest systemic issue
        let related_count = other_flags
            .iter()
            .filter(|f| self.flags_related(flag, f))
            .count();

        1.0 + (0.1 * related_count as f64).min(0.3)
    }

    /// Check if two flags are related (same entity, same claim type, etc.)
    fn flags_related(&self, flag1: &HallucinationFlag, flag2: &HallucinationFlag) -> bool {
        // Same entity mentioned
        // Same hallucination type
        // Overlapping content
        flag1.hallucination_type == flag2.hallucination_type
            || flag1.content.contains(&flag2.content)
            || flag2.content.contains(&flag1.content)
    }
}
```

---

## Mitigation Strategies

### Response to Hallucinations

```rust
/// Hallucination mitigation strategies
pub struct HallucinationMitigator {
    /// Response generator for corrections
    corrector: HallucinationCorrector,

    /// Configuration
    config: MitigationConfig,
}

/// Mitigation configuration
pub struct MitigationConfig {
    /// Threshold for automatic correction
    pub auto_correct_threshold: f64,

    /// Threshold for flagging
    pub flag_threshold: f64,

    /// Threshold for regeneration request
    pub regenerate_threshold: f64,

    /// Maximum corrections per response
    pub max_corrections: usize,
}

/// Mitigation action to take
pub enum MitigationAction {
    /// No action needed
    None,

    /// Add annotation/flag to text
    Flag {
        span: Range<usize>,
        annotation: String,
    },

    /// Replace with correct information
    Correct {
        span: Range<usize>,
        original: String,
        replacement: String,
        source: String,
    },

    /// Remove the problematic content
    Remove {
        span: Range<usize>,
        reason: String,
    },

    /// Request LLM to regenerate with guidance
    Regenerate {
        guidance: String,
    },

    /// Escalate to human review
    Escalate {
        reason: String,
    },
}

impl HallucinationMitigator {
    /// Determine mitigation action for each hallucination
    pub fn mitigate(
        &self,
        flags: &[HallucinationFlag],
        knowledge_base: &KnowledgeBase,
    ) -> Result<Vec<MitigationAction>, MitigationError> {
        let mut actions = Vec::new();

        // Sort flags by confidence (highest first)
        let mut sorted_flags = flags.to_vec();
        sorted_flags.sort_by(|a, b| b.confidence.partial_cmp(&a.confidence).unwrap());

        // Check for severe cases requiring regeneration
        let severe_count = sorted_flags
            .iter()
            .filter(|f| f.confidence >= self.config.regenerate_threshold)
            .count();

        if severe_count >= 3 {
            let guidance = self.generate_regeneration_guidance(&sorted_flags);
            return Ok(vec![MitigationAction::Regenerate { guidance }]);
        }

        // Process individual flags
        let mut corrections_applied = 0;

        for flag in &sorted_flags {
            let action = if flag.confidence >= self.config.auto_correct_threshold {
                // Try to find correction
                if corrections_applied < self.config.max_corrections {
                    if let Some(correction) = self.find_correction(flag, knowledge_base)? {
                        corrections_applied += 1;
                        MitigationAction::Correct {
                            span: flag.span.clone(),
                            original: flag.content.clone(),
                            replacement: correction.value,
                            source: correction.source,
                        }
                    } else {
                        // Can't correct, remove instead
                        MitigationAction::Remove {
                            span: flag.span.clone(),
                            reason: flag.hallucination_type.description().to_string(),
                        }
                    }
                } else {
                    // Max corrections reached, just flag
                    MitigationAction::Flag {
                        span: flag.span.clone(),
                        annotation: format!("[{}]", flag.hallucination_type.description()),
                    }
                }
            } else if flag.confidence >= self.config.flag_threshold {
                MitigationAction::Flag {
                    span: flag.span.clone(),
                    annotation: format!("[{}]", flag.hallucination_type.description()),
                }
            } else {
                MitigationAction::None
            };

            actions.push(action);
        }

        Ok(actions)
    }

    /// Find correction for a hallucinated claim
    fn find_correction(
        &self,
        flag: &HallucinationFlag,
        knowledge_base: &KnowledgeBase,
    ) -> Result<Option<Correction>, MitigationError> {
        match flag.hallucination_type {
            HallucinationType::WrongAttribute => {
                // Try to find correct attribute value
                if let Some(suggestion) = &flag.suggestion {
                    // Parse suggestion for entity and attribute
                    if let Some((entity, attr)) = self.parse_attribute_suggestion(suggestion) {
                        let entity = knowledge_base.get_entity(&entity)?;
                        if let Some(entity) = entity {
                            if let Some(value) = entity.get_attribute(&attr)? {
                                return Ok(Some(Correction {
                                    value: value.value,
                                    source: "Knowledge Base".to_string(),
                                }));
                            }
                        }
                    }
                }
            }

            HallucinationType::ContradictsFact => {
                // Use KB value as correction
                if let Some(evidence) = &flag.evidence {
                    // Parse KB value from evidence
                    if let Some(kb_value) = self.extract_kb_value(evidence) {
                        return Ok(Some(Correction {
                            value: kb_value,
                            source: "Knowledge Base".to_string(),
                        }));
                    }
                }
            }

            HallucinationType::ContradictsPrior => {
                // Use prior dialogue as correction
                if let Some(evidence) = &flag.evidence {
                    if let Some(prior_value) = self.extract_prior_value(evidence) {
                        return Ok(Some(Correction {
                            value: prior_value,
                            source: "Earlier conversation".to_string(),
                        }));
                    }
                }
            }

            _ => {}
        }

        // Use suggestion if available
        if let Some(suggestion) = &flag.suggestion {
            if !suggestion.starts_with("Could not") {
                return Ok(Some(Correction {
                    value: suggestion.clone(),
                    source: "Automated correction".to_string(),
                }));
            }
        }

        Ok(None)
    }

    /// Generate guidance for LLM regeneration
    fn generate_regeneration_guidance(&self, flags: &[HallucinationFlag]) -> String {
        let mut guidance_parts = Vec::new();

        guidance_parts.push("Please regenerate your response, addressing these issues:".to_string());

        for (i, flag) in flags.iter().take(5).enumerate() {
            let issue = match flag.hallucination_type {
                HallucinationType::FabricatedFact => {
                    format!("{}. Verify the fact: '{}'", i + 1, flag.content)
                }
                HallucinationType::NonexistentEntity => {
                    format!("{}. Check if '{}' exists", i + 1, flag.content)
                }
                HallucinationType::WrongAttribute => {
                    format!("{}. Verify attribute: '{}'", i + 1, flag.content)
                }
                HallucinationType::ContradictsFact => {
                    format!("{}. Correct: '{}' - {}", i + 1, flag.content,
                        flag.evidence.as_deref().unwrap_or("contradicts known facts"))
                }
                HallucinationType::ContradictsPrior => {
                    format!("{}. Consistent with earlier: '{}'", i + 1, flag.content)
                }
                _ => {
                    format!("{}. Address: '{}'", i + 1, flag.content)
                }
            };

            guidance_parts.push(issue);
        }

        guidance_parts.join("\n")
    }
}
```

---

## Implementation

### Full Detection Example

```rust
/// Example: Full hallucination detection pipeline
pub async fn detect_hallucinations(
    response: &str,
    session: &Session,
) -> Result<Vec<HallucinationFlag>, Error> {
    // Initialize detector
    let detector = HallucinationDetector::new(
        session.fact_detector.clone(),
        session.entity_checker.clone(),
        session.attribute_verifier.clone(),
        session.kb_contradiction_detector.clone(),
        session.history_contradiction_detector.clone(),
        session.claim_detector.clone(),
        session.temporal_checker.clone(),
        session.logical_checker.clone(),
        HallucinationDetectorConfig::default(),
    );

    // Get dialogue state and knowledge base
    let dialogue_state = session.dialogue_state.read().await;
    let knowledge_base = session.knowledge_base.read().await;

    // Run detection
    let flags = detector.detect(
        response,
        &dialogue_state,
        &knowledge_base,
    )?;

    // Log results
    tracing::info!(
        total_flags = flags.len(),
        high_confidence = flags.iter().filter(|f| f.confidence >= 0.8).count(),
        types = ?flags.iter().map(|f| &f.hallucination_type).collect::<Vec<_>>(),
        "Hallucination detection complete"
    );

    Ok(flags)
}
```

---

## MeTTa Predicates

```metta
; Core hallucination detection predicates
(: detect-hallucinations (-> String DialogueState KnowledgeBase (List HallucinationFlag)))
(: hallucination-confidence (-> HallucinationFlag Float))
(: hallucination-severity (-> HallucinationType Float))

; Specific detector predicates
(: detect-fabricated-facts (-> (List ResponseSegment) KnowledgeBase (List HallucinationFlag)))
(: detect-nonexistent-entities (-> (List ResponseSegment) DialogueState KnowledgeBase (List HallucinationFlag)))
(: detect-wrong-attributes (-> (List ResponseSegment) KnowledgeBase (List HallucinationFlag)))
(: detect-kb-contradictions (-> (List ResponseSegment) KnowledgeBase (List HallucinationFlag)))
(: detect-history-contradictions (-> (List ResponseSegment) DialogueState (List HallucinationFlag)))
(: detect-unsupported-claims (-> (List ResponseSegment) KnowledgeBase (List HallucinationFlag)))
(: detect-temporal-errors (-> (List ResponseSegment) (List HallucinationFlag)))
(: detect-logical-inconsistencies (-> (List ResponseSegment) (List HallucinationFlag)))

; Segmentation predicates
(: segment-response (-> String (List ResponseSegment)))
(: extract-claims (-> String (List Claim)))
(: extract-entities (-> String (List EntityMention)))
(: extract-temporals (-> String (List TemporalExpression)))

; Evidence predicates
(: entity-exists (-> String KnowledgeBase Bool))
(: attribute-matches (-> String String String KnowledgeBase Bool))
(: contradicts-kb (-> Claim KnowledgeBase Bool))
(: contradicts-history (-> Claim DialogueState Bool))

; Mitigation predicates
(: mitigate-hallucination (-> HallucinationFlag KnowledgeBase MitigationAction))
(: find-correction (-> HallucinationFlag KnowledgeBase (Maybe String)))
(: generate-regeneration-guidance (-> (List HallucinationFlag) String))

; Confidence scoring predicates
(: score-hallucination-confidence (-> HallucinationFlag KBEvidence HistoryEvidence (List LinguisticSignal) (List HallucinationFlag) Float))
(: linguistic-signals (-> String (List LinguisticSignal)))
(: evidence-strength (-> Evidence Float))
```

---

## PathMap Schema

```
PathMap Key Structure:
=======================

/hallucination/{session_id}/{turn_id}/
    /detection/
        total_flags         → Number of hallucination flags
        high_confidence     → Flags with confidence >= 0.8
        medium_confidence   → Flags with 0.5 <= confidence < 0.8

        /flag/{flag_idx}/
            span_start      → Start position in response
            span_end        → End position in response
            content         → Flagged content
            type            → Hallucination type
            confidence      → Detection confidence
            suggestion      → Correction suggestion (if any)
            evidence        → Evidence string (if any)

            /evidence/
                kb_lookup   → KB lookup result
                history_match → History match result
                linguistic  → Linguistic signals

    /mitigation/
        action_count        → Number of mitigation actions
        corrections_applied → Number of corrections
        regeneration_needed → Boolean

        /action/{action_idx}/
            type            → Mitigation action type
            span_start      → Start position
            span_end        → End position
            original        → Original content
            replacement     → Replacement (if correction)
            reason          → Reason for action

    /metrics/
        detection_time_ms   → Time for detection
        segments_analyzed   → Number of segments
        claims_checked      → Number of claims checked
        entities_verified   → Number of entities verified

/hallucination_patterns/{pattern_id}/
    type                    → Pattern type (fabrication, entity, etc.)
    description             → Pattern description
    frequency               → How often seen
    last_seen               → Last occurrence timestamp
    examples/               → Example occurrences
```

---

## Related Documentation

- [LLM Integration Overview](./README.md) - Layer architecture
- [Output Postprocessing](./02-output-postprocessing.md) - Response validation
- [Prompt Preprocessing](./01-prompt-preprocessing.md) - Input preparation
- [Context Injection](./04-context-injection.md) - Knowledge retrieval
- [Fact Validation](./02-output-postprocessing.md#fact-validation) - Fact checking
- [Coreference Resolution](../dialogue/02-coreference-resolution.md) - Entity tracking

---

## References

- Ji, Z. et al. (2023). "Survey of Hallucination in Natural Language Generation"
- Manakul, P. et al. (2023). "SelfCheckGPT: Zero-Resource Black-Box Hallucination Detection"
- Mündler, N. et al. (2023). "Self-contradictory Hallucinations of Large Language Models"
- Min, S. et al. (2023). "FActScore: Fine-grained Atomic Evaluation of Factual Precision"
- Kryscinski, W. et al. (2020). "Evaluating the Factual Consistency of Abstractive Text"
- Maynez, J. et al. (2020). "On Faithfulness and Factuality in Abstractive Summarization"
