# Discourse Semantics

This document describes discourse structure, coherence relations, and multi-turn
semantic reasoning within the dialogue context layer.

**Sources**:
- Grosz & Sidner (1986): Attention, Intentions, and Discourse Structure
- Mann & Thompson (1988): Rhetorical Structure Theory (RST)
- Hobbs (1979): Coherence and Coreference
- Asher & Lascarides (2003): Logics of Conversation (SDRT)

---

## Table of Contents

1. [Overview](#overview)
2. [Discourse Structure Models](#discourse-structure-models)
3. [Coherence Relations](#coherence-relations)
4. [Multi-Turn Reasoning](#multi-turn-reasoning)
5. [Consistency Validation](#consistency-validation)
6. [MeTTa Predicate Implementation](#metta-predicate-implementation)
7. [PathMap Storage](#pathmap-storage)
8. [Integration with Correction](#integration-with-correction)

---

## Overview

Discourse semantics studies how meaning arises from sequences of utterances in
context. While sentential semantics handles individual sentences, discourse
semantics addresses:

- **Coherence**: Why certain utterance sequences make sense together
- **Structure**: How utterances relate hierarchically and sequentially
- **Information flow**: How information is introduced, referenced, and updated
- **Intention**: What communicative goals drive the discourse

For correction, discourse semantics enables:
1. Validating that corrections preserve discourse coherence
2. Using discourse context to disambiguate corrections
3. Detecting anomalies that suggest uncorrected errors
4. Ranking correction candidates by discourse fit

```
┌─────────────────────────────────────────────────────────────────────┐
│                    DISCOURSE SEMANTICS LAYER                        │
│                                                                     │
│  ┌───────────────────────────────────────────────────────────────┐ │
│  │                    Discourse Structure                         │ │
│  │  ┌─────────┐   ┌─────────┐   ┌─────────┐   ┌─────────┐      │ │
│  │  │ Turn 1  │ → │ Turn 2  │ → │ Turn 3  │ → │ Turn 4  │      │ │
│  │  └────┬────┘   └────┬────┘   └────┬────┘   └────┬────┘      │ │
│  │       │             │             │             │            │ │
│  │       ▼             ▼             ▼             ▼            │ │
│  │  ┌─────────────────────────────────────────────────────────┐ │ │
│  │  │              Coherence Relation Graph                   │ │ │
│  │  │  T1 ──Elaboration──▶ T2                                │ │ │
│  │  │  T2 ──QA-Pair─────▶ T3                                 │ │ │
│  │  │  T3 ──Contrast────▶ T4                                 │ │ │
│  │  └─────────────────────────────────────────────────────────┘ │ │
│  └───────────────────────────────────────────────────────────────┘ │
│                              │                                      │
│                              ▼                                      │
│  ┌───────────────────────────────────────────────────────────────┐ │
│  │                 Discourse Validation                          │ │
│  │  • Coherence checking        • Temporal consistency           │ │
│  │  • Information structure     • Logical consistency            │ │
│  └───────────────────────────────────────────────────────────────┘ │
└─────────────────────────────────────────────────────────────────────┘
```

---

## Discourse Structure Models

### Grosz-Sidner Model

The Grosz-Sidner model (1986) proposes three interacting structures:

1. **Linguistic Structure**: Sequence of discourse segments
2. **Intentional Structure**: Hierarchy of discourse purposes
3. **Attentional State**: Stack of focus spaces

```rust
/// Grosz-Sidner discourse structure
pub struct DiscourseStructure {
    /// Linguistic segments
    segments: Vec<DiscourseSegment>,

    /// Intentional hierarchy
    purpose_tree: PurposeTree,

    /// Attentional state (focus stack)
    attention_stack: Vec<FocusSpace>,
}

/// Discourse segment with purpose
pub struct DiscourseSegment {
    /// Segment identifier
    id: SegmentId,

    /// Constituent turns
    turns: Vec<TurnId>,

    /// Segment purpose
    purpose: DiscoursePurpose,

    /// Parent segment (if subordinate)
    parent: Option<SegmentId>,

    /// Dominance relation to parent
    relation: Option<SegmentRelation>,
}

/// Discourse purposes
pub enum DiscoursePurpose {
    /// Provide information
    Inform { content: MettaValue },

    /// Seek information
    Query { focus: MettaValue },

    /// Request action
    Request { action: MettaValue },

    /// Social/phatic purpose
    Social { function: SocialFunction },
}

/// Relations between segments
pub enum SegmentRelation {
    /// S2 is subordinate to S1 (elaboration, evidence)
    Dominates,

    /// S2 satisfies purpose of S1 (answer to question)
    SatisfactionPrecedence,

    /// S2 continues S1 at same level
    Continuation,
}
```

### Focus Space Management

The attentional state tracks what entities and propositions are currently salient:

```rust
/// Focus space for attention tracking
pub struct FocusSpace {
    /// Segment this space belongs to
    segment_id: SegmentId,

    /// Entities in focus
    focused_entities: HashMap<EntityId, f64>,

    /// Propositions in focus
    focused_propositions: Vec<Proposition>,

    /// Open questions (QUD - Question Under Discussion)
    open_questions: Vec<Question>,
}

impl DialogueState {
    /// Get current focus space
    pub fn current_focus(&self) -> &FocusSpace {
        self.attention_stack.last()
            .expect("Attention stack should never be empty")
    }

    /// Push new focus space on segment entry
    pub fn push_segment(&mut self, segment: DiscourseSegment) {
        let focus = FocusSpace {
            segment_id: segment.id,
            focused_entities: HashMap::new(),
            focused_propositions: Vec::new(),
            open_questions: Vec::new(),
        };
        self.attention_stack.push(focus);
        self.segments.push(segment);
    }

    /// Pop focus space on segment completion
    pub fn pop_segment(&mut self) -> Option<FocusSpace> {
        if self.attention_stack.len() > 1 {
            self.attention_stack.pop()
        } else {
            None // Keep at least one focus space
        }
    }
}
```

---

## Coherence Relations

Coherence relations explain how utterances connect to form sensible discourse.
We implement a subset based on RST and SDRT:

### Relation Taxonomy

```rust
/// Coherence relations between discourse units
#[derive(Clone, Debug, PartialEq)]
pub enum CoherenceRelation {
    // === Nucleus-Satellite Relations ===

    /// S elaborates on N with more detail
    Elaboration {
        nucleus: TurnId,
        satellite: TurnId,
    },

    /// S provides evidence/justification for N
    Evidence {
        claim: TurnId,
        support: TurnId,
    },

    /// S provides background for understanding N
    Background {
        foreground: TurnId,
        background: TurnId,
    },

    /// S explains purpose/goal of N
    Purpose {
        action: TurnId,
        goal: TurnId,
    },

    /// S states condition under which N holds
    Condition {
        consequent: TurnId,
        antecedent: TurnId,
    },

    /// S concedes point but N still holds
    Concession {
        main_point: TurnId,
        concession: TurnId,
    },

    // === Multi-Nuclear Relations ===

    /// T1 and T2 are alternatives
    Contrast {
        turn1: TurnId,
        turn2: TurnId,
    },

    /// T1 and T2 are conjuncts
    Conjunction {
        turn1: TurnId,
        turn2: TurnId,
    },

    /// T1 and T2 are in sequence
    Sequence {
        first: TurnId,
        second: TurnId,
    },

    /// T1 causes T2 (or T2 results from T1)
    Cause {
        cause: TurnId,
        effect: TurnId,
    },

    // === Dialogue-Specific Relations ===

    /// T2 answers question in T1
    QuestionAnswer {
        question: TurnId,
        answer: TurnId,
    },

    /// T2 acknowledges T1
    Acknowledgment {
        acknowledged: TurnId,
        acknowledgment: TurnId,
    },

    /// T2 corrects/repairs T1
    Correction {
        original: TurnId,
        correction: TurnId,
    },

    /// T2 clarifies T1 (response to clarification request)
    Clarification {
        unclear: TurnId,
        clarification: TurnId,
    },
}
```

### Relation Detection

```rust
/// Coherence relation detector
pub struct CoherenceDetector {
    /// MORK space with relation patterns
    mork_space: MorkSpace,

    /// Trained relation classifier (optional neural component)
    classifier: Option<RelationClassifier>,
}

impl CoherenceDetector {
    /// Detect relation between adjacent turns
    pub fn detect_relation(
        &self,
        turn1: &Turn,
        turn2: &Turn,
        context: &DialogueState,
    ) -> Option<CoherenceRelation> {
        // Try pattern-based detection first (fast)
        if let Some(rel) = self.pattern_based_detection(turn1, turn2) {
            return Some(rel);
        }

        // Fall back to classifier if available
        if let Some(ref classifier) = self.classifier {
            return classifier.classify(turn1, turn2, context);
        }

        // Heuristic fallbacks
        self.heuristic_detection(turn1, turn2, context)
    }

    /// Pattern-based relation detection via MORK
    fn pattern_based_detection(
        &self,
        turn1: &Turn,
        turn2: &Turn,
    ) -> Option<CoherenceRelation> {
        // Question-Answer pattern
        if matches!(turn1.speech_act, SpeechAct::Question { .. }) {
            if matches!(turn2.speech_act, SpeechAct::Assert { .. }) {
                return Some(CoherenceRelation::QuestionAnswer {
                    question: turn1.turn_id,
                    answer: turn2.turn_id,
                });
            }
        }

        // Acknowledgment pattern
        if matches!(turn2.speech_act, SpeechAct::Backchannel { .. }) {
            return Some(CoherenceRelation::Acknowledgment {
                acknowledged: turn1.turn_id,
                acknowledgment: turn2.turn_id,
            });
        }

        // Check for explicit discourse markers
        let markers = self.extract_discourse_markers(&turn2.raw_text);
        for marker in markers {
            match marker.as_str() {
                "however" | "but" | "although" => {
                    return Some(CoherenceRelation::Contrast {
                        turn1: turn1.turn_id,
                        turn2: turn2.turn_id,
                    });
                }
                "because" | "since" | "as" => {
                    return Some(CoherenceRelation::Evidence {
                        claim: turn1.turn_id,
                        support: turn2.turn_id,
                    });
                }
                "therefore" | "so" | "thus" => {
                    return Some(CoherenceRelation::Cause {
                        cause: turn1.turn_id,
                        effect: turn2.turn_id,
                    });
                }
                "for example" | "specifically" | "in particular" => {
                    return Some(CoherenceRelation::Elaboration {
                        nucleus: turn1.turn_id,
                        satellite: turn2.turn_id,
                    });
                }
                _ => continue,
            }
        }

        None
    }

    /// Heuristic relation detection
    fn heuristic_detection(
        &self,
        turn1: &Turn,
        turn2: &Turn,
        context: &DialogueState,
    ) -> Option<CoherenceRelation> {
        // Same speaker continuing -> likely Elaboration or Sequence
        if turn1.speaker == turn2.speaker {
            // Check for temporal/causal cues
            if self.has_temporal_sequence(&turn1.parsed, &turn2.parsed) {
                return Some(CoherenceRelation::Sequence {
                    first: turn1.turn_id,
                    second: turn2.turn_id,
                });
            }

            // Default to Elaboration for same-speaker continuation
            return Some(CoherenceRelation::Elaboration {
                nucleus: turn1.turn_id,
                satellite: turn2.turn_id,
            });
        }

        // Different speaker -> check for QA, acknowledgment, etc.
        // Default to Conjunction if no specific relation found
        Some(CoherenceRelation::Conjunction {
            turn1: turn1.turn_id,
            turn2: turn2.turn_id,
        })
    }
}
```

---

## Multi-Turn Reasoning

### Question Under Discussion (QUD)

The QUD tracks what questions the discourse is currently addressing:

```rust
/// Question Under Discussion tracking
pub struct QUDTracker {
    /// Stack of open questions
    qud_stack: Vec<Question>,

    /// Resolved questions with answers
    resolved: Vec<(Question, TurnId)>,
}

/// Question representation
pub struct Question {
    /// Turn that raised the question
    source_turn: TurnId,

    /// Question type
    q_type: QuestionType,

    /// Focus of the question (what's being asked about)
    focus: MettaValue,

    /// Possible answers (for alternative questions)
    alternatives: Option<Vec<MettaValue>>,

    /// Implicit or explicit
    implicit: bool,
}

impl QUDTracker {
    /// Process new turn for QUD updates
    pub fn process_turn(&mut self, turn: &Turn, context: &DialogueState) {
        // Check if turn raises a question
        if let SpeechAct::Question { q_type, focus } = &turn.speech_act {
            self.push_question(Question {
                source_turn: turn.turn_id,
                q_type: q_type.clone(),
                focus: focus.clone(),
                alternatives: None,
                implicit: false,
            });
        }

        // Check if turn answers current QUD
        if let Some(current_qud) = self.current_qud() {
            if self.answers_question(turn, current_qud) {
                let resolved = self.qud_stack.pop().unwrap();
                self.resolved.push((resolved, turn.turn_id));
            }
        }

        // Check for implicit questions raised by assertions
        self.detect_implicit_questions(turn, context);
    }

    /// Get current question under discussion
    pub fn current_qud(&self) -> Option<&Question> {
        self.qud_stack.last()
    }

    /// Check if turn addresses current QUD
    fn answers_question(&self, turn: &Turn, question: &Question) -> bool {
        match &turn.speech_act {
            SpeechAct::Assert { content, .. } => {
                // Check if assertion content matches question focus
                self.content_matches_focus(content, &question.focus)
            }
            SpeechAct::Backchannel { signal_type } => {
                // Some backchannels can answer yes/no questions
                matches!(signal_type, BackchannelType::Affirm | BackchannelType::Deny)
                    && matches!(question.q_type, QuestionType::YesNo)
            }
            _ => false,
        }
    }
}
```

### Information State Update

Track how information evolves through discourse:

```rust
/// Information state for discourse
pub struct InformationState {
    /// Shared common ground
    common_ground: CommonGround,

    /// Commitments by each participant
    commitments: HashMap<ParticipantId, Vec<Commitment>>,

    /// Open issues (unresolved questions, pending actions)
    open_issues: Vec<OpenIssue>,
}

/// Common ground - shared knowledge
pub struct CommonGround {
    /// Propositions mutually believed true
    propositions: HashSet<Proposition>,

    /// Shared entity knowledge
    entity_knowledge: HashMap<EntityId, EntityKnowledge>,
}

/// Commitment made by a participant
pub struct Commitment {
    /// Who made the commitment
    speaker: ParticipantId,

    /// When (which turn)
    turn_id: TurnId,

    /// Content of commitment
    content: CommitmentContent,

    /// Current status
    status: CommitmentStatus,
}

/// Types of commitments
pub enum CommitmentContent {
    /// Assertion commitment (speaker committed to truth)
    Assertion { proposition: Proposition },

    /// Action commitment (speaker committed to do something)
    Action { action: MettaValue, deadline: Option<Timestamp> },

    /// Conditional commitment
    Conditional {
        condition: Proposition,
        commitment: Box<CommitmentContent>,
    },
}

/// Commitment status
pub enum CommitmentStatus {
    Active,
    Fulfilled,
    Violated,
    Retracted,
}

impl InformationState {
    /// Update state after new turn
    pub fn update(&mut self, turn: &Turn) {
        match &turn.speech_act {
            SpeechAct::Assert { content, confidence } => {
                // Add to speaker's commitments
                self.add_commitment(turn.speaker, Commitment {
                    speaker: turn.speaker,
                    turn_id: turn.turn_id,
                    content: CommitmentContent::Assertion {
                        proposition: Proposition::from_metta(content.clone()),
                    },
                    status: CommitmentStatus::Active,
                });

                // If confidence high enough, add to common ground
                if *confidence > 0.8 {
                    self.common_ground.propositions.insert(
                        Proposition::from_metta(content.clone())
                    );
                }
            }

            SpeechAct::Commissive { commitment } => {
                self.add_commitment(turn.speaker, Commitment {
                    speaker: turn.speaker,
                    turn_id: turn.turn_id,
                    content: CommitmentContent::Action {
                        action: commitment.clone(),
                        deadline: None,
                    },
                    status: CommitmentStatus::Active,
                });
            }

            SpeechAct::Question { focus, .. } => {
                self.open_issues.push(OpenIssue::Question {
                    asker: turn.speaker,
                    turn_id: turn.turn_id,
                    focus: focus.clone(),
                });
            }

            _ => {}
        }
    }
}
```

---

## Consistency Validation

### Logical Consistency

Check that new assertions don't contradict established information:

```rust
/// Logical consistency checker
pub struct ConsistencyChecker {
    /// MeTTaIL engine for predicate evaluation
    mettail: MettaILEngine,
}

impl ConsistencyChecker {
    /// Check if new assertion is consistent with common ground
    pub fn check_assertion_consistency(
        &self,
        assertion: &Proposition,
        common_ground: &CommonGround,
    ) -> ConsistencyResult {
        // Check direct contradiction
        if let Some(contradicting) = self.find_contradiction(assertion, common_ground) {
            return ConsistencyResult::Contradiction {
                new_assertion: assertion.clone(),
                contradicts: contradicting,
            };
        }

        // Check derived contradiction (via inference)
        if let Some(derived) = self.find_derived_contradiction(assertion, common_ground) {
            return ConsistencyResult::DerivedContradiction {
                new_assertion: assertion.clone(),
                derives: derived.derived,
                contradicts: derived.contradicts,
            };
        }

        ConsistencyResult::Consistent
    }

    /// Find direct contradiction
    fn find_contradiction(
        &self,
        assertion: &Proposition,
        common_ground: &CommonGround,
    ) -> Option<Proposition> {
        let negation = assertion.negate();

        for prop in &common_ground.propositions {
            if prop.semantically_equivalent(&negation) {
                return Some(prop.clone());
            }
        }

        None
    }

    /// MeTTa predicate for contradiction checking
    fn metta_contradiction_check(&self, p1: &Proposition, p2: &Proposition) -> bool {
        // (contradicts p1 p2)
        let query = format!(
            "(contradicts {} {})",
            p1.to_metta(),
            p2.to_metta()
        );

        self.mettail.query(&query)
            .map(|results| !results.is_empty())
            .unwrap_or(false)
    }
}

/// Consistency check result
pub enum ConsistencyResult {
    Consistent,

    Contradiction {
        new_assertion: Proposition,
        contradicts: Proposition,
    },

    DerivedContradiction {
        new_assertion: Proposition,
        derives: Proposition,
        contradicts: Proposition,
    },

    Uncertain {
        reason: String,
    },
}
```

### Temporal Consistency

Ensure temporal references are coherent:

```rust
/// Temporal consistency checker
pub struct TemporalChecker {
    /// Timeline of events mentioned
    timeline: EventTimeline,
}

/// Event with temporal information
pub struct Event {
    /// Event identifier
    id: EventId,

    /// Turn where event was mentioned
    source_turn: TurnId,

    /// Event description
    description: MettaValue,

    /// Temporal anchor
    temporal: TemporalAnchor,
}

/// Temporal anchoring
pub enum TemporalAnchor {
    /// Absolute time
    Absolute(DateTime),

    /// Relative to speech time
    Deictic(DeicticTense),

    /// Relative to another event
    Relative {
        reference: EventId,
        relation: TemporalRelation,
    },
}

/// Temporal relations (Allen's interval algebra simplified)
pub enum TemporalRelation {
    Before,
    After,
    During,
    Contains,
    Overlaps,
    Meets,
    Simultaneous,
}

impl TemporalChecker {
    /// Check temporal consistency of new event
    pub fn check_event_consistency(
        &self,
        event: &Event,
    ) -> Result<(), TemporalInconsistency> {
        // Build temporal constraints
        let constraints = self.build_constraints(event);

        // Check for contradictions
        for (e1, rel, e2) in &constraints {
            if let Some(existing) = self.get_relation(*e1, *e2) {
                if !self.relations_compatible(rel, &existing) {
                    return Err(TemporalInconsistency {
                        event1: *e1,
                        event2: *e2,
                        claimed: rel.clone(),
                        established: existing,
                    });
                }
            }
        }

        Ok(())
    }

    /// Check if two temporal relations are compatible
    fn relations_compatible(&self, r1: &TemporalRelation, r2: &TemporalRelation) -> bool {
        use TemporalRelation::*;

        match (r1, r2) {
            (Before, Before) => true,
            (After, After) => true,
            (Before, After) | (After, Before) => false,
            (Simultaneous, Simultaneous) => true,
            (Simultaneous, Before) | (Simultaneous, After) => false,
            // ... handle all combinations
            _ => true // Conservative: assume compatible if not clearly contradictory
        }
    }
}
```

---

## MeTTa Predicate Implementation

### Core Discourse Predicates

```metta
; === Discourse Structure Types ===

(: DiscourseSegment Type)
(: Turn Type)
(: CoherenceRelation Type)

; === Segment Relations ===

(: segment-turns (-> DiscourseSegment (List Turn)))
(: segment-purpose (-> DiscourseSegment DiscoursePurpose))
(: segment-parent (-> DiscourseSegment (Maybe DiscourseSegment)))

; === Coherence Relation Predicates ===

(: coherence-relation (-> Turn Turn (Maybe CoherenceRelation)))
(: is-elaboration (-> CoherenceRelation Bool))
(: is-contrast (-> CoherenceRelation Bool))
(: is-qa-pair (-> CoherenceRelation Bool))

; Relation detection rules
(= (coherence-relation $t1 $t2)
   (if (and (is-question $t1) (is-assertion $t2))
       (Just (QuestionAnswer $t1 $t2))
       (detect-by-markers $t1 $t2)))

; === Consistency Predicates ===

(: contradicts (-> Proposition Proposition Bool))
(: temporally-consistent (-> Event Event Bool))
(: logically-consistent (-> Proposition CommonGround Bool))

; Contradiction detection
(= (contradicts $p (Not $p)) True)
(= (contradicts (Not $p) $p) True)
(= (contradicts $p $q)
   (if (== $p $q)
       False
       (derives-contradiction $p $q)))

; === QUD Management ===

(: Question Type)
(: current-qud (-> DialogueState (Maybe Question)))
(: qud-addressed (-> Turn Question Bool))
(: raise-question (-> Turn DialogueState DialogueState))

; QUD operations
(= (qud-addressed $turn $question)
   (and (is-assertion $turn)
        (matches-focus (turn-content $turn) (question-focus $question))))

; === Information State ===

(: CommonGround Type)
(: Commitment Type)

(: in-common-ground (-> Proposition CommonGround Bool))
(: add-to-common-ground (-> Proposition CommonGround CommonGround))
(: commitment-status (-> Commitment CommitmentStatus))

; Common ground operations
(= (in-common-ground $prop $cg)
   (elem $prop (cg-propositions $cg)))

(= (add-to-common-ground $prop $cg)
   (CommonGround (cons $prop (cg-propositions $cg))
                 (cg-entities $cg)))
```

### Coherence Scoring

```metta
; === Coherence Scoring ===

(: coherence-score (-> Turn DialogueState Float))
(: relation-weight (-> CoherenceRelation Float))

; Relation weights (higher = more coherent connection)
(= (relation-weight (QuestionAnswer _ _)) 1.0)
(= (relation-weight (Elaboration _ _)) 0.9)
(= (relation-weight (Cause _ _)) 0.85)
(= (relation-weight (Contrast _ _)) 0.8)
(= (relation-weight (Sequence _ _)) 0.75)
(= (relation-weight (Conjunction _ _)) 0.5)

; Compute coherence score for turn in context
(= (coherence-score $turn $state)
   (let $prev (previous-turn $state)
        $rel (coherence-relation $prev $turn)
        (case $rel
          ((Just $r) (relation-weight $r))
          (Nothing 0.3))))  ; Baseline for unrelated turns
```

---

## PathMap Storage

### Discourse Structure Storage

```
/dialogue/{dialogue_id}/
    /discourse/
        /segment/{segment_id}/
            purpose         → encoded purpose
            parent          → parent segment_id (optional)
            relation        → relation to parent
            /turns/         → [turn_id, ...]

        /relation/{relation_id}/
            type            → relation type
            turn1           → first turn_id
            turn2           → second turn_id
            confidence      → detection confidence

        /qud/
            /open/          → stack of open question IDs
            /resolved/      → [(question_id, answering_turn_id), ...]

        /info_state/
            /common_ground/
                /propositions/  → [proposition_id, ...]
                /entities/      → {entity_id} → knowledge

            /commitments/{participant_id}/
                {commitment_id} → encoded commitment

            /open_issues/       → [issue_id, ...]

        /timeline/
            /events/{event_id}/
                description     → event description
                source_turn     → turn_id
                temporal        → temporal anchor

            /constraints/       → [(event1, relation, event2), ...]
```

### Storage Operations

```rust
impl DialogueState {
    /// Persist discourse segment to PathMap
    pub fn store_segment(&mut self, segment: &DiscourseSegment) -> Result<(), PathMapError> {
        let base = format!("/dialogue/{}/discourse/segment/{}/",
                          self.dialogue_id, segment.id);

        // Store segment data
        self.pathmap.insert(
            format!("{}purpose", base).as_bytes(),
            &segment.purpose.encode()
        )?;

        if let Some(parent) = &segment.parent {
            self.pathmap.insert(
                format!("{}parent", base).as_bytes(),
                parent.as_bytes()
            )?;
        }

        if let Some(relation) = &segment.relation {
            self.pathmap.insert(
                format!("{}relation", base).as_bytes(),
                &relation.encode()
            )?;
        }

        // Store turn list
        for turn_id in &segment.turns {
            self.pathmap.insert(
                format!("{}turns/{}", base, turn_id).as_bytes(),
                &[]  // Presence-only marker
            )?;
        }

        Ok(())
    }

    /// Store coherence relation
    pub fn store_relation(&mut self, relation: &CoherenceRelation) -> Result<(), PathMapError> {
        let rel_id = self.next_relation_id();
        let base = format!("/dialogue/{}/discourse/relation/{}/",
                          self.dialogue_id, rel_id);

        let (rel_type, t1, t2) = match relation {
            CoherenceRelation::Elaboration { nucleus, satellite } =>
                ("elaboration", nucleus, satellite),
            CoherenceRelation::QuestionAnswer { question, answer } =>
                ("qa", question, answer),
            CoherenceRelation::Contrast { turn1, turn2 } =>
                ("contrast", turn1, turn2),
            // ... handle all relation types
            _ => return Ok(()), // Skip unknown types
        };

        self.pathmap.insert(format!("{}type", base).as_bytes(), rel_type.as_bytes())?;
        self.pathmap.insert(format!("{}turn1", base).as_bytes(), t1.as_bytes())?;
        self.pathmap.insert(format!("{}turn2", base).as_bytes(), t2.as_bytes())?;

        Ok(())
    }
}
```

---

## Integration with Correction

### Coherence-Aware Correction Ranking

Use discourse coherence to rank correction candidates:

```rust
/// Coherence-aware correction ranker
pub struct CoherenceRanker {
    detector: CoherenceDetector,
    checker: ConsistencyChecker,
}

impl CoherenceRanker {
    /// Rank corrections by discourse coherence
    pub fn rank_corrections(
        &self,
        candidates: Vec<CorrectionCandidate>,
        turn: &Turn,
        context: &DialogueState,
    ) -> Vec<(CorrectionCandidate, f64)> {
        let prev_turn = context.previous_turn();

        candidates.into_iter()
            .map(|candidate| {
                let coherence = self.compute_coherence(&candidate, prev_turn, context);
                let consistency = self.compute_consistency(&candidate, context);

                // Combined score
                let score = 0.6 * coherence + 0.4 * consistency;
                (candidate, score)
            })
            .sorted_by(|a, b| b.1.partial_cmp(&a.1).unwrap())
            .collect()
    }

    /// Compute coherence score for candidate
    fn compute_coherence(
        &self,
        candidate: &CorrectionCandidate,
        prev_turn: Option<&Turn>,
        context: &DialogueState,
    ) -> f64 {
        let Some(prev) = prev_turn else {
            return 0.5; // No previous turn, neutral coherence
        };

        // Create hypothetical turn with correction applied
        let hypo_turn = candidate.apply_to_turn(context.current_turn());

        // Detect coherence relation
        if let Some(relation) = self.detector.detect_relation(prev, &hypo_turn, context) {
            relation.weight()
        } else {
            0.3 // Weak coherence if no relation detected
        }
    }

    /// Compute consistency score for candidate
    fn compute_consistency(
        &self,
        candidate: &CorrectionCandidate,
        context: &DialogueState,
    ) -> f64 {
        let hypo_turn = candidate.apply_to_turn(context.current_turn());

        // Extract propositions from hypothetical turn
        let propositions = self.extract_propositions(&hypo_turn);

        // Check each proposition for consistency
        let mut consistent_count = 0;
        let mut total = 0;

        for prop in propositions {
            total += 1;
            match self.checker.check_assertion_consistency(
                &prop,
                &context.information_state.common_ground
            ) {
                ConsistencyResult::Consistent => consistent_count += 1,
                _ => {}
            }
        }

        if total == 0 {
            1.0 // No propositions to check, assume consistent
        } else {
            consistent_count as f64 / total as f64
        }
    }
}
```

### Correction Rejection Based on Coherence

```rust
impl CorrectionEngine {
    /// Filter corrections that would break discourse coherence
    pub fn filter_coherence_violations(
        &self,
        candidates: Vec<CorrectionCandidate>,
        context: &DialogueState,
    ) -> Vec<CorrectionCandidate> {
        candidates.into_iter()
            .filter(|candidate| {
                // Reject if correction would create logical contradiction
                if self.creates_contradiction(candidate, context) {
                    return false;
                }

                // Reject if correction would break temporal consistency
                if self.breaks_temporal_consistency(candidate, context) {
                    return false;
                }

                // Reject if correction would make discourse incoherent
                if self.coherence_score(candidate, context) < 0.2 {
                    return false;
                }

                true
            })
            .collect()
    }
}
```

---

## Summary

Discourse semantics provides the foundation for multi-turn reasoning:

1. **Discourse Structure** - Grosz-Sidner model with segments, purposes, and attention
2. **Coherence Relations** - RST/SDRT-based relations between utterances
3. **QUD Tracking** - Managing questions and their resolution
4. **Information State** - Common ground, commitments, and open issues
5. **Consistency Validation** - Logical and temporal consistency checking
6. **Correction Integration** - Using coherence to rank and filter corrections

---

## References

- Grosz, B. & Sidner, C. (1986). "Attention, Intentions, and the Structure of Discourse"
- Mann, W. & Thompson, S. (1988). "Rhetorical Structure Theory"
- Hobbs, J. (1979). "Coherence and Coreference"
- Asher, N. & Lascarides, A. (2003). "Logics of Conversation"
- Ginzburg, J. (2012). "The Interactive Stance"
- Roberts, C. (2012). "Information Structure in Discourse"

See [02-coreference-resolution.md](./02-coreference-resolution.md) for entity tracking.
