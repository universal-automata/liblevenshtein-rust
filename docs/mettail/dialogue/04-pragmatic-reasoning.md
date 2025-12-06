# Pragmatic Reasoning

This document describes speech acts, implicatures, Gricean maxims, and indirect
meaning interpretation within the dialogue context layer.

**Sources**:
- Austin (1962): How to Do Things with Words
- Searle (1969): Speech Acts
- Grice (1975): Logic and Conversation
- Levinson (1983): Pragmatics
- Horn (2004): Implicature

---

## Table of Contents

1. [Overview](#overview)
2. [Speech Act Theory](#speech-act-theory)
3. [Speech Act Classification](#speech-act-classification)
4. [Gricean Maxims](#gricean-maxims)
5. [Implicature Computation](#implicature-computation)
6. [Indirect Speech Acts](#indirect-speech-acts)
7. [Relevance Theory](#relevance-theory)
8. [MeTTa Predicate Implementation](#metta-predicate-implementation)
9. [Integration with Correction](#integration-with-correction)

---

## Overview

Pragmatic reasoning goes beyond literal meaning to understand:

- **What speakers intend** - the illocutionary force behind utterances
- **What is implicated** - meaning derived through inference
- **Indirect meaning** - when literal form differs from intended meaning
- **Context sensitivity** - how meaning depends on situation

```
Literal:    "Can you pass the salt?"
            ↓
Semantic:   Question about ability (yes/no answer expected)
            ↓
Pragmatic:  Request to pass the salt (action expected)
```

For correction, pragmatics enables:
1. Preserving intended meaning across corrections
2. Validating that corrections maintain appropriate speech act type
3. Detecting when corrections would change communicative intent
4. Using pragmatic context to disambiguate corrections

```
┌─────────────────────────────────────────────────────────────────────┐
│                     PRAGMATIC REASONING                             │
│                                                                     │
│  ┌───────────────────────────────────────────────────────────────┐ │
│  │                    Input Utterance                             │ │
│  │            "Could you maybe help me with this?"               │ │
│  └───────────────────────────────────────────────────────────────┘ │
│                              │                                      │
│       ┌──────────────────────┼──────────────────────┐              │
│       ▼                      ▼                      ▼              │
│  ┌─────────┐          ┌─────────────┐        ┌──────────┐         │
│  │ Speech  │          │ Implicature │        │ Indirect │         │
│  │   Act   │          │ Computation │        │ Speech   │         │
│  │ Classify│          │             │        │ Act Res. │         │
│  └────┬────┘          └──────┬──────┘        └────┬─────┘         │
│       │                      │                    │                │
│       ▼                      ▼                    ▼                │
│  ┌─────────┐          ┌─────────────┐        ┌──────────┐         │
│  │Directive│          │ Politeness  │        │ Request  │         │
│  │(Request)│          │ Implicature │        │ (Direct) │         │
│  └─────────┘          └─────────────┘        └──────────┘         │
│                              │                                      │
│                              ▼                                      │
│  ┌───────────────────────────────────────────────────────────────┐ │
│  │              Pragmatic Interpretation                          │ │
│  │  Type: Request                                                 │ │
│  │  Content: help(speaker, addressee, this)                      │ │
│  │  Politeness: High (hedged, modal)                             │ │
│  │  Confidence: 0.95                                              │ │
│  └───────────────────────────────────────────────────────────────┘ │
└─────────────────────────────────────────────────────────────────────┘
```

---

## Speech Act Theory

### Austin's Framework

Austin distinguished three aspects of speech acts:

1. **Locutionary act** - the act of saying something (words, syntax, semantics)
2. **Illocutionary act** - what is done in saying it (asserting, requesting, etc.)
3. **Perlocutionary act** - the effect on the hearer (convincing, alarming, etc.)

```rust
/// Complete speech act with all three aspects
pub struct SpeechActAnalysis {
    /// What was said (locutionary)
    locution: Locution,

    /// What was done in saying it (illocutionary)
    illocution: Illocution,

    /// Expected/achieved effect (perlocutionary)
    perlocution: Perlocution,
}

/// Locutionary aspect: the utterance itself
pub struct Locution {
    /// Surface text
    text: String,

    /// Propositional content
    proposition: Proposition,

    /// Grammatical mood
    mood: GrammaticalMood,
}

/// Illocutionary aspect: the speech act performed
pub struct Illocution {
    /// Speech act type
    act_type: SpeechAct,

    /// Illocutionary force
    force: IllocutionaryForce,

    /// Felicity conditions satisfied
    felicity: FelicityConditions,
}

/// Perlocutionary aspect: intended effect
pub struct Perlocution {
    /// Intended effect type
    intended_effect: PerlocutionaryEffect,

    /// Whether effect was achieved (if known)
    achieved: Option<bool>,
}

#[derive(Clone, Debug)]
pub enum GrammaticalMood {
    Declarative,   // "The door is open."
    Interrogative, // "Is the door open?"
    Imperative,    // "Open the door."
    Exclamative,   // "What a door!"
    Optative,      // "May the door be open."
}

#[derive(Clone, Debug)]
pub enum PerlocutionaryEffect {
    Convince,
    Persuade,
    Frighten,
    Amuse,
    Comfort,
    Inform,
    Warn,
    Promise,
}
```

### Felicity Conditions

Speech acts require certain conditions to be successful:

```rust
/// Felicity conditions for speech acts
pub struct FelicityConditions {
    /// Propositional content conditions
    propositional: PropositionalConditions,

    /// Preparatory conditions
    preparatory: PreparatoryConditions,

    /// Sincerity conditions
    sincerity: SincerityConditions,

    /// Essential conditions
    essential: EssentialConditions,
}

/// Propositional content conditions
pub struct PropositionalConditions {
    /// Does content match act type?
    content_appropriate: bool,

    /// For promises: future act of speaker
    /// For requests: future act of hearer
    temporal_condition: Option<TemporalCondition>,
}

/// Preparatory conditions
pub struct PreparatoryConditions {
    /// Can hearer perform the action? (for requests)
    hearer_able: Option<bool>,

    /// Does speaker have authority? (for orders)
    speaker_authority: Option<bool>,

    /// Is the act non-obvious?
    non_obvious: bool,
}

/// Sincerity conditions
pub struct SincerityConditions {
    /// Does speaker believe the proposition? (assertions)
    speaker_believes: Option<bool>,

    /// Does speaker want the action? (requests)
    speaker_wants: Option<bool>,

    /// Does speaker intend to perform? (promises)
    speaker_intends: Option<bool>,
}

impl FelicityConditions {
    /// Check if conditions are satisfied for speech act
    pub fn satisfied_for(&self, act: &SpeechAct) -> bool {
        match act {
            SpeechAct::Assert { .. } => {
                self.propositional.content_appropriate
                    && self.sincerity.speaker_believes.unwrap_or(true)
            }
            SpeechAct::Directive { .. } => {
                self.propositional.content_appropriate
                    && self.preparatory.hearer_able.unwrap_or(true)
                    && self.sincerity.speaker_wants.unwrap_or(true)
            }
            SpeechAct::Commissive { .. } => {
                self.propositional.content_appropriate
                    && self.sincerity.speaker_intends.unwrap_or(true)
            }
            _ => self.propositional.content_appropriate,
        }
    }
}
```

---

## Speech Act Classification

### Searle's Taxonomy

```rust
/// Speech act types following Searle's taxonomy
#[derive(Clone, Debug)]
pub enum SpeechAct {
    /// Assertives: commit speaker to truth of proposition
    /// "It's raining", "I believe that..."
    Assert {
        /// Propositional content
        content: Proposition,
        /// Degree of commitment
        strength: AssertionStrength,
        /// Evidence type if any
        evidence: Option<EvidenceType>,
    },

    /// Directives: attempt to get hearer to do something
    /// "Close the door", "Could you help?"
    Directive {
        /// Requested action
        action: Action,
        /// Type of directive
        directive_type: DirectiveType,
        /// Addressee (if specific)
        addressee: Option<ParticipantId>,
    },

    /// Commissives: commit speaker to future action
    /// "I promise to come", "I'll do it"
    Commissive {
        /// Committed action
        commitment: Action,
        /// Type of commitment
        commitment_type: CommissiveType,
    },

    /// Expressives: express psychological state
    /// "Thank you", "I'm sorry", "Congratulations"
    Expressive {
        /// Expressed attitude
        attitude: ExpressiveAttitude,
        /// Target of attitude
        target: Option<MettaValue>,
    },

    /// Declaratives: change reality by utterance
    /// "I now pronounce you...", "You're fired"
    Declarative {
        /// Change effected
        change: StateChange,
        /// Institutional context required
        institution: Institution,
    },

    /// Questions: request information
    Question {
        /// Question type
        q_type: QuestionType,
        /// Focus of question
        focus: MettaValue,
        /// Expected answer type
        expected_type: Option<AnswerType>,
    },

    /// Backchannels: acknowledge, continue
    Backchannel {
        /// Signal type
        signal_type: BackchannelType,
    },
}

#[derive(Clone, Debug)]
pub enum AssertionStrength {
    Claim,      // Strong commitment
    Suggest,    // Tentative
    Guess,      // Weak commitment
    Hypothesize,// Exploratory
}

#[derive(Clone, Debug)]
pub enum DirectiveType {
    Command,    // Authority-based
    Request,    // Politeness-based
    Suggest,    // Low imposition
    Forbid,     // Negative directive
    Permit,     // Granting permission
}

#[derive(Clone, Debug)]
pub enum CommissiveType {
    Promise,    // Strong commitment
    Offer,      // Conditional on acceptance
    Threat,     // Negative for hearer
    Pledge,     // Formal commitment
}

#[derive(Clone, Debug)]
pub enum ExpressiveAttitude {
    Thanks,
    Apology,
    Congratulation,
    Complaint,
    Welcome,
    Sympathy,
}

#[derive(Clone, Debug)]
pub enum BackchannelType {
    Affirm,     // "yes", "uh-huh"
    Deny,       // "no"
    Continue,   // "go on", "and then?"
    Surprise,   // "really?", "wow"
    Understanding, // "I see", "right"
}
```

### Speech Act Classifier

```rust
/// Speech act classifier
pub struct SpeechActClassifier {
    /// Pattern-based rules
    patterns: Vec<SpeechActPattern>,

    /// MORK space for pattern queries
    mork_space: MorkSpace,

    /// Mood-to-act mapping
    mood_mapping: HashMap<GrammaticalMood, Vec<SpeechAct>>,
}

/// Pattern for speech act detection
pub struct SpeechActPattern {
    /// Linguistic indicators
    indicators: Vec<Indicator>,

    /// Resulting speech act type
    act_type: SpeechAct,

    /// Confidence weight
    weight: f64,
}

#[derive(Clone)]
pub enum Indicator {
    /// Lexical indicator (word/phrase)
    Lexical(String),

    /// Grammatical mood
    Mood(GrammaticalMood),

    /// Performative verb
    PerformativeVerb(String),

    /// Sentence-initial pattern
    SentenceInitial(String),

    /// Modal verb
    Modal(String),

    /// Hedging expression
    Hedge(String),
}

impl SpeechActClassifier {
    /// Classify speech act of a turn
    pub fn classify(&self, turn: &Turn, context: &DialogueState) -> SpeechActAnalysis {
        let text = &turn.raw_text;

        // Detect grammatical mood
        let mood = self.detect_mood(text);

        // Look for performative verbs ("I promise", "I request")
        if let Some(act) = self.detect_performative(text) {
            return self.build_analysis(act, mood, turn);
        }

        // Pattern-based classification
        let mut scores: HashMap<&SpeechAct, f64> = HashMap::new();

        for pattern in &self.patterns {
            if self.pattern_matches(pattern, text, mood.clone()) {
                *scores.entry(&pattern.act_type).or_default() += pattern.weight;
            }
        }

        // Context-based adjustment
        self.adjust_for_context(&mut scores, context);

        // Get highest scoring act
        let best_act = scores.into_iter()
            .max_by(|a, b| a.1.partial_cmp(&b.1).unwrap())
            .map(|(act, _)| act.clone());

        let act = best_act.unwrap_or_else(|| {
            // Default based on mood
            self.default_act_for_mood(&mood)
        });

        self.build_analysis(act, mood, turn)
    }

    /// Detect grammatical mood from surface features
    fn detect_mood(&self, text: &str) -> GrammaticalMood {
        let trimmed = text.trim();

        // Check for question marks
        if trimmed.ends_with('?') {
            return GrammaticalMood::Interrogative;
        }

        // Check for exclamation
        if trimmed.ends_with('!') && self.is_exclamative(trimmed) {
            return GrammaticalMood::Exclamative;
        }

        // Check for imperative (no subject, base verb form)
        if self.is_imperative(trimmed) {
            return GrammaticalMood::Imperative;
        }

        // Default to declarative
        GrammaticalMood::Declarative
    }

    /// Detect explicit performative verbs
    fn detect_performative(&self, text: &str) -> Option<SpeechAct> {
        let performatives = [
            ("I promise", SpeechAct::Commissive {
                commitment: Action::default(),
                commitment_type: CommissiveType::Promise,
            }),
            ("I apologize", SpeechAct::Expressive {
                attitude: ExpressiveAttitude::Apology,
                target: None,
            }),
            ("I order you", SpeechAct::Directive {
                action: Action::default(),
                directive_type: DirectiveType::Command,
                addressee: None,
            }),
            ("I request", SpeechAct::Directive {
                action: Action::default(),
                directive_type: DirectiveType::Request,
                addressee: None,
            }),
        ];

        for (pattern, act) in &performatives {
            if text.to_lowercase().contains(&pattern.to_lowercase()) {
                return Some(act.clone());
            }
        }

        None
    }

    /// Adjust scores based on dialogue context
    fn adjust_for_context(
        &self,
        scores: &mut HashMap<&SpeechAct, f64>,
        context: &DialogueState,
    ) {
        // If previous turn was a question, boost assertion/answer
        if let Some(prev) = context.previous_turn() {
            if matches!(prev.speech_act, SpeechAct::Question { .. }) {
                for (act, score) in scores.iter_mut() {
                    if matches!(act, SpeechAct::Assert { .. }) {
                        *score *= 1.5;
                    }
                }
            }
        }

        // If in formal context, boost directives
        if context.formality_level > 0.7 {
            for (act, score) in scores.iter_mut() {
                if matches!(act, SpeechAct::Declarative { .. }) {
                    *score *= 1.3;
                }
            }
        }
    }
}
```

---

## Gricean Maxims

### The Cooperative Principle

Grice's Cooperative Principle: "Make your conversational contribution such as is
required, at the stage at which it occurs, by the accepted purpose or direction
of the talk exchange in which you are engaged."

```rust
/// Gricean maxim checker
pub struct GriceanMaximChecker {
    /// Context for evaluation
    context: DialogueState,
}

/// The four maxims
pub enum GriceanMaxim {
    /// Quantity: Be as informative as required, no more
    Quantity,

    /// Quality: Be truthful, have evidence
    Quality,

    /// Relation: Be relevant
    Relation,

    /// Manner: Be clear, brief, orderly
    Manner,
}

/// Maxim violation with details
pub struct MaximViolation {
    /// Which maxim was violated
    maxim: GriceanMaxim,

    /// Type of violation
    violation_type: ViolationType,

    /// Specific issue
    issue: String,

    /// Is violation deliberate (generating implicature)?
    flouting: bool,
}

#[derive(Clone, Debug)]
pub enum ViolationType {
    // Quantity violations
    TooLittle,    // Not enough information
    TooMuch,      // Excessive information

    // Quality violations
    Untruthful,   // Known to be false
    Unsupported,  // No evidence

    // Relation violations
    Irrelevant,   // Off-topic
    Tangential,   // Weakly related

    // Manner violations
    Obscure,      // Hard to understand
    Ambiguous,    // Multiple interpretations
    Prolix,       // Unnecessarily long
    Disorderly,   // Poor organization
}

impl GriceanMaximChecker {
    /// Check all maxims for a turn
    pub fn check_maxims(&self, turn: &Turn, context: &DialogueState) -> Vec<MaximViolation> {
        let mut violations = Vec::new();

        violations.extend(self.check_quantity(turn, context));
        violations.extend(self.check_quality(turn, context));
        violations.extend(self.check_relation(turn, context));
        violations.extend(self.check_manner(turn, context));

        violations
    }

    /// Check Quantity maxim
    fn check_quantity(&self, turn: &Turn, context: &DialogueState) -> Vec<MaximViolation> {
        let mut violations = Vec::new();

        // Check if response to question provides enough info
        if let Some(prev) = context.previous_turn() {
            if let SpeechAct::Question { q_type, focus, .. } = &prev.speech_act {
                // Wh-questions need content answers
                if matches!(q_type, QuestionType::Wh) {
                    if self.is_minimal_response(&turn.raw_text) {
                        violations.push(MaximViolation {
                            maxim: GriceanMaxim::Quantity,
                            violation_type: ViolationType::TooLittle,
                            issue: "Minimal response to wh-question".to_string(),
                            flouting: false,
                        });
                    }
                }
            }
        }

        // Check for excessive information
        if self.is_overinformative(turn, context) {
            violations.push(MaximViolation {
                maxim: GriceanMaxim::Quantity,
                violation_type: ViolationType::TooMuch,
                issue: "More information than required".to_string(),
                flouting: self.likely_flouting(turn),
            });
        }

        violations
    }

    /// Check Quality maxim
    fn check_quality(&self, turn: &Turn, context: &DialogueState) -> Vec<MaximViolation> {
        let mut violations = Vec::new();

        // Check for contradictions with established facts
        for prop in self.extract_propositions(turn) {
            if self.contradicts_known_facts(&prop, context) {
                violations.push(MaximViolation {
                    maxim: GriceanMaxim::Quality,
                    violation_type: ViolationType::Untruthful,
                    issue: format!("Contradicts known fact: {:?}", prop),
                    flouting: self.likely_flouting(turn),
                });
            }
        }

        // Check for unsupported claims
        if let SpeechAct::Assert { strength: AssertionStrength::Claim, .. } = &turn.speech_act {
            if self.is_unsupported_claim(turn, context) {
                violations.push(MaximViolation {
                    maxim: GriceanMaxim::Quality,
                    violation_type: ViolationType::Unsupported,
                    issue: "Strong claim without evidence".to_string(),
                    flouting: false,
                });
            }
        }

        violations
    }

    /// Check Relation maxim
    fn check_relation(&self, turn: &Turn, context: &DialogueState) -> Vec<MaximViolation> {
        let mut violations = Vec::new();

        // Check topic relevance
        if let Some(current_topic) = context.topic_graph.current_topic() {
            let relevance = self.compute_topic_relevance(turn, current_topic);
            if relevance < 0.2 {
                violations.push(MaximViolation {
                    maxim: GriceanMaxim::Relation,
                    violation_type: ViolationType::Irrelevant,
                    issue: "Off-topic contribution".to_string(),
                    flouting: self.has_topic_shift_marker(&turn.raw_text),
                });
            } else if relevance < 0.5 {
                violations.push(MaximViolation {
                    maxim: GriceanMaxim::Relation,
                    violation_type: ViolationType::Tangential,
                    issue: "Weakly related to current topic".to_string(),
                    flouting: false,
                });
            }
        }

        // Check QUD relevance
        if let Some(qud) = context.qud_tracker.current_qud() {
            if !self.addresses_qud(turn, qud) {
                violations.push(MaximViolation {
                    maxim: GriceanMaxim::Relation,
                    violation_type: ViolationType::Irrelevant,
                    issue: "Does not address current question".to_string(),
                    flouting: false,
                });
            }
        }

        violations
    }

    /// Check Manner maxim
    fn check_manner(&self, turn: &Turn, context: &DialogueState) -> Vec<MaximViolation> {
        let mut violations = Vec::new();
        let text = &turn.raw_text;

        // Check for obscurity
        if self.is_obscure(text) {
            violations.push(MaximViolation {
                maxim: GriceanMaxim::Manner,
                violation_type: ViolationType::Obscure,
                issue: "Unclear expression".to_string(),
                flouting: self.likely_deliberate_obscurity(text),
            });
        }

        // Check for ambiguity
        if let Some(ambiguity) = self.detect_ambiguity(text, context) {
            violations.push(MaximViolation {
                maxim: GriceanMaxim::Manner,
                violation_type: ViolationType::Ambiguous,
                issue: format!("Ambiguous: {}", ambiguity),
                flouting: false,
            });
        }

        // Check for prolixity
        if self.is_unnecessarily_long(text, turn) {
            violations.push(MaximViolation {
                maxim: GriceanMaxim::Manner,
                violation_type: ViolationType::Prolix,
                issue: "Unnecessarily verbose".to_string(),
                flouting: false,
            });
        }

        violations
    }
}
```

---

## Implicature Computation

### Conversational Implicatures

```rust
/// Implicature computation engine
pub struct ImplicatureEngine {
    /// Maxim checker
    maxim_checker: GriceanMaximChecker,

    /// Scalar implicature rules
    scalar_rules: Vec<ScalarRule>,

    /// MORK space for implicature patterns
    mork_space: MorkSpace,
}

/// Types of implicatures
#[derive(Clone, Debug)]
pub enum Implicature {
    /// Scalar implicature (some → not all)
    Scalar {
        trigger: String,
        implicatum: Proposition,
        scale: Vec<String>,
    },

    /// Quantity implicature (exhaustive interpretation)
    Quantity {
        stated: Proposition,
        implicated: Proposition,
    },

    /// Manner implicature (marked form → marked meaning)
    Manner {
        marked_form: String,
        unmarked_alternative: String,
        meaning_difference: String,
    },

    /// Particularized implicature (context-specific)
    Particularized {
        context: String,
        utterance: String,
        implicated: Proposition,
    },

    /// Flouting implicature (deliberate maxim violation)
    Flouting {
        violated_maxim: GriceanMaxim,
        literal_meaning: Proposition,
        implicated_meaning: Proposition,
    },
}

/// Scalar rule (Horn scales)
pub struct ScalarRule {
    /// Scale members (ordered from weak to strong)
    scale: Vec<String>,

    /// Category (quantifier, modal, etc.)
    category: ScaleCategory,
}

#[derive(Clone, Debug)]
pub enum ScaleCategory {
    Quantifier,     // some < many < most < all
    Modal,          // possible < probable < certain
    Logical,        // or < and
    Evaluative,     // good < excellent < perfect
    Frequency,      // sometimes < often < always
}

impl ImplicatureEngine {
    /// Compute all implicatures for an utterance
    pub fn compute_implicatures(
        &self,
        turn: &Turn,
        context: &DialogueState,
    ) -> Vec<Implicature> {
        let mut implicatures = Vec::new();

        // Scalar implicatures
        implicatures.extend(self.compute_scalar_implicatures(&turn.raw_text));

        // Quantity implicatures
        implicatures.extend(self.compute_quantity_implicatures(turn, context));

        // Manner implicatures
        implicatures.extend(self.compute_manner_implicatures(&turn.raw_text));

        // Flouting implicatures (from maxim violations)
        let violations = self.maxim_checker.check_maxims(turn, context);
        for violation in violations {
            if violation.flouting {
                if let Some(imp) = self.derive_flouting_implicature(&violation, turn, context) {
                    implicatures.push(imp);
                }
            }
        }

        implicatures
    }

    /// Compute scalar implicatures
    fn compute_scalar_implicatures(&self, text: &str) -> Vec<Implicature> {
        let mut implicatures = Vec::new();
        let text_lower = text.to_lowercase();

        for rule in &self.scalar_rules {
            for (i, trigger) in rule.scale.iter().enumerate() {
                if text_lower.contains(trigger) && i < rule.scale.len() - 1 {
                    // Using weaker term implicates NOT stronger
                    let stronger_terms = &rule.scale[i + 1..];

                    implicatures.push(Implicature::Scalar {
                        trigger: trigger.clone(),
                        implicatum: Proposition::negation(
                            Proposition::disjunction(
                                stronger_terms.iter()
                                    .map(|t| Proposition::atom(t.clone()))
                                    .collect()
                            )
                        ),
                        scale: rule.scale.clone(),
                    });
                }
            }
        }

        implicatures
    }

    /// Compute quantity implicatures
    fn compute_quantity_implicatures(
        &self,
        turn: &Turn,
        context: &DialogueState,
    ) -> Vec<Implicature> {
        let mut implicatures = Vec::new();

        // Exhaustive interpretation of answers
        if let Some(prev) = context.previous_turn() {
            if let SpeechAct::Question { q_type: QuestionType::Wh, focus, .. } = &prev.speech_act {
                // "Who came?" - "John" → Only John came
                let mentioned = self.extract_mentioned_entities(turn);

                if !mentioned.is_empty() {
                    implicatures.push(Implicature::Quantity {
                        stated: Proposition::existential(mentioned.clone()),
                        implicated: Proposition::exhaustive(mentioned),
                    });
                }
            }
        }

        implicatures
    }

    /// Compute manner implicatures
    fn compute_manner_implicatures(&self, text: &str) -> Vec<Implicature> {
        let mut implicatures = Vec::new();

        // Marked form → marked meaning pairs
        let marked_pairs = [
            ("caused to die", "killed", "indirect causation, not direct"),
            ("not unhappy", "happy", "less than fully happy"),
            ("attempted to", "tried to", "unsuccessful attempt"),
        ];

        for (marked, unmarked, difference) in &marked_pairs {
            if text.to_lowercase().contains(*marked) {
                implicatures.push(Implicature::Manner {
                    marked_form: marked.to_string(),
                    unmarked_alternative: unmarked.to_string(),
                    meaning_difference: difference.to_string(),
                });
            }
        }

        implicatures
    }

    /// Derive implicature from deliberate maxim flouting
    fn derive_flouting_implicature(
        &self,
        violation: &MaximViolation,
        turn: &Turn,
        context: &DialogueState,
    ) -> Option<Implicature> {
        match violation.maxim {
            GriceanMaxim::Quality => {
                // Flouting quality → irony, metaphor, hyperbole
                // "He's a real Einstein" (about someone stupid) → sarcasm
                if self.is_hyperbolic(&turn.raw_text) {
                    return Some(Implicature::Flouting {
                        violated_maxim: GriceanMaxim::Quality,
                        literal_meaning: self.extract_literal_meaning(turn),
                        implicated_meaning: self.derive_ironic_meaning(turn),
                    });
                }
            }

            GriceanMaxim::Quantity => {
                // Flouting quantity → understatement, emphasis
                // Minimal response when more expected → reluctance
                if self.is_minimal_response(&turn.raw_text) {
                    return Some(Implicature::Flouting {
                        violated_maxim: GriceanMaxim::Quantity,
                        literal_meaning: self.extract_literal_meaning(turn),
                        implicated_meaning: Proposition::atom("reluctance".to_string()),
                    });
                }
            }

            GriceanMaxim::Relation => {
                // Flouting relation → topic change signal
                if self.has_topic_shift_marker(&turn.raw_text) {
                    return Some(Implicature::Particularized {
                        context: "topic shift".to_string(),
                        utterance: turn.raw_text.clone(),
                        implicated: Proposition::atom("change_topic".to_string()),
                    });
                }
            }

            GriceanMaxim::Manner => {
                // Flouting manner → formality, avoidance
                // Using long form → distancing
            }
        }

        None
    }
}
```

---

## Indirect Speech Acts

### Resolution of Indirect Forms

```rust
/// Indirect speech act resolver
pub struct IndirectActResolver {
    /// Patterns for indirect forms
    patterns: Vec<IndirectPattern>,

    /// Context for interpretation
    context: DialogueState,
}

/// Pattern for indirect speech act
pub struct IndirectPattern {
    /// Literal form (e.g., question about ability)
    literal_form: SpeechActTemplate,

    /// Indirect interpretation (e.g., request)
    indirect_form: SpeechActTemplate,

    /// Conditions for indirect reading
    conditions: Vec<IndirectCondition>,

    /// Confidence weight
    weight: f64,
}

/// Conditions that trigger indirect interpretation
#[derive(Clone)]
pub enum IndirectCondition {
    /// Hearer can perform action (for requests)
    HearerAble,

    /// Action is beneficial to speaker (for requests)
    BenefitsSpeaker,

    /// Question has obvious answer (literal reading pointless)
    ObviousAnswer,

    /// Social context requires politeness
    PolitenessRequired,

    /// Specific lexical markers present
    LexicalMarker(String),
}

impl IndirectActResolver {
    /// Resolve potential indirect speech act
    pub fn resolve(
        &self,
        turn: &Turn,
        literal_act: &SpeechAct,
    ) -> Option<SpeechAct> {
        // Check for indirect form patterns
        for pattern in &self.patterns {
            if self.matches_literal_form(literal_act, &pattern.literal_form) {
                // Check conditions
                let conditions_met = pattern.conditions.iter()
                    .all(|c| self.condition_met(c, turn));

                if conditions_met {
                    return Some(self.instantiate_indirect(&pattern.indirect_form, turn));
                }
            }
        }

        None
    }

    /// Check if condition is met
    fn condition_met(&self, condition: &IndirectCondition, turn: &Turn) -> bool {
        match condition {
            IndirectCondition::HearerAble => {
                // Assume hearer is able unless context says otherwise
                true
            }

            IndirectCondition::BenefitsSpeaker => {
                // Check if action would benefit speaker
                // (e.g., "pass the salt" benefits speaker)
                self.action_benefits_speaker(turn)
            }

            IndirectCondition::ObviousAnswer => {
                // "Can you pass the salt?" - obviously yes
                self.has_obvious_answer(turn)
            }

            IndirectCondition::PolitenessRequired => {
                // Check formality level of context
                self.context.formality_level > 0.5
            }

            IndirectCondition::LexicalMarker(marker) => {
                turn.raw_text.to_lowercase().contains(&marker.to_lowercase())
            }
        }
    }

    /// Common indirect speech act patterns
    pub fn default_patterns() -> Vec<IndirectPattern> {
        vec![
            // "Can you X?" → Request to X
            IndirectPattern {
                literal_form: SpeechActTemplate::Question {
                    about: Box::new(SpeechActTemplate::Ability),
                },
                indirect_form: SpeechActTemplate::Request,
                conditions: vec![
                    IndirectCondition::HearerAble,
                    IndirectCondition::BenefitsSpeaker,
                ],
                weight: 0.9,
            },

            // "Would you mind X?" → Request to X
            IndirectPattern {
                literal_form: SpeechActTemplate::Question {
                    about: Box::new(SpeechActTemplate::Willingness),
                },
                indirect_form: SpeechActTemplate::Request,
                conditions: vec![
                    IndirectCondition::PolitenessRequired,
                ],
                weight: 0.95,
            },

            // "I wonder if..." → Indirect question
            IndirectPattern {
                literal_form: SpeechActTemplate::Assert,
                indirect_form: SpeechActTemplate::IndirectQuestion,
                conditions: vec![
                    IndirectCondition::LexicalMarker("wonder".to_string()),
                ],
                weight: 0.85,
            },

            // "It's cold in here" → Request to close window/turn on heat
            IndirectPattern {
                literal_form: SpeechActTemplate::Assert,
                indirect_form: SpeechActTemplate::Request,
                conditions: vec![
                    IndirectCondition::BenefitsSpeaker,
                ],
                weight: 0.6, // Lower confidence, more context-dependent
            },
        ]
    }
}
```

---

## Relevance Theory

### Relevance-Based Interpretation

```rust
/// Relevance-theoretic interpretation engine
pub struct RelevanceEngine {
    /// Context for cognitive effects
    context: DialogueState,
}

/// Cognitive effects of an interpretation
pub struct CognitiveEffects {
    /// New information added
    new_information: Vec<Proposition>,

    /// Existing beliefs strengthened
    strengthened: Vec<(Proposition, f64)>,

    /// Existing beliefs contradicted/weakened
    contradicted: Vec<Proposition>,

    /// Contextual implications derived
    implications: Vec<Proposition>,
}

/// Processing effort for interpretation
pub struct ProcessingEffort {
    /// Lexical access difficulty
    lexical: f64,

    /// Syntactic complexity
    syntactic: f64,

    /// Reference resolution difficulty
    reference: f64,

    /// Inference required
    inference: f64,

    /// Total effort
    total: f64,
}

impl RelevanceEngine {
    /// Compute relevance of an interpretation
    pub fn compute_relevance(
        &self,
        turn: &Turn,
        interpretation: &Interpretation,
    ) -> f64 {
        let effects = self.compute_cognitive_effects(interpretation);
        let effort = self.compute_processing_effort(turn, interpretation);

        // Relevance = Effects / Effort
        let effect_score = self.score_effects(&effects);
        let effort_score = effort.total;

        if effort_score > 0.0 {
            effect_score / effort_score
        } else {
            effect_score
        }
    }

    /// Compute cognitive effects of interpretation
    fn compute_cognitive_effects(&self, interpretation: &Interpretation) -> CognitiveEffects {
        let mut effects = CognitiveEffects {
            new_information: Vec::new(),
            strengthened: Vec::new(),
            contradicted: Vec::new(),
            implications: Vec::new(),
        };

        // Check propositions against existing beliefs
        for prop in &interpretation.propositions {
            if self.is_new_information(prop) {
                effects.new_information.push(prop.clone());
            } else if self.strengthens_belief(prop) {
                let strength = self.compute_strengthening(prop);
                effects.strengthened.push((prop.clone(), strength));
            } else if self.contradicts_belief(prop) {
                effects.contradicted.push(prop.clone());
            }
        }

        // Derive contextual implications
        effects.implications = self.derive_implications(
            &interpretation.propositions,
            &self.context.information_state.common_ground
        );

        effects
    }

    /// Compute processing effort
    fn compute_processing_effort(
        &self,
        turn: &Turn,
        interpretation: &Interpretation,
    ) -> ProcessingEffort {
        let text = &turn.raw_text;

        // Lexical effort: rare words, technical terms
        let lexical = self.lexical_effort(text);

        // Syntactic effort: sentence length, embedding depth
        let syntactic = self.syntactic_effort(text);

        // Reference effort: pronouns, definite descriptions to resolve
        let reference = self.reference_effort(turn);

        // Inference effort: implicatures, indirect acts
        let inference = self.inference_effort(interpretation);

        let total = lexical + syntactic + reference + inference;

        ProcessingEffort { lexical, syntactic, reference, inference, total }
    }

    /// Score cognitive effects
    fn score_effects(&self, effects: &CognitiveEffects) -> f64 {
        let mut score = 0.0;

        // New information is valuable
        score += effects.new_information.len() as f64 * 1.0;

        // Strengthening is moderately valuable
        for (_, strength) in &effects.strengthened {
            score += strength * 0.5;
        }

        // Contextual implications are very valuable
        score += effects.implications.len() as f64 * 1.5;

        // Contradiction can be valuable (correction) or costly
        // Context-dependent

        score
    }

    /// Choose most relevant interpretation
    pub fn choose_interpretation(
        &self,
        turn: &Turn,
        candidates: Vec<Interpretation>,
    ) -> Interpretation {
        candidates.into_iter()
            .max_by(|a, b| {
                let rel_a = self.compute_relevance(turn, a);
                let rel_b = self.compute_relevance(turn, b);
                rel_a.partial_cmp(&rel_b).unwrap()
            })
            .unwrap_or_default()
    }
}
```

---

## MeTTa Predicate Implementation

### Pragmatic Predicates

```metta
; === Speech Act Types ===

(: SpeechAct Type)
(: Assert SpeechAct)
(: Directive SpeechAct)
(: Commissive SpeechAct)
(: Expressive SpeechAct)
(: Question SpeechAct)

; === Speech Act Classification ===

; Classify speech act of a turn
(: classify-speech-act (-> String DialogueState SpeechAct))

; Get speech act type
(: speech-act-type (-> SpeechAct SpeechActType))

; Check specific types
(: is-assertion (-> SpeechAct Bool))
(: is-directive (-> SpeechAct Bool))
(: is-question (-> SpeechAct Bool))

; === Implementation ===

(= (is-assertion (Assert _ _ _)) True)
(= (is-assertion _) False)

(= (is-directive (Directive _ _ _)) True)
(= (is-directive _) False)

(= (is-question (Question _ _ _)) True)
(= (is-question _) False)

; === Indirect Speech Acts ===

(: is-indirect-speech-act (-> SpeechAct Bool))
(: resolve-indirect (-> SpeechAct DialogueState SpeechAct))

; Indirect request pattern
(= (resolve-indirect (Question Ability $action) $state)
   (if (and (hearer-can-perform $action $state)
            (benefits-speaker $action $state))
       (Directive $action Request Nothing)
       (Question Ability $action)))

; === Gricean Maxims ===

(: GriceanMaxim Type)
(: Quantity GriceanMaxim)
(: Quality GriceanMaxim)
(: Relation GriceanMaxim)
(: Manner GriceanMaxim)

; Check maxim violations
(: violates-maxim (-> Turn DialogueState GriceanMaxim Bool))
(: maxim-violation-type (-> Turn DialogueState GriceanMaxim ViolationType))

; === Implicature ===

(: Implicature Type)
(: ScalarImplicature Implicature)
(: QuantityImplicature Implicature)
(: FloutingImplicature Implicature)

; Compute implicatures
(: compute-implicatures (-> Turn DialogueState (List Implicature)))

; Scalar implicature rules
(= (scalar-implicature "some" $context)
   (ScalarImplicature "some" (Not "all") ["some" "many" "most" "all"]))

(= (scalar-implicature "or" $context)
   (ScalarImplicature "or" (Not "and") ["or" "and"]))

(= (scalar-implicature "possible" $context)
   (ScalarImplicature "possible" (Not "certain") ["possible" "probable" "certain"]))

; === Relevance ===

(: relevance-score (-> Interpretation DialogueState Float))
(: cognitive-effects (-> Interpretation DialogueState Effects))
(: processing-effort (-> Turn Interpretation Float))

; Choose most relevant interpretation
(: choose-interpretation (-> Turn (List Interpretation) Interpretation))

(= (choose-interpretation $turn $interpretations)
   (argmax (lambda $i (relevance-score $i (turn-context $turn)))
           $interpretations))

; === Felicity Conditions ===

(: felicity-satisfied (-> SpeechAct DialogueState Bool))

; Assertion felicity: speaker believes proposition
(= (felicity-satisfied (Assert $prop _ _) $state)
   (speaker-believes $prop $state))

; Request felicity: hearer can perform
(= (felicity-satisfied (Directive $action Request $addressee) $state)
   (and (hearer-can-perform $action $state)
        (speaker-wants $action $state)))

; Promise felicity: speaker intends to perform
(= (felicity-satisfied (Commissive $action Promise) $state)
   (speaker-intends $action $state))
```

---

## Integration with Correction

### Pragmatics-Aware Correction

```rust
/// Pragmatics-aware correction validator
pub struct PragmaticCorrectionValidator {
    speech_act_classifier: SpeechActClassifier,
    implicature_engine: ImplicatureEngine,
    indirect_resolver: IndirectActResolver,
}

impl PragmaticCorrectionValidator {
    /// Validate that correction preserves pragmatic meaning
    pub fn validate_correction(
        &self,
        original: &Turn,
        correction: &CorrectionCandidate,
        context: &DialogueState,
    ) -> PragmaticValidation {
        // Classify original speech act
        let original_act = self.speech_act_classifier.classify(original, context);

        // Create hypothetical corrected turn
        let corrected_text = correction.apply_to(&original.raw_text);
        let corrected_turn = original.with_text(corrected_text);
        let corrected_act = self.speech_act_classifier.classify(&corrected_turn, context);

        // Check if speech act type preserved
        let act_preserved = self.same_act_type(&original_act.illocution.act_type,
                                                &corrected_act.illocution.act_type);

        // Check implicatures
        let original_implicatures = self.implicature_engine.compute_implicatures(original, context);
        let corrected_implicatures = self.implicature_engine.compute_implicatures(&corrected_turn, context);
        let implicatures_preserved = self.implicatures_compatible(
            &original_implicatures,
            &corrected_implicatures
        );

        // Check indirect meaning
        let indirect_preserved = self.check_indirect_preserved(
            &original_act,
            &corrected_act,
            context
        );

        PragmaticValidation {
            valid: act_preserved && implicatures_preserved && indirect_preserved,
            act_preserved,
            implicatures_preserved,
            indirect_preserved,
            original_act: original_act.illocution.act_type,
            corrected_act: corrected_act.illocution.act_type,
            lost_implicatures: self.find_lost_implicatures(
                &original_implicatures,
                &corrected_implicatures
            ),
        }
    }

    /// Check if same speech act type
    fn same_act_type(&self, act1: &SpeechAct, act2: &SpeechAct) -> bool {
        std::mem::discriminant(act1) == std::mem::discriminant(act2)
    }

    /// Check if implicatures are compatible
    fn implicatures_compatible(
        &self,
        original: &[Implicature],
        corrected: &[Implicature],
    ) -> bool {
        // All original scalar implicatures should be preserved
        for orig_imp in original {
            if let Implicature::Scalar { trigger, scale, .. } = orig_imp {
                let preserved = corrected.iter().any(|c| {
                    if let Implicature::Scalar { trigger: t, scale: s, .. } = c {
                        trigger == t && scale == s
                    } else {
                        false
                    }
                });

                if !preserved {
                    return false;
                }
            }
        }

        true
    }

    /// Find implicatures lost in correction
    fn find_lost_implicatures(
        &self,
        original: &[Implicature],
        corrected: &[Implicature],
    ) -> Vec<Implicature> {
        original.iter()
            .filter(|o| !corrected.iter().any(|c| self.implicature_equivalent(o, c)))
            .cloned()
            .collect()
    }

    /// Rank corrections by pragmatic preservation
    pub fn rank_by_pragmatics(
        &self,
        candidates: Vec<CorrectionCandidate>,
        original: &Turn,
        context: &DialogueState,
    ) -> Vec<(CorrectionCandidate, f64)> {
        candidates.into_iter()
            .map(|candidate| {
                let validation = self.validate_correction(original, &candidate, context);
                let score = self.compute_pragmatic_score(&validation);
                (candidate, score)
            })
            .sorted_by(|a, b| b.1.partial_cmp(&a.1).unwrap())
            .collect()
    }

    /// Compute pragmatic preservation score
    fn compute_pragmatic_score(&self, validation: &PragmaticValidation) -> f64 {
        let mut score = 0.0;

        if validation.act_preserved {
            score += 0.4;
        }

        if validation.implicatures_preserved {
            score += 0.3;
        }

        if validation.indirect_preserved {
            score += 0.2;
        }

        // Penalize for lost implicatures
        score -= 0.1 * validation.lost_implicatures.len() as f64;

        score.max(0.0)
    }
}

/// Result of pragmatic validation
pub struct PragmaticValidation {
    /// Overall validity
    valid: bool,

    /// Speech act type preserved
    act_preserved: bool,

    /// Implicatures preserved
    implicatures_preserved: bool,

    /// Indirect meaning preserved
    indirect_preserved: bool,

    /// Original speech act
    original_act: SpeechAct,

    /// Corrected speech act
    corrected_act: SpeechAct,

    /// Implicatures lost in correction
    lost_implicatures: Vec<Implicature>,
}
```

---

## Summary

Pragmatic reasoning provides deep understanding of communicative intent:

1. **Speech Act Theory** - Austin/Searle framework with felicity conditions
2. **Speech Act Classification** - Pattern and context-based classification
3. **Gricean Maxims** - Cooperative principle violation detection
4. **Implicature Computation** - Scalar, quantity, manner, and flouting implicatures
5. **Indirect Speech Acts** - Resolution of conventional indirect forms
6. **Relevance Theory** - Optimal relevance-based interpretation
7. **Correction Integration** - Validating pragmatic preservation

---

## References

- Austin, J.L. (1962). "How to Do Things with Words"
- Searle, J.R. (1969). "Speech Acts: An Essay in the Philosophy of Language"
- Grice, H.P. (1975). "Logic and Conversation"
- Levinson, S.C. (1983). "Pragmatics"
- Sperber, D. & Wilson, D. (1986). "Relevance: Communication and Cognition"
- Horn, L. (2004). "Implicature" in Handbook of Pragmatics

See [../llm-integration/README.md](../llm-integration/README.md) for LLM agent integration.
