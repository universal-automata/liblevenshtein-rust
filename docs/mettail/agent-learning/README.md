# Agent Learning and Feedback Integration

## Overview

The Agent Learning layer provides adaptive improvement capabilities for the correction
WFST architecture. By collecting user feedback, learning error patterns, modeling user
preferences, and performing online weight updates, the system continuously improves
correction quality over time.

This layer sits above the dialogue context and LLM integration layers, observing
corrections across the entire pipeline and adapting based on user responses.

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                    AGENT LEARNING ARCHITECTURE                               │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                              │
│  ┌────────────────────────────────────────────────────────────────────────┐ │
│  │                    FEEDBACK COLLECTION LAYER                           │ │
│  │  ┌──────────────────┐  ┌──────────────────┐  ┌──────────────────┐     │ │
│  │  │ Implicit Signal  │  │ Explicit Signal  │  │ Correction       │     │ │
│  │  │ Detector         │  │ Collector        │  │ Tracker          │     │ │
│  │  │ (acceptance,     │  │ (thumbs, stars,  │  │ (accept, reject, │     │ │
│  │  │  rejection,      │  │  comments)       │  │  modify)         │     │ │
│  │  │  modification)   │  │                  │  │                  │     │ │
│  │  └────────┬─────────┘  └────────┬─────────┘  └────────┬─────────┘     │ │
│  │           └─────────────────────┼─────────────────────┘               │ │
│  │                                 ▼                                      │ │
│  │              ┌──────────────────────────────────┐                     │ │
│  │              │        FeedbackStore             │                     │ │
│  │              │        (PathMap-backed)          │                     │ │
│  │              └────────────────┬─────────────────┘                     │ │
│  └───────────────────────────────┼───────────────────────────────────────┘ │
│                                  │                                         │
│  ┌───────────────────────────────┼───────────────────────────────────────┐ │
│  │                               ▼                                        │ │
│  │                    PATTERN LEARNING LAYER                              │ │
│  │  ┌──────────────────┐  ┌──────────────────┐  ┌──────────────────┐     │ │
│  │  │ Error Pattern    │  │ Pattern          │  │ Pattern          │     │ │
│  │  │ Extractor        │  │ Clusterer        │  │ Generalizer      │     │ │
│  │  │ (token, n-gram,  │  │ (similarity,     │  │ (abstraction,    │     │ │
│  │  │  phonetic)       │  │  frequency)      │  │  rule synthesis) │     │ │
│  │  └────────┬─────────┘  └────────┬─────────┘  └────────┬─────────┘     │ │
│  │           └─────────────────────┼─────────────────────┘               │ │
│  │                                 ▼                                      │ │
│  │              ┌──────────────────────────────────┐                     │ │
│  │              │        PatternStore              │                     │ │
│  │              │        (PathMap-backed)          │                     │ │
│  │              └────────────────┬─────────────────┘                     │ │
│  └───────────────────────────────┼───────────────────────────────────────┘ │
│                                  │                                         │
│  ┌───────────────────────────────┼───────────────────────────────────────┐ │
│  │                               ▼                                        │ │
│  │                    USER PREFERENCE LAYER                               │ │
│  │  ┌──────────────────┐  ┌──────────────────┐  ┌──────────────────┐     │ │
│  │  │ Vocabulary       │  │ Style            │  │ Domain           │     │ │
│  │  │ Modeler          │  │ Profiler         │  │ Detector         │     │ │
│  │  │ (personal dict,  │  │ (formality,      │  │ (technical,      │     │ │
│  │  │  technical)      │  │  tone)           │  │  casual)         │     │ │
│  │  └────────┬─────────┘  └────────┬─────────┘  └────────┬─────────┘     │ │
│  │           └─────────────────────┼─────────────────────┘               │ │
│  │                                 ▼                                      │ │
│  │              ┌──────────────────────────────────┐                     │ │
│  │              │        UserProfileStore          │                     │ │
│  │              │        (PathMap-backed)          │                     │ │
│  │              └────────────────┬─────────────────┘                     │ │
│  └───────────────────────────────┼───────────────────────────────────────┘ │
│                                  │                                         │
│  ┌───────────────────────────────┼───────────────────────────────────────┐ │
│  │                               ▼                                        │ │
│  │                    ONLINE LEARNING LAYER                               │ │
│  │  ┌──────────────────┐  ┌──────────────────┐  ┌──────────────────┐     │ │
│  │  │ Weight           │  │ Threshold        │  │ Model            │     │ │
│  │  │ Updater          │  │ Adapter          │  │ Versioner        │     │ │
│  │  │ (edit costs,     │  │ (confidence,     │  │ (checkpointing,  │     │ │
│  │  │  feature wts)    │  │  acceptance)     │  │  rollback)       │     │ │
│  │  └────────┬─────────┘  └────────┬─────────┘  └────────┬─────────┘     │ │
│  │           └─────────────────────┼─────────────────────┘               │ │
│  │                                 ▼                                      │ │
│  │              ┌──────────────────────────────────┐                     │ │
│  │              │        ModelStore                │                     │ │
│  │              │        (PathMap-backed)          │                     │ │
│  │              └──────────────────────────────────┘                     │ │
│  └────────────────────────────────────────────────────────────────────────┘ │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
```

## Core Components

### 1. Feedback Collection

The feedback collection layer captures user responses to corrections:

**Implicit Signals**:
- Acceptance (user proceeds without modification)
- Rejection (user reverts to original)
- Modification (user edits the correction)
- Time-to-decision (quick accept vs. deliberation)

**Explicit Signals**:
- Thumbs up/down ratings
- Star ratings (1-5)
- Written comments
- "Report error" actions

**Correction Tracking**:
- Original text
- Proposed correction
- Final user action
- Context at correction time

### 2. Pattern Learning

The pattern learning layer identifies recurring error patterns:

**Pattern Extraction**:
- Token-level patterns (word → word)
- N-gram patterns (context-sensitive)
- Phonetic patterns (pronunciation-based)
- Morphological patterns (suffix/prefix)

**Pattern Clustering**:
- Similarity-based grouping
- Frequency analysis
- Error type classification

**Pattern Generalization**:
- Abstract patterns from concrete examples
- Rule synthesis from clusters
- Confidence estimation

### 3. User Preferences

The user preference layer models individual user characteristics:

**Vocabulary Modeling**:
- Personal dictionary (accepted words)
- Technical vocabulary (domain terms)
- Ignored words (intentional spellings)

**Style Profiling**:
- Formality level (0.0 = casual, 1.0 = formal)
- Vocabulary complexity
- Preferred correction aggressiveness

**Domain Detection**:
- Technical domains (medical, legal, programming)
- Writing context (email, chat, document)
- Language variety (British vs. American English)

### 4. Online Learning

The online learning layer updates model parameters incrementally:

**Weight Updates**:
- Edit distance costs
- Feature weights for ranking
- Pattern confidence scores

**Threshold Adaptation**:
- Confidence thresholds for suggestions
- Acceptance thresholds for auto-correction
- User-specific calibration

**Model Versioning**:
- Checkpoint creation
- A/B testing support
- Rollback capability

---

## Data Flow

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                         LEARNING DATA FLOW                                   │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                              │
│  User Input                                                                  │
│      │                                                                       │
│      ▼                                                                       │
│  ┌───────────────────────────────────────────────────────────────────────┐  │
│  │               THREE-TIER WFST + DIALOGUE + LLM                        │  │
│  │               (correction with current model)                          │  │
│  └───────────────────────────────────────────────────────────────────────┘  │
│      │                                                                       │
│      ▼                                                                       │
│  Correction Proposal                                                         │
│      │                                                                       │
│      ├───────────────────────────────────────────────────────┐              │
│      │                                                       │              │
│      ▼                                                       ▼              │
│  User Decision                                          Log to              │
│  (accept/reject/modify)                                 FeedbackStore       │
│      │                                                       │              │
│      │                                                       │              │
│      ▼                                                       │              │
│  ┌─────────────────────────────────────────┐                │              │
│  │         Feedback Signal                 │◄───────────────┘              │
│  │  ┌─────────────┐  ┌─────────────┐      │                                │
│  │  │ Implicit    │  │ Explicit    │      │                                │
│  │  │ (action)    │  │ (rating)    │      │                                │
│  │  └──────┬──────┘  └──────┬──────┘      │                                │
│  │         └─────────┬──────┘             │                                │
│  └───────────────────┼────────────────────┘                                │
│                      │                                                      │
│      ┌───────────────┼───────────────┬───────────────┐                     │
│      │               │               │               │                     │
│      ▼               ▼               ▼               ▼                     │
│  ┌────────┐    ┌──────────┐   ┌──────────┐   ┌───────────┐                │
│  │Pattern │    │ User     │   │ Weight   │   │ Threshold │                │
│  │Extract │    │ Profile  │   │ Update   │   │ Adapt     │                │
│  └───┬────┘    └────┬─────┘   └────┬─────┘   └─────┬─────┘                │
│      │              │              │               │                       │
│      ▼              ▼              ▼               ▼                       │
│  PatternStore  ProfileStore   WeightStore   ThresholdStore                 │
│      │              │              │               │                       │
│      └──────────────┴──────────────┴───────────────┘                       │
│                              │                                              │
│                              ▼                                              │
│                    Updated Correction Model                                 │
│                              │                                              │
│                              ▼                                              │
│                    Next Correction Cycle                                    │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
```

---

## Core Data Structures

### Feedback Types

```rust
/// User feedback on a correction
pub struct Feedback {
    feedback_id: FeedbackId,
    user_id: UserId,
    session_id: SessionId,
    timestamp: Timestamp,

    /// The correction being evaluated
    correction: CorrectionRecord,

    /// User's response
    response: FeedbackResponse,

    /// Context at feedback time
    context: FeedbackContext,
}

/// User's response to a correction
pub enum FeedbackResponse {
    /// User accepted the correction as-is
    Accept {
        time_to_decision_ms: u64,
    },

    /// User rejected the correction, kept original
    Reject {
        time_to_decision_ms: u64,
    },

    /// User modified the correction
    Modify {
        modification: String,
        time_to_decision_ms: u64,
    },

    /// User provided explicit rating
    Rate {
        rating: Rating,
        comment: Option<String>,
    },
}

/// Rating scale
pub enum Rating {
    ThumbsUp,
    ThumbsDown,
    Stars(u8),  // 1-5
}
```

### Learned Patterns

```rust
/// A learned error pattern
pub struct LearnedPattern {
    pattern_id: PatternId,

    /// Pattern specification
    pattern: PatternSpec,

    /// Correction template
    correction: CorrectionTemplate,

    /// Learning statistics
    stats: PatternStats,

    /// Confidence score
    confidence: f64,
}

/// Pattern specification
pub enum PatternSpec {
    /// Exact token replacement
    TokenReplace {
        error: String,
        correction: String,
    },

    /// Context-sensitive n-gram
    NGram {
        left_context: Vec<String>,  // [] = any
        error: String,
        right_context: Vec<String>,
        correction: String,
    },

    /// Phonetic similarity
    Phonetic {
        error_phonemes: Vec<Phoneme>,
        correction: String,
    },

    /// Morphological pattern
    Morphological {
        error_pattern: MorphPattern,  // e.g., *tion -> *sion
        correction_template: String,
    },

    /// Regex-based pattern
    Regex {
        pattern: String,
        replacement: String,
    },
}

/// Pattern learning statistics
pub struct PatternStats {
    /// Times pattern matched
    match_count: u64,

    /// Times correction was accepted
    accept_count: u64,

    /// Times correction was rejected
    reject_count: u64,

    /// Times correction was modified
    modify_count: u64,

    /// First seen timestamp
    first_seen: Timestamp,

    /// Last seen timestamp
    last_seen: Timestamp,
}
```

### User Profile

```rust
/// User preference profile
pub struct UserProfile {
    user_id: UserId,

    /// Vocabulary preferences
    vocabulary: VocabularyProfile,

    /// Style preferences
    style: StyleProfile,

    /// Domain settings
    domains: Vec<DomainProfile>,

    /// Correction preferences
    correction: CorrectionPreferences,

    /// Learning metadata
    metadata: ProfileMetadata,
}

/// Vocabulary preferences
pub struct VocabularyProfile {
    /// Words always accepted (personal dictionary)
    accepted_words: HashSet<String>,

    /// Words to always ignore (intentional spellings)
    ignored_words: HashSet<String>,

    /// Technical vocabulary by domain
    technical_vocab: HashMap<Domain, HashSet<String>>,

    /// Vocabulary complexity level (0.0 = simple, 1.0 = advanced)
    complexity_level: f64,
}

/// Style preferences
pub struct StyleProfile {
    /// Formality level (0.0 = casual, 1.0 = formal)
    formality: f64,

    /// Correction aggressiveness (0.0 = conservative, 1.0 = aggressive)
    aggressiveness: f64,

    /// Preferred variety (British, American, etc.)
    language_variety: LanguageVariety,

    /// Tone preferences
    tone_preferences: TonePreferences,
}

/// Correction preferences
pub struct CorrectionPreferences {
    /// Enable auto-correction (vs. suggestions only)
    auto_correct: bool,

    /// Confidence threshold for showing suggestions
    suggestion_threshold: f64,

    /// Confidence threshold for auto-correction
    auto_correct_threshold: f64,

    /// Maximum suggestions to show
    max_suggestions: usize,

    /// Enable learning from user actions
    enable_learning: bool,
}
```

### Online Learning State

```rust
/// Online learning model state
pub struct LearningModel {
    model_id: ModelId,
    version: ModelVersion,

    /// Edit distance weights
    edit_weights: EditWeights,

    /// Feature weights for ranking
    feature_weights: FeatureWeights,

    /// Learned pattern weights
    pattern_weights: HashMap<PatternId, f64>,

    /// Adaptive thresholds
    thresholds: AdaptiveThresholds,

    /// Training metadata
    metadata: LearningMetadata,
}

/// Customizable edit distance weights
pub struct EditWeights {
    /// Insertion cost by character
    insertion: HashMap<char, f64>,

    /// Deletion cost by character
    deletion: HashMap<char, f64>,

    /// Substitution cost matrix
    substitution: HashMap<(char, char), f64>,

    /// Transposition cost
    transposition: f64,

    /// Default costs
    default_insertion: f64,
    default_deletion: f64,
    default_substitution: f64,
}

/// Feature weights for candidate ranking
pub struct FeatureWeights {
    /// Edit distance weight
    edit_distance: f64,

    /// Language model probability weight
    language_model: f64,

    /// Frequency weight
    frequency: f64,

    /// Phonetic similarity weight
    phonetic: f64,

    /// Context match weight
    context: f64,

    /// User preference weight
    user_preference: f64,
}

/// Adaptive thresholds
pub struct AdaptiveThresholds {
    /// Per-user threshold adjustments
    user_adjustments: HashMap<UserId, ThresholdAdjustment>,

    /// Per-domain threshold adjustments
    domain_adjustments: HashMap<Domain, ThresholdAdjustment>,

    /// Global baseline thresholds
    baseline: BaselineThresholds,
}
```

---

## PathMap Storage Schema

```
PathMap Key Structure (Agent Learning):
========================================

/learning/
    /feedback/{feedback_id}/
        user_id -> user identifier
        session_id -> session identifier
        timestamp -> unix timestamp
        correction/
            original -> original text
            proposed -> proposed correction
            final -> final text after user action
            tier -> correction tier (1=lexical, 2=syntactic, 3=semantic)
        response/
            type -> accept|reject|modify|rate
            time_ms -> time to decision
            rating -> optional rating value
            comment -> optional comment
        context/
            dialogue_id -> dialogue context (if applicable)
            turn_id -> turn context (if applicable)
            position -> position in text

    /pattern/{pattern_id}/
        type -> token_replace|ngram|phonetic|morphological|regex
        spec/ -> pattern specification (type-dependent)
        correction -> correction template
        stats/
            match_count -> total matches
            accept_count -> accepted corrections
            reject_count -> rejected corrections
            modify_count -> modified corrections
            first_seen -> timestamp
            last_seen -> timestamp
        confidence -> confidence score

    /user/{user_id}/
        vocabulary/
            accepted/ -> {word} -> true
            ignored/ -> {word} -> true
            technical/{domain}/ -> {word} -> true
            complexity -> complexity level
        style/
            formality -> formality level
            aggressiveness -> correction aggressiveness
            variety -> language variety
        preferences/
            auto_correct -> boolean
            suggestion_threshold -> float
            auto_correct_threshold -> float
            max_suggestions -> int
            enable_learning -> boolean
        metadata/
            created_at -> timestamp
            updated_at -> timestamp
            feedback_count -> total feedback items

    /model/{model_id}/
        version -> version number
        edit_weights/
            insertion/{char} -> cost
            deletion/{char} -> cost
            substitution/{char1}/{char2} -> cost
            transposition -> cost
            defaults/
                insertion -> default cost
                deletion -> default cost
                substitution -> default cost
        feature_weights/
            edit_distance -> weight
            language_model -> weight
            frequency -> weight
            phonetic -> weight
            context -> weight
            user_preference -> weight
        pattern_weights/{pattern_id} -> weight
        thresholds/
            baseline/
                suggestion -> threshold
                auto_correct -> threshold
                confidence_min -> threshold
            user/{user_id}/
                suggestion_delta -> adjustment
                auto_correct_delta -> adjustment
            domain/{domain}/
                suggestion_delta -> adjustment
                auto_correct_delta -> adjustment
        metadata/
            created_at -> timestamp
            updated_at -> timestamp
            training_samples -> count
            checkpoint_path -> optional checkpoint file
```

---

## MeTTa Predicates

### Feedback Predicates

```metta
; Feedback types
(: Feedback Type)
(: FeedbackResponse Type)

; Feedback constructors
(: feedback-accept (-> u64 FeedbackResponse))     ; time_ms
(: feedback-reject (-> u64 FeedbackResponse))     ; time_ms
(: feedback-modify (-> String u64 FeedbackResponse))  ; modification, time_ms
(: feedback-rate (-> Rating String FeedbackResponse)) ; rating, comment

; Feedback analysis
(: feedback-positive (-> FeedbackResponse Bool))
(: feedback-negative (-> FeedbackResponse Bool))
(: feedback-signal-strength (-> FeedbackResponse Float))

; Aggregate feedback
(: pattern-acceptance-rate (-> PatternId Float))
(: user-acceptance-rate (-> UserId Float))
(: correction-success-rate (-> CorrectionTier Float))
```

### Pattern Learning Predicates

```metta
; Pattern types
(: PatternSpec Type)
(: LearnedPattern Type)

; Pattern constructors
(: token-pattern (-> String String PatternSpec))
(: ngram-pattern (-> (List String) String (List String) String PatternSpec))
(: phonetic-pattern (-> (List Phoneme) String PatternSpec))
(: morph-pattern (-> String String PatternSpec))

; Pattern operations
(: pattern-matches (-> PatternSpec String Bool))
(: pattern-apply (-> PatternSpec String (Maybe String)))
(: pattern-confidence (-> LearnedPattern Float))
(: pattern-should-apply (-> LearnedPattern String Float Bool))

; Pattern learning
(: extract-patterns (-> (List Feedback) (List PatternSpec)))
(: cluster-patterns (-> (List PatternSpec) (List (List PatternSpec))))
(: generalize-pattern (-> (List PatternSpec) (Maybe PatternSpec)))
(: update-pattern-stats (-> LearnedPattern Feedback LearnedPattern))
```

### User Preference Predicates

```metta
; User profile types
(: UserProfile Type)
(: VocabularyProfile Type)
(: StyleProfile Type)

; Profile queries
(: user-accepts-word (-> UserId String Bool))
(: user-ignores-word (-> UserId String Bool))
(: user-formality (-> UserId Float))
(: user-aggressiveness (-> UserId Float))
(: user-domain (-> UserId (Maybe Domain)))

; Profile updates
(: add-accepted-word (-> UserId String UserProfile UserProfile))
(: add-ignored-word (-> UserId String UserProfile UserProfile))
(: update-formality (-> UserId Float UserProfile UserProfile))
(: update-from-feedback (-> UserId Feedback UserProfile UserProfile))

; Personalization
(: personalize-corrections (-> UserId (List Correction) (List Correction)))
(: personalize-threshold (-> UserId Float Float))
```

### Online Learning Predicates

```metta
; Model types
(: LearningModel Type)
(: EditWeights Type)
(: FeatureWeights Type)

; Weight queries
(: edit-cost (-> LearningModel Char Char Float))
(: feature-weight (-> LearningModel Feature Float))
(: pattern-weight (-> LearningModel PatternId Float))

; Weight updates
(: update-edit-weight (-> LearningModel Char Char Float LearningModel))
(: update-feature-weight (-> LearningModel Feature Float LearningModel))
(: update-from-feedback (-> LearningModel Feedback LearningModel))

; Threshold adaptation
(: adapt-threshold (-> LearningModel UserId Feedback LearningModel))
(: get-effective-threshold (-> LearningModel UserId ThresholdType Float))

; Model management
(: checkpoint-model (-> LearningModel Path (Result () Error)))
(: restore-model (-> Path (Result LearningModel Error)))
(: model-version (-> LearningModel ModelVersion))
```

---

## Integration with Correction Pipeline

The agent learning layer integrates with the three-tier WFST, dialogue, and LLM layers:

```
┌─────────────────────────────────────────────────────────────────────────────┐
│              FULL CORRECTION ARCHITECTURE WITH LEARNING                      │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                              │
│  User Input                                                                  │
│      │                                                                       │
│      ▼                                                                       │
│  ┌────────────────────────────────────────────────────────────────────────┐ │
│  │                    DIALOGUE CONTEXT LAYER                              │ │
│  │  (Turn tracking, entity registry, topic graph)                         │ │
│  └───────────────────────────────────────────────────────────────────────┬┘ │
│                                                                          │  │
│      ┌───────────────────────────────────────────────────────────────────┘  │
│      │                                                                       │
│      ▼                                                                       │
│  ┌────────────────────────────────────────────────────────────────────────┐ │
│  │                    THREE-TIER WFST                                     │ │
│  │  ┌──────────────┐  ┌──────────────┐  ┌──────────────┐                 │ │
│  │  │ Tier 1:      │→ │ Tier 2:      │→ │ Tier 3:      │                 │ │
│  │  │ Lexical      │  │ Syntactic    │  │ Semantic     │                 │ │
│  │  │              │  │              │  │              │                 │ │
│  │  │ ┌──────────┐ │  │ ┌──────────┐ │  │ ┌──────────┐ │                 │ │
│  │  │ │Learned   │ │  │ │Learned   │ │  │ │Learned   │ │◄── Learning    │ │
│  │  │ │Patterns  │ │  │ │Patterns  │ │  │ │Patterns  │ │    Model       │ │
│  │  │ └──────────┘ │  │ └──────────┘ │  │ └──────────┘ │                 │ │
│  │  │ ┌──────────┐ │  │ ┌──────────┐ │  │ ┌──────────┐ │                 │ │
│  │  │ │User Dict │ │  │ │User      │ │  │ │User      │ │◄── User        │ │
│  │  │ │          │ │  │ │Prefs     │ │  │ │Prefs     │ │    Profile     │ │
│  │  │ └──────────┘ │  │ └──────────┘ │  │ └──────────┘ │                 │ │
│  │  │ ┌──────────┐ │  │              │  │              │                 │ │
│  │  │ │Edit      │ │  │              │  │              │◄── Adaptive    │ │
│  │  │ │Weights   │ │  │              │  │              │    Weights     │ │
│  │  │ └──────────┘ │  │              │  │              │                 │ │
│  │  └──────────────┘  └──────────────┘  └──────────────┘                 │ │
│  └───────────────────────────────────────────────────────────────────────┬┘ │
│                                                                          │  │
│      ┌───────────────────────────────────────────────────────────────────┘  │
│      │                                                                       │
│      ▼                                                                       │
│  ┌────────────────────────────────────────────────────────────────────────┐ │
│  │                    LLM INTEGRATION LAYER                               │ │
│  │  (Prompt preprocessing, response postprocessing)                       │ │
│  └───────────────────────────────────────────────────────────────────────┬┘ │
│                                                                          │  │
│      ┌───────────────────────────────────────────────────────────────────┘  │
│      │                                                                       │
│      ▼                                                                       │
│  Correction Proposal ────────────────────────────────────────┐              │
│      │                                                       │              │
│      ▼                                                       ▼              │
│  User Sees Correction                               Log Correction          │
│      │                                                       │              │
│      ▼                                                       │              │
│  User Action ────────────────────────────────────────────────┤              │
│  (accept/reject/modify)                                      │              │
│      │                                                       │              │
│      ▼                                                       ▼              │
│  Final Output                                       ┌─────────────────────┐ │
│                                                     │   AGENT LEARNING    │ │
│                                                     │   (feedback →       │ │
│                                                     │    pattern/profile/ │ │
│                                                     │    weight update)   │ │
│                                                     └─────────────────────┘ │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
```

---

## Learning Feedback Loop

The learning feedback loop ensures continuous improvement:

1. **Correction Proposal**: System generates correction using current model
2. **User Response**: User accepts, rejects, or modifies the correction
3. **Feedback Collection**: System logs the feedback with full context
4. **Pattern Extraction**: Extract error patterns from feedback
5. **Profile Update**: Update user preferences based on action
6. **Weight Adjustment**: Incrementally update model weights
7. **Threshold Adaptation**: Adjust thresholds based on user behavior
8. **Model Application**: Apply updated model to next correction

This creates a continuous learning loop that personalizes and improves over time.

---

## Document Organization

This section is organized into the following documents:

| Document | Description |
|----------|-------------|
| [01-feedback-collection.md](./01-feedback-collection.md) | Capturing implicit and explicit user feedback |
| [02-pattern-learning.md](./02-pattern-learning.md) | Extracting and generalizing error patterns |
| [03-user-preferences.md](./03-user-preferences.md) | Modeling vocabulary, style, and domain preferences |
| [04-online-learning.md](./04-online-learning.md) | Incremental weight updates and threshold adaptation |

---

## Related Documentation

- [Dialogue Context Layer](../dialogue/README.md) - Dialogue state management
- [LLM Integration Layer](../llm-integration/README.md) - LLM preprocessing/postprocessing
- [Three-Tier WFST Architecture](../correction-wfst/01-architecture-overview.md) - Base correction architecture
- [Gap Analysis](../reference/gap-analysis.md) - Implementation gaps and priorities

---

## Key Design Principles

### 1. Privacy-First Learning

All learning happens locally by default:
- User profiles stored in user-controlled PathMap
- No feedback shared without explicit consent
- Federated learning for cross-user patterns (opt-in)

### 2. Incremental Updates

Learning happens incrementally:
- No batch retraining required
- Immediate feedback incorporation
- Graceful degradation if learning disabled

### 3. Explainability

Learning decisions are explainable:
- Pattern provenance tracked
- Weight changes logged
- User can inspect learned patterns

### 4. Reversibility

All learning is reversible:
- Model checkpoints for rollback
- User can reset preferences
- Patterns can be deleted

### 5. Adaptive Sensitivity

System adapts to user sensitivity:
- More conservative for users who reject often
- More aggressive for users who accept often
- Per-domain and per-context calibration
