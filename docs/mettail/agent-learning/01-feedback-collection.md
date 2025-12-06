# Feedback Collection

## Overview

The feedback collection layer captures user responses to corrections, forming the foundation
for all learning in the agent learning system. It distinguishes between implicit signals
(user behavior) and explicit signals (user ratings), normalizes feedback for downstream
processing, and maintains a comprehensive feedback history in PathMap storage.

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                    FEEDBACK COLLECTION ARCHITECTURE                          │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                              │
│  Correction Proposal                                                         │
│  (from WFST/LLM pipeline)                                                   │
│      │                                                                       │
│      ▼                                                                       │
│  ┌───────────────────────────────────────────────────────────────────────┐  │
│  │                    CORRECTION TRACKER                                  │  │
│  │  ┌─────────────────────────────────────────────────────────────────┐  │  │
│  │  │ CorrectionRecord                                                │  │  │
│  │  │  - correction_id: unique identifier                             │  │  │
│  │  │  - original: original text                                      │  │  │
│  │  │  - proposed: proposed correction                                │  │  │
│  │  │  - tier: lexical/syntactic/semantic                            │  │  │
│  │  │  - confidence: correction confidence                            │  │  │
│  │  │  - context: dialogue/document context                           │  │  │
│  │  │  - timestamp: proposal time                                     │  │  │
│  │  └─────────────────────────────────────────────────────────────────┘  │  │
│  └───────────────────────────────────────────────────────────────────────┘  │
│      │                                                                       │
│      ├────────────────────────────────┬───────────────────────────┐         │
│      │                                │                           │         │
│      ▼                                ▼                           ▼         │
│  User Sees                      Timer Starts               Log Pending      │
│  Correction                     (time_to_decision)         Correction       │
│      │                                │                           │         │
│      ▼                                │                           │         │
│  ┌──────────────────────────────────────────────────────────────────────┐  │
│  │                    USER ACTION                                        │  │
│  │  ┌─────────────┐  ┌─────────────┐  ┌─────────────┐  ┌─────────────┐  │  │
│  │  │   ACCEPT    │  │   REJECT    │  │   MODIFY    │  │   IGNORE    │  │  │
│  │  │ (proceed    │  │ (revert to  │  │ (edit the   │  │ (dismiss    │  │  │
│  │  │  with       │  │  original)  │  │  correction)│  │  without    │  │  │
│  │  │  correction)│  │             │  │             │  │  action)    │  │  │
│  │  └──────┬──────┘  └──────┬──────┘  └──────┬──────┘  └──────┬──────┘  │  │
│  │         │                │                │                │         │  │
│  └─────────┼────────────────┼────────────────┼────────────────┼─────────┘  │
│            │                │                │                │            │
│            └────────────────┴────────────────┴────────────────┘            │
│                                      │                                      │
│                                      ▼                                      │
│  ┌───────────────────────────────────────────────────────────────────────┐  │
│  │                    IMPLICIT SIGNAL DETECTOR                           │  │
│  │  ┌─────────────────────────────────────────────────────────────────┐  │  │
│  │  │ Behavioral Analysis                                             │  │  │
│  │  │  - action_type: accept/reject/modify/ignore                     │  │  │
│  │  │  - time_to_decision: milliseconds                               │  │  │
│  │  │  - edit_distance: for modifications                             │  │  │
│  │  │  - cursor_behavior: hesitation patterns                         │  │  │
│  │  │  - subsequent_edits: edits after acceptance                     │  │  │
│  │  └─────────────────────────────────────────────────────────────────┘  │  │
│  └───────────────────────────────────────────────────────────────────────┘  │
│      │                                                                       │
│      │         ┌────────────────────────────────────────────────────────┐   │
│      │         │                                                        │   │
│      │         ▼                                                        │   │
│      │  ┌───────────────────────────────────────────────────────────┐  │   │
│      │  │                 EXPLICIT SIGNAL COLLECTOR                  │  │   │
│      │  │  ┌─────────────────────────────────────────────────────┐  │  │   │
│      │  │  │ User Ratings                                        │  │  │   │
│      │  │  │  - thumbs_up/thumbs_down: binary rating             │  │  │   │
│      │  │  │  - star_rating: 1-5 scale                           │  │  │   │
│      │  │  │  - comment: free-form text                          │  │  │   │
│      │  │  │  - report_type: "wrong", "offensive", "other"       │  │  │   │
│      │  │  └─────────────────────────────────────────────────────┘  │  │   │
│      │  └───────────────────────────────────────────────────────────┘  │   │
│      │         │                                                        │   │
│      │         │                                                        │   │
│      └─────────┴────────────────────────┬───────────────────────────────┘   │
│                                         │                                    │
│                                         ▼                                    │
│  ┌───────────────────────────────────────────────────────────────────────┐  │
│  │                    FEEDBACK NORMALIZER                                │  │
│  │  ┌─────────────────────────────────────────────────────────────────┐  │  │
│  │  │ NormalizedFeedback                                              │  │  │
│  │  │  - signal_strength: -1.0 (strong negative) to +1.0 (positive)   │  │  │
│  │  │  - confidence: how confident we are in this signal              │  │  │
│  │  │  - learning_weight: how much this should affect learning        │  │  │
│  │  └─────────────────────────────────────────────────────────────────┘  │  │
│  └───────────────────────────────────────────────────────────────────────┘  │
│                                         │                                    │
│                                         ▼                                    │
│  ┌───────────────────────────────────────────────────────────────────────┐  │
│  │                    FEEDBACK STORE (PathMap)                           │  │
│  └───────────────────────────────────────────────────────────────────────┘  │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
```

---

## Feedback Signal Types

### Implicit Signals

Implicit signals are derived from user behavior without explicit rating actions:

| Signal | Detection Method | Interpretation |
|--------|-----------------|----------------|
| **Quick Accept** | Accept within 500ms | Strong positive (confident) |
| **Deliberate Accept** | Accept after 500ms-2s | Moderate positive (considered) |
| **Slow Accept** | Accept after >2s | Weak positive (uncertain) |
| **Immediate Reject** | Reject within 500ms | Strong negative (obvious error) |
| **Deliberate Reject** | Reject after 500ms-2s | Moderate negative (disagreement) |
| **Minor Modification** | Edit distance < 3 | Weak negative (close but wrong) |
| **Major Modification** | Edit distance >= 3 | Strong negative (significantly wrong) |
| **Ignore** | No action within timeout | Ambiguous (may not have noticed) |
| **Subsequent Edit** | Edit accepted text later | Delayed negative (accepted but wrong) |

### Explicit Signals

Explicit signals are direct user ratings:

| Signal | Values | Interpretation |
|--------|--------|----------------|
| **Thumbs Up** | Single action | Strong positive |
| **Thumbs Down** | Single action | Strong negative |
| **Star Rating** | 1-5 | Gradient signal |
| **Comment** | Free text | Qualitative feedback |
| **Report Wrong** | Single action | Very strong negative |
| **Report Offensive** | Single action | Content policy violation |

---

## Core Data Structures

### Correction Record

```rust
/// A record of a proposed correction
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct CorrectionRecord {
    /// Unique identifier for this correction
    pub correction_id: CorrectionId,

    /// Original text before correction
    pub original: String,

    /// Proposed correction
    pub proposed: String,

    /// Which tier produced this correction
    pub tier: CorrectionTier,

    /// Confidence score from the correction engine
    pub confidence: f64,

    /// Timestamp when correction was proposed
    pub timestamp: Timestamp,

    /// User who received the correction
    pub user_id: UserId,

    /// Session context
    pub session_id: SessionId,

    /// Position in the input
    pub position: TextPosition,

    /// Additional context
    pub context: CorrectionContext,
}

/// Correction tier
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum CorrectionTier {
    Lexical,    // Tier 1: Edit distance, phonetic
    Syntactic,  // Tier 2: Grammar, CFG
    Semantic,   // Tier 3: Type checking, coherence
    LLM,        // LLM-based correction
}

/// Position in text
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct TextPosition {
    /// Start offset (bytes)
    pub start: usize,
    /// End offset (bytes)
    pub end: usize,
    /// Line number (0-indexed)
    pub line: usize,
    /// Column number (0-indexed)
    pub column: usize,
}

/// Context surrounding a correction
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct CorrectionContext {
    /// Text before the correction span
    pub left_context: String,

    /// Text after the correction span
    pub right_context: String,

    /// Dialogue context (if applicable)
    pub dialogue_id: Option<DialogueId>,

    /// Turn context (if applicable)
    pub turn_id: Option<TurnId>,

    /// Document type
    pub document_type: DocumentType,

    /// Domain (if detected)
    pub domain: Option<Domain>,

    /// Alternative candidates that were not chosen
    pub alternatives: Vec<(String, f64)>,
}
```

### Feedback Types

```rust
/// Complete feedback record
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Feedback {
    /// Unique feedback identifier
    pub feedback_id: FeedbackId,

    /// The correction being evaluated
    pub correction: CorrectionRecord,

    /// User's response
    pub response: FeedbackResponse,

    /// Normalized signal for learning
    pub normalized: NormalizedFeedback,

    /// Timestamp of feedback
    pub timestamp: Timestamp,
}

/// User's response to a correction
#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum FeedbackResponse {
    /// User accepted the correction
    Accept(AcceptFeedback),

    /// User rejected the correction
    Reject(RejectFeedback),

    /// User modified the correction
    Modify(ModifyFeedback),

    /// User ignored the correction
    Ignore(IgnoreFeedback),

    /// User explicitly rated the correction
    Rate(RateFeedback),
}

/// Accept feedback details
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct AcceptFeedback {
    /// Time from proposal to acceptance (ms)
    pub time_to_decision_ms: u64,

    /// Whether user subsequently edited the accepted text
    pub subsequent_edit: Option<SubsequentEdit>,
}

/// Reject feedback details
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct RejectFeedback {
    /// Time from proposal to rejection (ms)
    pub time_to_decision_ms: u64,

    /// How user rejected (revert, delete, explicit reject button)
    pub rejection_method: RejectionMethod,
}

/// Modify feedback details
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ModifyFeedback {
    /// Time from proposal to modification (ms)
    pub time_to_decision_ms: u64,

    /// The user's modified version
    pub modified_text: String,

    /// Edit distance from proposed to modified
    pub edit_distance: usize,

    /// Type of modification
    pub modification_type: ModificationType,
}

/// Ignore feedback details
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct IgnoreFeedback {
    /// How long the correction was visible before timeout
    pub visible_duration_ms: u64,

    /// Whether user interacted with other parts of UI
    pub had_other_activity: bool,
}

/// Explicit rating feedback
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct RateFeedback {
    /// Rating type
    pub rating: Rating,

    /// Optional comment
    pub comment: Option<String>,

    /// Report type (if reporting)
    pub report_type: Option<ReportType>,
}

/// Rating types
#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum Rating {
    ThumbsUp,
    ThumbsDown,
    Stars(u8),  // 1-5
}

/// Report types for problematic corrections
#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum ReportType {
    Wrong,      // Factually incorrect
    Offensive,  // Content policy violation
    Unhelpful,  // Not useful
    Other(String),
}

/// Subsequent edit after acceptance
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct SubsequentEdit {
    /// Time after acceptance until edit (ms)
    pub time_after_accept_ms: u64,

    /// The edited text
    pub edited_text: String,

    /// Edit distance from accepted to edited
    pub edit_distance: usize,
}
```

### Normalized Feedback

```rust
/// Normalized feedback for learning algorithms
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct NormalizedFeedback {
    /// Signal strength: -1.0 (strong negative) to +1.0 (strong positive)
    pub signal_strength: f64,

    /// Confidence in the signal interpretation (0.0 to 1.0)
    pub confidence: f64,

    /// Learning weight (how much this should affect model updates)
    pub learning_weight: f64,

    /// Breakdown of contributing factors
    pub factors: FeedbackFactors,
}

/// Factors contributing to the normalized signal
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct FeedbackFactors {
    /// Action-based signal (-1.0 to 1.0)
    pub action_signal: f64,

    /// Timing-based signal (-1.0 to 1.0)
    pub timing_signal: f64,

    /// Edit-distance signal (for modifications, 0.0 to -1.0)
    pub edit_signal: Option<f64>,

    /// Explicit rating signal (if present)
    pub rating_signal: Option<f64>,

    /// Context confidence adjustment
    pub context_factor: f64,
}
```

---

## Feedback Collection Pipeline

### Stage 1: Correction Tracking

```rust
/// Tracks corrections awaiting feedback
pub struct CorrectionTracker {
    /// Pending corrections awaiting user response
    pending: HashMap<CorrectionId, PendingCorrection>,

    /// Timeout for implicit ignore detection
    ignore_timeout: Duration,

    /// PathMap storage
    pathmap: PathMap,
}

/// A correction awaiting feedback
struct PendingCorrection {
    record: CorrectionRecord,
    proposed_at: Instant,
    displayed_at: Option<Instant>,
    timer_handle: Option<TimerHandle>,
}

impl CorrectionTracker {
    /// Register a new correction proposal
    pub fn track_correction(&mut self, correction: CorrectionRecord) -> CorrectionId {
        let id = correction.correction_id.clone();

        let pending = PendingCorrection {
            record: correction,
            proposed_at: Instant::now(),
            displayed_at: None,
            timer_handle: None,
        };

        self.pending.insert(id.clone(), pending);

        // Start ignore timeout timer
        self.start_ignore_timer(&id);

        id
    }

    /// Mark correction as displayed to user
    pub fn mark_displayed(&mut self, id: &CorrectionId) {
        if let Some(pending) = self.pending.get_mut(id) {
            pending.displayed_at = Some(Instant::now());
        }
    }

    /// Record user action on a correction
    pub fn record_action(
        &mut self,
        id: &CorrectionId,
        action: UserAction,
    ) -> Result<Feedback, FeedbackError> {
        let pending = self.pending.remove(id)
            .ok_or(FeedbackError::CorrectionNotFound)?;

        // Cancel ignore timer
        if let Some(handle) = pending.timer_handle {
            handle.cancel();
        }

        // Calculate time to decision
        let time_to_decision = pending.displayed_at
            .map(|d| d.elapsed())
            .unwrap_or_else(|| pending.proposed_at.elapsed());

        // Create feedback response
        let response = self.action_to_response(action, time_to_decision);

        // Normalize feedback
        let normalized = self.normalize_feedback(&pending.record, &response);

        // Create feedback record
        let feedback = Feedback {
            feedback_id: FeedbackId::new(),
            correction: pending.record,
            response,
            normalized,
            timestamp: Timestamp::now(),
        };

        // Store in PathMap
        self.store_feedback(&feedback)?;

        Ok(feedback)
    }

    /// Handle ignore timeout
    fn handle_ignore_timeout(&mut self, id: &CorrectionId) -> Option<Feedback> {
        let pending = self.pending.remove(id)?;

        let visible_duration = pending.displayed_at
            .map(|d| d.elapsed())
            .unwrap_or_else(|| pending.proposed_at.elapsed());

        let response = FeedbackResponse::Ignore(IgnoreFeedback {
            visible_duration_ms: visible_duration.as_millis() as u64,
            had_other_activity: false, // Would need UI integration to detect
        });

        let normalized = self.normalize_feedback(&pending.record, &response);

        let feedback = Feedback {
            feedback_id: FeedbackId::new(),
            correction: pending.record,
            response,
            normalized,
            timestamp: Timestamp::now(),
        };

        self.store_feedback(&feedback).ok()?;

        Some(feedback)
    }
}
```

### Stage 2: Implicit Signal Detection

```rust
/// Detects implicit signals from user behavior
pub struct ImplicitSignalDetector {
    /// Timing thresholds for signal interpretation
    thresholds: TimingThresholds,
}

/// Timing thresholds for implicit signal detection
#[derive(Clone, Debug)]
pub struct TimingThresholds {
    /// Below this is "quick" (strong signal)
    pub quick_threshold_ms: u64,

    /// Below this is "deliberate" (moderate signal)
    pub deliberate_threshold_ms: u64,

    /// Above this is "slow" (weak signal)
    pub slow_threshold_ms: u64,
}

impl Default for TimingThresholds {
    fn default() -> Self {
        Self {
            quick_threshold_ms: 500,
            deliberate_threshold_ms: 2000,
            slow_threshold_ms: 5000,
        }
    }
}

impl ImplicitSignalDetector {
    /// Analyze user action for implicit signals
    pub fn analyze_action(
        &self,
        action: &UserAction,
        time_ms: u64,
    ) -> ImplicitSignal {
        match action {
            UserAction::Accept => self.analyze_accept(time_ms),
            UserAction::Reject(_) => self.analyze_reject(time_ms),
            UserAction::Modify(text) => self.analyze_modify(text, time_ms),
            UserAction::Ignore => ImplicitSignal::Ambiguous,
        }
    }

    fn analyze_accept(&self, time_ms: u64) -> ImplicitSignal {
        if time_ms < self.thresholds.quick_threshold_ms {
            ImplicitSignal::StrongPositive {
                reason: "Quick accept indicates high confidence".into(),
            }
        } else if time_ms < self.thresholds.deliberate_threshold_ms {
            ImplicitSignal::ModeratePositive {
                reason: "Deliberate accept indicates considered agreement".into(),
            }
        } else if time_ms < self.thresholds.slow_threshold_ms {
            ImplicitSignal::WeakPositive {
                reason: "Slow accept indicates uncertainty".into(),
            }
        } else {
            ImplicitSignal::Ambiguous
        }
    }

    fn analyze_reject(&self, time_ms: u64) -> ImplicitSignal {
        if time_ms < self.thresholds.quick_threshold_ms {
            ImplicitSignal::StrongNegative {
                reason: "Quick reject indicates obvious error".into(),
            }
        } else if time_ms < self.thresholds.deliberate_threshold_ms {
            ImplicitSignal::ModerateNegative {
                reason: "Deliberate reject indicates disagreement".into(),
            }
        } else {
            ImplicitSignal::WeakNegative {
                reason: "Slow reject indicates reluctant disagreement".into(),
            }
        }
    }

    fn analyze_modify(&self, modified: &str, time_ms: u64) -> ImplicitSignal {
        // Would need original and proposed to calculate edit distance
        // This is a simplified version
        ImplicitSignal::ModerateNegative {
            reason: "Modification indicates partial disagreement".into(),
        }
    }
}

/// Implicit signal interpretation
#[derive(Clone, Debug)]
pub enum ImplicitSignal {
    StrongPositive { reason: String },
    ModeratePositive { reason: String },
    WeakPositive { reason: String },
    Ambiguous,
    WeakNegative { reason: String },
    ModerateNegative { reason: String },
    StrongNegative { reason: String },
}

impl ImplicitSignal {
    /// Convert to numeric signal strength
    pub fn strength(&self) -> f64 {
        match self {
            Self::StrongPositive { .. } => 1.0,
            Self::ModeratePositive { .. } => 0.6,
            Self::WeakPositive { .. } => 0.3,
            Self::Ambiguous => 0.0,
            Self::WeakNegative { .. } => -0.3,
            Self::ModerateNegative { .. } => -0.6,
            Self::StrongNegative { .. } => -1.0,
        }
    }

    /// Confidence in this interpretation
    pub fn confidence(&self) -> f64 {
        match self {
            Self::StrongPositive { .. } | Self::StrongNegative { .. } => 0.9,
            Self::ModeratePositive { .. } | Self::ModerateNegative { .. } => 0.7,
            Self::WeakPositive { .. } | Self::WeakNegative { .. } => 0.5,
            Self::Ambiguous => 0.2,
        }
    }
}
```

### Stage 3: Explicit Signal Collection

```rust
/// Collects explicit user ratings
pub struct ExplicitSignalCollector {
    /// PathMap storage for ratings
    pathmap: PathMap,
}

impl ExplicitSignalCollector {
    /// Record a thumbs up/down rating
    pub fn record_thumbs(
        &mut self,
        correction_id: &CorrectionId,
        is_positive: bool,
    ) -> Result<RateFeedback, FeedbackError> {
        let rating = if is_positive {
            Rating::ThumbsUp
        } else {
            Rating::ThumbsDown
        };

        let feedback = RateFeedback {
            rating,
            comment: None,
            report_type: None,
        };

        self.store_rating(correction_id, &feedback)?;

        Ok(feedback)
    }

    /// Record a star rating
    pub fn record_stars(
        &mut self,
        correction_id: &CorrectionId,
        stars: u8,
    ) -> Result<RateFeedback, FeedbackError> {
        if stars < 1 || stars > 5 {
            return Err(FeedbackError::InvalidRating);
        }

        let feedback = RateFeedback {
            rating: Rating::Stars(stars),
            comment: None,
            report_type: None,
        };

        self.store_rating(correction_id, &feedback)?;

        Ok(feedback)
    }

    /// Record a comment
    pub fn record_comment(
        &mut self,
        correction_id: &CorrectionId,
        comment: String,
    ) -> Result<RateFeedback, FeedbackError> {
        // Try to infer sentiment from comment
        let inferred_rating = self.infer_sentiment(&comment);

        let feedback = RateFeedback {
            rating: inferred_rating,
            comment: Some(comment),
            report_type: None,
        };

        self.store_rating(correction_id, &feedback)?;

        Ok(feedback)
    }

    /// Record a problem report
    pub fn record_report(
        &mut self,
        correction_id: &CorrectionId,
        report_type: ReportType,
        comment: Option<String>,
    ) -> Result<RateFeedback, FeedbackError> {
        let feedback = RateFeedback {
            rating: Rating::ThumbsDown,  // Reports are always negative
            comment,
            report_type: Some(report_type),
        };

        self.store_rating(correction_id, &feedback)?;

        Ok(feedback)
    }

    /// Simple sentiment inference from comment
    fn infer_sentiment(&self, comment: &str) -> Rating {
        let lower = comment.to_lowercase();

        let positive_indicators = ["good", "great", "thanks", "helpful", "correct", "right"];
        let negative_indicators = ["bad", "wrong", "incorrect", "unhelpful", "mistake", "error"];

        let positive_count = positive_indicators.iter()
            .filter(|&w| lower.contains(w))
            .count();
        let negative_count = negative_indicators.iter()
            .filter(|&w| lower.contains(w))
            .count();

        if positive_count > negative_count {
            Rating::ThumbsUp
        } else if negative_count > positive_count {
            Rating::ThumbsDown
        } else {
            Rating::Stars(3)  // Neutral
        }
    }
}
```

### Stage 4: Feedback Normalization

```rust
/// Normalizes feedback signals for learning
pub struct FeedbackNormalizer {
    /// Implicit signal detector
    implicit_detector: ImplicitSignalDetector,

    /// Weights for combining signals
    weights: NormalizationWeights,
}

/// Weights for combining feedback signals
#[derive(Clone, Debug)]
pub struct NormalizationWeights {
    /// Weight for implicit action signal
    pub action_weight: f64,

    /// Weight for timing signal
    pub timing_weight: f64,

    /// Weight for edit distance signal (modifications)
    pub edit_weight: f64,

    /// Weight for explicit rating signal
    pub rating_weight: f64,

    /// Minimum learning weight (even ambiguous feedback counts a little)
    pub min_learning_weight: f64,
}

impl Default for NormalizationWeights {
    fn default() -> Self {
        Self {
            action_weight: 0.4,
            timing_weight: 0.2,
            edit_weight: 0.2,
            rating_weight: 0.8,  // Explicit ratings are highly weighted
            min_learning_weight: 0.1,
        }
    }
}

impl FeedbackNormalizer {
    /// Normalize a feedback response into a learning signal
    pub fn normalize(
        &self,
        correction: &CorrectionRecord,
        response: &FeedbackResponse,
    ) -> NormalizedFeedback {
        let factors = self.compute_factors(correction, response);
        let (signal_strength, confidence) = self.combine_factors(&factors);
        let learning_weight = self.compute_learning_weight(&factors, confidence);

        NormalizedFeedback {
            signal_strength,
            confidence,
            learning_weight,
            factors,
        }
    }

    fn compute_factors(
        &self,
        correction: &CorrectionRecord,
        response: &FeedbackResponse,
    ) -> FeedbackFactors {
        match response {
            FeedbackResponse::Accept(a) => {
                let implicit = self.implicit_detector.analyze_action(
                    &UserAction::Accept,
                    a.time_to_decision_ms,
                );

                // Check for subsequent edits
                let subsequent_penalty = a.subsequent_edit.as_ref()
                    .map(|e| -0.5 * (1.0 - 1.0 / (1.0 + e.edit_distance as f64)))
                    .unwrap_or(0.0);

                FeedbackFactors {
                    action_signal: 1.0 + subsequent_penalty,
                    timing_signal: self.timing_to_signal(a.time_to_decision_ms, true),
                    edit_signal: None,
                    rating_signal: None,
                    context_factor: self.context_confidence(correction),
                }
            }

            FeedbackResponse::Reject(r) => {
                let implicit = self.implicit_detector.analyze_action(
                    &UserAction::Reject(r.rejection_method.clone()),
                    r.time_to_decision_ms,
                );

                FeedbackFactors {
                    action_signal: -1.0,
                    timing_signal: self.timing_to_signal(r.time_to_decision_ms, false),
                    edit_signal: None,
                    rating_signal: None,
                    context_factor: self.context_confidence(correction),
                }
            }

            FeedbackResponse::Modify(m) => {
                // Edit distance relative to original correction
                let original_len = correction.original.len();
                let proposed_len = correction.proposed.len();
                let max_len = original_len.max(proposed_len).max(1);

                // Normalized edit signal: 0 = identical, -1 = completely different
                let normalized_edit = -(m.edit_distance as f64 / max_len as f64).min(1.0);

                FeedbackFactors {
                    action_signal: -0.5,  // Modification is weakly negative
                    timing_signal: self.timing_to_signal(m.time_to_decision_ms, false),
                    edit_signal: Some(normalized_edit),
                    rating_signal: None,
                    context_factor: self.context_confidence(correction),
                }
            }

            FeedbackResponse::Ignore(i) => {
                FeedbackFactors {
                    action_signal: 0.0,  // Ambiguous
                    timing_signal: 0.0,
                    edit_signal: None,
                    rating_signal: None,
                    context_factor: self.context_confidence(correction) * 0.5,
                }
            }

            FeedbackResponse::Rate(r) => {
                let rating_signal = match &r.rating {
                    Rating::ThumbsUp => 1.0,
                    Rating::ThumbsDown => -1.0,
                    Rating::Stars(s) => (*s as f64 - 3.0) / 2.0,  // 1-5 → -1.0 to 1.0
                };

                // Reports are very strong negative signals
                let rating_signal = if r.report_type.is_some() {
                    -1.0
                } else {
                    rating_signal
                };

                FeedbackFactors {
                    action_signal: 0.0,  // No action signal for explicit ratings
                    timing_signal: 0.0,
                    edit_signal: None,
                    rating_signal: Some(rating_signal),
                    context_factor: 1.0,  // Explicit ratings have full context confidence
                }
            }
        }
    }

    fn timing_to_signal(&self, time_ms: u64, is_positive: bool) -> f64 {
        // Quick responses have stronger signals
        let quick_bonus = if time_ms < 500 {
            0.3
        } else if time_ms < 2000 {
            0.1
        } else {
            -0.1
        };

        if is_positive { quick_bonus } else { -quick_bonus }
    }

    fn context_confidence(&self, correction: &CorrectionRecord) -> f64 {
        // Higher confidence in corrections with more context
        let has_dialogue = correction.context.dialogue_id.is_some();
        let has_domain = correction.context.domain.is_some();
        let correction_confidence = correction.confidence;

        let mut context_factor = 0.5;
        if has_dialogue { context_factor += 0.2; }
        if has_domain { context_factor += 0.1; }
        context_factor += 0.2 * correction_confidence;

        context_factor.min(1.0)
    }

    fn combine_factors(&self, factors: &FeedbackFactors) -> (f64, f64) {
        let mut weighted_sum = 0.0;
        let mut total_weight = 0.0;

        // Action signal
        weighted_sum += factors.action_signal * self.weights.action_weight;
        total_weight += self.weights.action_weight;

        // Timing signal
        weighted_sum += factors.timing_signal * self.weights.timing_weight;
        total_weight += self.weights.timing_weight;

        // Edit signal (if present)
        if let Some(edit_signal) = factors.edit_signal {
            weighted_sum += edit_signal * self.weights.edit_weight;
            total_weight += self.weights.edit_weight;
        }

        // Rating signal (if present, overrides most other signals)
        if let Some(rating_signal) = factors.rating_signal {
            weighted_sum += rating_signal * self.weights.rating_weight;
            total_weight += self.weights.rating_weight;
        }

        let signal_strength = if total_weight > 0.0 {
            (weighted_sum / total_weight).clamp(-1.0, 1.0)
        } else {
            0.0
        };

        // Confidence based on signal clarity and context
        let signal_clarity = signal_strength.abs();
        let confidence = (0.5 * signal_clarity + 0.5 * factors.context_factor).clamp(0.0, 1.0);

        (signal_strength, confidence)
    }

    fn compute_learning_weight(
        &self,
        factors: &FeedbackFactors,
        confidence: f64,
    ) -> f64 {
        // Explicit ratings have high learning weight
        if factors.rating_signal.is_some() {
            return 1.0;
        }

        // Learning weight scales with confidence
        let base_weight = confidence;

        // But never below minimum
        base_weight.max(self.weights.min_learning_weight)
    }
}
```

---

## PathMap Storage Schema

```
PathMap Key Structure (Feedback):
=================================

/learning/feedback/
    /pending/{correction_id}/
        correction -> serialized CorrectionRecord
        proposed_at -> timestamp
        displayed_at -> optional timestamp
        status -> pending|resolved

    /completed/{feedback_id}/
        correction_id -> reference to original correction
        user_id -> user identifier
        session_id -> session identifier
        timestamp -> feedback timestamp

        response/
            type -> accept|reject|modify|ignore|rate
            time_to_decision_ms -> milliseconds
            modified_text -> optional (for modify)
            edit_distance -> optional (for modify)
            rating -> optional (for rate)
            comment -> optional (for rate)
            report_type -> optional (for rate)

        normalized/
            signal_strength -> -1.0 to 1.0
            confidence -> 0.0 to 1.0
            learning_weight -> 0.0 to 1.0
            factors/
                action_signal -> float
                timing_signal -> float
                edit_signal -> optional float
                rating_signal -> optional float
                context_factor -> float

        correction/
            original -> original text
            proposed -> proposed correction
            tier -> lexical|syntactic|semantic|llm
            confidence -> original confidence
            position -> (start, end, line, column)

    /by_user/{user_id}/
        {feedback_id} -> true  ; Index for user queries

    /by_correction/{correction_id}/
        {feedback_id} -> true  ; Index for correction queries

    /by_date/{date}/
        {feedback_id} -> true  ; Index for date range queries

    /aggregates/
        /user/{user_id}/
            total_feedback -> count
            accept_count -> count
            reject_count -> count
            modify_count -> count
            average_signal -> float
        /tier/{tier}/
            total_feedback -> count
            accept_rate -> float
            average_confidence -> float
```

---

## MeTTa Predicates

### Feedback Collection Predicates

```metta
; Feedback types
(: Feedback Type)
(: FeedbackResponse Type)
(: NormalizedFeedback Type)

; Feedback response constructors
(: fb-accept (-> u64 FeedbackResponse))                    ; time_ms
(: fb-reject (-> u64 RejectionMethod FeedbackResponse))    ; time_ms, method
(: fb-modify (-> u64 String u64 FeedbackResponse))         ; time_ms, text, edit_dist
(: fb-ignore (-> u64 Bool FeedbackResponse))               ; duration, had_activity
(: fb-rate (-> Rating (Maybe String) FeedbackResponse))    ; rating, comment

; Rating constructors
(: thumbs-up Rating)
(: thumbs-down Rating)
(: stars (-> u8 Rating))  ; 1-5

; Feedback queries
(: feedback-response (-> Feedback FeedbackResponse))
(: feedback-correction (-> Feedback CorrectionRecord))
(: feedback-normalized (-> Feedback NormalizedFeedback))
(: feedback-timestamp (-> Feedback Timestamp))
```

### Signal Analysis Predicates

```metta
; Signal analysis
(: signal-strength (-> NormalizedFeedback Float))
(: signal-confidence (-> NormalizedFeedback Float))
(: learning-weight (-> NormalizedFeedback Float))

; Signal classification
(: is-positive-feedback (-> Feedback Bool))
(: is-negative-feedback (-> Feedback Bool))
(: is-ambiguous-feedback (-> Feedback Bool))

; Implicit signal detection
(: analyze-timing (-> u64 Bool ImplicitSignal))  ; time_ms, is_accept
(: implicit-strength (-> ImplicitSignal Float))
(: implicit-confidence (-> ImplicitSignal Float))
```

### Aggregation Predicates

```metta
; Aggregate queries
(: user-acceptance-rate (-> UserId Float))
(: tier-acceptance-rate (-> CorrectionTier Float))
(: correction-success-rate (-> CorrectionId Float))

; Aggregate computation
(: count-feedback (-> (List Feedback) u64))
(: average-signal (-> (List Feedback) Float))
(: feedback-distribution (-> (List Feedback) (Map String u64)))

; Time-based queries
(: feedback-since (-> Timestamp (List Feedback)))
(: feedback-between (-> Timestamp Timestamp (List Feedback)))
```

### Storage Predicates

```metta
; Storage operations
(: store-feedback (-> Feedback (Result () Error)))
(: load-feedback (-> FeedbackId (Result Feedback Error)))
(: load-user-feedback (-> UserId (List Feedback)))
(: load-correction-feedback (-> CorrectionId (Maybe Feedback)))

; Index queries
(: feedback-by-user (-> UserId (List FeedbackId)))
(: feedback-by-date (-> Date (List FeedbackId)))
(: feedback-by-tier (-> CorrectionTier (List FeedbackId)))
```

---

## Integration with Learning Pipeline

The feedback collection layer feeds into pattern learning and weight updates:

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                FEEDBACK → LEARNING INTEGRATION                               │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                              │
│  FeedbackStore (PathMap)                                                     │
│      │                                                                       │
│      ├─────────────────────────────────────────────┐                        │
│      │                                             │                        │
│      ▼                                             ▼                        │
│  ┌─────────────────────────────────┐   ┌─────────────────────────────────┐  │
│  │        PATTERN LEARNING         │   │        WEIGHT UPDATES           │  │
│  │                                 │   │                                 │  │
│  │  Input:                         │   │  Input:                         │  │
│  │   - Feedback with negative      │   │   - All feedback signals        │  │
│  │     signals                     │   │   - Signal strength             │  │
│  │   - Original + proposed +       │   │   - Learning weight             │  │
│  │     modified text               │   │                                 │  │
│  │                                 │   │  Output:                        │  │
│  │  Output:                        │   │   - Updated edit costs          │  │
│  │   - Error patterns              │   │   - Updated feature weights     │  │
│  │   - Pattern confidence          │   │   - Updated thresholds          │  │
│  │                                 │   │                                 │  │
│  └────────────────┬────────────────┘   └────────────────┬────────────────┘  │
│                   │                                     │                   │
│                   ▼                                     ▼                   │
│              PatternStore                          ModelStore               │
│                                                                              │
│      ┌────────────────────────────────────────────────────────────────────┐ │
│      │                                                                    │ │
│      ▼                                                                    │ │
│  ┌─────────────────────────────────┐                                      │ │
│  │       USER PREFERENCES          │                                      │ │
│  │                                 │                                      │ │
│  │  Input:                         │                                      │ │
│  │   - Feedback per user           │                                      │ │
│  │   - Accepted/rejected words     │                                      │ │
│  │   - Style indicators            │                                      │ │
│  │                                 │                                      │ │
│  │  Output:                        │                                      │ │
│  │   - Personal dictionary         │                                      │ │
│  │   - Style profile               │                                      │ │
│  │   - Threshold adjustments       │                                      │ │
│  │                                 │                                      │ │
│  └────────────────┬────────────────┘                                      │ │
│                   │                                                        │ │
│                   ▼                                                        │ │
│              UserProfileStore                                              │ │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
```

---

## Error Handling

```rust
/// Feedback collection errors
#[derive(Debug, Clone, thiserror::Error)]
pub enum FeedbackError {
    #[error("Correction not found: {0}")]
    CorrectionNotFound(CorrectionId),

    #[error("Feedback already recorded for correction: {0}")]
    FeedbackAlreadyRecorded(CorrectionId),

    #[error("Invalid rating: stars must be 1-5")]
    InvalidRating,

    #[error("Storage error: {0}")]
    StorageError(String),

    #[error("Serialization error: {0}")]
    SerializationError(String),
}
```

---

## Configuration

```rust
/// Feedback collection configuration
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct FeedbackConfig {
    /// Timeout for implicit ignore detection (ms)
    pub ignore_timeout_ms: u64,

    /// Timing thresholds for implicit signals
    pub timing_thresholds: TimingThresholds,

    /// Normalization weights
    pub normalization_weights: NormalizationWeights,

    /// Enable subsequent edit tracking
    pub track_subsequent_edits: bool,

    /// Maximum time to track subsequent edits (ms)
    pub subsequent_edit_window_ms: u64,

    /// Enable sentiment inference from comments
    pub infer_comment_sentiment: bool,

    /// Storage settings
    pub storage: StorageConfig,
}

impl Default for FeedbackConfig {
    fn default() -> Self {
        Self {
            ignore_timeout_ms: 30_000,  // 30 seconds
            timing_thresholds: TimingThresholds::default(),
            normalization_weights: NormalizationWeights::default(),
            track_subsequent_edits: true,
            subsequent_edit_window_ms: 60_000,  // 1 minute
            infer_comment_sentiment: true,
            storage: StorageConfig::default(),
        }
    }
}
```

---

## Related Documentation

- [README](./README.md) - Agent learning overview
- [Pattern Learning](./02-pattern-learning.md) - Learning from collected feedback
- [User Preferences](./03-user-preferences.md) - Building user profiles
- [Online Learning](./04-online-learning.md) - Updating model weights
