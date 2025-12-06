# Online Learning

## Overview

The online learning layer performs incremental updates to model parameters based on user
feedback. This includes updating edit distance weights, feature weights for candidate
ranking, pattern confidence scores, and adaptive thresholds. The system learns continuously
without requiring batch retraining, enabling immediate personalization and improvement.

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                    ONLINE LEARNING ARCHITECTURE                              │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                              │
│  User Feedback                                                               │
│  (from FeedbackStore)                                                        │
│      │                                                                       │
│      ▼                                                                       │
│  ┌───────────────────────────────────────────────────────────────────────┐  │
│  │                    WEIGHT UPDATER                                      │  │
│  │  ┌─────────────────────────────────────────────────────────────────┐  │  │
│  │  │ Edit Distance Weights                                           │  │  │
│  │  │  - Insertion costs per character                                │  │  │
│  │  │  - Deletion costs per character                                 │  │  │
│  │  │  - Substitution cost matrix                                     │  │  │
│  │  │  - Transposition costs                                          │  │  │
│  │  └─────────────────────────────────────────────────────────────────┘  │  │
│  │  ┌─────────────────────────────────────────────────────────────────┐  │  │
│  │  │ Feature Weights                                                 │  │  │
│  │  │  - Edit distance weight                                         │  │  │
│  │  │  - Language model weight                                        │  │  │
│  │  │  - Frequency weight                                             │  │  │
│  │  │  - Phonetic similarity weight                                   │  │  │
│  │  │  - Context match weight                                         │  │  │
│  │  └─────────────────────────────────────────────────────────────────┘  │  │
│  │  ┌─────────────────────────────────────────────────────────────────┐  │  │
│  │  │ Pattern Weights                                                 │  │  │
│  │  │  - Per-pattern confidence adjustments                           │  │  │
│  │  │  - Pattern priority ordering                                    │  │  │
│  │  └─────────────────────────────────────────────────────────────────┘  │  │
│  └───────────────────────────────────────────────────────────────────────┘  │
│      │                                                                       │
│      ▼                                                                       │
│  ┌───────────────────────────────────────────────────────────────────────┐  │
│  │                    THRESHOLD ADAPTER                                   │  │
│  │  ┌─────────────────────────────────────────────────────────────────┐  │  │
│  │  │ Per-User Thresholds                                             │  │  │
│  │  │  - Suggestion threshold adjustment                              │  │  │
│  │  │  - Auto-correct threshold adjustment                            │  │  │
│  │  │  - Based on accept/reject patterns                              │  │  │
│  │  └─────────────────────────────────────────────────────────────────┘  │  │
│  │  ┌─────────────────────────────────────────────────────────────────┐  │  │
│  │  │ Per-Domain Thresholds                                           │  │  │
│  │  │  - Domain-specific confidence adjustments                       │  │  │
│  │  │  - Technical vs casual threshold differences                    │  │  │
│  │  └─────────────────────────────────────────────────────────────────┘  │  │
│  │  ┌─────────────────────────────────────────────────────────────────┐  │  │
│  │  │ Per-Tier Thresholds                                             │  │  │
│  │  │  - Tier 1 (lexical) threshold                                   │  │  │
│  │  │  - Tier 2 (syntactic) threshold                                 │  │  │
│  │  │  - Tier 3 (semantic) threshold                                  │  │  │
│  │  └─────────────────────────────────────────────────────────────────┘  │  │
│  └───────────────────────────────────────────────────────────────────────┘  │
│      │                                                                       │
│      ▼                                                                       │
│  ┌───────────────────────────────────────────────────────────────────────┐  │
│  │                    MODEL VERSIONER                                     │  │
│  │  ┌─────────────────────────────────────────────────────────────────┐  │  │
│  │  │ Checkpointing                                                   │  │  │
│  │  │  - Periodic model snapshots                                     │  │  │
│  │  │  - Before major updates                                         │  │  │
│  │  │  - Recovery points                                              │  │  │
│  │  └─────────────────────────────────────────────────────────────────┘  │  │
│  │  ┌─────────────────────────────────────────────────────────────────┐  │  │
│  │  │ Rollback                                                        │  │  │
│  │  │  - Restore previous model version                               │  │  │
│  │  │  - Undo recent updates                                          │  │  │
│  │  │  - Performance regression recovery                              │  │  │
│  │  └─────────────────────────────────────────────────────────────────┘  │  │
│  │  ┌─────────────────────────────────────────────────────────────────┐  │  │
│  │  │ A/B Testing                                                     │  │  │
│  │  │  - Compare model versions                                       │  │  │
│  │  │  - Gradual rollout                                              │  │  │
│  │  │  - Performance monitoring                                       │  │  │
│  │  └─────────────────────────────────────────────────────────────────┘  │  │
│  └───────────────────────────────────────────────────────────────────────┘  │
│      │                                                                       │
│      ▼                                                                       │
│  ┌───────────────────────────────────────────────────────────────────────┐  │
│  │                    MODEL STORE (PathMap)                              │  │
│  └───────────────────────────────────────────────────────────────────────┘  │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
```

---

## Core Data Structures

### Learning Model

```rust
/// Complete learning model state
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct LearningModel {
    /// Model identifier
    pub model_id: ModelId,

    /// Model version (incremented on each update)
    pub version: ModelVersion,

    /// Edit distance weights
    pub edit_weights: EditWeights,

    /// Feature weights for candidate ranking
    pub feature_weights: FeatureWeights,

    /// Learned pattern weights
    pub pattern_weights: HashMap<PatternId, f64>,

    /// Adaptive thresholds
    pub thresholds: AdaptiveThresholds,

    /// Learning hyperparameters
    pub hyperparameters: LearningHyperparameters,

    /// Model metadata
    pub metadata: ModelMetadata,
}

/// Model metadata
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ModelMetadata {
    /// When model was created
    pub created_at: Timestamp,

    /// When model was last updated
    pub updated_at: Timestamp,

    /// Total training samples processed
    pub training_samples: u64,

    /// Checkpoint path (if saved)
    pub checkpoint_path: Option<PathBuf>,

    /// Parent model (if forked)
    pub parent_model: Option<ModelId>,

    /// Performance metrics
    pub metrics: ModelMetrics,
}

/// Model performance metrics
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ModelMetrics {
    /// Overall acceptance rate
    pub acceptance_rate: f64,

    /// Precision (accepted / proposed)
    pub precision: f64,

    /// Recall (issues caught / total issues)
    pub recall: f64,

    /// F1 score
    pub f1_score: f64,

    /// Rolling window metrics
    pub rolling: RollingMetrics,
}

/// Rolling window metrics for recent performance
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct RollingMetrics {
    /// Window size (number of recent samples)
    pub window_size: usize,

    /// Recent acceptance rate
    pub recent_acceptance_rate: f64,

    /// Recent precision
    pub recent_precision: f64,

    /// Trend (improving, degrading, stable)
    pub trend: PerformanceTrend,
}

/// Performance trend
#[derive(Clone, Debug, Serialize, Deserialize, PartialEq)]
pub enum PerformanceTrend {
    Improving,
    Stable,
    Degrading,
}
```

### Edit Weights

```rust
/// Customizable edit distance weights
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct EditWeights {
    /// Insertion cost by character
    pub insertion: HashMap<char, f64>,

    /// Deletion cost by character
    pub deletion: HashMap<char, f64>,

    /// Substitution cost matrix (sparse)
    pub substitution: HashMap<(char, char), f64>,

    /// Transposition cost (for Damerau-Levenshtein)
    pub transposition: f64,

    /// Default costs for unlisted characters
    pub defaults: DefaultEditCosts,

    /// Keyboard layout for adjacent key costs
    pub keyboard_layout: KeyboardLayout,
}

/// Default edit costs
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct DefaultEditCosts {
    pub insertion: f64,
    pub deletion: f64,
    pub substitution: f64,
}

impl Default for DefaultEditCosts {
    fn default() -> Self {
        Self {
            insertion: 1.0,
            deletion: 1.0,
            substitution: 1.0,
        }
    }
}

/// Keyboard layout for computing adjacent key costs
#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum KeyboardLayout {
    QWERTY,
    DVORAK,
    AZERTY,
    Custom(HashMap<char, (f64, f64)>),  // char -> (x, y) position
}

impl EditWeights {
    /// Get insertion cost for a character
    pub fn insertion_cost(&self, c: char) -> f64 {
        *self.insertion.get(&c).unwrap_or(&self.defaults.insertion)
    }

    /// Get deletion cost for a character
    pub fn deletion_cost(&self, c: char) -> f64 {
        *self.deletion.get(&c).unwrap_or(&self.defaults.deletion)
    }

    /// Get substitution cost for a character pair
    pub fn substitution_cost(&self, from: char, to: char) -> f64 {
        if from == to {
            return 0.0;
        }

        // Check explicit cost
        if let Some(&cost) = self.substitution.get(&(from, to)) {
            return cost;
        }

        // Check reverse (substitution is often symmetric)
        if let Some(&cost) = self.substitution.get(&(to, from)) {
            return cost;
        }

        // Use keyboard distance if available
        if let Some(distance) = self.keyboard_distance(from, to) {
            // Adjacent keys have lower cost
            return self.defaults.substitution * (0.5 + 0.5 * distance);
        }

        self.defaults.substitution
    }

    fn keyboard_distance(&self, a: char, b: char) -> Option<f64> {
        let positions = self.get_keyboard_positions()?;

        let (ax, ay) = positions.get(&a.to_ascii_lowercase())?;
        let (bx, by) = positions.get(&b.to_ascii_lowercase())?;

        let distance = ((ax - bx).powi(2) + (ay - by).powi(2)).sqrt();
        let normalized = (distance / 5.0).min(1.0);  // Normalize to [0, 1]

        Some(normalized)
    }

    fn get_keyboard_positions(&self) -> Option<&HashMap<char, (f64, f64)>> {
        match &self.keyboard_layout {
            KeyboardLayout::Custom(positions) => Some(positions),
            KeyboardLayout::QWERTY => {
                // Would return precomputed QWERTY positions
                None
            }
            _ => None,
        }
    }
}
```

### Feature Weights

```rust
/// Feature weights for candidate ranking
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct FeatureWeights {
    /// Edit distance weight (lower distance = better)
    pub edit_distance: f64,

    /// Language model log-probability weight
    pub language_model: f64,

    /// Word frequency weight (more common = better)
    pub frequency: f64,

    /// Phonetic similarity weight
    pub phonetic: f64,

    /// Context match weight
    pub context: f64,

    /// User preference weight (matching user style)
    pub user_preference: f64,

    /// Pattern match weight (learned patterns)
    pub pattern_match: f64,

    /// Recency weight (recently accepted words)
    pub recency: f64,
}

impl Default for FeatureWeights {
    fn default() -> Self {
        Self {
            edit_distance: 0.3,
            language_model: 0.2,
            frequency: 0.15,
            phonetic: 0.1,
            context: 0.1,
            user_preference: 0.05,
            pattern_match: 0.05,
            recency: 0.05,
        }
    }
}

impl FeatureWeights {
    /// Score a correction candidate
    pub fn score(&self, features: &CandidateFeatures) -> f64 {
        let mut score = 0.0;

        // Edit distance (invert: lower is better)
        score += self.edit_distance * (1.0 - features.edit_distance_normalized);

        // Language model
        score += self.language_model * features.lm_score;

        // Frequency
        score += self.frequency * features.frequency_score;

        // Phonetic similarity
        score += self.phonetic * features.phonetic_similarity;

        // Context match
        score += self.context * features.context_score;

        // User preference
        score += self.user_preference * features.user_pref_score;

        // Pattern match
        score += self.pattern_match * features.pattern_score;

        // Recency
        score += self.recency * features.recency_score;

        score
    }

    /// Normalize weights to sum to 1.0
    pub fn normalize(&mut self) {
        let sum = self.edit_distance + self.language_model + self.frequency
            + self.phonetic + self.context + self.user_preference
            + self.pattern_match + self.recency;

        if sum > 0.0 {
            self.edit_distance /= sum;
            self.language_model /= sum;
            self.frequency /= sum;
            self.phonetic /= sum;
            self.context /= sum;
            self.user_preference /= sum;
            self.pattern_match /= sum;
            self.recency /= sum;
        }
    }
}

/// Features of a correction candidate
#[derive(Clone, Debug)]
pub struct CandidateFeatures {
    /// Normalized edit distance (0.0 = identical, 1.0 = very different)
    pub edit_distance_normalized: f64,

    /// Language model score (0.0 to 1.0)
    pub lm_score: f64,

    /// Frequency score (0.0 = rare, 1.0 = common)
    pub frequency_score: f64,

    /// Phonetic similarity (0.0 = different, 1.0 = identical)
    pub phonetic_similarity: f64,

    /// Context match score (0.0 = no match, 1.0 = perfect)
    pub context_score: f64,

    /// User preference score (0.0 = mismatch, 1.0 = match)
    pub user_pref_score: f64,

    /// Pattern match score (0.0 = no match, 1.0 = exact match)
    pub pattern_score: f64,

    /// Recency score (0.0 = never seen, 1.0 = just used)
    pub recency_score: f64,
}
```

### Adaptive Thresholds

```rust
/// Adaptive thresholds for correction decisions
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct AdaptiveThresholds {
    /// Global baseline thresholds
    pub baseline: BaselineThresholds,

    /// Per-user threshold adjustments
    pub user_adjustments: HashMap<UserId, ThresholdAdjustment>,

    /// Per-domain threshold adjustments
    pub domain_adjustments: HashMap<Domain, ThresholdAdjustment>,

    /// Per-tier threshold adjustments
    pub tier_adjustments: HashMap<CorrectionTier, ThresholdAdjustment>,
}

/// Baseline thresholds
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct BaselineThresholds {
    /// Minimum confidence to show suggestion
    pub suggestion: f64,

    /// Minimum confidence for auto-correction
    pub auto_correct: f64,

    /// Minimum confidence for any action
    pub minimum: f64,
}

impl Default for BaselineThresholds {
    fn default() -> Self {
        Self {
            suggestion: 0.6,
            auto_correct: 0.95,
            minimum: 0.3,
        }
    }
}

/// Threshold adjustment (additive)
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ThresholdAdjustment {
    /// Adjustment to suggestion threshold
    pub suggestion_delta: f64,

    /// Adjustment to auto-correct threshold
    pub auto_correct_delta: f64,

    /// When adjustment was last updated
    pub updated_at: Timestamp,

    /// Number of samples contributing to this adjustment
    pub sample_count: u64,
}

impl AdaptiveThresholds {
    /// Get effective suggestion threshold for a context
    pub fn get_suggestion_threshold(
        &self,
        user_id: Option<&UserId>,
        domain: Option<&Domain>,
        tier: Option<&CorrectionTier>,
    ) -> f64 {
        let mut threshold = self.baseline.suggestion;

        if let Some(uid) = user_id {
            if let Some(adj) = self.user_adjustments.get(uid) {
                threshold += adj.suggestion_delta;
            }
        }

        if let Some(d) = domain {
            if let Some(adj) = self.domain_adjustments.get(d) {
                threshold += adj.suggestion_delta;
            }
        }

        if let Some(t) = tier {
            if let Some(adj) = self.tier_adjustments.get(t) {
                threshold += adj.suggestion_delta;
            }
        }

        threshold.clamp(self.baseline.minimum, 1.0)
    }

    /// Get effective auto-correct threshold for a context
    pub fn get_auto_correct_threshold(
        &self,
        user_id: Option<&UserId>,
        domain: Option<&Domain>,
        tier: Option<&CorrectionTier>,
    ) -> f64 {
        let mut threshold = self.baseline.auto_correct;

        if let Some(uid) = user_id {
            if let Some(adj) = self.user_adjustments.get(uid) {
                threshold += adj.auto_correct_delta;
            }
        }

        if let Some(d) = domain {
            if let Some(adj) = self.domain_adjustments.get(d) {
                threshold += adj.auto_correct_delta;
            }
        }

        if let Some(t) = tier {
            if let Some(adj) = self.tier_adjustments.get(t) {
                threshold += adj.auto_correct_delta;
            }
        }

        threshold.clamp(self.baseline.suggestion, 1.0)
    }
}
```

### Learning Hyperparameters

```rust
/// Hyperparameters controlling the learning process
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct LearningHyperparameters {
    /// Learning rate for weight updates
    pub learning_rate: f64,

    /// Decay factor for old data (exponential moving average)
    pub decay_factor: f64,

    /// Minimum samples before updating
    pub min_samples: u64,

    /// Regularization strength (L2)
    pub regularization: f64,

    /// Momentum for gradient updates
    pub momentum: f64,

    /// Maximum weight change per update
    pub max_delta: f64,

    /// Checkpoint frequency (updates between checkpoints)
    pub checkpoint_frequency: u64,
}

impl Default for LearningHyperparameters {
    fn default() -> Self {
        Self {
            learning_rate: 0.01,
            decay_factor: 0.99,
            min_samples: 10,
            regularization: 0.001,
            momentum: 0.9,
            max_delta: 0.1,
            checkpoint_frequency: 100,
        }
    }
}
```

---

## Weight Update Algorithms

### Edit Weight Updates

```rust
/// Updates edit distance weights based on feedback
pub struct EditWeightUpdater {
    /// Hyperparameters
    hyperparams: LearningHyperparameters,

    /// Momentum accumulators
    momentum: EditWeightMomentum,
}

/// Momentum for edit weight updates
struct EditWeightMomentum {
    insertion: HashMap<char, f64>,
    deletion: HashMap<char, f64>,
    substitution: HashMap<(char, char), f64>,
}

impl EditWeightUpdater {
    /// Update edit weights from a single feedback item
    pub fn update(&mut self, model: &mut LearningModel, feedback: &Feedback) {
        // Only update from modifications (where user provided correct answer)
        if let FeedbackResponse::Modify(m) = &feedback.response {
            let original = &feedback.correction.original;
            let proposed = &feedback.correction.proposed;
            let correct = &m.modified_text;

            // Compute edit operations needed
            let ops_to_proposed = self.compute_edits(original, proposed);
            let ops_to_correct = self.compute_edits(original, correct);

            // Operations in proposed but not in correct were wrong
            for op in &ops_to_proposed {
                if !ops_to_correct.contains(op) {
                    // Increase cost for this operation (make it less likely)
                    self.increase_cost(&mut model.edit_weights, op);
                }
            }

            // Operations in correct but not in proposed were missed
            for op in &ops_to_correct {
                if !ops_to_proposed.contains(op) {
                    // Decrease cost for this operation (make it more likely)
                    self.decrease_cost(&mut model.edit_weights, op);
                }
            }
        }
    }

    fn compute_edits(&self, from: &str, to: &str) -> Vec<EditOperation> {
        // Use dynamic programming to compute edit sequence
        // Simplified: would use full Wagner-Fischer with backtracking
        vec![]
    }

    fn increase_cost(&mut self, weights: &mut EditWeights, op: &EditOperation) {
        let delta = self.hyperparams.learning_rate;
        let max_delta = self.hyperparams.max_delta;

        match op {
            EditOperation::Insert(c) => {
                let cost = weights.insertion.entry(*c).or_insert(weights.defaults.insertion);
                let momentum = self.momentum.insertion.entry(*c).or_insert(0.0);

                *momentum = self.hyperparams.momentum * *momentum + delta;
                *cost = (*cost + momentum.min(&max_delta)).min(5.0);  // Cap at 5.0
            }
            EditOperation::Delete(c) => {
                let cost = weights.deletion.entry(*c).or_insert(weights.defaults.deletion);
                let momentum = self.momentum.deletion.entry(*c).or_insert(0.0);

                *momentum = self.hyperparams.momentum * *momentum + delta;
                *cost = (*cost + momentum.min(&max_delta)).min(5.0);
            }
            EditOperation::Substitute(from, to) => {
                let cost = weights.substitution.entry((*from, *to))
                    .or_insert(weights.defaults.substitution);
                let momentum = self.momentum.substitution.entry((*from, *to)).or_insert(0.0);

                *momentum = self.hyperparams.momentum * *momentum + delta;
                *cost = (*cost + momentum.min(&max_delta)).min(5.0);
            }
            _ => {}
        }
    }

    fn decrease_cost(&mut self, weights: &mut EditWeights, op: &EditOperation) {
        let delta = self.hyperparams.learning_rate;
        let max_delta = self.hyperparams.max_delta;

        match op {
            EditOperation::Insert(c) => {
                let cost = weights.insertion.entry(*c).or_insert(weights.defaults.insertion);
                let momentum = self.momentum.insertion.entry(*c).or_insert(0.0);

                *momentum = self.hyperparams.momentum * *momentum - delta;
                *cost = (*cost + momentum.max(&-max_delta)).max(0.1);  // Floor at 0.1
            }
            EditOperation::Delete(c) => {
                let cost = weights.deletion.entry(*c).or_insert(weights.defaults.deletion);
                let momentum = self.momentum.deletion.entry(*c).or_insert(0.0);

                *momentum = self.hyperparams.momentum * *momentum - delta;
                *cost = (*cost + momentum.max(&-max_delta)).max(0.1);
            }
            EditOperation::Substitute(from, to) => {
                let cost = weights.substitution.entry((*from, *to))
                    .or_insert(weights.defaults.substitution);
                let momentum = self.momentum.substitution.entry((*from, *to)).or_insert(0.0);

                *momentum = self.hyperparams.momentum * *momentum - delta;
                *cost = (*cost + momentum.max(&-max_delta)).max(0.1);
            }
            _ => {}
        }
    }
}

/// Edit operation types
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum EditOperation {
    Insert(char),
    Delete(char),
    Substitute(char, char),
    Transpose(char, char),
}
```

### Feature Weight Updates

```rust
/// Updates feature weights based on feedback
pub struct FeatureWeightUpdater {
    /// Hyperparameters
    hyperparams: LearningHyperparameters,

    /// Gradient accumulator
    gradient_acc: FeatureWeights,
}

impl FeatureWeightUpdater {
    /// Update feature weights from feedback
    pub fn update(&mut self, model: &mut LearningModel, feedback: &Feedback) {
        let signal = feedback.normalized.signal_strength;
        let weight = feedback.normalized.learning_weight;

        // Skip if signal is weak
        if weight < 0.1 {
            return;
        }

        // Compute feature gradient based on feedback
        let features = self.extract_features(feedback);
        let gradient = self.compute_gradient(&features, signal);

        // Apply gradient with momentum
        self.apply_gradient(&mut model.feature_weights, &gradient, weight);

        // Normalize weights
        model.feature_weights.normalize();
    }

    fn extract_features(&self, feedback: &Feedback) -> CandidateFeatures {
        // Extract features that were present in the correction
        // Simplified: would compute from actual correction data
        CandidateFeatures {
            edit_distance_normalized: 0.5,
            lm_score: 0.5,
            frequency_score: 0.5,
            phonetic_similarity: 0.5,
            context_score: 0.5,
            user_pref_score: 0.5,
            pattern_score: 0.0,
            recency_score: 0.0,
        }
    }

    fn compute_gradient(
        &self,
        features: &CandidateFeatures,
        signal: f64,
    ) -> FeatureWeights {
        // Gradient: increase weights for features that contributed to good corrections
        // decrease weights for features that contributed to bad corrections

        let scale = signal * self.hyperparams.learning_rate;

        FeatureWeights {
            edit_distance: (1.0 - features.edit_distance_normalized) * scale,
            language_model: features.lm_score * scale,
            frequency: features.frequency_score * scale,
            phonetic: features.phonetic_similarity * scale,
            context: features.context_score * scale,
            user_preference: features.user_pref_score * scale,
            pattern_match: features.pattern_score * scale,
            recency: features.recency_score * scale,
        }
    }

    fn apply_gradient(
        &mut self,
        weights: &mut FeatureWeights,
        gradient: &FeatureWeights,
        weight: f64,
    ) {
        let lr = self.hyperparams.learning_rate * weight;
        let mom = self.hyperparams.momentum;
        let reg = self.hyperparams.regularization;
        let max_delta = self.hyperparams.max_delta;

        // Update with momentum and regularization
        self.gradient_acc.edit_distance = mom * self.gradient_acc.edit_distance
            + gradient.edit_distance - reg * weights.edit_distance;
        weights.edit_distance += (lr * self.gradient_acc.edit_distance).clamp(-max_delta, max_delta);

        self.gradient_acc.language_model = mom * self.gradient_acc.language_model
            + gradient.language_model - reg * weights.language_model;
        weights.language_model += (lr * self.gradient_acc.language_model).clamp(-max_delta, max_delta);

        // ... similar for other weights

        // Ensure non-negative
        weights.edit_distance = weights.edit_distance.max(0.01);
        weights.language_model = weights.language_model.max(0.01);
        // ... similar for other weights
    }
}
```

### Threshold Adaptation

```rust
/// Adapts thresholds based on user behavior
pub struct ThresholdAdapter {
    /// Hyperparameters
    hyperparams: LearningHyperparameters,

    /// Rolling acceptance rate per user
    user_acceptance: HashMap<UserId, RollingAverage>,

    /// Rolling acceptance rate per domain
    domain_acceptance: HashMap<Domain, RollingAverage>,
}

/// Rolling average calculator
struct RollingAverage {
    values: VecDeque<f64>,
    window_size: usize,
}

impl RollingAverage {
    fn new(window_size: usize) -> Self {
        Self {
            values: VecDeque::with_capacity(window_size),
            window_size,
        }
    }

    fn add(&mut self, value: f64) {
        if self.values.len() >= self.window_size {
            self.values.pop_front();
        }
        self.values.push_back(value);
    }

    fn average(&self) -> f64 {
        if self.values.is_empty() {
            return 0.5;
        }
        self.values.iter().sum::<f64>() / self.values.len() as f64
    }
}

impl ThresholdAdapter {
    /// Update thresholds based on feedback
    pub fn update(&mut self, model: &mut LearningModel, feedback: &Feedback) {
        let user_id = feedback.correction.user_id.clone();
        let domain = feedback.correction.context.domain.clone();
        let tier = feedback.correction.tier;

        // Track acceptance
        let was_accepted = matches!(feedback.response, FeedbackResponse::Accept(_));
        let acceptance_value = if was_accepted { 1.0 } else { 0.0 };

        // Update user rolling average
        let user_avg = self.user_acceptance
            .entry(user_id.clone())
            .or_insert_with(|| RollingAverage::new(50));
        user_avg.add(acceptance_value);

        // Compute threshold adjustment
        let avg_acceptance = user_avg.average();
        let adjustment = self.compute_adjustment(avg_acceptance, feedback.correction.confidence);

        // Apply to user thresholds
        let user_adj = model.thresholds.user_adjustments
            .entry(user_id)
            .or_insert_with(|| ThresholdAdjustment {
                suggestion_delta: 0.0,
                auto_correct_delta: 0.0,
                updated_at: Timestamp::now(),
                sample_count: 0,
            });

        user_adj.suggestion_delta = (user_adj.suggestion_delta + adjustment.suggestion_delta) / 2.0;
        user_adj.auto_correct_delta = (user_adj.auto_correct_delta + adjustment.auto_correct_delta) / 2.0;
        user_adj.updated_at = Timestamp::now();
        user_adj.sample_count += 1;

        // Similar updates for domain and tier...
    }

    fn compute_adjustment(&self, acceptance_rate: f64, correction_confidence: f64) -> ThresholdAdjustment {
        // If user accepts most corrections, lower thresholds (show more)
        // If user rejects most corrections, raise thresholds (show fewer)

        let target_acceptance = 0.7;  // Target 70% acceptance rate
        let difference = acceptance_rate - target_acceptance;

        // Scale adjustment by how far from target
        let suggestion_delta = -difference * 0.1;  // Move opposite to difference
        let auto_correct_delta = -difference * 0.05;  // More conservative for auto-correct

        ThresholdAdjustment {
            suggestion_delta: suggestion_delta.clamp(-0.1, 0.1),
            auto_correct_delta: auto_correct_delta.clamp(-0.05, 0.05),
            updated_at: Timestamp::now(),
            sample_count: 1,
        }
    }
}
```

---

## Model Versioning

### Checkpointing

```rust
/// Manages model checkpoints
pub struct ModelCheckpointer {
    /// Checkpoint directory
    checkpoint_dir: PathBuf,

    /// Maximum checkpoints to keep
    max_checkpoints: usize,
}

impl ModelCheckpointer {
    /// Create a checkpoint of the current model
    pub fn checkpoint(&self, model: &LearningModel) -> Result<PathBuf, LearningError> {
        let timestamp = Timestamp::now().as_millis();
        let filename = format!("model_v{}_{}.checkpoint", model.version.0, timestamp);
        let path = self.checkpoint_dir.join(&filename);

        // Serialize model
        let serialized = serde_json::to_vec(model)
            .map_err(|e| LearningError::SerializationError(e.to_string()))?;

        // Write to file
        std::fs::write(&path, serialized)
            .map_err(|e| LearningError::IoError(e.to_string()))?;

        // Clean up old checkpoints
        self.cleanup_old_checkpoints()?;

        Ok(path)
    }

    /// Restore model from checkpoint
    pub fn restore(&self, path: &Path) -> Result<LearningModel, LearningError> {
        let data = std::fs::read(path)
            .map_err(|e| LearningError::IoError(e.to_string()))?;

        let model: LearningModel = serde_json::from_slice(&data)
            .map_err(|e| LearningError::SerializationError(e.to_string()))?;

        Ok(model)
    }

    /// List available checkpoints
    pub fn list_checkpoints(&self) -> Result<Vec<CheckpointInfo>, LearningError> {
        let entries = std::fs::read_dir(&self.checkpoint_dir)
            .map_err(|e| LearningError::IoError(e.to_string()))?;

        let mut checkpoints = Vec::new();

        for entry in entries {
            let entry = entry.map_err(|e| LearningError::IoError(e.to_string()))?;
            let path = entry.path();

            if path.extension().map(|e| e == "checkpoint").unwrap_or(false) {
                if let Some(info) = self.parse_checkpoint_info(&path) {
                    checkpoints.push(info);
                }
            }
        }

        checkpoints.sort_by(|a, b| b.timestamp.cmp(&a.timestamp));
        Ok(checkpoints)
    }

    fn cleanup_old_checkpoints(&self) -> Result<(), LearningError> {
        let mut checkpoints = self.list_checkpoints()?;

        while checkpoints.len() > self.max_checkpoints {
            if let Some(oldest) = checkpoints.pop() {
                std::fs::remove_file(&oldest.path)
                    .map_err(|e| LearningError::IoError(e.to_string()))?;
            }
        }

        Ok(())
    }

    fn parse_checkpoint_info(&self, path: &Path) -> Option<CheckpointInfo> {
        let filename = path.file_stem()?.to_str()?;
        let parts: Vec<&str> = filename.split('_').collect();

        if parts.len() >= 3 && parts[0] == "model" {
            let version = parts[1].strip_prefix('v')?.parse().ok()?;
            let timestamp = parts[2].parse().ok()?;

            Some(CheckpointInfo {
                path: path.to_path_buf(),
                version: ModelVersion(version),
                timestamp: Timestamp::from_millis(timestamp),
            })
        } else {
            None
        }
    }
}

/// Checkpoint information
#[derive(Clone, Debug)]
pub struct CheckpointInfo {
    pub path: PathBuf,
    pub version: ModelVersion,
    pub timestamp: Timestamp,
}
```

### Rollback

```rust
/// Handles model rollback
pub struct ModelRollback {
    /// Checkpointer
    checkpointer: ModelCheckpointer,

    /// Current model reference
    current_model: Arc<RwLock<LearningModel>>,
}

impl ModelRollback {
    /// Rollback to a specific version
    pub fn rollback_to(&self, version: &ModelVersion) -> Result<(), LearningError> {
        let checkpoints = self.checkpointer.list_checkpoints()?;

        let checkpoint = checkpoints.into_iter()
            .find(|c| &c.version == version)
            .ok_or_else(|| LearningError::VersionNotFound(version.clone()))?;

        let restored = self.checkpointer.restore(&checkpoint.path)?;

        let mut model = self.current_model.write()
            .map_err(|_| LearningError::LockError)?;

        *model = restored;

        Ok(())
    }

    /// Rollback to previous version
    pub fn rollback_one(&self) -> Result<(), LearningError> {
        let checkpoints = self.checkpointer.list_checkpoints()?;

        if checkpoints.len() < 2 {
            return Err(LearningError::NoPreviousVersion);
        }

        let previous = &checkpoints[1];
        let restored = self.checkpointer.restore(&previous.path)?;

        let mut model = self.current_model.write()
            .map_err(|_| LearningError::LockError)?;

        *model = restored;

        Ok(())
    }

    /// Rollback recent updates (undo last N updates)
    pub fn undo_updates(&self, count: usize) -> Result<(), LearningError> {
        let checkpoints = self.checkpointer.list_checkpoints()?;

        if checkpoints.len() <= count {
            return Err(LearningError::InsufficientHistory);
        }

        let target = &checkpoints[count];
        let restored = self.checkpointer.restore(&target.path)?;

        let mut model = self.current_model.write()
            .map_err(|_| LearningError::LockError)?;

        *model = restored;

        Ok(())
    }
}
```

---

## PathMap Storage Schema

```
PathMap Key Structure (Online Learning):
========================================

/learning/model/{model_id}/
    version -> model version number

    /edit_weights/
        /insertion/
            {char_code} -> cost
        /deletion/
            {char_code} -> cost
        /substitution/
            {from_code}_{to_code} -> cost
        transposition -> cost
        /defaults/
            insertion -> default cost
            deletion -> default cost
            substitution -> default cost
        keyboard_layout -> qwerty|dvorak|azerty|custom

    /feature_weights/
        edit_distance -> weight
        language_model -> weight
        frequency -> weight
        phonetic -> weight
        context -> weight
        user_preference -> weight
        pattern_match -> weight
        recency -> weight

    /pattern_weights/
        {pattern_id} -> weight

    /thresholds/
        /baseline/
            suggestion -> threshold
            auto_correct -> threshold
            minimum -> threshold
        /user/{user_id}/
            suggestion_delta -> adjustment
            auto_correct_delta -> adjustment
            updated_at -> timestamp
            sample_count -> count
        /domain/{domain}/
            suggestion_delta -> adjustment
            auto_correct_delta -> adjustment
            updated_at -> timestamp
            sample_count -> count
        /tier/{tier}/
            suggestion_delta -> adjustment
            auto_correct_delta -> adjustment
            updated_at -> timestamp
            sample_count -> count

    /hyperparameters/
        learning_rate -> float
        decay_factor -> float
        min_samples -> int
        regularization -> float
        momentum -> float
        max_delta -> float
        checkpoint_frequency -> int

    /metadata/
        created_at -> timestamp
        updated_at -> timestamp
        training_samples -> count
        checkpoint_path -> optional path
        parent_model -> optional model_id
        /metrics/
            acceptance_rate -> float
            precision -> float
            recall -> float
            f1_score -> float
            /rolling/
                window_size -> int
                recent_acceptance_rate -> float
                recent_precision -> float
                trend -> improving|stable|degrading

/learning/checkpoints/
    {checkpoint_filename} -> checkpoint data

/learning/momentum/
    /edit/
        /insertion/{char_code} -> momentum value
        /deletion/{char_code} -> momentum value
        /substitution/{from}_{to} -> momentum value
    /feature/
        {feature_name} -> momentum value
```

---

## MeTTa Predicates

### Model Predicates

```metta
; Model types
(: LearningModel Type)
(: EditWeights Type)
(: FeatureWeights Type)
(: AdaptiveThresholds Type)

; Model queries
(: model-version (-> LearningModel ModelVersion))
(: model-edit-weights (-> LearningModel EditWeights))
(: model-feature-weights (-> LearningModel FeatureWeights))
(: model-thresholds (-> LearningModel AdaptiveThresholds))
```

### Weight Predicates

```metta
; Edit weight queries
(: insertion-cost (-> EditWeights Char Float))
(: deletion-cost (-> EditWeights Char Float))
(: substitution-cost (-> EditWeights Char Char Float))

; Feature weight queries
(: feature-weight (-> FeatureWeights Feature Float))
(: score-candidate (-> FeatureWeights CandidateFeatures Float))

; Weight updates
(: update-edit-weight (-> LearningModel EditOperation Float LearningModel))
(: update-feature-weight (-> LearningModel Feature Float LearningModel))
(: normalize-feature-weights (-> FeatureWeights FeatureWeights))
```

### Threshold Predicates

```metta
; Threshold queries
(: suggestion-threshold (-> AdaptiveThresholds (Maybe UserId) (Maybe Domain) Float))
(: auto-correct-threshold (-> AdaptiveThresholds (Maybe UserId) (Maybe Domain) Float))

; Threshold updates
(: adapt-threshold (-> LearningModel UserId Feedback LearningModel))
(: reset-user-thresholds (-> LearningModel UserId LearningModel))
```

### Learning Predicates

```metta
; Online learning operations
(: update-from-feedback (-> LearningModel Feedback LearningModel))
(: batch-update (-> LearningModel (List Feedback) LearningModel))

; Model management
(: checkpoint-model (-> LearningModel Path (Result Path Error)))
(: restore-model (-> Path (Result LearningModel Error)))
(: rollback-model (-> LearningModel ModelVersion (Result LearningModel Error)))

; Metrics
(: model-acceptance-rate (-> LearningModel Float))
(: model-precision (-> LearningModel Float))
(: model-f1 (-> LearningModel Float))
(: performance-trend (-> LearningModel PerformanceTrend))
```

---

## Learning Pipeline Integration

```
┌─────────────────────────────────────────────────────────────────────────────┐
│              ONLINE LEARNING IN CORRECTION PIPELINE                          │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                              │
│  Feedback Event                                                              │
│      │                                                                       │
│      ▼                                                                       │
│  ┌───────────────────────────────────────────────────────────────────────┐  │
│  │                    FEEDBACK PROCESSOR                                  │  │
│  │                                                                        │  │
│  │  1. Normalize feedback signal                                         │  │
│  │  2. Extract features                                                  │  │
│  │  3. Compute learning weight                                           │  │
│  │                                                                        │  │
│  └───────────────────────────────────────────────────────────────────────┘  │
│      │                                                                       │
│      ├──────────────────┬──────────────────┬──────────────────┐             │
│      │                  │                  │                  │             │
│      ▼                  ▼                  ▼                  ▼             │
│  ┌──────────┐     ┌──────────┐     ┌──────────┐     ┌──────────┐          │
│  │ Edit     │     │ Feature  │     │ Threshold│     │ Pattern  │          │
│  │ Weight   │     │ Weight   │     │ Adapter  │     │ Weight   │          │
│  │ Updater  │     │ Updater  │     │          │     │ Updater  │          │
│  └────┬─────┘     └────┬─────┘     └────┬─────┘     └────┬─────┘          │
│       │                │                │                │                 │
│       └────────────────┴────────────────┴────────────────┘                 │
│                                    │                                        │
│                                    ▼                                        │
│  ┌───────────────────────────────────────────────────────────────────────┐  │
│  │                    MODEL MERGER                                        │  │
│  │                                                                        │  │
│  │  1. Combine weight updates                                            │  │
│  │  2. Apply regularization                                              │  │
│  │  3. Increment version                                                 │  │
│  │                                                                        │  │
│  └───────────────────────────────────────────────────────────────────────┘  │
│      │                                                                       │
│      ▼                                                                       │
│  ┌───────────────────────────────────────────────────────────────────────┐  │
│  │                    CHECKPOINT DECISION                                 │  │
│  │                                                                        │  │
│  │  if (updates % checkpoint_frequency == 0):                            │  │
│  │      create_checkpoint()                                              │  │
│  │  if (performance_degrading):                                          │  │
│  │      consider_rollback()                                              │  │
│  │                                                                        │  │
│  └───────────────────────────────────────────────────────────────────────┘  │
│      │                                                                       │
│      ▼                                                                       │
│  ┌───────────────────────────────────────────────────────────────────────┐  │
│  │                    UPDATED MODEL                                       │  │
│  │                                                                        │  │
│  │  Ready for next correction cycle                                      │  │
│  │                                                                        │  │
│  └───────────────────────────────────────────────────────────────────────┘  │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
```

---

## Error Handling

```rust
/// Online learning errors
#[derive(Debug, Clone, thiserror::Error)]
pub enum LearningError {
    #[error("Serialization error: {0}")]
    SerializationError(String),

    #[error("IO error: {0}")]
    IoError(String),

    #[error("Model version not found: {0:?}")]
    VersionNotFound(ModelVersion),

    #[error("No previous version available")]
    NoPreviousVersion,

    #[error("Insufficient history for rollback")]
    InsufficientHistory,

    #[error("Lock error")]
    LockError,

    #[error("Invalid hyperparameters: {0}")]
    InvalidHyperparameters(String),

    #[error("Update rejected: {0}")]
    UpdateRejected(String),
}
```

---

## Related Documentation

- [README](./README.md) - Agent learning overview
- [Feedback Collection](./01-feedback-collection.md) - Source of learning signals
- [Pattern Learning](./02-pattern-learning.md) - Pattern weight updates
- [User Preferences](./03-user-preferences.md) - Personalized threshold adaptation
