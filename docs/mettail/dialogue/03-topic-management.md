# Topic Management

This document describes topic graphs, continuity detection, and discourse segmentation
within the dialogue context layer.

**Sources**:
- Topic modeling: Blei et al. (2003) - LDA
- Discourse segmentation: Hearst (1997) - TextTiling
- Dialogue topic tracking: Xu & Reitter (2018)

---

## Table of Contents

1. [Overview](#overview)
2. [Topic Representation](#topic-representation)
3. [Topic Detection](#topic-detection)
4. [Topic Graph Management](#topic-graph-management)
5. [Topic Shifts and Continuity](#topic-shifts-and-continuity)
6. [Discourse Segmentation](#discourse-segmentation)
7. [MeTTa Predicate Implementation](#metta-predicate-implementation)
8. [PathMap Storage](#pathmap-storage)
9. [Integration with Correction](#integration-with-correction)

---

## Overview

Topic management tracks what the conversation is about and how it evolves. This
enables:

- **Contextual interpretation** - understanding utterances in topical context
- **Coherence validation** - detecting when corrections break topic flow
- **Reference resolution** - using topic to disambiguate references
- **Dialogue summarization** - identifying key topics discussed
- **Topic-aware ranking** - preferring corrections consistent with current topic

```
┌─────────────────────────────────────────────────────────────────────┐
│                      TOPIC MANAGEMENT                               │
│                                                                     │
│  Turn 1: "I went to Paris last summer."                            │
│          Topic: Travel/Paris                                        │
│                    │                                                │
│  Turn 2: "The Eiffel Tower was amazing."                           │
│          Topic: Travel/Paris/Attractions  (continuation)           │
│                    │                                                │
│  Turn 3: "Speaking of towers, have you seen the new office?"       │
│          Topic: Architecture/Office  (shift via bridging)          │
│                    │                                                │
│  Turn 4: "Yes, it has great views of the city."                    │
│          Topic: Architecture/Office  (continuation)                │
│                                                                     │
│  ┌───────────────────────────────────────────────────────────────┐ │
│  │                    Topic Graph                                 │ │
│  │                                                                │ │
│  │                    [Root]                                      │ │
│  │                   /      \                                     │ │
│  │            [Travel]    [Architecture]                          │ │
│  │               |             |                                  │ │
│  │           [Paris]       [Office]                               │ │
│  │               |             |                                  │ │
│  │        [Attractions]   [Views]                                 │ │
│  │                                                                │ │
│  └───────────────────────────────────────────────────────────────┘ │
└─────────────────────────────────────────────────────────────────────┘
```

---

## Topic Representation

### Topic Structure

```rust
/// Topic in the dialogue
pub struct Topic {
    /// Unique identifier
    id: TopicId,

    /// Human-readable label
    label: String,

    /// Parent topic (if hierarchical)
    parent: Option<TopicId>,

    /// Child topics
    children: Vec<TopicId>,

    /// Keywords associated with this topic
    keywords: HashMap<String, f64>,  // keyword -> weight

    /// Entities strongly associated with this topic
    associated_entities: Vec<EntityId>,

    /// Turns where this topic is active
    active_turns: Vec<TurnId>,

    /// Activation level (0.0 to 1.0)
    activation: f64,

    /// When first introduced
    introduced_at: TurnId,

    /// When last active
    last_active: TurnId,
}

/// Topic graph for hierarchical topic structure
pub struct TopicGraph {
    /// All topics
    topics: HashMap<TopicId, Topic>,

    /// Root topics (no parent)
    roots: Vec<TopicId>,

    /// Currently active topic stack
    active_stack: Vec<TopicId>,

    /// Topic similarity cache
    similarity_cache: HashMap<(TopicId, TopicId), f64>,

    /// Keyword index for fast lookup
    keyword_index: HashMap<String, Vec<TopicId>>,
}

/// Reference to a topic from a turn
pub struct TopicRef {
    /// Topic being referenced
    topic_id: TopicId,

    /// Confidence in this topic assignment
    confidence: f64,

    /// Whether this is the primary topic of the turn
    is_primary: bool,

    /// Keywords that triggered this topic
    trigger_keywords: Vec<String>,
}
```

### Topic Features

```rust
/// Features for topic representation
pub struct TopicFeatures {
    /// Bag-of-words representation
    bow: HashMap<String, f64>,

    /// Embedding vector (if using neural topics)
    embedding: Option<Vec<f64>>,

    /// Named entities typical of this topic
    typical_entities: Vec<EntityType>,

    /// Typical speech acts
    typical_acts: Vec<SpeechActType>,
}

impl Topic {
    /// Compute similarity to another topic
    pub fn similarity(&self, other: &Topic) -> f64 {
        // Keyword overlap (Jaccard-like)
        let mut overlap = 0.0;
        let mut total = 0.0;

        for (keyword, weight) in &self.keywords {
            total += weight;
            if let Some(other_weight) = other.keywords.get(keyword) {
                overlap += weight.min(*other_weight);
            }
        }

        for (keyword, weight) in &other.keywords {
            if !self.keywords.contains_key(keyword) {
                total += weight;
            }
        }

        if total > 0.0 {
            overlap / total
        } else {
            0.0
        }
    }

    /// Check if this topic is a subtopic of another
    pub fn is_subtopic_of(&self, potential_parent: TopicId, graph: &TopicGraph) -> bool {
        let mut current = self.parent;
        while let Some(parent_id) = current {
            if parent_id == potential_parent {
                return true;
            }
            current = graph.topics.get(&parent_id).and_then(|t| t.parent);
        }
        false
    }
}
```

---

## Topic Detection

### Keyword-Based Detection

```rust
/// Topic detector using keywords and patterns
pub struct TopicDetector {
    /// Known topic patterns in MORK space
    mork_space: MorkSpace,

    /// Keyword to topic mapping
    keyword_map: HashMap<String, Vec<(TopicId, f64)>>,

    /// Stop words to ignore
    stop_words: HashSet<String>,

    /// Minimum keyword weight threshold
    min_weight: f64,
}

impl TopicDetector {
    /// Detect topics in a turn
    pub fn detect_topics(&self, turn: &Turn, graph: &TopicGraph) -> Vec<TopicRef> {
        let mut topic_scores: HashMap<TopicId, f64> = HashMap::new();
        let mut trigger_keywords: HashMap<TopicId, Vec<String>> = HashMap::new();

        // Extract keywords from turn
        let keywords = self.extract_keywords(&turn.raw_text);

        // Score topics by keyword matches
        for keyword in &keywords {
            if let Some(topics) = self.keyword_map.get(keyword) {
                for (topic_id, weight) in topics {
                    *topic_scores.entry(*topic_id).or_default() += weight;
                    trigger_keywords.entry(*topic_id).or_default().push(keyword.clone());
                }
            }
        }

        // Consider entities mentioned
        for entity in &turn.entities {
            if let Some(entity_id) = entity.entity_id {
                for (topic_id, topic) in &graph.topics {
                    if topic.associated_entities.contains(&entity_id) {
                        *topic_scores.entry(*topic_id).or_default() += 0.5;
                    }
                }
            }
        }

        // Consider parent topic activation (topic inheritance)
        for topic_id in &graph.active_stack {
            if let Some(topic) = graph.topics.get(topic_id) {
                // Boost subtopics of active topics
                for child_id in &topic.children {
                    if let Some(score) = topic_scores.get_mut(child_id) {
                        *score *= 1.2; // 20% boost for subtopics
                    }
                }
            }
        }

        // Convert to TopicRefs
        let mut refs: Vec<TopicRef> = topic_scores.into_iter()
            .filter(|(_, score)| *score >= self.min_weight)
            .map(|(topic_id, score)| TopicRef {
                topic_id,
                confidence: score.min(1.0),
                is_primary: false,
                trigger_keywords: trigger_keywords.remove(&topic_id).unwrap_or_default(),
            })
            .collect();

        // Sort by confidence and mark primary
        refs.sort_by(|a, b| b.confidence.partial_cmp(&a.confidence).unwrap());
        if let Some(first) = refs.first_mut() {
            first.is_primary = true;
        }

        refs
    }

    /// Extract keywords from text
    fn extract_keywords(&self, text: &str) -> Vec<String> {
        text.split_whitespace()
            .map(|w| w.to_lowercase())
            .filter(|w| !self.stop_words.contains(w))
            .filter(|w| w.len() > 2)
            .collect()
    }

    /// Create a new topic from detected keywords
    pub fn create_topic(
        &self,
        keywords: &[String],
        turn: &Turn,
        graph: &mut TopicGraph,
    ) -> TopicId {
        let topic_id = graph.next_topic_id();

        // Determine parent by finding most similar existing topic
        let parent = self.find_best_parent(keywords, graph);

        // Create keyword weights (TF-based for now)
        let mut keyword_weights = HashMap::new();
        for kw in keywords {
            *keyword_weights.entry(kw.clone()).or_default() += 1.0;
        }

        // Normalize weights
        let total: f64 = keyword_weights.values().sum();
        for weight in keyword_weights.values_mut() {
            *weight /= total;
        }

        let topic = Topic {
            id: topic_id,
            label: self.generate_label(keywords),
            parent,
            children: Vec::new(),
            keywords: keyword_weights,
            associated_entities: turn.entities.iter()
                .filter_map(|e| e.entity_id)
                .collect(),
            active_turns: vec![turn.turn_id],
            activation: 1.0,
            introduced_at: turn.turn_id,
            last_active: turn.turn_id,
        };

        graph.topics.insert(topic_id, topic);

        // Update parent's children
        if let Some(parent_id) = parent {
            if let Some(parent_topic) = graph.topics.get_mut(&parent_id) {
                parent_topic.children.push(topic_id);
            }
        } else {
            graph.roots.push(topic_id);
        }

        // Update keyword index
        for keyword in keywords {
            graph.keyword_index.entry(keyword.clone())
                .or_default()
                .push(topic_id);
        }

        topic_id
    }

    /// Find best parent topic for keywords
    fn find_best_parent(&self, keywords: &[String], graph: &TopicGraph) -> Option<TopicId> {
        let mut best_parent = None;
        let mut best_score = 0.3; // Minimum threshold

        for (topic_id, topic) in &graph.topics {
            // Compute keyword overlap
            let overlap: f64 = keywords.iter()
                .filter_map(|kw| topic.keywords.get(kw))
                .sum();

            if overlap > best_score {
                best_score = overlap;
                best_parent = Some(*topic_id);
            }
        }

        best_parent
    }

    /// Generate readable label from keywords
    fn generate_label(&self, keywords: &[String]) -> String {
        // Use top 2-3 keywords
        keywords.iter()
            .take(3)
            .cloned()
            .collect::<Vec<_>>()
            .join("/")
    }
}
```

### Neural Topic Detection (Optional)

```rust
/// Neural topic detector using embeddings
pub struct NeuralTopicDetector {
    /// Sentence encoder
    encoder: SentenceEncoder,

    /// Topic embeddings
    topic_embeddings: HashMap<TopicId, Vec<f64>>,

    /// Similarity threshold
    threshold: f64,
}

impl NeuralTopicDetector {
    /// Detect topics using embedding similarity
    pub fn detect_topics(&self, turn: &Turn, graph: &TopicGraph) -> Vec<TopicRef> {
        // Encode the turn text
        let turn_embedding = self.encoder.encode(&turn.raw_text);

        // Compute similarity to all topic embeddings
        let mut similarities: Vec<(TopicId, f64)> = self.topic_embeddings.iter()
            .map(|(topic_id, embedding)| {
                let sim = cosine_similarity(&turn_embedding, embedding);
                (*topic_id, sim)
            })
            .filter(|(_, sim)| *sim >= self.threshold)
            .collect();

        similarities.sort_by(|a, b| b.1.partial_cmp(&a.1).unwrap());

        similarities.into_iter()
            .enumerate()
            .map(|(i, (topic_id, sim))| TopicRef {
                topic_id,
                confidence: sim,
                is_primary: i == 0,
                trigger_keywords: Vec::new(), // Neural doesn't use keywords
            })
            .collect()
    }

    /// Update topic embedding after new turn
    pub fn update_topic_embedding(&mut self, topic_id: TopicId, turn: &Turn) {
        let turn_embedding = self.encoder.encode(&turn.raw_text);

        self.topic_embeddings.entry(topic_id)
            .and_modify(|emb| {
                // Running average update
                for (i, val) in emb.iter_mut().enumerate() {
                    *val = 0.9 * *val + 0.1 * turn_embedding[i];
                }
            })
            .or_insert(turn_embedding);
    }
}

/// Compute cosine similarity between vectors
fn cosine_similarity(a: &[f64], b: &[f64]) -> f64 {
    let dot: f64 = a.iter().zip(b.iter()).map(|(x, y)| x * y).sum();
    let norm_a: f64 = a.iter().map(|x| x * x).sum::<f64>().sqrt();
    let norm_b: f64 = b.iter().map(|x| x * x).sum::<f64>().sqrt();

    if norm_a > 0.0 && norm_b > 0.0 {
        dot / (norm_a * norm_b)
    } else {
        0.0
    }
}
```

---

## Topic Graph Management

### Graph Operations

```rust
impl TopicGraph {
    /// Get current active topic
    pub fn current_topic(&self) -> Option<&Topic> {
        self.active_stack.last()
            .and_then(|id| self.topics.get(id))
    }

    /// Push a new topic onto the active stack
    pub fn push_topic(&mut self, topic_id: TopicId) {
        if !self.active_stack.contains(&topic_id) {
            self.active_stack.push(topic_id);
        }

        if let Some(topic) = self.topics.get_mut(&topic_id) {
            topic.activation = 1.0;
        }
    }

    /// Pop topic from active stack
    pub fn pop_topic(&mut self) -> Option<TopicId> {
        self.active_stack.pop()
    }

    /// Update topic activations after a turn
    pub fn update_activations(&mut self, turn: &Turn, topic_refs: &[TopicRef]) {
        // Decay all activations
        for topic in self.topics.values_mut() {
            topic.activation *= 0.9; // 10% decay per turn
        }

        // Boost mentioned topics
        for topic_ref in topic_refs {
            if let Some(topic) = self.topics.get_mut(&topic_ref.topic_id) {
                topic.activation = (topic.activation + topic_ref.confidence).min(1.0);
                topic.active_turns.push(turn.turn_id);
                topic.last_active = turn.turn_id;
            }
        }

        // Remove very low activation topics from active stack
        self.active_stack.retain(|id| {
            self.topics.get(id)
                .map(|t| t.activation > 0.1)
                .unwrap_or(false)
        });

        // Add high activation topics to stack
        for topic_ref in topic_refs {
            if topic_ref.confidence > 0.5 && !self.active_stack.contains(&topic_ref.topic_id) {
                self.active_stack.push(topic_ref.topic_id);
            }
        }
    }

    /// Get topics related to a given topic
    pub fn related_topics(&self, topic_id: TopicId) -> Vec<(TopicId, f64)> {
        let topic = match self.topics.get(&topic_id) {
            Some(t) => t,
            None => return Vec::new(),
        };

        let mut related = Vec::new();

        // Parent and siblings
        if let Some(parent_id) = topic.parent {
            related.push((parent_id, 0.8));

            if let Some(parent) = self.topics.get(&parent_id) {
                for sibling_id in &parent.children {
                    if *sibling_id != topic_id {
                        related.push((*sibling_id, 0.6));
                    }
                }
            }
        }

        // Children
        for child_id in &topic.children {
            related.push((*child_id, 0.9));
        }

        // Similar topics by keywords
        for (other_id, other_topic) in &self.topics {
            if *other_id != topic_id && !related.iter().any(|(id, _)| id == other_id) {
                let sim = topic.similarity(other_topic);
                if sim > 0.3 {
                    related.push((*other_id, sim));
                }
            }
        }

        related.sort_by(|a, b| b.1.partial_cmp(&a.1).unwrap());
        related
    }

    /// Merge two topics
    pub fn merge_topics(&mut self, topic1: TopicId, topic2: TopicId) -> TopicId {
        let t1 = self.topics.remove(&topic1);
        let t2 = self.topics.remove(&topic2);

        if let (Some(mut t1), Some(t2)) = (t1, t2) {
            // Merge keywords
            for (kw, weight) in t2.keywords {
                *t1.keywords.entry(kw).or_default() += weight;
            }

            // Merge entities
            for entity_id in t2.associated_entities {
                if !t1.associated_entities.contains(&entity_id) {
                    t1.associated_entities.push(entity_id);
                }
            }

            // Merge active turns
            t1.active_turns.extend(t2.active_turns);
            t1.active_turns.sort();
            t1.active_turns.dedup();

            // Adopt children of t2
            for child_id in t2.children {
                if let Some(child) = self.topics.get_mut(&child_id) {
                    child.parent = Some(topic1);
                }
                if !t1.children.contains(&child_id) {
                    t1.children.push(child_id);
                }
            }

            // Update label
            t1.label = format!("{}/{}", t1.label, t2.label);

            self.topics.insert(topic1, t1);

            // Update keyword index
            for topics in self.keyword_index.values_mut() {
                topics.retain(|id| *id != topic2);
            }

            // Update active stack
            self.active_stack.retain(|id| *id != topic2);

            topic1
        } else {
            topic1
        }
    }
}
```

---

## Topic Shifts and Continuity

### Topic Transition Types

```rust
/// Types of topic transitions
#[derive(Clone, Debug, PartialEq)]
pub enum TopicTransition {
    /// Same topic continues
    Continuation,

    /// Topic deepens (parent to child)
    Specialization {
        from: TopicId,
        to: TopicId,
    },

    /// Topic broadens (child to parent)
    Generalization {
        from: TopicId,
        to: TopicId,
    },

    /// Related topic via shared parent
    SiblingShift {
        from: TopicId,
        to: TopicId,
        common_parent: TopicId,
    },

    /// Bridging shift (via entity or keyword)
    BridgingShift {
        from: TopicId,
        to: TopicId,
        bridge: TopicBridge,
    },

    /// Abrupt topic change
    AbruptShift {
        from: TopicId,
        to: TopicId,
    },

    /// Return to earlier topic
    Return {
        to: TopicId,
        from: TopicId,
    },
}

/// Bridge element connecting topics
pub enum TopicBridge {
    SharedEntity(EntityId),
    SharedKeyword(String),
    ExplicitMarker(String),  // "Speaking of...", "That reminds me..."
}
```

### Transition Detection

```rust
/// Topic transition detector
pub struct TransitionDetector {
    /// Topic graph
    graph: TopicGraph,

    /// Transition markers
    shift_markers: Vec<(String, ShiftMarkerType)>,
}

#[derive(Clone)]
pub enum ShiftMarkerType {
    Continuation,    // "also", "and", "moreover"
    Contrast,        // "but", "however", "on the other hand"
    Bridge,          // "speaking of", "that reminds me"
    Return,          // "anyway", "as I was saying", "back to"
    New,             // "by the way", "incidentally"
}

impl TransitionDetector {
    /// Detect topic transition between turns
    pub fn detect_transition(
        &self,
        prev_turn: &Turn,
        current_turn: &Turn,
    ) -> TopicTransition {
        let prev_topics = &prev_turn.topics;
        let curr_topics = &current_turn.topics;

        // Get primary topics
        let prev_primary = prev_topics.iter().find(|t| t.is_primary);
        let curr_primary = curr_topics.iter().find(|t| t.is_primary);

        match (prev_primary, curr_primary) {
            (Some(prev), Some(curr)) if prev.topic_id == curr.topic_id => {
                TopicTransition::Continuation
            }

            (Some(prev), Some(curr)) => {
                let prev_topic = self.graph.topics.get(&prev.topic_id);
                let curr_topic = self.graph.topics.get(&curr.topic_id);

                match (prev_topic, curr_topic) {
                    (Some(pt), Some(ct)) => {
                        // Check for specialization (parent to child)
                        if ct.parent == Some(prev.topic_id) {
                            return TopicTransition::Specialization {
                                from: prev.topic_id,
                                to: curr.topic_id,
                            };
                        }

                        // Check for generalization (child to parent)
                        if pt.parent == Some(curr.topic_id) {
                            return TopicTransition::Generalization {
                                from: prev.topic_id,
                                to: curr.topic_id,
                            };
                        }

                        // Check for sibling shift
                        if pt.parent == ct.parent && pt.parent.is_some() {
                            return TopicTransition::SiblingShift {
                                from: prev.topic_id,
                                to: curr.topic_id,
                                common_parent: pt.parent.unwrap(),
                            };
                        }

                        // Check for return to earlier topic
                        if self.is_return_to_earlier(curr.topic_id, prev.topic_id) {
                            return TopicTransition::Return {
                                to: curr.topic_id,
                                from: prev.topic_id,
                            };
                        }

                        // Check for bridging
                        if let Some(bridge) = self.find_bridge(pt, ct, current_turn) {
                            return TopicTransition::BridgingShift {
                                from: prev.topic_id,
                                to: curr.topic_id,
                                bridge,
                            };
                        }

                        // Default to abrupt shift
                        TopicTransition::AbruptShift {
                            from: prev.topic_id,
                            to: curr.topic_id,
                        }
                    }
                    _ => TopicTransition::Continuation,
                }
            }

            _ => TopicTransition::Continuation,
        }
    }

    /// Find bridge element between topics
    fn find_bridge(
        &self,
        from_topic: &Topic,
        to_topic: &Topic,
        turn: &Turn,
    ) -> Option<TopicBridge> {
        // Check for explicit shift markers
        for (marker, marker_type) in &self.shift_markers {
            if turn.raw_text.to_lowercase().contains(marker) {
                if matches!(marker_type, ShiftMarkerType::Bridge) {
                    return Some(TopicBridge::ExplicitMarker(marker.clone()));
                }
            }
        }

        // Check for shared entities
        for entity_id in &from_topic.associated_entities {
            if to_topic.associated_entities.contains(entity_id) {
                return Some(TopicBridge::SharedEntity(*entity_id));
            }
        }

        // Check for shared keywords
        for keyword in from_topic.keywords.keys() {
            if to_topic.keywords.contains_key(keyword) {
                return Some(TopicBridge::SharedKeyword(keyword.clone()));
            }
        }

        None
    }

    /// Check if this is a return to an earlier active topic
    fn is_return_to_earlier(&self, topic_id: TopicId, current_id: TopicId) -> bool {
        // Topic was in active stack before current topic
        let topic = self.graph.topics.get(&topic_id);
        let current = self.graph.topics.get(&current_id);

        match (topic, current) {
            (Some(t), Some(c)) => {
                // Earlier introduced and was active recently
                t.introduced_at < c.introduced_at && t.activation > 0.2
            }
            _ => false,
        }
    }
}
```

---

## Discourse Segmentation

### TextTiling-Inspired Segmentation

```rust
/// Discourse segmenter for topic boundaries
pub struct DiscourseSegmenter {
    /// Window size for similarity computation
    window_size: usize,

    /// Threshold for boundary detection
    boundary_threshold: f64,

    /// Topic graph for segment labeling
    topic_graph: TopicGraph,
}

/// Discourse segment
pub struct DiscourseSegment {
    /// Segment identifier
    id: SegmentId,

    /// Turns in this segment
    turns: Vec<TurnId>,

    /// Primary topic of segment
    primary_topic: Option<TopicId>,

    /// All topics mentioned in segment
    topics: Vec<TopicId>,

    /// Start turn
    start_turn: TurnId,

    /// End turn
    end_turn: TurnId,

    /// Boundary strength at end (if not last segment)
    boundary_strength: Option<f64>,
}

impl DiscourseSegmenter {
    /// Segment a dialogue into topic-coherent blocks
    pub fn segment(&self, dialogue: &DialogueState) -> Vec<DiscourseSegment> {
        let turns: Vec<&Turn> = dialogue.turns.iter().collect();

        if turns.len() < 2 {
            // Single turn is one segment
            return vec![self.create_segment(&turns, 0, turns.len())];
        }

        // Compute similarity between adjacent blocks
        let similarities = self.compute_block_similarities(&turns);

        // Find boundaries (local minima below threshold)
        let boundaries = self.find_boundaries(&similarities);

        // Create segments from boundaries
        let mut segments = Vec::new();
        let mut start = 0;

        for boundary in boundaries {
            if boundary > start {
                segments.push(self.create_segment(&turns, start, boundary));
            }
            start = boundary;
        }

        // Add final segment
        if start < turns.len() {
            segments.push(self.create_segment(&turns, start, turns.len()));
        }

        segments
    }

    /// Compute similarity between adjacent blocks of turns
    fn compute_block_similarities(&self, turns: &[&Turn]) -> Vec<f64> {
        let mut similarities = Vec::new();

        for i in self.window_size..(turns.len() - self.window_size) {
            // Left block: turns[i-window..i]
            let left_keywords = self.extract_block_keywords(
                &turns[(i - self.window_size)..i]
            );

            // Right block: turns[i..i+window]
            let right_keywords = self.extract_block_keywords(
                &turns[i..(i + self.window_size).min(turns.len())]
            );

            // Cosine similarity between keyword vectors
            let sim = self.keyword_similarity(&left_keywords, &right_keywords);
            similarities.push(sim);
        }

        similarities
    }

    /// Extract keywords from a block of turns
    fn extract_block_keywords(&self, turns: &[&Turn]) -> HashMap<String, f64> {
        let mut keywords = HashMap::new();

        for turn in turns {
            for topic_ref in &turn.topics {
                if let Some(topic) = self.topic_graph.topics.get(&topic_ref.topic_id) {
                    for (kw, weight) in &topic.keywords {
                        *keywords.entry(kw.clone()).or_default() += weight * topic_ref.confidence;
                    }
                }
            }
        }

        keywords
    }

    /// Find boundaries as local minima
    fn find_boundaries(&self, similarities: &[f64]) -> Vec<usize> {
        let mut boundaries = Vec::new();

        // Compute depth scores (how much lower than neighbors)
        let depth_scores: Vec<f64> = similarities.iter()
            .enumerate()
            .map(|(i, &sim)| {
                let left = if i > 0 { similarities[i - 1] } else { sim };
                let right = if i < similarities.len() - 1 { similarities[i + 1] } else { sim };
                (left - sim).max(0.0) + (right - sim).max(0.0)
            })
            .collect();

        // Find peaks in depth scores
        let mean_depth: f64 = depth_scores.iter().sum::<f64>() / depth_scores.len() as f64;
        let std_depth: f64 = (depth_scores.iter()
            .map(|d| (d - mean_depth).powi(2))
            .sum::<f64>() / depth_scores.len() as f64).sqrt();

        let threshold = mean_depth + std_depth;

        for (i, &depth) in depth_scores.iter().enumerate() {
            if depth > threshold {
                boundaries.push(i + self.window_size); // Adjust for window offset
            }
        }

        boundaries
    }

    /// Create a segment from a range of turns
    fn create_segment(&self, turns: &[&Turn], start: usize, end: usize) -> DiscourseSegment {
        let segment_turns: Vec<TurnId> = turns[start..end].iter()
            .map(|t| t.turn_id)
            .collect();

        // Collect all topics in segment
        let mut topic_counts: HashMap<TopicId, usize> = HashMap::new();
        for turn in &turns[start..end] {
            for topic_ref in &turn.topics {
                *topic_counts.entry(topic_ref.topic_id).or_default() += 1;
            }
        }

        // Primary topic is most frequent
        let primary_topic = topic_counts.iter()
            .max_by_key(|(_, count)| *count)
            .map(|(id, _)| *id);

        DiscourseSegment {
            id: SegmentId::new(),
            turns: segment_turns,
            primary_topic,
            topics: topic_counts.keys().cloned().collect(),
            start_turn: turns[start].turn_id,
            end_turn: turns[end - 1].turn_id,
            boundary_strength: None,
        }
    }
}
```

---

## MeTTa Predicate Implementation

### Topic Predicates

```metta
; === Topic Types ===

(: Topic Type)
(: TopicId Type)
(: TopicRef Type)
(: TopicTransition Type)

; === Topic Graph Predicates ===

; Get current active topic
(: current-topic (-> DialogueState (Maybe Topic)))

; Get topic by ID
(: get-topic (-> TopicId TopicGraph (Maybe Topic)))

; Get topic label
(: topic-label (-> Topic String))

; Get topic parent
(: topic-parent (-> Topic (Maybe TopicId)))

; Get topic children
(: topic-children (-> Topic (List TopicId)))

; Get topic activation level
(: topic-activation (-> Topic Float))

; === Topic Detection Predicates ===

; Detect topics in a turn
(: detect-topics (-> Turn TopicGraph (List TopicRef)))

; Get primary topic of turn
(: primary-topic (-> Turn (Maybe TopicId)))

; Check if turn mentions topic
(: mentions-topic (-> Turn TopicId Bool))

; === Topic Relationship Predicates ===

; Compute topic similarity
(: topic-similarity (-> Topic Topic Float))

; Check if subtopic relationship
(: is-subtopic (-> TopicId TopicId TopicGraph Bool))

; Get related topics
(: related-topics (-> TopicId TopicGraph (List (Pair TopicId Float))))

; === Topic Transition Predicates ===

; Detect topic shift between turns
(: topic-shift (-> Turn Turn Bool))

; Get transition type
(: transition-type (-> Turn Turn TopicTransition))

; Check transition types
(: is-continuation (-> TopicTransition Bool))
(: is-abrupt-shift (-> TopicTransition Bool))

; === Implementations ===

; Topic similarity via keyword overlap
(= (topic-similarity $t1 $t2)
   (let $kw1 (topic-keywords $t1)
        $kw2 (topic-keywords $t2)
        (jaccard-similarity $kw1 $kw2)))

; Check for topic shift
(= (topic-shift $prev $curr)
   (not (== (primary-topic $prev) (primary-topic $curr))))

; Transition classification
(= (is-continuation (Continuation)) True)
(= (is-continuation _) False)

(= (is-abrupt-shift (AbruptShift _ _)) True)
(= (is-abrupt-shift _) False)

; Get active topics
(= (current-topic $state)
   (let $stack (active-topic-stack $state)
        (if (empty? $stack)
            Nothing
            (Just (head $stack)))))

; === Coherence Predicates ===

; Check if turn is topically coherent with context
(: topically-coherent (-> Turn DialogueState Bool))

(= (topically-coherent $turn $state)
   (let $current (current-topic $state)
        $turn-topics (turn-topics $turn)
        (case $current
          (Nothing True)  ; No active topic, anything is coherent
          ((Just $topic) (any (related-to $topic) $turn-topics)))))

; Check if topic is related to another
(= (related-to $topic1 $topic2)
   (or (== $topic1 $topic2)
       (is-subtopic $topic1 $topic2)
       (is-subtopic $topic2 $topic1)
       (> (topic-similarity $topic1 $topic2) 0.3)))
```

---

## PathMap Storage

### Topic Storage Schema

```
/dialogue/{dialogue_id}/
    /topic/{topic_id}/
        label           → topic label string
        parent          → parent topic_id (optional)
        activation      → current activation level
        introduced_at   → turn_id
        last_active     → turn_id

        /children/
            {child_id}  → true

        /keywords/
            {keyword}   → weight (float)

        /entities/
            {entity_id} → true

        /active_turns/
            {turn_id}   → true

    /topic_graph/
        /roots/
            {topic_id}  → true

        /active_stack   → [topic_id, ...] (ordered list)

        /similarity/
            {topic1_id}/{topic2_id} → cached similarity

    /segment/{segment_id}/
        start_turn      → turn_id
        end_turn        → turn_id
        primary_topic   → topic_id

        /turns/
            {turn_id}   → true

        /topics/
            {topic_id}  → true
```

### Storage Operations

```rust
impl TopicGraph {
    /// Persist topic to PathMap
    pub fn store_topic(&self, topic: &Topic, pathmap: &mut PathMap) -> Result<(), Error> {
        let base = format!("/dialogue/{}/topic/{}/", self.dialogue_id, topic.id);

        pathmap.insert(format!("{}label", base).as_bytes(), topic.label.as_bytes())?;

        if let Some(parent) = topic.parent {
            pathmap.insert(format!("{}parent", base).as_bytes(), &parent.0.to_le_bytes())?;
        }

        pathmap.insert(format!("{}activation", base).as_bytes(), &topic.activation.to_le_bytes())?;
        pathmap.insert(format!("{}introduced_at", base).as_bytes(), &topic.introduced_at.0.to_le_bytes())?;
        pathmap.insert(format!("{}last_active", base).as_bytes(), &topic.last_active.0.to_le_bytes())?;

        // Store children
        for child_id in &topic.children {
            pathmap.insert(format!("{}children/{}", base, child_id.0).as_bytes(), &[1])?;
        }

        // Store keywords
        for (keyword, weight) in &topic.keywords {
            pathmap.insert(
                format!("{}keywords/{}", base, keyword).as_bytes(),
                &weight.to_le_bytes()
            )?;
        }

        // Store entities
        for entity_id in &topic.associated_entities {
            pathmap.insert(format!("{}entities/{}", base, entity_id.0).as_bytes(), &[1])?;
        }

        // Store active turns
        for turn_id in &topic.active_turns {
            pathmap.insert(format!("{}active_turns/{}", base, turn_id.0).as_bytes(), &[1])?;
        }

        Ok(())
    }

    /// Load topic from PathMap
    pub fn load_topic(&self, topic_id: TopicId, pathmap: &PathMap) -> Result<Topic, Error> {
        let base = format!("/dialogue/{}/topic/{}/", self.dialogue_id, topic_id);

        let label = pathmap.get(format!("{}label", base).as_bytes())?
            .map(|b| String::from_utf8_lossy(&b).to_string())
            .unwrap_or_default();

        let parent = pathmap.get(format!("{}parent", base).as_bytes())?
            .map(|b| TopicId(u64::from_le_bytes(b.try_into().unwrap_or_default())));

        let activation = pathmap.get(format!("{}activation", base).as_bytes())?
            .map(|b| f64::from_le_bytes(b.try_into().unwrap_or_default()))
            .unwrap_or(0.0);

        // Load children
        let children = pathmap.query_prefix(format!("{}children/", base).as_bytes())?
            .map(|(key, _)| {
                let id_str = String::from_utf8_lossy(&key).to_string();
                let id = id_str.rsplit('/').next().unwrap_or("0");
                TopicId(id.parse().unwrap_or(0))
            })
            .collect();

        // Load keywords
        let keywords = pathmap.query_prefix(format!("{}keywords/", base).as_bytes())?
            .map(|(key, value)| {
                let keyword = String::from_utf8_lossy(&key)
                    .rsplit('/')
                    .next()
                    .unwrap_or("")
                    .to_string();
                let weight = f64::from_le_bytes(value.try_into().unwrap_or_default());
                (keyword, weight)
            })
            .collect();

        Ok(Topic {
            id: topic_id,
            label,
            parent,
            children,
            keywords,
            associated_entities: Vec::new(), // Load separately
            active_turns: Vec::new(),        // Load separately
            activation,
            introduced_at: TurnId(0),        // Load from storage
            last_active: TurnId(0),          // Load from storage
        })
    }
}
```

---

## Integration with Correction

### Topic-Aware Correction Ranking

```rust
/// Topic-aware correction ranker
pub struct TopicCorrectionRanker {
    topic_graph: TopicGraph,
    topic_detector: TopicDetector,
}

impl TopicCorrectionRanker {
    /// Rank corrections by topic coherence
    pub fn rank_by_topic(
        &self,
        candidates: Vec<CorrectionCandidate>,
        turn: &Turn,
        context: &DialogueState,
    ) -> Vec<(CorrectionCandidate, f64)> {
        let current_topic = self.topic_graph.current_topic();

        candidates.into_iter()
            .map(|candidate| {
                let score = self.compute_topic_score(&candidate, current_topic, turn);
                (candidate, score)
            })
            .sorted_by(|a, b| b.1.partial_cmp(&a.1).unwrap())
            .collect()
    }

    /// Compute topic coherence score for a correction
    fn compute_topic_score(
        &self,
        candidate: &CorrectionCandidate,
        current_topic: Option<&Topic>,
        turn: &Turn,
    ) -> f64 {
        let corrected_text = candidate.apply_to(&turn.raw_text);

        // Detect topics in corrected text
        let corrected_topics = self.topic_detector.detect_from_text(&corrected_text);

        let Some(topic) = current_topic else {
            // No active topic, all corrections equally valid topically
            return 1.0;
        };

        // Check if correction maintains topic coherence
        let mut coherence = 0.0;

        for corrected_topic in &corrected_topics {
            if corrected_topic.topic_id == topic.id {
                coherence += corrected_topic.confidence;
            } else if let Some(ct) = self.topic_graph.topics.get(&corrected_topic.topic_id) {
                // Related topic is also acceptable
                coherence += topic.similarity(ct) * corrected_topic.confidence;
            }
        }

        coherence.min(1.0)
    }

    /// Filter corrections that introduce off-topic content
    pub fn filter_off_topic(
        &self,
        candidates: Vec<CorrectionCandidate>,
        context: &DialogueState,
        threshold: f64,
    ) -> Vec<CorrectionCandidate> {
        let current_topic = self.topic_graph.current_topic();

        candidates.into_iter()
            .filter(|candidate| {
                let score = self.compute_topic_score(
                    candidate,
                    current_topic,
                    context.current_turn()
                );
                score >= threshold
            })
            .collect()
    }
}
```

---

## Summary

Topic management provides discourse-level context for correction:

1. **Topic Representation** - Hierarchical topics with keywords and entity associations
2. **Topic Detection** - Keyword-based and neural topic detection
3. **Topic Graph** - Management of topic hierarchy and activation
4. **Topic Transitions** - Detection of continuation, shifts, and returns
5. **Discourse Segmentation** - TextTiling-inspired boundary detection
6. **Correction Integration** - Topic-aware ranking and filtering

---

## References

- Blei, D., Ng, A., & Jordan, M. (2003). "Latent Dirichlet Allocation"
- Hearst, M. (1997). "TextTiling: Segmenting Text into Multi-paragraph Subtopic Passages"
- Xu, Y. & Reitter, D. (2018). "Topic Modeling for Computational Discourse Analysis"
- Purver, M. (2011). "Topic Segmentation" in Handbook of Discourse Analysis

See [04-pragmatic-reasoning.md](./04-pragmatic-reasoning.md) for speech acts and implicatures.
