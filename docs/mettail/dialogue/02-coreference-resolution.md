# Coreference Resolution

This document describes entity tracking, pronoun resolution, and salience modeling
within the dialogue context layer.

**Sources**:
- Centering Theory: Grosz, Joshi, & Weinstein (1995)
- Entity-based models: Clark & Manning (2015)
- Neural coreference: Lee et al. (2017)

---

## Table of Contents

1. [Overview](#overview)
2. [Entity Registry](#entity-registry)
3. [Mention Detection](#mention-detection)
4. [Salience Modeling](#salience-modeling)
5. [Resolution Algorithms](#resolution-algorithms)
6. [Cross-Turn Coreference](#cross-turn-coreference)
7. [MeTTa Predicate Implementation](#metta-predicate-implementation)
8. [PathMap Storage](#pathmap-storage)
9. [Integration with Correction](#integration-with-correction)

---

## Overview

Coreference resolution identifies when different expressions refer to the same
entity. In dialogue, this is crucial because:

- Pronouns are frequent ("he", "it", "they")
- Definite descriptions assume shared knowledge ("the meeting")
- Entity references span multiple turns
- Speakers use bridging references ("the door" → door of mentioned house)

```
Turn 1: "I met John at the conference yesterday."
              ^^^^      ^^^^^^^^^^^^^^^
              Entity1   Entity2

Turn 2: "He gave an interesting talk about AI."
         ^^                          ^^
         Entity1                     Entity3

Turn 3: "It was the highlight of the event."
         ^^              ^^^^^
         Entity3         Entity2 (bridging)
```

The coreference system must:
1. **Detect mentions** - identify referring expressions
2. **Track entities** - maintain entity registry across turns
3. **Resolve references** - link mentions to entities
4. **Model salience** - track which entities are currently prominent

```
┌─────────────────────────────────────────────────────────────────────┐
│                    COREFERENCE RESOLUTION                           │
│                                                                     │
│  ┌───────────────────────────────────────────────────────────────┐ │
│  │                  Mention Detection                             │ │
│  │  "John"  "the conference"  "He"  "an interesting talk"       │ │
│  │    │           │            │           │                     │ │
│  │    ▼           ▼            ▼           ▼                     │ │
│  │  ProperName  DefiniteDesc  Pronoun  IndefiniteDesc           │ │
│  └───────────────────────────────────────────────────────────────┘ │
│                              │                                      │
│                              ▼                                      │
│  ┌───────────────────────────────────────────────────────────────┐ │
│  │                   Entity Registry                              │ │
│  │  ┌─────────┐  ┌─────────┐  ┌─────────┐  ┌─────────┐         │ │
│  │  │ Entity1 │  │ Entity2 │  │ Entity3 │  │ Entity4 │         │ │
│  │  │ "John"  │  │"conf."  │  │ "talk"  │  │ "AI"    │         │ │
│  │  │ sal=0.9 │  │ sal=0.5 │  │ sal=0.7 │  │ sal=0.3 │         │ │
│  │  └─────────┘  └─────────┘  └─────────┘  └─────────┘         │ │
│  └───────────────────────────────────────────────────────────────┘ │
│                              │                                      │
│                              ▼                                      │
│  ┌───────────────────────────────────────────────────────────────┐ │
│  │                 Resolution Algorithm                           │ │
│  │  Pronoun "He" → Entity1 "John" (highest salience, gender ok)  │ │
│  └───────────────────────────────────────────────────────────────┘ │
└─────────────────────────────────────────────────────────────────────┘
```

---

## Entity Registry

The entity registry maintains all entities mentioned in the dialogue:

```rust
/// Entity registry for tracking entities across turns
pub struct EntityRegistry {
    /// All known entities
    entities: HashMap<EntityId, Entity>,

    /// Coreference chains: entity → list of mentions
    coreference_chains: HashMap<EntityId, Vec<MentionRef>>,

    /// Current salience scores
    salience_scores: HashMap<EntityId, f64>,

    /// Entity type hierarchy for compatibility checking
    type_hierarchy: TypeHierarchy,

    /// Gender/number features for agreement
    entity_features: HashMap<EntityId, EntityFeatures>,
}

/// Reference to a mention in context
pub struct MentionRef {
    /// Turn containing the mention
    turn_id: TurnId,

    /// Character span in turn text
    span: Range<usize>,

    /// Position in mention sequence
    mention_index: usize,
}

/// Entity representation
pub struct Entity {
    /// Unique identifier
    id: EntityId,

    /// Canonical name (most informative mention)
    canonical_name: String,

    /// Entity type
    entity_type: EntityType,

    /// All known attributes
    attributes: HashMap<String, AttributeValue>,

    /// Turn where first mentioned
    introduced_at: TurnId,

    /// Most recent mention
    last_mentioned: TurnId,

    /// Is this entity currently in focus?
    in_focus: bool,
}

/// Entity types
#[derive(Clone, Debug, PartialEq)]
pub enum EntityType {
    Person,
    Organization,
    Location,
    Event,
    Object,
    Time,
    Abstract,
    Unknown,
}

/// Grammatical features for agreement
pub struct EntityFeatures {
    /// Grammatical gender
    gender: Gender,

    /// Grammatical number
    number: Number,

    /// Person (for reflexive binding)
    person: Person,

    /// Animacy (for pronoun selection)
    animacy: Animacy,
}

#[derive(Clone, Debug, PartialEq)]
pub enum Gender {
    Masculine,
    Feminine,
    Neuter,
    Unknown,
}

#[derive(Clone, Debug, PartialEq)]
pub enum Number {
    Singular,
    Plural,
    Unknown,
}

#[derive(Clone, Debug, PartialEq)]
pub enum Animacy {
    Animate,
    Inanimate,
    Unknown,
}
```

### Entity Registration

```rust
impl EntityRegistry {
    /// Register a new entity from a mention
    pub fn register_entity(
        &mut self,
        mention: &EntityMention,
        turn: &Turn,
    ) -> EntityId {
        let entity_id = self.next_entity_id();

        // Infer entity type from context
        let entity_type = self.infer_entity_type(mention, turn);

        // Infer grammatical features
        let features = self.infer_features(mention);

        let entity = Entity {
            id: entity_id,
            canonical_name: mention.surface.clone(),
            entity_type,
            attributes: HashMap::new(),
            introduced_at: turn.turn_id,
            last_mentioned: turn.turn_id,
            in_focus: true,
        };

        self.entities.insert(entity_id, entity);
        self.entity_features.insert(entity_id, features);
        self.salience_scores.insert(entity_id, 1.0); // New entities are highly salient
        self.coreference_chains.insert(entity_id, vec![MentionRef {
            turn_id: turn.turn_id,
            span: mention.span.clone(),
            mention_index: 0,
        }]);

        entity_id
    }

    /// Add a mention to an existing entity's coreference chain
    pub fn add_mention(
        &mut self,
        entity_id: EntityId,
        mention: &EntityMention,
        turn: &Turn,
    ) {
        if let Some(chain) = self.coreference_chains.get_mut(&entity_id) {
            let mention_index = chain.len();
            chain.push(MentionRef {
                turn_id: turn.turn_id,
                span: mention.span.clone(),
                mention_index,
            });
        }

        // Update entity's last mention
        if let Some(entity) = self.entities.get_mut(&entity_id) {
            entity.last_mentioned = turn.turn_id;
            entity.in_focus = true;

            // Update canonical name if this mention is more informative
            if self.more_informative(&mention.surface, &entity.canonical_name) {
                entity.canonical_name = mention.surface.clone();
            }
        }

        // Boost salience
        self.boost_salience(entity_id);
    }

    /// Check if name1 is more informative than name2
    fn more_informative(&self, name1: &str, name2: &str) -> bool {
        // Proper names > definite descriptions > pronouns
        let score1 = self.informativeness_score(name1);
        let score2 = self.informativeness_score(name2);
        score1 > score2
    }

    fn informativeness_score(&self, name: &str) -> i32 {
        if self.is_proper_name(name) {
            3
        } else if self.is_definite_description(name) {
            2
        } else if self.is_pronoun(name) {
            1
        } else {
            0
        }
    }
}
```

---

## Mention Detection

### Mention Types

```rust
/// Types of referring expressions
#[derive(Clone, Debug, PartialEq)]
pub enum MentionType {
    /// Proper name: "John", "Paris", "Microsoft"
    ProperName,

    /// Personal pronoun: "he", "she", "it", "they"
    Pronoun(PronounType),

    /// Definite description: "the cat", "the tall building"
    DefiniteDescription,

    /// Indefinite description: "a cat", "some books"
    IndefiniteDescription,

    /// Demonstrative: "this", "that", "those people"
    Demonstrative(Proximity),

    /// Reflexive: "himself", "themselves"
    Reflexive,

    /// Relative: "who", "which", "that" (in relative clauses)
    Relative,

    /// Zero anaphora: implicit subject/object
    ZeroAnaphora,

    /// Possessive: "his car", "their house"
    Possessive,

    /// Bare nominal: "cats" (generic reference)
    BareNominal,
}

#[derive(Clone, Debug, PartialEq)]
pub enum PronounType {
    Personal,      // he, she, it, they
    Possessive,    // his, her, its, their
    Reflexive,     // himself, herself, itself
    Demonstrative, // this, that
    Relative,      // who, which, that
    Interrogative, // who, what
}

#[derive(Clone, Debug, PartialEq)]
pub enum Proximity {
    Proximal,  // this, these
    Distal,    // that, those
}
```

### Mention Detector

```rust
/// Mention detector using pattern matching and NER
pub struct MentionDetector {
    /// Named entity recognizer
    ner: NamedEntityRecognizer,

    /// Pronoun patterns
    pronoun_patterns: HashMap<String, PronounInfo>,

    /// Determiner patterns for descriptions
    determiner_patterns: Vec<DeterminerPattern>,
}

/// Information about a pronoun
pub struct PronounInfo {
    pub pronoun_type: PronounType,
    pub gender: Gender,
    pub number: Number,
    pub person: Person,
}

impl MentionDetector {
    /// Detect all mentions in a turn
    pub fn detect_mentions(&self, turn: &Turn) -> Vec<EntityMention> {
        let mut mentions = Vec::new();
        let text = &turn.raw_text;

        // 1. Detect named entities
        for ne in self.ner.recognize(text) {
            mentions.push(EntityMention {
                surface: ne.text.to_string(),
                span: ne.span.clone(),
                entity_id: None, // To be resolved
                mention_type: MentionType::ProperName,
                salience: 0.0, // To be computed
            });
        }

        // 2. Detect pronouns
        for (pronoun, span) in self.find_pronouns(text) {
            if let Some(info) = self.pronoun_patterns.get(&pronoun.to_lowercase()) {
                mentions.push(EntityMention {
                    surface: pronoun.to_string(),
                    span,
                    entity_id: None,
                    mention_type: MentionType::Pronoun(info.pronoun_type.clone()),
                    salience: 0.0,
                });
            }
        }

        // 3. Detect definite descriptions
        for (desc, span) in self.find_definite_descriptions(text) {
            mentions.push(EntityMention {
                surface: desc,
                span,
                entity_id: None,
                mention_type: MentionType::DefiniteDescription,
                salience: 0.0,
            });
        }

        // 4. Detect indefinite descriptions
        for (desc, span) in self.find_indefinite_descriptions(text) {
            mentions.push(EntityMention {
                surface: desc,
                span,
                entity_id: None,
                mention_type: MentionType::IndefiniteDescription,
                salience: 0.0,
            });
        }

        // 5. Detect demonstratives
        for (dem, span, proximity) in self.find_demonstratives(text) {
            mentions.push(EntityMention {
                surface: dem,
                span,
                entity_id: None,
                mention_type: MentionType::Demonstrative(proximity),
                salience: 0.0,
            });
        }

        // Sort by position and deduplicate overlaps
        mentions.sort_by_key(|m| m.span.start);
        self.remove_overlaps(&mut mentions);

        mentions
    }

    /// Find pronouns using pattern matching
    fn find_pronouns(&self, text: &str) -> Vec<(String, Range<usize>)> {
        let mut results = Vec::new();

        // Common pronoun patterns
        let pronoun_regex = regex::Regex::new(
            r"\b(I|me|my|mine|myself|you|your|yours|yourself|he|him|his|himself|she|her|hers|herself|it|its|itself|we|us|our|ours|ourselves|they|them|their|theirs|themselves|this|that|these|those)\b"
        ).unwrap();

        for cap in pronoun_regex.captures_iter(text) {
            if let Some(m) = cap.get(0) {
                results.push((m.as_str().to_string(), m.start()..m.end()));
            }
        }

        results
    }

    /// Find definite descriptions (the + NP)
    fn find_definite_descriptions(&self, text: &str) -> Vec<(String, Range<usize>)> {
        let mut results = Vec::new();

        // Pattern: the + adjectives* + noun
        let def_desc_regex = regex::Regex::new(
            r"\b(the\s+(?:\w+\s+)*?\w+)"
        ).unwrap();

        for cap in def_desc_regex.captures_iter(text) {
            if let Some(m) = cap.get(1) {
                // Filter out function words following "the"
                let desc = m.as_str();
                if self.is_valid_description(desc) {
                    results.push((desc.to_string(), m.start()..m.end()));
                }
            }
        }

        results
    }
}
```

---

## Salience Modeling

Salience determines which entities are most likely to be referred to next.
We implement a modified Centering Theory approach:

### Centering Theory Concepts

```rust
/// Centering-based salience model
pub struct CenteringModel {
    /// Forward-looking centers (ranked entities from current utterance)
    cf_list: Vec<EntityId>,

    /// Backward-looking center (most salient entity from previous utterance)
    cb: Option<EntityId>,

    /// Preferred center (highest-ranked entity in Cf)
    cp: Option<EntityId>,

    /// Transition type from previous utterance
    transition: Option<CenteringTransition>,
}

/// Centering transitions (ordered by preference)
#[derive(Clone, Debug, PartialEq, Ord, PartialOrd, Eq)]
pub enum CenteringTransition {
    /// Cb = Cp, Cb(n) = Cb(n-1) → Continue
    Continue,

    /// Cb = Cp, Cb(n) ≠ Cb(n-1) → Smooth Shift
    SmoothShift,

    /// Cb ≠ Cp, Cb(n) = Cb(n-1) → Retain
    Retain,

    /// Cb ≠ Cp, Cb(n) ≠ Cb(n-1) → Rough Shift
    RoughShift,
}

impl CenteringModel {
    /// Update centering state after new turn
    pub fn update(&mut self, turn: &Turn, entities: &[EntityId], registry: &EntityRegistry) {
        let prev_cb = self.cb;

        // Compute new Cf list (ordered by grammatical role salience)
        self.cf_list = self.rank_by_salience(entities, turn, registry);

        // Cp is the highest-ranked element of Cf
        self.cp = self.cf_list.first().cloned();

        // Cb is the highest-ranked element of Cf(n) that is also in Cf(n-1)
        self.cb = self.compute_cb(&self.cf_list, registry);

        // Compute transition type
        self.transition = self.compute_transition(prev_cb);
    }

    /// Rank entities by salience factors
    fn rank_by_salience(
        &self,
        entities: &[EntityId],
        turn: &Turn,
        registry: &EntityRegistry,
    ) -> Vec<EntityId> {
        let mut scored: Vec<(EntityId, f64)> = entities.iter()
            .map(|&e| (e, self.compute_entity_salience(e, turn, registry)))
            .collect();

        scored.sort_by(|a, b| b.1.partial_cmp(&a.1).unwrap());
        scored.into_iter().map(|(e, _)| e).collect()
    }

    /// Compute salience score for an entity
    fn compute_entity_salience(
        &self,
        entity_id: EntityId,
        turn: &Turn,
        registry: &EntityRegistry,
    ) -> f64 {
        let mut score = 0.0;

        if let Some(entity) = registry.entities.get(&entity_id) {
            // Grammatical role weights (Centering Theory)
            let role_weight = self.grammatical_role_weight(entity_id, turn);
            score += role_weight * 3.0;

            // Recency: more recent = more salient
            let recency = self.recency_score(entity, turn);
            score += recency * 2.0;

            // First mention bias (entities introduced early are often important)
            let first_mention_bias = self.first_mention_score(entity, turn);
            score += first_mention_bias * 0.5;

            // Frequency: mentioned more often = more salient
            if let Some(chain) = registry.coreference_chains.get(&entity_id) {
                score += (chain.len() as f64).ln() * 0.5;
            }

            // Animacy: animate entities more salient for subjects
            if let Some(features) = registry.entity_features.get(&entity_id) {
                if features.animacy == Animacy::Animate {
                    score += 0.3;
                }
            }
        }

        score
    }

    /// Get grammatical role weight
    fn grammatical_role_weight(&self, entity_id: EntityId, turn: &Turn) -> f64 {
        // Subject > Direct Object > Indirect Object > Oblique
        // This requires syntactic parsing; simplified version:
        if self.is_subject(entity_id, turn) {
            1.0
        } else if self.is_direct_object(entity_id, turn) {
            0.7
        } else if self.is_indirect_object(entity_id, turn) {
            0.5
        } else {
            0.3
        }
    }

    /// Compute recency score (exponential decay)
    fn recency_score(&self, entity: &Entity, current_turn: &Turn) -> f64 {
        let turns_since = current_turn.turn_id.0 - entity.last_mentioned.0;
        (-0.5 * turns_since as f64).exp()
    }
}
```

### Salience Decay

```rust
impl EntityRegistry {
    /// Decay salience scores after each turn
    pub fn decay_salience(&mut self, decay_rate: f64) {
        for (_, score) in self.salience_scores.iter_mut() {
            *score *= decay_rate;
        }

        // Remove entities with very low salience from focus
        for (entity_id, entity) in self.entities.iter_mut() {
            if let Some(&score) = self.salience_scores.get(entity_id) {
                if score < 0.1 {
                    entity.in_focus = false;
                }
            }
        }
    }

    /// Boost salience when entity is mentioned
    pub fn boost_salience(&mut self, entity_id: EntityId) {
        if let Some(score) = self.salience_scores.get_mut(&entity_id) {
            // Boost but cap at 1.0
            *score = (*score + 0.5).min(1.0);
        }

        // Bring entity back into focus
        if let Some(entity) = self.entities.get_mut(&entity_id) {
            entity.in_focus = true;
        }
    }

    /// Get most salient entities
    pub fn most_salient(&self, n: usize) -> Vec<EntityId> {
        let mut scored: Vec<_> = self.salience_scores.iter()
            .filter(|(id, _)| self.entities.get(id).map(|e| e.in_focus).unwrap_or(false))
            .collect();

        scored.sort_by(|a, b| b.1.partial_cmp(a.1).unwrap());
        scored.into_iter().take(n).map(|(id, _)| *id).collect()
    }
}
```

---

## Resolution Algorithms

### Pronoun Resolution

```rust
/// Pronoun resolution using salience and constraints
pub struct PronounResolver {
    /// Entity registry
    registry: EntityRegistry,

    /// Centering model
    centering: CenteringModel,

    /// Feature compatibility checker
    feature_checker: FeatureChecker,
}

impl PronounResolver {
    /// Resolve a pronoun mention to an entity
    pub fn resolve_pronoun(
        &self,
        pronoun: &EntityMention,
        turn: &Turn,
        context: &DialogueState,
    ) -> Option<EntityId> {
        // Get pronoun features
        let pronoun_features = self.get_pronoun_features(&pronoun.surface);

        // Get candidate antecedents
        let candidates = self.get_candidates(context);

        // Score each candidate
        let mut scored: Vec<(EntityId, f64)> = candidates.iter()
            .filter_map(|&entity_id| {
                // Check feature compatibility (gender, number agreement)
                if !self.features_compatible(entity_id, &pronoun_features) {
                    return None;
                }

                // Check binding constraints
                if !self.binding_constraints_ok(pronoun, entity_id, turn) {
                    return None;
                }

                // Compute score based on salience and other factors
                let score = self.score_candidate(entity_id, pronoun, context);
                Some((entity_id, score))
            })
            .collect();

        // Sort by score and return best
        scored.sort_by(|a, b| b.1.partial_cmp(&a.1).unwrap());
        scored.first().map(|(id, _)| *id)
    }

    /// Get pronoun grammatical features
    fn get_pronoun_features(&self, pronoun: &str) -> EntityFeatures {
        match pronoun.to_lowercase().as_str() {
            "he" | "him" | "his" | "himself" => EntityFeatures {
                gender: Gender::Masculine,
                number: Number::Singular,
                person: Person::Third,
                animacy: Animacy::Animate,
            },
            "she" | "her" | "hers" | "herself" => EntityFeatures {
                gender: Gender::Feminine,
                number: Number::Singular,
                person: Person::Third,
                animacy: Animacy::Animate,
            },
            "it" | "its" | "itself" => EntityFeatures {
                gender: Gender::Neuter,
                number: Number::Singular,
                person: Person::Third,
                animacy: Animacy::Inanimate,
            },
            "they" | "them" | "their" | "theirs" | "themselves" => EntityFeatures {
                gender: Gender::Unknown, // Plural or singular they
                number: Number::Plural,  // Usually
                person: Person::Third,
                animacy: Animacy::Unknown,
            },
            "I" | "me" | "my" | "mine" | "myself" => EntityFeatures {
                gender: Gender::Unknown,
                number: Number::Singular,
                person: Person::First,
                animacy: Animacy::Animate,
            },
            "we" | "us" | "our" | "ours" | "ourselves" => EntityFeatures {
                gender: Gender::Unknown,
                number: Number::Plural,
                person: Person::First,
                animacy: Animacy::Animate,
            },
            "you" | "your" | "yours" | "yourself" | "yourselves" => EntityFeatures {
                gender: Gender::Unknown,
                number: Number::Unknown, // Can be singular or plural
                person: Person::Second,
                animacy: Animacy::Animate,
            },
            _ => EntityFeatures {
                gender: Gender::Unknown,
                number: Number::Unknown,
                person: Person::Third,
                animacy: Animacy::Unknown,
            },
        }
    }

    /// Check if entity features are compatible with pronoun
    fn features_compatible(&self, entity_id: EntityId, pronoun_features: &EntityFeatures) -> bool {
        if let Some(entity_features) = self.registry.entity_features.get(&entity_id) {
            // Gender must match (or one is unknown)
            let gender_ok = entity_features.gender == pronoun_features.gender
                || entity_features.gender == Gender::Unknown
                || pronoun_features.gender == Gender::Unknown;

            // Number must match (or one is unknown)
            let number_ok = entity_features.number == pronoun_features.number
                || entity_features.number == Number::Unknown
                || pronoun_features.number == Number::Unknown;

            // Animacy should match for it/they distinction
            let animacy_ok = entity_features.animacy == pronoun_features.animacy
                || entity_features.animacy == Animacy::Unknown
                || pronoun_features.animacy == Animacy::Unknown;

            gender_ok && number_ok && animacy_ok
        } else {
            true // No features known, assume compatible
        }
    }

    /// Check binding constraints (Binding Theory)
    fn binding_constraints_ok(
        &self,
        pronoun: &EntityMention,
        entity_id: EntityId,
        turn: &Turn,
    ) -> bool {
        // Principle A: Reflexives must be bound in local domain
        if matches!(pronoun.mention_type, MentionType::Reflexive) {
            return self.is_in_local_domain(pronoun, entity_id, turn);
        }

        // Principle B: Pronouns must be free in local domain
        if matches!(pronoun.mention_type, MentionType::Pronoun(_)) {
            return !self.is_in_local_domain(pronoun, entity_id, turn);
        }

        true
    }

    /// Score a candidate antecedent
    fn score_candidate(
        &self,
        entity_id: EntityId,
        pronoun: &EntityMention,
        context: &DialogueState,
    ) -> f64 {
        let mut score = 0.0;

        // Salience (from centering model)
        if let Some(&salience) = self.registry.salience_scores.get(&entity_id) {
            score += salience * 2.0;
        }

        // Prefer backward-looking center
        if self.centering.cb == Some(entity_id) {
            score += 1.0;
        }

        // Prefer entities in current focus space
        if let Some(entity) = self.registry.entities.get(&entity_id) {
            if entity.in_focus {
                score += 0.5;
            }
        }

        // Recency bonus
        if let Some(entity) = self.registry.entities.get(&entity_id) {
            let current_turn_num = context.current_turn().turn_id.0;
            let last_mention_num = entity.last_mentioned.0;
            let recency = (-0.3 * (current_turn_num - last_mention_num) as f64).exp();
            score += recency;
        }

        score
    }
}
```

### Definite Description Resolution

```rust
/// Resolve definite descriptions
pub struct DescriptionResolver {
    registry: EntityRegistry,
    mork_space: MorkSpace,
}

impl DescriptionResolver {
    /// Resolve a definite description to an entity
    pub fn resolve_description(
        &self,
        description: &EntityMention,
        turn: &Turn,
        context: &DialogueState,
    ) -> Option<EntityId> {
        let desc_text = &description.surface;

        // Extract head noun and modifiers
        let (head, modifiers) = self.parse_description(desc_text);

        // Find entities matching the head noun
        let candidates: Vec<EntityId> = self.registry.entities.iter()
            .filter(|(_, entity)| self.head_matches(entity, &head))
            .map(|(id, _)| *id)
            .collect();

        if candidates.is_empty() {
            // No matching entity - might be bridging reference
            return self.try_bridging_resolution(description, context);
        }

        // Score candidates by modifier match and salience
        let mut scored: Vec<(EntityId, f64)> = candidates.into_iter()
            .map(|entity_id| {
                let modifier_score = self.score_modifiers(entity_id, &modifiers);
                let salience = self.registry.salience_scores.get(&entity_id)
                    .copied().unwrap_or(0.0);
                (entity_id, modifier_score + salience)
            })
            .collect();

        scored.sort_by(|a, b| b.1.partial_cmp(&a.1).unwrap());
        scored.first().map(|(id, _)| *id)
    }

    /// Try to resolve via bridging inference
    fn try_bridging_resolution(
        &self,
        description: &EntityMention,
        context: &DialogueState,
    ) -> Option<EntityId> {
        // Bridging: "the door" when a house was mentioned
        // Look for part-whole, set-member, or other relations

        let (head, _) = self.parse_description(&description.surface);

        // Query MORK for bridging patterns
        let pattern = format!("bridging/{}", head);
        let potential_relations = self.mork_space.query_pattern(pattern.as_bytes());

        for (_, relation_data) in potential_relations {
            // relation_data contains: (anchor_type, relation)
            // e.g., ("house", "has-door")

            let anchor_type = self.decode_anchor_type(&relation_data);

            // Find entities of the anchor type in focus
            for (entity_id, entity) in &self.registry.entities {
                if entity.entity_type.matches(&anchor_type) && entity.in_focus {
                    // Create a new entity for the bridged referent
                    return Some(self.create_bridged_entity(
                        description,
                        *entity_id,
                        context
                    ));
                }
            }
        }

        None
    }
}
```

---

## Cross-Turn Coreference

### Turn Boundary Handling

```rust
/// Cross-turn coreference resolver
pub struct CrossTurnResolver {
    pronoun_resolver: PronounResolver,
    description_resolver: DescriptionResolver,
    registry: EntityRegistry,
}

impl CrossTurnResolver {
    /// Resolve all mentions in a new turn
    pub fn resolve_turn(
        &mut self,
        turn: &Turn,
        context: &mut DialogueState,
    ) -> Vec<ResolvedMention> {
        let mut resolved = Vec::new();

        // Detect mentions in this turn
        let mentions = self.detect_mentions(turn);

        // Process mentions in order
        for mention in mentions {
            let resolution = match &mention.mention_type {
                MentionType::Pronoun(_) => {
                    self.pronoun_resolver.resolve_pronoun(&mention, turn, context)
                }
                MentionType::DefiniteDescription => {
                    self.description_resolver.resolve_description(&mention, turn, context)
                }
                MentionType::Demonstrative(_) => {
                    self.resolve_demonstrative(&mention, turn, context)
                }
                MentionType::ProperName => {
                    self.resolve_or_register_name(&mention, turn, context)
                }
                MentionType::IndefiniteDescription => {
                    // Indefinites typically introduce new entities
                    Some(self.registry.register_entity(&mention, turn))
                }
                _ => None,
            };

            if let Some(entity_id) = resolution {
                // Update coreference chain
                self.registry.add_mention(entity_id, &mention, turn);

                resolved.push(ResolvedMention {
                    mention: mention.clone(),
                    entity_id,
                    confidence: self.compute_confidence(&mention, entity_id),
                });
            } else {
                // Could not resolve - might be a new entity or error
                resolved.push(ResolvedMention {
                    mention: mention.clone(),
                    entity_id: self.registry.register_entity(&mention, turn),
                    confidence: 0.5, // Lower confidence for unresolved
                });
            }
        }

        // Decay salience for unmentioned entities
        self.registry.decay_salience(0.8);

        // Update centering model
        let mentioned_entities: Vec<EntityId> = resolved.iter()
            .map(|r| r.entity_id)
            .collect();
        context.update_centering(&mentioned_entities);

        resolved
    }

    /// Resolve proper name (may match existing entity)
    fn resolve_or_register_name(
        &mut self,
        mention: &EntityMention,
        turn: &Turn,
        context: &DialogueState,
    ) -> Option<EntityId> {
        let name = &mention.surface;

        // Check if this name matches an existing entity
        for (entity_id, entity) in &self.registry.entities {
            if self.names_match(&entity.canonical_name, name) {
                return Some(*entity_id);
            }

            // Check aliases
            if let Some(aliases) = entity.attributes.get("aliases") {
                if self.any_alias_matches(aliases, name) {
                    return Some(*entity_id);
                }
            }
        }

        // New entity
        Some(self.registry.register_entity(mention, turn))
    }

    /// Check if two names refer to the same entity
    fn names_match(&self, name1: &str, name2: &str) -> bool {
        // Exact match
        if name1.eq_ignore_ascii_case(name2) {
            return true;
        }

        // Partial match (last name, first name)
        let parts1: Vec<&str> = name1.split_whitespace().collect();
        let parts2: Vec<&str> = name2.split_whitespace().collect();

        // "John Smith" matches "Smith" or "John"
        for p1 in &parts1 {
            for p2 in &parts2 {
                if p1.eq_ignore_ascii_case(p2) && p1.len() > 2 {
                    return true;
                }
            }
        }

        false
    }
}
```

---

## MeTTa Predicate Implementation

### Coreference Predicates

```metta
; === Entity and Mention Types ===

(: Entity Type)
(: EntityMention Type)
(: EntityId Type)

; === Core Resolution Predicates ===

; Resolve a referring expression to an entity
(: resolve-reference (-> String DialogueState (Maybe Entity)))

; Get the coreference chain for an entity
(: coreference-chain (-> Entity DialogueState (List EntityMention)))

; Get current salience of an entity
(: entity-salience (-> Entity DialogueState Float))

; Check if two mentions corefer
(: corefer (-> EntityMention EntityMention Bool))

; === Resolution Implementation ===

; Main resolution entry point
(= (resolve-reference $text $state)
   (let $mention (detect-mention $text)
        (case (mention-type $mention)
          ((Pronoun $ptype) (resolve-pronoun $mention $state))
          ((DefiniteDescription) (resolve-description $mention $state))
          ((ProperName) (resolve-name $mention $state))
          (_ Nothing))))

; Pronoun resolution
(= (resolve-pronoun $mention $state)
   (let $candidates (get-antecedent-candidates $state)
        $compatible (filter (compatible-features $mention) $candidates)
        $ranked (sort-by-salience $compatible $state)
        (head $ranked)))

; Feature compatibility
(= (compatible-features $mention $entity)
   (and (gender-compatible (mention-gender $mention) (entity-gender $entity))
        (number-compatible (mention-number $mention) (entity-number $entity))))

; === Salience Predicates ===

; Compute salience for an entity
(= (entity-salience $entity $state)
   (+ (* 2.0 (grammatical-role-weight $entity $state))
      (* 1.5 (recency-score $entity $state))
      (* 0.5 (frequency-score $entity $state))))

; Recency decay
(= (recency-score $entity $state)
   (exp (* -0.3 (turns-since-mention $entity $state))))

; === Centering Predicates ===

(: forward-looking-centers (-> Turn DialogueState (List Entity)))
(: backward-looking-center (-> DialogueState (Maybe Entity)))
(: centering-transition (-> Turn Turn CenteringTransition))

; Compute Cf list
(= (forward-looking-centers $turn $state)
   (sort-by (lambda $e (entity-salience $e $state))
            (turn-entities $turn)))

; Determine Cb
(= (backward-looking-center $state)
   (let $cf (forward-looking-centers (current-turn $state) $state)
        $prev-cf (forward-looking-centers (previous-turn $state) $state)
        (find-highest-in-both $cf $prev-cf)))

; === Feature Agreement ===

(: Gender Type)
(: Masculine Gender)
(: Feminine Gender)
(: Neuter Gender)

(: Number Type)
(: Singular Number)
(: Plural Number)

(= (gender-compatible Masculine Masculine) True)
(= (gender-compatible Feminine Feminine) True)
(= (gender-compatible Neuter Neuter) True)
(= (gender-compatible $g Unknown) True)
(= (gender-compatible Unknown $g) True)
(= (gender-compatible _ _) False)

(= (number-compatible Singular Singular) True)
(= (number-compatible Plural Plural) True)
(= (number-compatible $n Unknown) True)
(= (number-compatible Unknown $n) True)
(= (number-compatible _ _) False)
```

---

## PathMap Storage

### Coreference Storage Schema

```
/dialogue/{dialogue_id}/
    /entity/{entity_id}/
        name            → canonical name
        type            → entity type (Person, Location, etc.)
        introduced_at   → turn_id where first mentioned
        last_mentioned  → most recent turn_id
        in_focus        → true/false

        /attributes/
            {key}       → attribute value

        /features/
            gender      → Masculine|Feminine|Neuter|Unknown
            number      → Singular|Plural|Unknown
            animacy     → Animate|Inanimate|Unknown

    /coref/{entity_id}/
        {mention_idx}/
            turn_id     → turn containing this mention
            span_start  → character offset start
            span_end    → character offset end
            surface     → surface text
            type        → mention type

    /salience/
        {entity_id}     → current salience score (float)

    /centering/
        cf_list         → [entity_id, ...] (forward-looking centers)
        cb              → entity_id (backward-looking center)
        cp              → entity_id (preferred center)
        transition      → Continue|SmoothShift|Retain|RoughShift
```

### Storage Operations

```rust
impl EntityRegistry {
    /// Persist entity to PathMap
    pub fn store_entity(&self, entity: &Entity, pathmap: &mut PathMap) -> Result<(), Error> {
        let base = format!("/dialogue/{}/entity/{}/", self.dialogue_id, entity.id);

        pathmap.insert(format!("{}name", base).as_bytes(), entity.canonical_name.as_bytes())?;
        pathmap.insert(format!("{}type", base).as_bytes(), entity.entity_type.encode().as_bytes())?;
        pathmap.insert(format!("{}introduced_at", base).as_bytes(), &entity.introduced_at.0.to_le_bytes())?;
        pathmap.insert(format!("{}last_mentioned", base).as_bytes(), &entity.last_mentioned.0.to_le_bytes())?;
        pathmap.insert(format!("{}in_focus", base).as_bytes(), &[entity.in_focus as u8])?;

        // Store attributes
        for (key, value) in &entity.attributes {
            pathmap.insert(
                format!("{}attributes/{}", base, key).as_bytes(),
                &value.encode()
            )?;
        }

        // Store features
        if let Some(features) = self.entity_features.get(&entity.id) {
            pathmap.insert(format!("{}features/gender", base).as_bytes(), features.gender.encode().as_bytes())?;
            pathmap.insert(format!("{}features/number", base).as_bytes(), features.number.encode().as_bytes())?;
            pathmap.insert(format!("{}features/animacy", base).as_bytes(), features.animacy.encode().as_bytes())?;
        }

        Ok(())
    }

    /// Store coreference chain
    pub fn store_coref_chain(&self, entity_id: EntityId, pathmap: &mut PathMap) -> Result<(), Error> {
        if let Some(chain) = self.coreference_chains.get(&entity_id) {
            for (idx, mention_ref) in chain.iter().enumerate() {
                let base = format!("/dialogue/{}/coref/{}/{}/", self.dialogue_id, entity_id, idx);

                pathmap.insert(format!("{}turn_id", base).as_bytes(), &mention_ref.turn_id.0.to_le_bytes())?;
                pathmap.insert(format!("{}span_start", base).as_bytes(), &mention_ref.span.start.to_le_bytes())?;
                pathmap.insert(format!("{}span_end", base).as_bytes(), &mention_ref.span.end.to_le_bytes())?;
            }
        }

        Ok(())
    }
}
```

---

## Integration with Correction

### Coreference-Aware Correction

```rust
/// Use coreference to improve corrections
pub struct CoreferenceCorrector {
    resolver: CrossTurnResolver,
    registry: EntityRegistry,
}

impl CoreferenceCorrector {
    /// Enhance corrections with coreference information
    pub fn enhance_corrections(
        &self,
        candidates: Vec<CorrectionCandidate>,
        turn: &Turn,
        context: &DialogueState,
    ) -> Vec<CorrectionCandidate> {
        candidates.into_iter()
            .filter_map(|mut candidate| {
                // Check if correction affects a referring expression
                if let Some(mention) = self.find_affected_mention(&candidate, turn) {
                    // Verify corrected form maintains valid reference
                    if !self.valid_reference_after_correction(&candidate, &mention, context) {
                        return None; // Reject correction
                    }

                    // Add coreference metadata to candidate
                    candidate.metadata.insert(
                        "resolved_entity".to_string(),
                        mention.entity_id.map(|id| id.to_string()).unwrap_or_default()
                    );
                }

                Some(candidate)
            })
            .collect()
    }

    /// Check if correction maintains valid coreference
    fn valid_reference_after_correction(
        &self,
        candidate: &CorrectionCandidate,
        mention: &EntityMention,
        context: &DialogueState,
    ) -> bool {
        // Get the corrected text
        let corrected_mention = candidate.apply_to_mention(mention);

        // Try to resolve the corrected mention
        match self.resolver.resolve_mention(&corrected_mention, context) {
            Some(entity_id) => {
                // Should resolve to same entity as original
                mention.entity_id == Some(entity_id)
            }
            None => {
                // Could not resolve - might be acceptable for new entities
                matches!(mention.mention_type, MentionType::IndefiniteDescription)
            }
        }
    }

    /// Use coreference to suggest corrections
    pub fn suggest_reference_corrections(
        &self,
        turn: &Turn,
        context: &DialogueState,
    ) -> Vec<CorrectionSuggestion> {
        let mut suggestions = Vec::new();

        for mention in self.resolver.detect_mentions(turn) {
            // Check for potentially wrong pronouns
            if let MentionType::Pronoun(_) = &mention.mention_type {
                if let Some(entity_id) = self.resolver.resolve_pronoun(&mention, turn, context) {
                    let entity_features = self.registry.entity_features.get(&entity_id);
                    let pronoun_features = self.get_pronoun_features(&mention.surface);

                    // Check for gender/number mismatch
                    if let Some(ef) = entity_features {
                        if ef.gender != pronoun_features.gender && ef.gender != Gender::Unknown {
                            // Suggest correct pronoun
                            let correct_pronoun = self.suggest_pronoun(ef);
                            suggestions.push(CorrectionSuggestion {
                                span: mention.span.clone(),
                                original: mention.surface.clone(),
                                suggested: correct_pronoun,
                                reason: "Pronoun gender agreement".to_string(),
                                confidence: 0.8,
                            });
                        }
                    }
                }
            }
        }

        suggestions
    }
}
```

---

## Summary

Coreference resolution provides essential capability for dialogue understanding:

1. **Entity Registry** - Tracks all entities with canonical names, types, and features
2. **Mention Detection** - Identifies referring expressions (pronouns, descriptions, names)
3. **Salience Modeling** - Centering-based salience with recency and grammatical role weights
4. **Resolution Algorithms** - Pronoun and description resolution with feature agreement
5. **Cross-Turn Tracking** - Maintains coreference chains across conversation turns
6. **Correction Integration** - Uses coreference to validate and improve corrections

---

## References

- Grosz, B., Joshi, A., & Weinstein, S. (1995). "Centering: A Framework for Modeling the Local Coherence of Discourse"
- Hobbs, J. (1978). "Resolving Pronoun References"
- Clark, K. & Manning, C. (2015). "Entity-Centric Coreference Resolution with Model Stacking"
- Lee, K., He, L., Lewis, M., & Zettlemoyer, L. (2017). "End-to-end Neural Coreference Resolution"
- Jurafsky, D. & Martin, J. (2023). "Speech and Language Processing", Ch. 21

See [03-topic-management.md](./03-topic-management.md) for discourse topic tracking.
