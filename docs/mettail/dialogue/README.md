# Dialogue Context Management

This section documents the dialogue context layer that extends the three-tier WFST
correction architecture to support multi-turn conversations, both for human-to-human
communication and LLM-based conversational agents.

**Sources**:
- Plan: Part V - Dialogue Context and LLM Agent Correction Extension
- PathMap: `/home/dylon/Workspace/f1r3fly.io/PathMap/`
- MORK: `/home/dylon/Workspace/f1r3fly.io/MORK/`
- MeTTaIL: `/home/dylon/Workspace/f1r3fly.io/mettail-rust/`

---

## Table of Contents

1. [Overview](#overview)
2. [Architecture Position](#architecture-position)
3. [Key Capabilities](#key-capabilities)
4. [Core Data Structures](#core-data-structures)
5. [PathMap Storage Schema](#pathmap-storage-schema)
6. [Integration Points](#integration-points)
7. [Document Guide](#document-guide)

---

## Overview

The Dialogue Context Layer sits above the three-tier WFST correction system and provides
contextual awareness for multi-turn conversations. While the base correction system
handles single utterances in isolation, real conversations require:

- **Turn-by-turn history tracking** - understanding what was said before
- **Entity persistence** - tracking who and what across turns
- **Coreference resolution** - linking pronouns to their referents
- **Topic continuity** - following conversational threads
- **Speech act understanding** - recognizing intent beyond literal meaning
- **Pragmatic inference** - deriving implied meaning from context

```
┌─────────────────────────────────────────────────────────────────────┐
│                     DIALOGUE CONTEXT LAYER                          │
│                                                                     │
│  ┌───────────────┐  ┌───────────────┐  ┌───────────────┐          │
│  │ Turn Tracker  │  │    Entity     │  │  Topic Graph  │          │
│  │   (history)   │  │   Registry    │  │  (discourse)  │          │
│  └───────┬───────┘  └───────┬───────┘  └───────┬───────┘          │
│          │                  │                  │                   │
│          └──────────────────┼──────────────────┘                   │
│                             ▼                                      │
│                  ┌─────────────────────┐                          │
│                  │   DialogueState     │                          │
│                  │  (PathMap-backed)   │                          │
│                  └──────────┬──────────┘                          │
│                             │                                      │
└─────────────────────────────┼──────────────────────────────────────┘
                              │
                              ▼
┌─────────────────────────────────────────────────────────────────────┐
│                  THREE-TIER WFST CORRECTION                         │
│  ┌────────────┐    ┌────────────┐    ┌────────────┐               │
│  │  Tier 1:   │ →  │  Tier 2:   │ →  │  Tier 3:   │               │
│  │  Lexical   │    │  Syntactic │    │  Semantic  │               │
│  └────────────┘    └────────────┘    └────────────┘               │
└─────────────────────────────────────────────────────────────────────┘
```

---

## Architecture Position

The Dialogue Context Layer operates **before** the three-tier WFST system:

1. **Input arrives** - a new user utterance in an ongoing conversation
2. **Dialogue Layer processes** - resolves references, tracks entities, updates topics
3. **Enhanced input** - utterance enriched with contextual metadata
4. **WFST correction** - three-tier correction with context awareness
5. **Output integration** - corrections validated against dialogue coherence

### Why Context Matters for Correction

Consider this conversation:

```
Turn 1: "I saw John at the store yesterday."
Turn 2: "He bought some apples."
Turn 3: "Their very expensive this time of year."
```

Without dialogue context:
- Turn 3 correction: "Their" → "They're" (grammatical fix only)

With dialogue context:
- Turn 3 correction: "Their" → "They're" (grammar)
- Additional: Semantic check that "they" refers to "apples" (valid)
- Coherence: Statement about expense is relevant to "bought" action

The dialogue layer enables **context-sensitive correction** that goes beyond
isolated utterance analysis.

---

## Key Capabilities

### 1. Turn-by-Turn History

Maintains ordered sequence of conversation turns with:
- Speaker identification
- Timestamps
- Raw and corrected text
- Parsed semantic representation
- Speech act classification

### 2. Entity Registry

Tracks entities mentioned in the conversation:
- Named entities (people, places, organizations)
- Definite descriptions ("the cat", "my car")
- Pronouns and their antecedents
- Entity salience (recency, syntactic prominence)

### 3. Coreference Resolution

Links referring expressions to their referents:
- Pronoun resolution ("he" → "John")
- Definite description matching ("the store" → previously mentioned store)
- Zero anaphora in pro-drop contexts
- Bridging references ("the door" → door of mentioned house)

### 4. Topic Graph

Models discourse structure:
- Current and previous topics
- Topic shifts and continuations
- Hierarchical topic relations
- Keyword-to-topic mapping

### 5. Speech Act Classification

Identifies communicative intent:
- **Assertives**: Statements of fact or belief
- **Questions**: Information-seeking utterances
- **Directives**: Requests, commands, suggestions
- **Commissives**: Promises, offers, commitments
- **Expressives**: Emotions, attitudes, social acts
- **Backchannels**: Acknowledgments, continuers

### 6. Pragmatic Reasoning

Derives implied meaning:
- Scalar implicatures ("some" → "not all")
- Conversational implicatures (Gricean maxims)
- Indirect speech acts ("Can you pass the salt?" → request)
- Presupposition accommodation

---

## Core Data Structures

### DialogueState

The central structure backing all dialogue context:

```rust
/// Dialogue state backed by PathMap for persistence
pub struct DialogueState {
    /// PathMap storage backend
    pathmap: PathMap,

    /// Ordered conversation history (sliding window)
    turns: VecDeque<Turn>,

    /// Maximum history size
    max_history: usize,

    /// Entity tracking across turns
    entity_registry: EntityRegistry,

    /// Discourse topic structure
    topic_graph: TopicGraph,

    /// Per-speaker models (style, vocabulary, etc.)
    speaker_models: HashMap<ParticipantId, SpeakerModel>,
}
```

### Turn

Represents a single conversational turn:

```rust
/// Single dialogue turn with full annotation
pub struct Turn {
    /// Unique turn identifier
    turn_id: TurnId,

    /// Who said this
    speaker: ParticipantId,

    /// When it was said
    timestamp: Timestamp,

    /// Original input text
    raw_text: String,

    /// Corrected text (if any)
    corrected_text: Option<String>,

    /// Parsed MeTTa representation
    parsed: Vec<MettaValue>,

    /// Classified speech act
    speech_act: SpeechAct,

    /// Entity mentions in this turn
    entities: Vec<EntityMention>,

    /// Topics referenced
    topics: Vec<TopicRef>,
}
```

### Speech Acts

Classification of communicative intent:

```rust
/// Speech act classification following Searle's taxonomy
pub enum SpeechAct {
    /// Statement of fact or belief
    Assert {
        content: MettaValue,
        confidence: f64,
    },

    /// Information-seeking utterance
    Question {
        q_type: QuestionType,  // Yes/No, Wh-, Alternative, Tag
        focus: MettaValue,
    },

    /// Request, command, or suggestion
    Directive {
        action: MettaValue,
        addressee: Option<ParticipantId>,
    },

    /// Promise, offer, or commitment
    Commissive {
        commitment: MettaValue,
    },

    /// Expression of attitude or emotion
    Expressive {
        attitude: String,
        target: Option<MettaValue>,
    },

    /// Acknowledgment or continuer
    Backchannel {
        signal_type: BackchannelType,
    },
}

/// Question subtypes
pub enum QuestionType {
    YesNo,       // "Did you go?"
    Wh,          // "Where did you go?"
    Alternative, // "Did you walk or drive?"
    Tag,         // "You went, didn't you?"
    Echo,        // "You did WHAT?"
}
```

### Entity Mention

Tracking entities within turns:

```rust
/// Entity mention in dialogue
pub struct EntityMention {
    /// Surface form ("the cat", "it", "John")
    surface: String,

    /// Character span in turn text
    span: Range<usize>,

    /// Resolved entity (if any)
    entity_id: Option<EntityId>,

    /// Type of mention
    mention_type: MentionType,

    /// Current salience score
    salience: f64,
}

/// Types of referring expressions
pub enum MentionType {
    ProperName,      // "John", "Paris"
    Pronoun,         // "he", "it", "they"
    DefiniteDesc,    // "the cat", "the tall building"
    IndefiniteDesc,  // "a cat", "some books"
    Demonstrative,   // "this", "that one"
    ZeroAnaphora,    // Implicit subject (pro-drop)
}
```

---

## PathMap Storage Schema

All dialogue state persists to PathMap for durability and efficient querying:

```
/dialogue/{dialogue_id}/
    /meta/
        created_at      → timestamp
        participants    → [participant_id, ...]
        status          → active|archived

    /turn/{turn_id}/
        raw             → raw text bytes
        corrected       → corrected text bytes
        speaker         → participant_id
        timestamp       → unix timestamp
        speech_act      → encoded speech act
        /entities/      → entity mention data
        /topics/        → topic references

    /entity/{entity_id}/
        name            → canonical name
        type            → entity type
        /attributes/    → key-value attributes
        introduced_at   → turn_id

    /coref/{entity_id}/
        {mention_idx}   → (turn_id, span_start, span_end)

    /topic/{topic_id}/
        label           → topic label
        parent          → parent topic_id (optional)
        /keywords/      → {keyword} → count
        /active_turns/  → [turn_id, ...]

    /commitment/{commitment_id}/
        speaker         → participant_id
        content         → MeTTa value
        status          → active|fulfilled|violated|retracted
```

### Query Examples

```rust
// Get all turns by a specific speaker
let pattern = format!("/dialogue/{}/turn/*/speaker", dialogue_id);
let speaker_turns = pathmap.query_pattern(pattern.as_bytes())?
    .filter(|(_, val)| val == speaker_id.as_bytes());

// Get all mentions of an entity
let pattern = format!("/dialogue/{}/coref/{}/", dialogue_id, entity_id);
let mentions = pathmap.query_prefix(pattern.as_bytes())?;

// Get active topics
let pattern = format!("/dialogue/{}/topic/*/active_turns/", dialogue_id);
let active_topics = pathmap.query_pattern(pattern.as_bytes())?;
```

---

## Integration Points

### With Three-Tier WFST

The dialogue layer enhances each tier:

| Tier | Enhancement |
|------|-------------|
| **Lexical** | User-specific vocabulary, speaker style adaptation |
| **Syntactic** | Dialogue-aware grammar (fragments, repairs, overlap) |
| **Semantic** | Coreference constraints, topic coherence, speech act validation |

### With MORK Pattern Matching

MORK stores and queries:
- Pragmatic inference rules
- Speech act classification patterns
- Entity type hierarchies
- Topic similarity measures

### With MeTTaIL Predicates

New predicates for dialogue reasoning:

```metta
; Turn and dialogue structure
(: Turn Type)
(: turn-speaker (-> Turn ParticipantId))
(: turn-text (-> Turn String))
(: turn-speech-act (-> Turn SpeechAct))

; Coreference resolution
(: resolve-reference (-> String DialogueState (Maybe Entity)))
(: coreference-chain (-> Entity DialogueState (List Mention)))
(: entity-salience (-> Entity DialogueState Float))

; Topic tracking
(: topic-similarity (-> Topic Topic Float))
(: topic-shift (-> Turn Turn Bool))

; Speech acts
(: classify-speech-act (-> String DialogueState SpeechAct))
(: is-indirect-speech-act (-> SpeechAct Bool))
```

---

## Document Guide

This section contains four detailed documents:

| Document | Description |
|----------|-------------|
| [01-discourse-semantics.md](./01-discourse-semantics.md) | Discourse structure, coherence relations, and multi-turn reasoning |
| [02-coreference-resolution.md](./02-coreference-resolution.md) | Entity tracking, pronoun resolution, salience modeling |
| [03-topic-management.md](./03-topic-management.md) | Topic graphs, continuity detection, discourse segmentation |
| [04-pragmatic-reasoning.md](./04-pragmatic-reasoning.md) | Speech acts, implicatures, Gricean maxims, indirect meaning |

### Reading Order

**For implementers**:
1. This README (overview)
2. [02-coreference-resolution.md](./02-coreference-resolution.md) (most concrete)
3. [03-topic-management.md](./03-topic-management.md) (builds on entities)
4. [01-discourse-semantics.md](./01-discourse-semantics.md) (ties it together)
5. [04-pragmatic-reasoning.md](./04-pragmatic-reasoning.md) (advanced reasoning)

**For theorists**:
1. [01-discourse-semantics.md](./01-discourse-semantics.md) (theoretical foundation)
2. [04-pragmatic-reasoning.md](./04-pragmatic-reasoning.md) (formal pragmatics)
3. [02-coreference-resolution.md](./02-coreference-resolution.md) (algorithmic details)
4. [03-topic-management.md](./03-topic-management.md) (discourse structure)

---

## Related Documentation

- [Correction WFST Architecture](../correction-wfst/01-architecture-overview.md) - Base three-tier system
- [LLM Integration](../llm-integration/README.md) - Agent preprocessing/postprocessing
- [Agent Learning](../agent-learning/README.md) - Feedback integration
- [MeTTaIL Implementation](../implementation/02-mettail-rust-prototype.md) - Predicate engine

---

## References

- Grosz, B. & Sidner, C. (1986). "Attention, Intentions, and the Structure of Discourse"
- Hobbs, J. (1979). "Coherence and Coreference"
- Searle, J. (1969). "Speech Acts: An Essay in the Philosophy of Language"
- Grice, H. P. (1975). "Logic and Conversation"
- Mann, W. & Thompson, S. (1988). "Rhetorical Structure Theory"
