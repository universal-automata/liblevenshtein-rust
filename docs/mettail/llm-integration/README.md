# LLM Agent Integration

This section documents the LLM integration layer that enables the correction system to
preprocess user inputs and postprocess LLM outputs for conversational AI agents.

**Sources**:
- Plan: Part V - Dialogue Context and LLM Agent Correction Extension
- PathMap: `/home/dylon/Workspace/f1r3fly.io/PathMap/`
- MORK: `/home/dylon/Workspace/f1r3fly.io/MORK/`
- MeTTaIL: `/home/dylon/Workspace/f1r3fly.io/mettail-rust/`

---

## Table of Contents

1. [Overview](#overview)
2. [Architecture Position](#architecture-position)
3. [Bidirectional Correction Flow](#bidirectional-correction-flow)
4. [Core Components](#core-components)
5. [Data Structures](#data-structures)
6. [PathMap Storage Schema](#pathmap-storage-schema)
7. [Integration with Dialogue Layer](#integration-with-dialogue-layer)
8. [Document Guide](#document-guide)

---

## Overview

The LLM Integration Layer provides bidirectional correction for conversational AI agents:

1. **Prompt Preprocessing** - Corrects user input before sending to the LLM
   - Spelling and grammar correction
   - Entity resolution and disambiguation
   - Context injection from dialogue history
   - RAG (Retrieval-Augmented Generation) integration

2. **Response Postprocessing** - Validates and corrects LLM output
   - Coherence checking against dialogue context
   - Factual consistency validation
   - Hallucination detection and flagging
   - Style normalization

```
┌─────────────────────────────────────────────────────────────────────────┐
│                      LLM INTEGRATION LAYER                               │
│                                                                          │
│  User Input                                                              │
│      │                                                                   │
│      ▼                                                                   │
│  ┌──────────────────────────────────────────────────────────────────┐   │
│  │                    PROMPT PREPROCESSING                           │   │
│  │  ┌─────────────┐  ┌─────────────┐  ┌─────────────┐              │   │
│  │  │   Three-    │  │  Context    │  │    RAG      │              │   │
│  │  │   Tier      │→ │  Injection  │→ │  Retrieval  │              │   │
│  │  │   WFST      │  │             │  │             │              │   │
│  │  └─────────────┘  └─────────────┘  └─────────────┘              │   │
│  │         Corrected input + dialogue context + relevant knowledge  │   │
│  └────────────────────────────────┬─────────────────────────────────┘   │
│                                   │                                      │
│                                   ▼                                      │
│                          ┌──────────────┐                               │
│                          │   LLM API    │                               │
│                          │  (External)  │                               │
│                          └──────┬───────┘                               │
│                                 │                                        │
│                                 ▼                                        │
│  ┌──────────────────────────────────────────────────────────────────┐   │
│  │                   RESPONSE POSTPROCESSING                         │   │
│  │  ┌─────────────┐  ┌─────────────┐  ┌─────────────┐              │   │
│  │  │  Coherence  │  │   Fact      │  │ Hallucin.   │              │   │
│  │  │  Checking   │→ │  Validation │→ │ Detection   │              │   │
│  │  └─────────────┘  └─────────────┘  └─────────────┘              │   │
│  │              Validated response + confidence scores              │   │
│  └────────────────────────────────┬─────────────────────────────────┘   │
│                                   │                                      │
│                                   ▼                                      │
│                           Agent Response                                 │
│                                                                          │
└─────────────────────────────────────────────────────────────────────────┘
```

---

## Architecture Position

The LLM Integration Layer sits between the Dialogue Context Layer and the external LLM API:

```
┌─────────────────────────────────────────────────────────────────────────┐
│                         FULL ARCHITECTURE STACK                          │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                          │
│  ┌────────────────────────────────────────────────────────────────────┐ │
│  │                    DIALOGUE CONTEXT LAYER                          │ │
│  │           (Turn History, Entities, Topics, Pragmatics)             │ │
│  └───────────────────────────────┬────────────────────────────────────┘ │
│                                  │                                       │
│                                  ▼                                       │
│  ┌────────────────────────────────────────────────────────────────────┐ │
│  │                     THREE-TIER WFST                                │ │
│  │              (Lexical → Syntactic → Semantic)                      │ │
│  └───────────────────────────────┬────────────────────────────────────┘ │
│                                  │                                       │
│                                  ▼                                       │
│  ┌────────────────────────────────────────────────────────────────────┐ │
│  │                    LLM INTEGRATION LAYER                           │ │
│  │  ┌──────────────────────┐      ┌──────────────────────┐           │ │
│  │  │ Prompt Preprocessing │      │ Response Postprocess │           │ │
│  │  │ ┌──────────────────┐ │      │ ┌──────────────────┐ │           │ │
│  │  │ │ Input Correction │ │      │ │ Coherence Check  │ │           │ │
│  │  │ │ Context Inject   │ │      │ │ Fact Validation  │ │           │ │
│  │  │ │ RAG Retrieval    │ │      │ │ Hallucin. Detect │ │           │ │
│  │  │ └──────────────────┘ │      │ └──────────────────┘ │           │ │
│  │  └──────────┬───────────┘      └───────────┬──────────┘           │ │
│  │             │                              ▲                       │ │
│  │             └──────────┬───────────────────┘                       │ │
│  └────────────────────────┼───────────────────────────────────────────┘ │
│                           │                                              │
│                           ▼                                              │
│  ┌────────────────────────────────────────────────────────────────────┐ │
│  │                       EXTERNAL LLM API                             │ │
│  │        (OpenAI, Anthropic, Local Models, Custom Endpoints)         │ │
│  └────────────────────────────────────────────────────────────────────┘ │
│                                                                          │
└─────────────────────────────────────────────────────────────────────────┘
```

### Why This Layer Matters

LLMs are powerful but have limitations:
- **Input quality affects output quality** - typos and ambiguity confuse the model
- **No persistent memory** - LLMs don't track entities across conversations
- **Hallucination risk** - LLMs can generate plausible but false information
- **Context window limits** - can't fit entire dialogue history in prompt

The LLM Integration Layer addresses these by:
- Correcting input errors before they reach the LLM
- Injecting relevant context from dialogue history
- Validating responses against known facts
- Detecting and flagging hallucinated content

---

## Bidirectional Correction Flow

### Preprocessing Flow (User → LLM)

```
User Input: "can u help me find johns email from yesterdya"
     │
     ▼
┌────────────────────────────────────────────────────────────────┐
│ STEP 1: Three-Tier WFST Correction                             │
│                                                                 │
│ Tier 1 (Lexical):                                              │
│   "u" → "you"                                                  │
│   "yesterdya" → "yesterday"                                    │
│                                                                 │
│ Tier 2 (Syntactic):                                            │
│   "can you help me" → "Can you help me"                        │
│   (sentence-initial capitalization)                            │
│                                                                 │
│ Tier 3 (Semantic):                                             │
│   "johns" → "John's" (possessive form)                         │
│   entity reference detected: "john"                            │
│                                                                 │
│ Result: "Can you help me find John's email from yesterday?"    │
└────────────────────────────────────────────────────────────────┘
     │
     ▼
┌────────────────────────────────────────────────────────────────┐
│ STEP 2: Entity Resolution (from Dialogue Context)              │
│                                                                 │
│ Query entity registry:                                         │
│   "John" matches EntityId::E42 (John Smith, colleague)         │
│                                                                 │
│ Resolved: John Smith <john.smith@company.com>                  │
└────────────────────────────────────────────────────────────────┘
     │
     ▼
┌────────────────────────────────────────────────────────────────┐
│ STEP 3: Context Injection                                      │
│                                                                 │
│ Dialogue history summary:                                      │
│   - Previous turn mentioned scheduling a meeting               │
│   - John Smith discussed 3 times in last 5 turns              │
│   - Topic: work coordination                                   │
│                                                                 │
│ Injected context:                                              │
│   "[Context: User previously discussed meeting with            │
│    John Smith (john.smith@company.com), colleague]"            │
└────────────────────────────────────────────────────────────────┘
     │
     ▼
┌────────────────────────────────────────────────────────────────┐
│ STEP 4: RAG Retrieval (if applicable)                          │
│                                                                 │
│ Query knowledge base:                                          │
│   - Recent emails from John Smith                              │
│   - Meeting notes from yesterday                               │
│                                                                 │
│ Retrieved: Email subject "Meeting confirmation" from yesterday │
└────────────────────────────────────────────────────────────────┘
     │
     ▼
Final Preprocessed Prompt (sent to LLM)
```

### Postprocessing Flow (LLM → User)

```
LLM Response: "John's email is john.s@company.org. He mentioned
              the meeting in his message yesterday about the
              Q4 budget review with Sarah from marketing."
     │
     ▼
┌────────────────────────────────────────────────────────────────┐
│ STEP 1: Coherence Checking                                     │
│                                                                 │
│ Verify against dialogue context:                               │
│   ✓ Responds to user's question about email                    │
│   ✓ References same John from context                          │
│   ? Introduces new entity "Sarah" - need verification          │
│                                                                 │
│ Coherence score: 0.82                                          │
└────────────────────────────────────────────────────────────────┘
     │
     ▼
┌────────────────────────────────────────────────────────────────┐
│ STEP 2: Fact Validation                                        │
│                                                                 │
│ Check against knowledge base:                                  │
│   ✗ Email "john.s@company.org" doesn't match known             │
│     address "john.smith@company.com"                           │
│   ✓ Meeting topic "Q4 budget review" matches calendar          │
│   ? "Sarah from marketing" - unverified entity                 │
│                                                                 │
│ Factual issues found: 1 (email mismatch)                       │
└────────────────────────────────────────────────────────────────┘
     │
     ▼
┌────────────────────────────────────────────────────────────────┐
│ STEP 3: Hallucination Detection                                │
│                                                                 │
│ Analysis:                                                      │
│   HIGH: Email address fabricated (john.s@company.org)          │
│   LOW:  Meeting topic plausible and verified                   │
│   MEDIUM: "Sarah" - unverifiable, may be hallucinated          │
│                                                                 │
│ Hallucination flags:                                           │
│   - Email: FabricatedFact, confidence 0.95                     │
│   - Sarah: UnverifiedEntity, confidence 0.60                   │
└────────────────────────────────────────────────────────────────┘
     │
     ▼
┌────────────────────────────────────────────────────────────────┐
│ STEP 4: Response Correction/Annotation                         │
│                                                                 │
│ Options:                                                       │
│   A) Correct silently (if high confidence)                     │
│   B) Flag for user review                                      │
│   C) Request LLM regeneration with correction guidance         │
│                                                                 │
│ Selected: B (flag for user review)                             │
│                                                                 │
│ Corrected: "John's email is john.smith@company.com [corrected].│
│            He mentioned the meeting in his message yesterday   │
│            about the Q4 budget review with Sarah from          │
│            marketing [unverified]."                            │
└────────────────────────────────────────────────────────────────┘
     │
     ▼
Final Response to User (with annotations)
```

---

## Core Components

### 1. Prompt Preprocessor

Prepares user input for optimal LLM processing:

| Component | Function |
|-----------|----------|
| **InputCorrector** | Applies three-tier WFST correction to user input |
| **EntityResolver** | Resolves entity references using dialogue context |
| **ContextFormatter** | Formats dialogue history for prompt injection |
| **RAGRetriever** | Retrieves relevant knowledge for augmentation |
| **PromptAssembler** | Combines all components into final prompt |

### 2. Response Postprocessor

Validates and enhances LLM output:

| Component | Function |
|-----------|----------|
| **CoherenceChecker** | Validates response against dialogue context |
| **FactValidator** | Checks claims against knowledge base |
| **HallucinationDetector** | Identifies fabricated content |
| **ResponseCorrector** | Applies corrections or flags issues |
| **ConfidenceScorer** | Computes overall response confidence |

### 3. LLM API Adapter

Abstracts communication with various LLM providers:

| Feature | Description |
|---------|-------------|
| **Provider abstraction** | Unified interface for OpenAI, Anthropic, local models |
| **Token management** | Tracks and optimizes token usage |
| **Retry logic** | Handles rate limits and transient failures |
| **Response streaming** | Supports streaming for real-time display |
| **Cost tracking** | Monitors API costs per conversation |

### 4. Knowledge Base

Supports fact validation and RAG:

| Component | Purpose |
|-----------|---------|
| **EntityStore** | Known entities with attributes |
| **FactStore** | Verified facts and relationships |
| **DocumentStore** | Indexed documents for RAG retrieval |
| **EmbeddingIndex** | Vector similarity for semantic search |

---

## Data Structures

### PreprocessedPrompt

```rust
/// Preprocessed prompt ready for LLM
pub struct PreprocessedPrompt {
    /// Original user input
    pub original_input: String,

    /// Corrected user input (after three-tier WFST)
    pub corrected_input: String,

    /// List of corrections applied
    pub corrections: Vec<CorrectionRecord>,

    /// Entities resolved from input
    pub resolved_entities: Vec<ResolvedEntity>,

    /// Formatted dialogue context
    pub context_injection: ContextInjection,

    /// RAG-retrieved knowledge chunks
    pub rag_chunks: Vec<KnowledgeChunk>,

    /// Final assembled prompt (sent to LLM)
    pub assembled_prompt: String,

    /// Overall preprocessing confidence
    pub confidence: f64,

    /// Token count estimate
    pub estimated_tokens: usize,
}

/// Record of a single correction
pub struct CorrectionRecord {
    /// Position in original input
    pub span: Range<usize>,

    /// Original text
    pub original: String,

    /// Corrected text
    pub corrected: String,

    /// Correction type (Spelling, Grammar, EntityResolution, etc.)
    pub correction_type: CorrectionType,

    /// Confidence score
    pub confidence: f64,
}

/// Resolved entity from user input
pub struct ResolvedEntity {
    /// Surface form in input
    pub surface: String,

    /// Resolved entity ID
    pub entity_id: EntityId,

    /// Canonical name
    pub canonical_name: String,

    /// Entity attributes
    pub attributes: HashMap<String, String>,

    /// Resolution confidence
    pub confidence: f64,
}
```

### PostprocessedResponse

```rust
/// Postprocessed LLM response
pub struct PostprocessedResponse {
    /// Original LLM response
    pub original: String,

    /// Corrected response (if modifications made)
    pub corrected: Option<String>,

    /// Coherence check results
    pub coherence: CoherenceResult,

    /// Factual validation results
    pub factual_validation: FactualValidationResult,

    /// Hallucination detection results
    pub hallucination_flags: Vec<HallucinationFlag>,

    /// New entities mentioned in response
    pub new_entities: Vec<EntityMention>,

    /// Overall confidence score
    pub confidence: f64,

    /// Recommendations for handling
    pub recommendation: ResponseRecommendation,
}

/// Coherence check results
pub struct CoherenceResult {
    /// Overall coherence score (0.0 - 1.0)
    pub score: f64,

    /// Whether response addresses the question/request
    pub addresses_qud: bool,

    /// Topic consistency with dialogue
    pub topic_consistent: bool,

    /// Entity consistency
    pub entity_consistent: bool,

    /// Specific coherence issues found
    pub issues: Vec<CoherenceIssue>,
}

/// Factual validation results
pub struct FactualValidationResult {
    /// Number of claims checked
    pub claims_checked: usize,

    /// Number verified as correct
    pub claims_verified: usize,

    /// Number contradicted by knowledge base
    pub claims_contradicted: usize,

    /// Number that couldn't be verified
    pub claims_unverifiable: usize,

    /// Detailed validation per claim
    pub claim_details: Vec<ClaimValidation>,
}

/// Hallucination detection flag
pub struct HallucinationFlag {
    /// Span in response text
    pub span: Range<usize>,

    /// Flagged content
    pub content: String,

    /// Type of hallucination
    pub hallucination_type: HallucinationType,

    /// Detection confidence
    pub confidence: f64,

    /// Suggested correction (if available)
    pub suggestion: Option<String>,

    /// Evidence for the flag
    pub evidence: Option<String>,
}

/// Types of hallucination
pub enum HallucinationType {
    /// Made-up fact not in knowledge base
    FabricatedFact,

    /// Reference to non-existent entity
    NonexistentEntity,

    /// Incorrect attribute of known entity
    WrongAttribute,

    /// Contradicts known fact
    ContradictsFact,

    /// Contradicts earlier dialogue turn
    ContradictsPrior,

    /// Claim without supporting evidence
    UnsupportedClaim,

    /// Temporal inconsistency
    TemporalError,

    /// Logical inconsistency
    LogicalInconsistency,
}

/// Recommendation for response handling
pub enum ResponseRecommendation {
    /// Response is safe to deliver
    Accept,

    /// Deliver with annotations/warnings
    AcceptWithFlags {
        flags: Vec<Range<usize>>,
        severity: Severity,
    },

    /// Apply corrections before delivery
    CorrectAndDeliver {
        corrections: Vec<ResponseCorrection>,
    },

    /// Request LLM regeneration
    Regenerate {
        guidance: String,
    },

    /// Escalate to human review
    HumanReview {
        reason: String,
    },
}
```

### Context Injection

```rust
/// Formatted context for prompt injection
pub struct ContextInjection {
    /// Dialogue history summary
    pub dialogue_summary: String,

    /// Active entities with descriptions
    pub active_entities: Vec<EntityContext>,

    /// Current topic context
    pub topic_context: String,

    /// User preferences (communication style)
    pub user_preferences: Option<UserPreferences>,

    /// System instructions
    pub system_instructions: Option<String>,

    /// Total tokens used for context
    pub token_count: usize,
}

/// Entity context for injection
pub struct EntityContext {
    /// Entity ID
    pub entity_id: EntityId,

    /// Canonical name
    pub name: String,

    /// Brief description
    pub description: String,

    /// Relevance to current query
    pub relevance: f64,

    /// Key attributes to include
    pub attributes: Vec<(String, String)>,
}

/// Knowledge chunk from RAG retrieval
pub struct KnowledgeChunk {
    /// Chunk ID
    pub chunk_id: ChunkId,

    /// Source document
    pub source: DocumentRef,

    /// Chunk text content
    pub content: String,

    /// Relevance score to query
    pub relevance: f64,

    /// Embedding vector (for further ranking)
    pub embedding: Option<Vec<f32>>,
}
```

---

## PathMap Storage Schema

```
PathMap Key Structure:
=======================

/agent/{agent_id}/
    /config/
        endpoint            → LLM API endpoint URL
        model               → Model identifier
        max_tokens          → Token limit per request
        temperature         → Sampling temperature
        correction_level    → 0.0-1.0 (how aggressive)
        hallucination_threshold → Flag threshold (0.0-1.0)

    /session/{session_id}/
        created_at          → Timestamp
        total_tokens        → Running token count
        total_cost          → Running cost estimate
        turns_count         → Number of turns

        /turn/{turn_id}/
            /preprocessing/
                original    → Original user input
                corrected   → Corrected input
                corrections → JSON array of corrections
                entities    → Resolved entities
                context     → Injected context
                rag_chunks  → Retrieved knowledge
                prompt      → Final assembled prompt
                confidence  → Preprocessing confidence

            /llm/
                request_tokens  → Tokens in request
                response_tokens → Tokens in response
                latency_ms      → API latency
                model_used      → Actual model

            /postprocessing/
                original        → Raw LLM response
                corrected       → Corrected response (if any)
                coherence_score → 0.0-1.0
                factual_issues  → JSON array of issues
                hallucinations  → JSON array of flags
                recommendation  → Accept/Correct/Regenerate/etc.
                confidence      → Overall confidence

/knowledge/
    /entity/{entity_id}/
        canonical_name      → Primary name
        type                → Person, Organization, etc.
        /aliases/           → Alternative names
        /attributes/        → Key-value attributes
        verified            → Is entity verified?
        last_updated        → Timestamp

    /fact/{fact_id}/
        subject             → Entity ID or string
        predicate           → Relation name
        object              → Entity ID, value, or string
        confidence          → 0.0-1.0
        source              → Where fact came from
        verified            → Is fact verified?
        last_updated        → Timestamp

    /document/{doc_id}/
        title               → Document title
        source_url          → Original URL (if applicable)
        content_hash        → Hash of content
        /chunks/            → Indexed chunks
        indexed_at          → When indexed

    /embedding/{chunk_id}/
        vector              → Embedding vector bytes
        model               → Embedding model used
        created_at          → When created
```

---

## Integration with Dialogue Layer

The LLM Integration Layer tightly integrates with the Dialogue Context Layer:

### Information Flow

```
┌─────────────────────────────────────────────────────────────────────────┐
│                    DIALOGUE ↔ LLM INTEGRATION                            │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                          │
│  DIALOGUE CONTEXT LAYER                                                  │
│  ┌─────────────────┐  ┌─────────────────┐  ┌─────────────────┐         │
│  │  Turn History   │  │ Entity Registry │  │   Topic Graph   │         │
│  │                 │  │                 │  │                 │         │
│  │ • Past turns    │  │ • Known entities│  │ • Active topics │         │
│  │ • Speech acts   │  │ • Coreference   │  │ • Topic history │         │
│  │ • QUD stack     │  │ • Salience      │  │ • Keywords      │         │
│  └────────┬────────┘  └────────┬────────┘  └────────┬────────┘         │
│           │                    │                    │                   │
│           └────────────────────┼────────────────────┘                   │
│                                │                                         │
│                     ┌──────────▼──────────┐                             │
│                     │   DialogueState     │                             │
│                     │   (PathMap-backed)  │                             │
│                     └──────────┬──────────┘                             │
│                                │                                         │
│  ══════════════════════════════╪═════════════════════════════════════   │
│                                │                                         │
│  LLM INTEGRATION LAYER         │                                         │
│                                │                                         │
│  PREPROCESSING uses:           │        POSTPROCESSING updates:          │
│  ┌─────────────────────────────┼─────────────────────────────────────┐  │
│  │                             │                                     │  │
│  │  ┌────────────────────┐     │     ┌────────────────────┐         │  │
│  │  │ EntityResolver     │◄────┤     │ EntityExtractor    │────────►│  │
│  │  │ • Resolve pronouns │     │     │ • Extract new ents │  UPDATE │  │
│  │  │ • Resolve names    │ QUERY    │ • Update salience  │         │  │
│  │  │ • Get attributes   │     │     │ • Add coreferences │         │  │
│  │  └────────────────────┘     │     └────────────────────┘         │  │
│  │                             │                                     │  │
│  │  ┌────────────────────┐     │     ┌────────────────────┐         │  │
│  │  │ ContextFormatter   │◄────┤     │ TurnRecorder       │────────►│  │
│  │  │ • Get turn history │     │     │ • Record LLM turn  │  UPDATE │  │
│  │  │ • Format summary   │ QUERY    │ • Update QUD       │         │  │
│  │  │ • Get topic context│     │     │ • Track commitments│         │  │
│  │  └────────────────────┘     │     └────────────────────┘         │  │
│  │                             │                                     │  │
│  │  ┌────────────────────┐     │     ┌────────────────────┐         │  │
│  │  │ CoherenceChecker   │◄────┤     │ TopicUpdater       │────────►│  │
│  │  │ • Check QUD        │     │     │ • Detect shifts    │  UPDATE │  │
│  │  │ • Check topic fit  │ QUERY    │ • Update graph     │         │  │
│  │  │ • Check consistency│     │     │ • Add keywords     │         │  │
│  │  └────────────────────┘     │     └────────────────────┘         │  │
│  │                             │                                     │  │
│  └─────────────────────────────┴─────────────────────────────────────┘  │
│                                                                          │
└─────────────────────────────────────────────────────────────────────────┘
```

### MeTTa Predicates for LLM Integration

```metta
; Prompt preprocessing predicates
(: preprocess-input (-> String DialogueState PreprocessedPrompt))
(: resolve-input-entities (-> String DialogueState (List ResolvedEntity)))
(: format-context (-> DialogueState ContextInjection))
(: retrieve-rag (-> String KnowledgeBase (List KnowledgeChunk)))
(: assemble-prompt (-> PreprocessedPrompt String))

; Response postprocessing predicates
(: postprocess-response (-> String DialogueState PostprocessedResponse))
(: check-coherence (-> String DialogueState CoherenceResult))
(: validate-facts (-> String KnowledgeBase FactualValidationResult))
(: detect-hallucinations (-> String DialogueState KnowledgeBase (List HallucinationFlag)))
(: recommend-handling (-> PostprocessedResponse ResponseRecommendation))

; Hallucination-specific predicates
(: is-fabricated-fact (-> Claim KnowledgeBase Bool))
(: entity-exists-in-kb (-> String KnowledgeBase Bool))
(: contradicts-known-fact (-> Claim KnowledgeBase (Maybe Fact)))
(: contradicts-dialogue-history (-> Claim DialogueState (Maybe Turn)))

; Knowledge base predicates
(: add-fact (-> Fact KnowledgeBase KnowledgeBase))
(: query-facts (-> Entity KnowledgeBase (List Fact)))
(: index-document (-> Document KnowledgeBase KnowledgeBase))
(: semantic-search (-> String KnowledgeBase (List KnowledgeChunk)))
```

---

## Document Guide

This section contains four detailed documents:

| Document | Description |
|----------|-------------|
| [01-prompt-preprocessing.md](./01-prompt-preprocessing.md) | Input correction, entity resolution, context injection, RAG |
| [02-output-postprocessing.md](./02-output-postprocessing.md) | Coherence checking, fact validation, response correction |
| [03-hallucination-detection.md](./03-hallucination-detection.md) | Detection algorithms, confidence scoring, mitigation strategies |
| [04-context-injection.md](./04-context-injection.md) | Dialogue history formatting, RAG integration, token optimization |

### Reading Order

**For implementers**:
1. This README (overview)
2. [01-prompt-preprocessing.md](./01-prompt-preprocessing.md) (input path first)
3. [04-context-injection.md](./04-context-injection.md) (context details)
4. [02-output-postprocessing.md](./02-output-postprocessing.md) (output path)
5. [03-hallucination-detection.md](./03-hallucination-detection.md) (specialized detection)

**For integration architects**:
1. This README (overview)
2. [04-context-injection.md](./04-context-injection.md) (system design)
3. [03-hallucination-detection.md](./03-hallucination-detection.md) (safety)
4. [01-prompt-preprocessing.md](./01-prompt-preprocessing.md) (input handling)
5. [02-output-postprocessing.md](./02-output-postprocessing.md) (output handling)

---

## Related Documentation

- [Dialogue Context Management](../dialogue/README.md) - Turn history, entities, topics
- [Correction WFST Architecture](../correction-wfst/01-architecture-overview.md) - Three-tier correction
- [Coreference Resolution](../dialogue/02-coreference-resolution.md) - Entity tracking
- [Pragmatic Reasoning](../dialogue/04-pragmatic-reasoning.md) - Speech act understanding
- [Agent Learning](../agent-learning/README.md) - Feedback integration

---

## References

- Brown, T. et al. (2020). "Language Models are Few-Shot Learners" (GPT-3)
- Lewis, P. et al. (2020). "Retrieval-Augmented Generation for Knowledge-Intensive NLP Tasks"
- Ji, Z. et al. (2023). "Survey of Hallucination in Natural Language Generation"
- Maynez, J. et al. (2020). "On Faithfulness and Factuality in Abstractive Summarization"
- Kryscinski, W. et al. (2020). "Evaluating the Factual Consistency of Abstractive Text Summarization"
