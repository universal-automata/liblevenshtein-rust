# Prompt Preprocessing

This document details the prompt preprocessing pipeline that corrects user input,
resolves entities, injects context, and retrieves relevant knowledge before
sending prompts to the LLM.

**Sources**:
- Plan: Part V - Dialogue Context and LLM Agent Correction Extension
- Dialogue Layer: `../dialogue/`
- Correction WFST: `../correction-wfst/`
- PathMap: `/home/dylon/Workspace/f1r3fly.io/PathMap/`
- MORK: `/home/dylon/Workspace/f1r3fly.io/MORK/`

---

## Table of Contents

1. [Overview](#overview)
2. [Pipeline Architecture](#pipeline-architecture)
3. [Input Correction Stage](#input-correction-stage)
4. [Entity Resolution Stage](#entity-resolution-stage)
5. [Context Injection Stage](#context-injection-stage)
6. [RAG Retrieval Stage](#rag-retrieval-stage)
7. [Prompt Assembly Stage](#prompt-assembly-stage)
8. [Implementation](#implementation)
9. [MeTTa Predicates](#metta-predicates)
10. [PathMap Schema](#pathmap-schema)

---

## Overview

The Prompt Preprocessor transforms raw user input into an optimized prompt for LLM
consumption. This involves:

1. **Correcting errors** in user input (spelling, grammar, syntax)
2. **Resolving entities** by linking mentions to known entities
3. **Injecting context** from dialogue history and user profile
4. **Retrieving knowledge** via RAG for factual grounding
5. **Assembling the prompt** with optimal structure and token usage

```
┌─────────────────────────────────────────────────────────────────────────┐
│                    PROMPT PREPROCESSING PIPELINE                         │
│                                                                          │
│  Raw User Input                                                          │
│       │                                                                  │
│       ▼                                                                  │
│  ┌────────────────────────────────────────────────────────────────────┐ │
│  │ STAGE 1: INPUT CORRECTION                                          │ │
│  │  ┌─────────────┐  ┌─────────────┐  ┌─────────────┐                │ │
│  │  │   Tier 1    │→ │   Tier 2    │→ │   Tier 3    │                │ │
│  │  │  Lexical    │  │  Syntactic  │  │  Semantic   │                │ │
│  │  └─────────────┘  └─────────────┘  └─────────────┘                │ │
│  └───────────────────────────┬────────────────────────────────────────┘ │
│                              ▼                                           │
│  ┌────────────────────────────────────────────────────────────────────┐ │
│  │ STAGE 2: ENTITY RESOLUTION                                         │ │
│  │  ┌─────────────┐  ┌─────────────┐  ┌─────────────┐                │ │
│  │  │  Mention    │→ │  Candidate  │→ │   Entity    │                │ │
│  │  │  Detection  │  │  Generation │  │   Linking   │                │ │
│  │  └─────────────┘  └─────────────┘  └─────────────┘                │ │
│  └───────────────────────────┬────────────────────────────────────────┘ │
│                              ▼                                           │
│  ┌────────────────────────────────────────────────────────────────────┐ │
│  │ STAGE 3: CONTEXT INJECTION                                         │ │
│  │  ┌─────────────┐  ┌─────────────┐  ┌─────────────┐                │ │
│  │  │  Dialogue   │→ │   Entity    │→ │   User      │                │ │
│  │  │  History    │  │   Context   │  │   Prefs     │                │ │
│  │  └─────────────┘  └─────────────┘  └─────────────┘                │ │
│  └───────────────────────────┬────────────────────────────────────────┘ │
│                              ▼                                           │
│  ┌────────────────────────────────────────────────────────────────────┐ │
│  │ STAGE 4: RAG RETRIEVAL                                             │ │
│  │  ┌─────────────┐  ┌─────────────┐  ┌─────────────┐                │ │
│  │  │   Query     │→ │  Semantic   │→ │   Chunk     │                │ │
│  │  │  Formation  │  │   Search    │  │  Selection  │                │ │
│  │  └─────────────┘  └─────────────┘  └─────────────┘                │ │
│  └───────────────────────────┬────────────────────────────────────────┘ │
│                              ▼                                           │
│  ┌────────────────────────────────────────────────────────────────────┐ │
│  │ STAGE 5: PROMPT ASSEMBLY                                           │ │
│  │  ┌─────────────┐  ┌─────────────┐  ┌─────────────┐                │ │
│  │  │  Template   │→ │   Token     │→ │   Final     │                │ │
│  │  │  Selection  │  │   Budget    │  │   Assembly  │                │ │
│  │  └─────────────┘  └─────────────┘  └─────────────┘                │ │
│  └───────────────────────────┬────────────────────────────────────────┘ │
│                              ▼                                           │
│                    Preprocessed Prompt                                   │
│                                                                          │
└─────────────────────────────────────────────────────────────────────────┘
```

---

## Pipeline Architecture

### Core Components

```rust
/// Main prompt preprocessing pipeline
pub struct PromptPreprocessor {
    /// Three-tier WFST correction engine
    correction_engine: CorrectionEngine,

    /// Entity resolution system
    entity_resolver: EntityResolver,

    /// Context injection formatter
    context_formatter: ContextFormatter,

    /// RAG retrieval system
    rag_retriever: RAGRetriever,

    /// Prompt assembly engine
    prompt_assembler: PromptAssembler,

    /// Configuration
    config: PreprocessorConfig,
}

/// Preprocessor configuration
pub struct PreprocessorConfig {
    /// Maximum tokens for entire prompt
    pub max_prompt_tokens: usize,

    /// Token budget allocation
    pub token_budget: TokenBudget,

    /// Correction aggressiveness (0.0 = minimal, 1.0 = aggressive)
    pub correction_level: f64,

    /// Whether to include RAG results
    pub enable_rag: bool,

    /// Minimum confidence for entity resolution
    pub entity_confidence_threshold: f64,

    /// Context window size (turns to include)
    pub context_window_size: usize,
}

/// Token budget allocation across prompt components
pub struct TokenBudget {
    /// Budget for system instructions
    pub system_tokens: usize,

    /// Budget for dialogue history
    pub history_tokens: usize,

    /// Budget for entity context
    pub entity_tokens: usize,

    /// Budget for RAG chunks
    pub rag_tokens: usize,

    /// Budget for user query (reserved)
    pub query_tokens: usize,
}

impl Default for TokenBudget {
    fn default() -> Self {
        // For a 4096 token model
        Self {
            system_tokens: 500,
            history_tokens: 1000,
            entity_tokens: 500,
            rag_tokens: 1500,
            query_tokens: 596,  // Remaining
        }
    }
}
```

### Pipeline Execution

```rust
impl PromptPreprocessor {
    /// Process user input through the full preprocessing pipeline
    pub fn preprocess(
        &self,
        input: &str,
        dialogue_state: &DialogueState,
        knowledge_base: &KnowledgeBase,
    ) -> Result<PreprocessedPrompt, PreprocessingError> {
        // Stage 1: Input Correction
        let correction_result = self.correction_engine.correct(input)?;

        // Stage 2: Entity Resolution
        let resolved_entities = self.entity_resolver.resolve(
            &correction_result.corrected_text,
            dialogue_state,
        )?;

        // Stage 3: Context Injection
        let context = self.context_formatter.format(
            dialogue_state,
            &resolved_entities,
            self.config.context_window_size,
        )?;

        // Stage 4: RAG Retrieval (if enabled)
        let rag_chunks = if self.config.enable_rag {
            self.rag_retriever.retrieve(
                &correction_result.corrected_text,
                knowledge_base,
            )?
        } else {
            Vec::new()
        };

        // Stage 5: Prompt Assembly
        let assembled = self.prompt_assembler.assemble(
            &correction_result,
            &resolved_entities,
            &context,
            &rag_chunks,
            &self.config.token_budget,
        )?;

        Ok(PreprocessedPrompt {
            original_input: input.to_string(),
            corrected_input: correction_result.corrected_text,
            corrections: correction_result.corrections,
            resolved_entities,
            context_injection: context,
            rag_chunks,
            assembled_prompt: assembled.prompt,
            confidence: assembled.confidence,
            estimated_tokens: assembled.token_count,
        })
    }
}
```

---

## Input Correction Stage

The first stage applies the three-tier WFST correction system to fix errors in user input.

### Correction Flow

```
User Input: "can u hlep me find the emial from john yesterdya"
     │
     ▼
┌────────────────────────────────────────────────────────────────┐
│ TIER 1: LEXICAL CORRECTION (liblevenshtein)                    │
│                                                                 │
│ Edit distance analysis:                                        │
│   "u" → "you" (common abbreviation expansion)                  │
│   "hlep" → "help" (distance 2, transposition)                  │
│   "emial" → "email" (distance 2, transposition)                │
│   "yesterdya" → "yesterday" (distance 2)                       │
│                                                                 │
│ Phonetic analysis:                                             │
│   "hlep" sounds like "help" (Metaphone match)                  │
│                                                                 │
│ Candidates generated per token:                                │
│   Token    | Candidates (score)                                │
│   ---------|------------------------------------------         │
│   "u"      | "you" (0.95), "a" (0.60), "I" (0.55)             │
│   "hlep"   | "help" (0.92), "heap" (0.70), "held" (0.68)      │
│   "emial"  | "email" (0.94), "Emil" (0.65), "enamel" (0.50)   │
│   "yesterdya" | "yesterday" (0.96), "yesterdays" (0.75)       │
│                                                                 │
│ Output: "can you help me find the email from john yesterday"   │
└────────────────────────────────────────────────────────────────┘
     │
     ▼
┌────────────────────────────────────────────────────────────────┐
│ TIER 2: SYNTACTIC CORRECTION (MORK/CFG)                        │
│                                                                 │
│ Grammar analysis:                                              │
│   "can you help me" - valid interrogative structure            │
│   Sentence-initial should be capitalized                       │
│   "john" - proper noun, should be capitalized                  │
│                                                                 │
│ Syntactic corrections:                                         │
│   "can" → "Can" (sentence-initial capitalization)              │
│   "john" → "John" (proper noun capitalization)                 │
│                                                                 │
│ Output: "Can you help me find the email from John yesterday"   │
└────────────────────────────────────────────────────────────────┘
     │
     ▼
┌────────────────────────────────────────────────────────────────┐
│ TIER 3: SEMANTIC CORRECTION (MeTTaIL)                          │
│                                                                 │
│ Semantic analysis:                                             │
│   "the email" - definite description, assumes prior context    │
│   "from John" - entity reference detected                      │
│   "yesterday" - temporal reference                             │
│                                                                 │
│ Type checking:                                                 │
│   (find (email (from Person) (date Date))) - valid structure   │
│                                                                 │
│ Semantic corrections:                                          │
│   None needed at this stage                                    │
│                                                                 │
│ Entity markers detected:                                       │
│   "John" - marked as PERSON entity for resolution              │
│   "yesterday" - marked as DATE for temporal resolution         │
│                                                                 │
│ Output: "Can you help me find the email from John yesterday?"  │
│         (added question mark for interrogative)                │
└────────────────────────────────────────────────────────────────┘
```

### Correction Engine Implementation

```rust
/// Three-tier correction engine
pub struct CorrectionEngine {
    /// Tier 1: Lexical correction (liblevenshtein)
    lexical: LexicalCorrector,

    /// Tier 2: Syntactic correction (MORK/CFG)
    syntactic: SyntacticCorrector,

    /// Tier 3: Semantic correction (MeTTaIL)
    semantic: SemanticCorrector,

    /// Configuration
    config: CorrectionConfig,
}

/// Correction result from all tiers
pub struct CorrectionResult {
    /// Corrected text
    pub corrected_text: String,

    /// All corrections applied
    pub corrections: Vec<CorrectionRecord>,

    /// Overall confidence
    pub confidence: f64,

    /// Entity markers found
    pub entity_markers: Vec<EntityMarker>,

    /// Tier-specific metadata
    pub tier_metadata: TierMetadata,
}

/// Individual correction record
pub struct CorrectionRecord {
    /// Tier that made the correction
    pub tier: CorrectionTier,

    /// Original span in input
    pub original_span: Range<usize>,

    /// Original text
    pub original: String,

    /// Corrected text
    pub corrected: String,

    /// Correction type
    pub correction_type: CorrectionType,

    /// Confidence score
    pub confidence: f64,

    /// Alternative corrections considered
    pub alternatives: Vec<(String, f64)>,
}

/// Types of corrections
pub enum CorrectionType {
    // Tier 1: Lexical
    Spelling,
    Transposition,
    Phonetic,
    Abbreviation,
    CaseNormalization,

    // Tier 2: Syntactic
    Grammar,
    Capitalization,
    Punctuation,
    WordOrder,

    // Tier 3: Semantic
    EntityCorrection,
    TypeMismatch,
    AmbiguityResolution,
    PragmaticAdjustment,
}

impl CorrectionEngine {
    /// Apply all three tiers of correction
    pub fn correct(&self, input: &str) -> Result<CorrectionResult, CorrectionError> {
        let mut current = input.to_string();
        let mut all_corrections = Vec::new();
        let mut entity_markers = Vec::new();

        // Tier 1: Lexical
        let tier1_result = self.lexical.correct(&current)?;
        current = tier1_result.text;
        all_corrections.extend(tier1_result.corrections);

        // Tier 2: Syntactic
        let tier2_result = self.syntactic.correct(&current)?;
        current = tier2_result.text;
        all_corrections.extend(tier2_result.corrections);

        // Tier 3: Semantic
        let tier3_result = self.semantic.correct(&current)?;
        current = tier3_result.text;
        all_corrections.extend(tier3_result.corrections);
        entity_markers = tier3_result.entity_markers;

        // Calculate overall confidence
        let confidence = self.calculate_confidence(&all_corrections);

        Ok(CorrectionResult {
            corrected_text: current,
            corrections: all_corrections,
            confidence,
            entity_markers,
            tier_metadata: TierMetadata {
                tier1_confidence: tier1_result.confidence,
                tier2_confidence: tier2_result.confidence,
                tier3_confidence: tier3_result.confidence,
            },
        })
    }

    fn calculate_confidence(&self, corrections: &[CorrectionRecord]) -> f64 {
        if corrections.is_empty() {
            return 1.0;  // No corrections = high confidence in original
        }

        // Weighted average of correction confidences
        let total: f64 = corrections.iter().map(|c| c.confidence).sum();
        total / corrections.len() as f64
    }
}
```

---

## Entity Resolution Stage

The second stage resolves entity mentions to known entities from the dialogue context
and knowledge base.

### Resolution Process

```
Input: "Can you help me find the email from John yesterday?"
Entity Markers: ["John" @ position 37..41]
     │
     ▼
┌────────────────────────────────────────────────────────────────┐
│ STEP 1: MENTION DETECTION                                      │
│                                                                 │
│ Named entity recognition:                                      │
│   "John" - PERSON (from Tier 3 marker)                         │
│   "yesterday" - DATE/TIME                                      │
│   "the email" - DEFINITE_DESC (referential)                    │
│                                                                 │
│ Detected mentions:                                             │
│   ┌─────────────────────────────────────────────────────────┐  │
│   │ Surface    │ Type           │ Span     │ Confidence     │  │
│   │------------|----------------|----------|----------------|  │
│   │ "John"     │ PERSON         │ 37..41   │ 0.95          │  │
│   │ "yesterday"│ DATE           │ 42..51   │ 0.98          │  │
│   │ "the email"│ DEFINITE_DESC  │ 23..32   │ 0.85          │  │
│   └─────────────────────────────────────────────────────────┘  │
└────────────────────────────────────────────────────────────────┘
     │
     ▼
┌────────────────────────────────────────────────────────────────┐
│ STEP 2: CANDIDATE GENERATION                                   │
│                                                                 │
│ For "John":                                                    │
│   Query DialogueState.entity_registry for PERSON named "John": │
│                                                                 │
│   ┌─────────────────────────────────────────────────────────┐  │
│   │ EntityId │ Name           │ Context Score │ Salience   │  │
│   │----------|----------------|---------------|------------|  │
│   │ E42      │ John Smith     │ 0.85         │ 0.92       │  │
│   │ E78      │ John Doe       │ 0.60         │ 0.45       │  │
│   │ E103     │ Johnny Walker  │ 0.30         │ 0.20       │  │
│   └─────────────────────────────────────────────────────────┘  │
│                                                                 │
│ For "yesterday":                                               │
│   Resolve to calendar date:                                    │
│   Current date: 2025-12-06                                     │
│   "yesterday" → 2025-12-05                                     │
│                                                                 │
│ For "the email":                                               │
│   Query recent turns for email references:                     │
│   Found: Turn T5 mentioned "email about Q4 budget"             │
│   Candidate: EmailRef(subject="Q4 budget review")              │
└────────────────────────────────────────────────────────────────┘
     │
     ▼
┌────────────────────────────────────────────────────────────────┐
│ STEP 3: ENTITY LINKING                                         │
│                                                                 │
│ Ranking candidates by combined score:                          │
│   Score = context_score × 0.4 + salience × 0.4 + prior × 0.2   │
│                                                                 │
│ For "John":                                                    │
│   E42 (John Smith): 0.85×0.4 + 0.92×0.4 + 0.70×0.2 = 0.848    │
│   E78 (John Doe):   0.60×0.4 + 0.45×0.4 + 0.50×0.2 = 0.520    │
│   E103 (Johnny W):  0.30×0.4 + 0.20×0.4 + 0.30×0.2 = 0.260    │
│                                                                 │
│ Selection: E42 (John Smith) with confidence 0.848              │
│                                                                 │
│ Resolved entities:                                             │
│   ┌─────────────────────────────────────────────────────────┐  │
│   │ Surface     │ EntityId │ Canonical      │ Confidence   │  │
│   │-------------|----------|----------------|--------------|  │
│   │ "John"      │ E42      │ John Smith     │ 0.848        │  │
│   │ "yesterday" │ -        │ 2025-12-05     │ 0.980        │  │
│   │ "the email" │ D128     │ Q4 Budget Email│ 0.720        │  │
│   └─────────────────────────────────────────────────────────┘  │
└────────────────────────────────────────────────────────────────┘
```

### Entity Resolution Implementation

```rust
/// Entity resolution system
pub struct EntityResolver {
    /// Named entity recognizer
    ner: NERModel,

    /// Dialogue state reference
    dialogue_state: Arc<RwLock<DialogueState>>,

    /// Knowledge base reference
    knowledge_base: Arc<RwLock<KnowledgeBase>>,

    /// Date/time resolver
    temporal_resolver: TemporalResolver,

    /// Configuration
    config: EntityResolutionConfig,
}

/// Entity resolution configuration
pub struct EntityResolutionConfig {
    /// Minimum confidence for linking
    pub min_confidence: f64,

    /// Weight for context match score
    pub context_weight: f64,

    /// Weight for salience score
    pub salience_weight: f64,

    /// Weight for prior probability
    pub prior_weight: f64,

    /// Maximum candidates to consider
    pub max_candidates: usize,
}

impl EntityResolver {
    /// Resolve entities in corrected input
    pub fn resolve(
        &self,
        input: &str,
        dialogue_state: &DialogueState,
    ) -> Result<Vec<ResolvedEntity>, EntityResolutionError> {
        // Step 1: Detect mentions
        let mentions = self.detect_mentions(input)?;

        // Step 2: Generate and rank candidates for each mention
        let mut resolved = Vec::new();
        for mention in mentions {
            let candidates = self.generate_candidates(&mention, dialogue_state)?;

            if let Some(best) = self.link_entity(&mention, candidates)? {
                if best.confidence >= self.config.min_confidence {
                    resolved.push(best);
                }
            }
        }

        Ok(resolved)
    }

    /// Detect entity mentions in text
    fn detect_mentions(&self, input: &str) -> Result<Vec<EntityMention>, EntityResolutionError> {
        let mut mentions = Vec::new();

        // Run NER
        let ner_results = self.ner.predict(input)?;
        for (span, entity_type, conf) in ner_results {
            mentions.push(EntityMention {
                surface: input[span.clone()].to_string(),
                span,
                mention_type: entity_type.into(),
                confidence: conf,
                entity_id: None,  // To be resolved
            });
        }

        // Detect temporal expressions
        let temporal_mentions = self.temporal_resolver.detect(input)?;
        mentions.extend(temporal_mentions);

        // Detect definite descriptions
        let definite_mentions = self.detect_definite_descriptions(input)?;
        mentions.extend(definite_mentions);

        Ok(mentions)
    }

    /// Generate entity candidates from dialogue context and KB
    fn generate_candidates(
        &self,
        mention: &EntityMention,
        dialogue_state: &DialogueState,
    ) -> Result<Vec<EntityCandidate>, EntityResolutionError> {
        let mut candidates = Vec::new();

        match mention.mention_type {
            MentionType::ProperName | MentionType::Pronoun => {
                // Query entity registry
                let registry_candidates = dialogue_state
                    .entity_registry
                    .query_by_name(&mention.surface)?;

                for entity in registry_candidates {
                    let context_score = self.compute_context_score(&entity, dialogue_state);
                    let salience = dialogue_state
                        .entity_registry
                        .get_salience(&entity.id)?;

                    candidates.push(EntityCandidate {
                        entity_id: entity.id,
                        canonical_name: entity.canonical_name.clone(),
                        context_score,
                        salience,
                        prior: self.get_prior(&entity),
                        attributes: entity.attributes.clone(),
                    });
                }
            }

            MentionType::DefiniteDesc => {
                // Search recent turns for matching references
                let turn_candidates = self.search_recent_turns(
                    &mention.surface,
                    dialogue_state,
                )?;
                candidates.extend(turn_candidates);
            }

            MentionType::Temporal => {
                // Temporal expressions resolved separately
            }

            _ => {}
        }

        // Sort by combined score
        candidates.sort_by(|a, b| {
            let score_a = self.combined_score(a);
            let score_b = self.combined_score(b);
            score_b.partial_cmp(&score_a).unwrap()
        });

        // Limit candidates
        candidates.truncate(self.config.max_candidates);

        Ok(candidates)
    }

    /// Link mention to best candidate entity
    fn link_entity(
        &self,
        mention: &EntityMention,
        candidates: Vec<EntityCandidate>,
    ) -> Result<Option<ResolvedEntity>, EntityResolutionError> {
        if candidates.is_empty() {
            return Ok(None);
        }

        let best = &candidates[0];
        let score = self.combined_score(best);

        Ok(Some(ResolvedEntity {
            surface: mention.surface.clone(),
            span: mention.span.clone(),
            entity_id: best.entity_id.clone(),
            canonical_name: best.canonical_name.clone(),
            attributes: best.attributes.clone(),
            confidence: score,
        }))
    }

    /// Compute combined ranking score
    fn combined_score(&self, candidate: &EntityCandidate) -> f64 {
        self.config.context_weight * candidate.context_score
            + self.config.salience_weight * candidate.salience
            + self.config.prior_weight * candidate.prior
    }
}
```

---

## Context Injection Stage

The third stage formats dialogue context for prompt injection.

### Context Components

```
┌────────────────────────────────────────────────────────────────┐
│ CONTEXT INJECTION COMPONENTS                                   │
│                                                                 │
│ ┌──────────────────────────────────────────────────────────┐   │
│ │ 1. DIALOGUE HISTORY SUMMARY                              │   │
│ │                                                          │   │
│ │ Recent turns (within window):                            │   │
│ │   Turn T-3: User asked about meeting schedule            │   │
│ │   Turn T-2: Assistant provided calendar options          │   │
│ │   Turn T-1: User mentioned John Smith joining            │   │
│ │                                                          │   │
│ │ Condensed summary:                                       │   │
│ │ "[Previous context: Discussing scheduling a meeting.     │   │
│ │  John Smith to be invited. Options: Mon 2pm, Tue 10am]"  │   │
│ └──────────────────────────────────────────────────────────┘   │
│                                                                 │
│ ┌──────────────────────────────────────────────────────────┐   │
│ │ 2. ACTIVE ENTITY CONTEXT                                 │   │
│ │                                                          │   │
│ │ High-salience entities:                                  │   │
│ │   • John Smith (colleague, Engineering)                  │   │
│ │     - Email: john.smith@company.com                      │   │
│ │     - Recent emails: Q4 budget review                    │   │
│ │   • Meeting (event)                                      │   │
│ │     - Topic: Q4 Budget Planning                          │   │
│ │     - Proposed times: Mon 2pm, Tue 10am                  │   │
│ │                                                          │   │
│ │ Formatted:                                               │   │
│ │ "[Entities: John Smith <john.smith@company.com>,         │   │
│ │  colleague in Engineering. Recent topic: Q4 budget.]"    │   │
│ └──────────────────────────────────────────────────────────┘   │
│                                                                 │
│ ┌──────────────────────────────────────────────────────────┐   │
│ │ 3. TOPIC CONTEXT                                         │   │
│ │                                                          │   │
│ │ Current topic graph state:                               │   │
│ │   Root: Work Communication                               │   │
│ │     └── Scheduling                                       │   │
│ │           └── Q4 Budget Meeting (active)                 │   │
│ │                                                          │   │
│ │ Topic keywords: budget, meeting, schedule, Q4, planning  │   │
│ │                                                          │   │
│ │ Formatted:                                               │   │
│ │ "[Topic: Scheduling Q4 Budget Meeting]"                  │   │
│ └──────────────────────────────────────────────────────────┘   │
│                                                                 │
│ ┌──────────────────────────────────────────────────────────┐   │
│ │ 4. USER PREFERENCES                                      │   │
│ │                                                          │   │
│ │ Communication style: Professional, concise               │   │
│ │ Response format: Bullet points preferred                 │   │
│ │ Knowledge level: Technical (engineering)                 │   │
│ │                                                          │   │
│ │ Formatted (as system instruction):                       │   │
│ │ "[Respond professionally and concisely. Use bullet       │   │
│ │  points when listing options. User has technical         │   │
│ │  background.]"                                           │   │
│ └──────────────────────────────────────────────────────────┘   │
│                                                                 │
└────────────────────────────────────────────────────────────────┘
```

### Context Formatter Implementation

```rust
/// Context injection formatter
pub struct ContextFormatter {
    /// Summarization model for dialogue history
    summarizer: DialogueSummarizer,

    /// Token counter
    tokenizer: Tokenizer,

    /// Configuration
    config: ContextFormatterConfig,
}

/// Context formatter configuration
pub struct ContextFormatterConfig {
    /// Maximum tokens for dialogue history
    pub max_history_tokens: usize,

    /// Maximum tokens for entity context
    pub max_entity_tokens: usize,

    /// Maximum tokens for topic context
    pub max_topic_tokens: usize,

    /// Number of turns to include verbatim
    pub verbatim_turn_count: usize,

    /// Format template
    pub template: ContextTemplate,
}

/// Formatted context injection
pub struct ContextInjection {
    /// Dialogue history summary
    pub dialogue_summary: String,

    /// Active entity descriptions
    pub entity_context: Vec<EntityContext>,

    /// Current topic description
    pub topic_context: String,

    /// User preference instructions
    pub user_preferences: Option<String>,

    /// System instructions
    pub system_instructions: Option<String>,

    /// Total token count
    pub total_tokens: usize,
}

impl ContextFormatter {
    /// Format dialogue context for prompt injection
    pub fn format(
        &self,
        dialogue_state: &DialogueState,
        resolved_entities: &[ResolvedEntity],
        window_size: usize,
    ) -> Result<ContextInjection, ContextFormattingError> {
        // 1. Format dialogue history
        let dialogue_summary = self.format_dialogue_history(
            dialogue_state,
            window_size,
            self.config.max_history_tokens,
        )?;

        // 2. Format entity context
        let entity_context = self.format_entity_context(
            dialogue_state,
            resolved_entities,
            self.config.max_entity_tokens,
        )?;

        // 3. Format topic context
        let topic_context = self.format_topic_context(
            dialogue_state,
            self.config.max_topic_tokens,
        )?;

        // 4. Format user preferences
        let user_preferences = self.format_user_preferences(dialogue_state)?;

        // 5. Format system instructions
        let system_instructions = self.format_system_instructions(dialogue_state)?;

        // Calculate total tokens
        let total_tokens = self.count_tokens(&dialogue_summary)
            + self.count_entity_tokens(&entity_context)
            + self.count_tokens(&topic_context)
            + self.count_tokens_opt(&user_preferences)
            + self.count_tokens_opt(&system_instructions);

        Ok(ContextInjection {
            dialogue_summary,
            entity_context,
            topic_context,
            user_preferences,
            system_instructions,
            total_tokens,
        })
    }

    /// Format dialogue history with summarization
    fn format_dialogue_history(
        &self,
        dialogue_state: &DialogueState,
        window_size: usize,
        max_tokens: usize,
    ) -> Result<String, ContextFormattingError> {
        let recent_turns: Vec<_> = dialogue_state
            .turns
            .iter()
            .rev()
            .take(window_size)
            .rev()
            .collect();

        if recent_turns.is_empty() {
            return Ok(String::new());
        }

        // Include last few turns verbatim
        let verbatim_count = self.config.verbatim_turn_count.min(recent_turns.len());
        let older_turns = &recent_turns[..recent_turns.len() - verbatim_count];
        let verbatim_turns = &recent_turns[recent_turns.len() - verbatim_count..];

        // Summarize older turns
        let summary = if !older_turns.is_empty() {
            self.summarizer.summarize(older_turns, max_tokens / 2)?
        } else {
            String::new()
        };

        // Format verbatim turns
        let mut verbatim = String::new();
        for turn in verbatim_turns {
            let speaker = match turn.speaker {
                ParticipantId::User => "User",
                ParticipantId::Assistant => "Assistant",
                ParticipantId::System => "System",
                _ => "Other",
            };
            writeln!(verbatim, "{}: {}", speaker, turn.corrected_text.as_ref()
                .unwrap_or(&turn.raw_text))?;
        }

        // Combine
        if summary.is_empty() {
            Ok(verbatim.trim().to_string())
        } else {
            Ok(format!("[Summary: {}]\n\n{}", summary, verbatim.trim()))
        }
    }

    /// Format entity context
    fn format_entity_context(
        &self,
        dialogue_state: &DialogueState,
        resolved_entities: &[ResolvedEntity],
        max_tokens: usize,
    ) -> Result<Vec<EntityContext>, ContextFormattingError> {
        let mut contexts = Vec::new();

        // Start with resolved entities from current query
        for resolved in resolved_entities {
            if let Some(entity) = dialogue_state
                .entity_registry
                .get(&resolved.entity_id)?
            {
                contexts.push(EntityContext {
                    entity_id: resolved.entity_id.clone(),
                    name: entity.canonical_name.clone(),
                    description: self.generate_entity_description(&entity),
                    relevance: resolved.confidence,
                    attributes: self.select_key_attributes(&entity),
                });
            }
        }

        // Add high-salience entities not in resolved list
        let high_salience = dialogue_state
            .entity_registry
            .get_high_salience_entities(5)?;

        for entity in high_salience {
            if !contexts.iter().any(|c| c.entity_id == entity.id) {
                let salience = dialogue_state
                    .entity_registry
                    .get_salience(&entity.id)?;

                contexts.push(EntityContext {
                    entity_id: entity.id.clone(),
                    name: entity.canonical_name.clone(),
                    description: self.generate_entity_description(&entity),
                    relevance: salience * 0.5,  // Lower weight for unreferenced
                    attributes: self.select_key_attributes(&entity),
                });
            }
        }

        // Sort by relevance and truncate to token budget
        contexts.sort_by(|a, b| {
            b.relevance.partial_cmp(&a.relevance).unwrap()
        });

        self.truncate_to_token_budget(&mut contexts, max_tokens);

        Ok(contexts)
    }

    /// Format topic context
    fn format_topic_context(
        &self,
        dialogue_state: &DialogueState,
        max_tokens: usize,
    ) -> Result<String, ContextFormattingError> {
        let active_topic = dialogue_state.topic_graph.get_current_topic()?;

        match active_topic {
            Some(topic) => {
                let keywords: Vec<_> = topic.keywords
                    .iter()
                    .take(10)
                    .map(|(k, _)| k.as_str())
                    .collect();

                let formatted = format!(
                    "Current topic: {}\nKeywords: {}",
                    topic.label,
                    keywords.join(", ")
                );

                // Truncate if needed
                self.truncate_string(&formatted, max_tokens)
            }
            None => Ok(String::new()),
        }
    }
}
```

---

## RAG Retrieval Stage

The fourth stage retrieves relevant knowledge chunks for factual grounding.

### RAG Pipeline

```
Query: "Can you help me find the email from John yesterday?"
     │
     ▼
┌────────────────────────────────────────────────────────────────┐
│ STEP 1: QUERY FORMATION                                        │
│                                                                 │
│ Extract search queries from input:                             │
│   Primary: "email from John Smith 2025-12-05"                  │
│   Secondary: "Q4 budget meeting communication"                 │
│                                                                 │
│ Expand with context:                                           │
│   "John Smith email Q4 budget December 2025"                   │
│   "meeting schedule confirmation john.smith@company.com"       │
└────────────────────────────────────────────────────────────────┘
     │
     ▼
┌────────────────────────────────────────────────────────────────┐
│ STEP 2: SEMANTIC SEARCH                                        │
│                                                                 │
│ Generate query embedding:                                      │
│   embed("email from John Smith 2025-12-05") → [0.12, -0.34, ...]│
│                                                                 │
│ Search vector index:                                           │
│   ┌─────────────────────────────────────────────────────────┐  │
│   │ ChunkId │ Document           │ Similarity │ Date       │  │
│   │---------|--------------------|-----------:|------------|  │
│   │ C2341   │ Email: Q4 Budget   │     0.89  │ 2025-12-05 │  │
│   │ C1892   │ Meeting Notes      │     0.76  │ 2025-12-04 │  │
│   │ C3102   │ Budget Spreadsheet │     0.71  │ 2025-12-03 │  │
│   │ C1456   │ Team Directory     │     0.65  │ 2025-11-01 │  │
│   └─────────────────────────────────────────────────────────┘  │
└────────────────────────────────────────────────────────────────┘
     │
     ▼
┌────────────────────────────────────────────────────────────────┐
│ STEP 3: CHUNK SELECTION & RANKING                              │
│                                                                 │
│ Apply filters:                                                 │
│   - Date filter: prefer recent documents                       │
│   - Entity filter: must mention John Smith                     │
│   - Type filter: emails prioritized for this query             │
│                                                                 │
│ Rerank with cross-encoder:                                     │
│   cross_encode(query, chunk) → fine-grained relevance          │
│                                                                 │
│ Final selection:                                               │
│   ┌─────────────────────────────────────────────────────────┐  │
│   │ ChunkId │ Content Preview               │ Final Score  │  │
│   │---------|-------------------------------|--------------|  │
│   │ C2341   │ "From: John Smith <john.sm... │     0.94     │  │
│   │ C1892   │ "Meeting with John to disc... │     0.78     │  │
│   └─────────────────────────────────────────────────────────┘  │
└────────────────────────────────────────────────────────────────┘
     │
     ▼
┌────────────────────────────────────────────────────────────────┐
│ STEP 4: CHUNK PREPARATION                                      │
│                                                                 │
│ Format selected chunks:                                        │
│                                                                 │
│ [Relevant Knowledge]                                           │
│ Source: Email from John Smith (2025-12-05)                     │
│ ---                                                            │
│ From: John Smith <john.smith@company.com>                      │
│ Subject: Q4 Budget Review Meeting                              │
│ Date: December 5, 2025                                         │
│                                                                 │
│ Hi team, I've attached the Q4 budget spreadsheet for review.   │
│ Let's discuss at our meeting on Monday at 2pm.                 │
│ ---                                                            │
│                                                                 │
│ Token count: 87 tokens                                         │
└────────────────────────────────────────────────────────────────┘
```

### RAG Implementation

```rust
/// RAG retrieval system
pub struct RAGRetriever {
    /// Embedding model
    embedder: EmbeddingModel,

    /// Vector index
    vector_index: VectorIndex,

    /// Cross-encoder reranker
    reranker: CrossEncoderReranker,

    /// Document store
    document_store: DocumentStore,

    /// Configuration
    config: RAGConfig,
}

/// RAG configuration
pub struct RAGConfig {
    /// Maximum chunks to retrieve
    pub max_chunks: usize,

    /// Maximum tokens for RAG content
    pub max_tokens: usize,

    /// Minimum similarity threshold
    pub min_similarity: f64,

    /// Use reranking
    pub enable_reranking: bool,

    /// Recency bias factor (0 = no bias, 1 = strong recency preference)
    pub recency_bias: f64,

    /// Entity match boost factor
    pub entity_match_boost: f64,
}

impl RAGRetriever {
    /// Retrieve relevant knowledge chunks
    pub fn retrieve(
        &self,
        query: &str,
        knowledge_base: &KnowledgeBase,
    ) -> Result<Vec<KnowledgeChunk>, RAGError> {
        // Step 1: Form queries
        let queries = self.form_queries(query)?;

        // Step 2: Semantic search
        let mut candidates = Vec::new();
        for q in &queries {
            let embedding = self.embedder.embed(q)?;
            let results = self.vector_index.search(&embedding, self.config.max_chunks * 2)?;
            candidates.extend(results);
        }

        // Deduplicate
        candidates.sort_by_key(|c| c.chunk_id.clone());
        candidates.dedup_by_key(|c| c.chunk_id.clone());

        // Step 3: Apply filters and boost
        let filtered = self.apply_filters(candidates, query)?;

        // Step 4: Rerank if enabled
        let ranked = if self.config.enable_reranking {
            self.reranker.rerank(query, filtered)?
        } else {
            filtered
        };

        // Step 5: Select top chunks within token budget
        let selected = self.select_within_budget(
            ranked,
            self.config.max_tokens,
        )?;

        Ok(selected)
    }

    /// Form search queries from user input
    fn form_queries(&self, input: &str) -> Result<Vec<String>, RAGError> {
        let mut queries = vec![input.to_string()];

        // Extract key phrases
        let key_phrases = self.extract_key_phrases(input)?;
        for phrase in key_phrases {
            queries.push(phrase);
        }

        // Expand with synonyms/related terms
        let expanded = self.expand_query(input)?;
        if expanded != input {
            queries.push(expanded);
        }

        Ok(queries)
    }

    /// Apply filters and boosts to candidates
    fn apply_filters(
        &self,
        mut candidates: Vec<SearchResult>,
        query: &str,
    ) -> Result<Vec<SearchResult>, RAGError> {
        // Filter by minimum similarity
        candidates.retain(|c| c.similarity >= self.config.min_similarity);

        // Apply recency bias
        let now = Utc::now();
        for candidate in &mut candidates {
            let age_days = (now - candidate.document_date).num_days() as f64;
            let recency_factor = (-age_days / 30.0 * self.config.recency_bias).exp();
            candidate.similarity *= (1.0 + recency_factor * 0.2);
        }

        // Boost entity matches
        let query_entities = self.extract_entities(query)?;
        for candidate in &mut candidates {
            let chunk_entities = self.extract_entities(&candidate.content)?;
            let overlap = query_entities.intersection(&chunk_entities).count();
            if overlap > 0 {
                candidate.similarity *= (1.0 + self.config.entity_match_boost
                    * overlap as f64);
            }
        }

        // Re-sort by adjusted similarity
        candidates.sort_by(|a, b| {
            b.similarity.partial_cmp(&a.similarity).unwrap()
        });

        Ok(candidates)
    }

    /// Select chunks within token budget
    fn select_within_budget(
        &self,
        candidates: Vec<SearchResult>,
        max_tokens: usize,
    ) -> Result<Vec<KnowledgeChunk>, RAGError> {
        let mut selected = Vec::new();
        let mut total_tokens = 0;

        for candidate in candidates {
            let chunk = self.document_store.get_chunk(&candidate.chunk_id)?;
            let chunk_tokens = self.count_tokens(&chunk.content);

            if total_tokens + chunk_tokens <= max_tokens {
                selected.push(KnowledgeChunk {
                    chunk_id: candidate.chunk_id,
                    source: chunk.source,
                    content: chunk.content,
                    relevance: candidate.similarity,
                    embedding: None,
                });
                total_tokens += chunk_tokens;
            }

            if selected.len() >= self.config.max_chunks {
                break;
            }
        }

        Ok(selected)
    }
}
```

---

## Prompt Assembly Stage

The final stage combines all components into the assembled prompt.

### Assembly Structure

```
┌─────────────────────────────────────────────────────────────────────────┐
│                        ASSEMBLED PROMPT STRUCTURE                        │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                          │
│  ┌────────────────────────────────────────────────────────────────────┐ │
│  │ SECTION 1: SYSTEM INSTRUCTIONS                                     │ │
│  │                                                                    │ │
│  │ You are a helpful assistant. Respond professionally and concisely. │ │
│  │ Use bullet points when listing options. The user has a technical   │ │
│  │ background in engineering.                                         │ │
│  │                                                                    │ │
│  │ [~80 tokens]                                                       │ │
│  └────────────────────────────────────────────────────────────────────┘ │
│                                                                          │
│  ┌────────────────────────────────────────────────────────────────────┐ │
│  │ SECTION 2: DIALOGUE CONTEXT                                        │ │
│  │                                                                    │ │
│  │ [Previous conversation summary]                                    │ │
│  │ The user has been discussing scheduling a Q4 budget meeting with   │ │
│  │ John Smith from Engineering.                                       │ │
│  │                                                                    │ │
│  │ Recent messages:                                                   │ │
│  │ User: Can we schedule the meeting for Monday?                      │ │
│  │ Assistant: Monday at 2pm works. Should I send the invite to John?  │ │
│  │ User: Yes, please include him.                                     │ │
│  │                                                                    │ │
│  │ [~150 tokens]                                                      │ │
│  └────────────────────────────────────────────────────────────────────┘ │
│                                                                          │
│  ┌────────────────────────────────────────────────────────────────────┐ │
│  │ SECTION 3: ENTITY CONTEXT                                          │ │
│  │                                                                    │ │
│  │ [Relevant entities]                                                │ │
│  │ • John Smith - Colleague in Engineering Department                 │ │
│  │   Email: john.smith@company.com                                    │ │
│  │   Recent topic: Q4 budget planning                                 │ │
│  │                                                                    │ │
│  │ [~60 tokens]                                                       │ │
│  └────────────────────────────────────────────────────────────────────┘ │
│                                                                          │
│  ┌────────────────────────────────────────────────────────────────────┐ │
│  │ SECTION 4: RETRIEVED KNOWLEDGE (RAG)                               │ │
│  │                                                                    │ │
│  │ [Relevant information]                                             │ │
│  │ Source: Email from John Smith (December 5, 2025)                   │ │
│  │ ---                                                                │ │
│  │ From: John Smith <john.smith@company.com>                          │ │
│  │ Subject: Q4 Budget Review Meeting                                  │ │
│  │                                                                    │ │
│  │ Hi team, I've attached the Q4 budget spreadsheet for review.       │ │
│  │ Let's discuss at our meeting on Monday at 2pm.                     │ │
│  │ ---                                                                │ │
│  │                                                                    │ │
│  │ [~100 tokens]                                                      │ │
│  └────────────────────────────────────────────────────────────────────┘ │
│                                                                          │
│  ┌────────────────────────────────────────────────────────────────────┐ │
│  │ SECTION 5: USER QUERY                                              │ │
│  │                                                                    │ │
│  │ User: Can you help me find the email from John yesterday?          │ │
│  │                                                                    │ │
│  │ [~20 tokens]                                                       │ │
│  └────────────────────────────────────────────────────────────────────┘ │
│                                                                          │
│  ═══════════════════════════════════════════════════════════════════════ │
│  Total: ~410 tokens (well within 4096 limit)                            │
│                                                                          │
└─────────────────────────────────────────────────────────────────────────┘
```

### Prompt Assembler Implementation

```rust
/// Prompt assembly engine
pub struct PromptAssembler {
    /// Tokenizer for counting
    tokenizer: Tokenizer,

    /// Prompt templates
    templates: PromptTemplates,

    /// Configuration
    config: AssemblerConfig,
}

/// Assembled prompt result
pub struct AssembledPrompt {
    /// Final prompt string
    pub prompt: String,

    /// Breakdown by section
    pub sections: Vec<PromptSection>,

    /// Total token count
    pub token_count: usize,

    /// Assembly confidence
    pub confidence: f64,

    /// Truncation warnings
    pub warnings: Vec<AssemblyWarning>,
}

/// Individual prompt section
pub struct PromptSection {
    /// Section name
    pub name: String,

    /// Section content
    pub content: String,

    /// Token count
    pub tokens: usize,

    /// Was truncated
    pub truncated: bool,
}

impl PromptAssembler {
    /// Assemble final prompt from all components
    pub fn assemble(
        &self,
        correction: &CorrectionResult,
        entities: &[ResolvedEntity],
        context: &ContextInjection,
        rag_chunks: &[KnowledgeChunk],
        budget: &TokenBudget,
    ) -> Result<AssembledPrompt, AssemblyError> {
        let mut sections = Vec::new();
        let mut warnings = Vec::new();

        // Section 1: System Instructions
        let system_section = self.assemble_system_section(
            context.system_instructions.as_deref(),
            context.user_preferences.as_deref(),
            budget.system_tokens,
        )?;
        sections.push(system_section);

        // Section 2: Dialogue Context
        let dialogue_section = self.assemble_dialogue_section(
            &context.dialogue_summary,
            budget.history_tokens,
        )?;
        if dialogue_section.truncated {
            warnings.push(AssemblyWarning::DialogueTruncated);
        }
        sections.push(dialogue_section);

        // Section 3: Entity Context
        let entity_section = self.assemble_entity_section(
            &context.entity_context,
            entities,
            budget.entity_tokens,
        )?;
        if entity_section.truncated {
            warnings.push(AssemblyWarning::EntityContextTruncated);
        }
        sections.push(entity_section);

        // Section 4: RAG Knowledge
        let rag_section = self.assemble_rag_section(
            rag_chunks,
            budget.rag_tokens,
        )?;
        if rag_section.truncated {
            warnings.push(AssemblyWarning::RAGTruncated);
        }
        sections.push(rag_section);

        // Section 5: User Query
        let query_section = self.assemble_query_section(
            &correction.corrected_text,
            budget.query_tokens,
        )?;
        sections.push(query_section);

        // Combine sections
        let prompt = self.combine_sections(&sections)?;
        let token_count: usize = sections.iter().map(|s| s.tokens).sum();

        // Calculate confidence
        let confidence = self.calculate_assembly_confidence(
            correction,
            &sections,
            &warnings,
        );

        Ok(AssembledPrompt {
            prompt,
            sections,
            token_count,
            confidence,
            warnings,
        })
    }

    /// Assemble system instructions section
    fn assemble_system_section(
        &self,
        system_instructions: Option<&str>,
        user_preferences: Option<&str>,
        max_tokens: usize,
    ) -> Result<PromptSection, AssemblyError> {
        let template = &self.templates.system;

        let mut content = template.base.clone();

        if let Some(instructions) = system_instructions {
            content.push_str("\n\n");
            content.push_str(instructions);
        }

        if let Some(prefs) = user_preferences {
            content.push_str("\n\n");
            content.push_str(prefs);
        }

        let (content, truncated) = self.truncate_to_tokens(&content, max_tokens);

        Ok(PromptSection {
            name: "system".to_string(),
            content,
            tokens: self.count_tokens(&content),
            truncated,
        })
    }

    /// Assemble dialogue history section
    fn assemble_dialogue_section(
        &self,
        summary: &str,
        max_tokens: usize,
    ) -> Result<PromptSection, AssemblyError> {
        if summary.is_empty() {
            return Ok(PromptSection {
                name: "dialogue".to_string(),
                content: String::new(),
                tokens: 0,
                truncated: false,
            });
        }

        let template = &self.templates.dialogue;
        let content = template.format(summary);

        let (content, truncated) = self.truncate_to_tokens(&content, max_tokens);

        Ok(PromptSection {
            name: "dialogue".to_string(),
            content,
            tokens: self.count_tokens(&content),
            truncated,
        })
    }

    /// Assemble entity context section
    fn assemble_entity_section(
        &self,
        entity_context: &[EntityContext],
        resolved: &[ResolvedEntity],
        max_tokens: usize,
    ) -> Result<PromptSection, AssemblyError> {
        if entity_context.is_empty() {
            return Ok(PromptSection {
                name: "entities".to_string(),
                content: String::new(),
                tokens: 0,
                truncated: false,
            });
        }

        let template = &self.templates.entities;
        let mut content = template.header.clone();

        for entity in entity_context {
            let entity_str = format!(
                "\n• {} - {}\n  {}",
                entity.name,
                entity.description,
                entity.attributes
                    .iter()
                    .map(|(k, v)| format!("{}: {}", k, v))
                    .collect::<Vec<_>>()
                    .join(", ")
            );
            content.push_str(&entity_str);
        }

        let (content, truncated) = self.truncate_to_tokens(&content, max_tokens);

        Ok(PromptSection {
            name: "entities".to_string(),
            content,
            tokens: self.count_tokens(&content),
            truncated,
        })
    }

    /// Assemble RAG knowledge section
    fn assemble_rag_section(
        &self,
        chunks: &[KnowledgeChunk],
        max_tokens: usize,
    ) -> Result<PromptSection, AssemblyError> {
        if chunks.is_empty() {
            return Ok(PromptSection {
                name: "rag".to_string(),
                content: String::new(),
                tokens: 0,
                truncated: false,
            });
        }

        let template = &self.templates.rag;
        let mut content = template.header.clone();
        let mut current_tokens = self.count_tokens(&content);
        let mut truncated = false;

        for chunk in chunks {
            let chunk_content = format!(
                "\n\nSource: {}\n---\n{}\n---",
                chunk.source.title,
                chunk.content
            );
            let chunk_tokens = self.count_tokens(&chunk_content);

            if current_tokens + chunk_tokens > max_tokens {
                truncated = true;
                break;
            }

            content.push_str(&chunk_content);
            current_tokens += chunk_tokens;
        }

        Ok(PromptSection {
            name: "rag".to_string(),
            content,
            tokens: current_tokens,
            truncated,
        })
    }

    /// Assemble user query section
    fn assemble_query_section(
        &self,
        query: &str,
        max_tokens: usize,
    ) -> Result<PromptSection, AssemblyError> {
        let template = &self.templates.query;
        let content = template.format(query);

        let (content, truncated) = self.truncate_to_tokens(&content, max_tokens);

        Ok(PromptSection {
            name: "query".to_string(),
            content,
            tokens: self.count_tokens(&content),
            truncated,
        })
    }

    /// Combine all sections into final prompt
    fn combine_sections(
        &self,
        sections: &[PromptSection],
    ) -> Result<String, AssemblyError> {
        let mut prompt = String::new();

        for section in sections {
            if !section.content.is_empty() {
                if !prompt.is_empty() {
                    prompt.push_str("\n\n");
                }
                prompt.push_str(&section.content);
            }
        }

        Ok(prompt)
    }
}
```

---

## Implementation

### Full Pipeline Example

```rust
/// Example: Full preprocessing pipeline execution
pub async fn preprocess_user_input(
    user_input: &str,
    session: &Session,
) -> Result<PreprocessedPrompt, Error> {
    // Initialize pipeline
    let preprocessor = PromptPreprocessor::new(
        session.correction_engine.clone(),
        session.entity_resolver.clone(),
        session.context_formatter.clone(),
        session.rag_retriever.clone(),
        session.prompt_assembler.clone(),
        PreprocessorConfig::default(),
    );

    // Get current dialogue state
    let dialogue_state = session.dialogue_state.read().await;

    // Get knowledge base
    let knowledge_base = session.knowledge_base.read().await;

    // Run preprocessing
    let result = preprocessor.preprocess(
        user_input,
        &dialogue_state,
        &knowledge_base,
    )?;

    // Log preprocessing metrics
    tracing::info!(
        original = %user_input,
        corrected = %result.corrected_input,
        corrections = result.corrections.len(),
        entities = result.resolved_entities.len(),
        rag_chunks = result.rag_chunks.len(),
        tokens = result.estimated_tokens,
        confidence = result.confidence,
        "Prompt preprocessing complete"
    );

    Ok(result)
}
```

---

## MeTTa Predicates

```metta
; Core preprocessing predicates
(: preprocess-prompt (-> String DialogueState KnowledgeBase PreprocessedPrompt))
(: correct-input (-> String CorrectionResult))
(: resolve-entities (-> String DialogueState (List ResolvedEntity)))
(: format-context (-> DialogueState (List ResolvedEntity) ContextInjection))
(: retrieve-rag (-> String KnowledgeBase (List KnowledgeChunk)))
(: assemble-prompt (-> CorrectionResult (List ResolvedEntity) ContextInjection (List KnowledgeChunk) String))

; Correction predicates
(: apply-lexical-correction (-> String CorrectionResult))
(: apply-syntactic-correction (-> String CorrectionResult))
(: apply-semantic-correction (-> String CorrectionResult))
(: correction-confidence (-> CorrectionResult Float))

; Entity resolution predicates
(: detect-mentions (-> String (List EntityMention)))
(: generate-candidates (-> EntityMention DialogueState (List EntityCandidate)))
(: link-entity (-> EntityMention (List EntityCandidate) (Maybe ResolvedEntity)))
(: entity-resolution-score (-> EntityCandidate Float))

; Context formatting predicates
(: summarize-dialogue (-> (List Turn) Int String))
(: format-entity-context (-> (List Entity) String))
(: format-topic-context (-> TopicGraph String))
(: apply-token-budget (-> String Int String))

; RAG predicates
(: form-search-queries (-> String (List String)))
(: semantic-search (-> String KnowledgeBase (List SearchResult)))
(: rerank-results (-> String (List SearchResult) (List SearchResult)))
(: select-chunks (-> (List SearchResult) Int (List KnowledgeChunk)))

; Assembly predicates
(: select-template (-> PreprocessorConfig PromptTemplate))
(: allocate-token-budget (-> Int TokenBudget))
(: combine-sections (-> (List PromptSection) String))
(: calculate-assembly-confidence (-> (List PromptSection) Float))
```

---

## PathMap Schema

```
PathMap Key Structure:
=======================

/preprocessing/{session_id}/{turn_id}/
    /input/
        raw                 → Original user input
        corrected           → Corrected input text
        confidence          → Overall confidence score

    /corrections/
        count               → Number of corrections
        /{correction_idx}/
            tier            → 1, 2, or 3
            original        → Original text
            corrected       → Corrected text
            type            → Correction type
            confidence      → Correction confidence
            span_start      → Start position
            span_end        → End position

    /entities/
        count               → Number of resolved entities
        /{entity_idx}/
            surface         → Surface form
            entity_id       → Resolved entity ID
            canonical       → Canonical name
            confidence      → Resolution confidence
            /attributes/    → Entity attributes

    /context/
        dialogue_summary    → Formatted dialogue history
        topic_context       → Current topic description
        user_preferences    → User preference string
        system_instructions → System instruction string
        total_tokens        → Token count for context

    /rag/
        count               → Number of chunks retrieved
        /{chunk_idx}/
            chunk_id        → Chunk identifier
            source          → Source document reference
            content         → Chunk content
            relevance       → Relevance score

    /assembled/
        prompt              → Final assembled prompt
        token_count         → Total tokens
        confidence          → Assembly confidence
        /sections/
            system          → System section tokens
            dialogue        → Dialogue section tokens
            entities        → Entity section tokens
            rag             → RAG section tokens
            query           → Query section tokens
        /warnings/          → List of assembly warnings
```

---

## Related Documentation

- [LLM Integration Overview](./README.md) - Layer architecture
- [Output Postprocessing](./02-output-postprocessing.md) - Response validation
- [Hallucination Detection](./03-hallucination-detection.md) - Fabrication detection
- [Context Injection](./04-context-injection.md) - RAG and history formatting
- [Dialogue Context](../dialogue/README.md) - Turn and entity tracking
- [Correction WFST](../correction-wfst/01-architecture-overview.md) - Three-tier correction

---

## References

- Lewis, P. et al. (2020). "Retrieval-Augmented Generation for Knowledge-Intensive NLP Tasks"
- Guu, K. et al. (2020). "REALM: Retrieval-Augmented Language Model Pre-Training"
- Izacard, G. & Grave, E. (2021). "Leveraging Passage Retrieval with Generative Models"
- Karpukhin, V. et al. (2020). "Dense Passage Retrieval for Open-Domain QA"
- Nogueira, R. & Cho, K. (2019). "Passage Re-ranking with BERT"
