# Context Injection

This document details the context injection system that prepares dialogue history,
entity information, and retrieved knowledge (RAG) for LLM prompts.

**Sources**:
- Plan: Part V - Dialogue Context and LLM Agent Correction Extension
- Dialogue Layer: `../dialogue/`
- PathMap: `/home/dylon/Workspace/f1r3fly.io/PathMap/`
- MORK: `/home/dylon/Workspace/f1r3fly.io/MORK/`

---

## Table of Contents

1. [Overview](#overview)
2. [Token Budget Management](#token-budget-management)
3. [Dialogue History Formatting](#dialogue-history-formatting)
4. [Entity Context Injection](#entity-context-injection)
5. [RAG Integration](#rag-integration)
6. [System Prompt Assembly](#system-prompt-assembly)
7. [Dynamic Compression](#dynamic-compression)
8. [Implementation](#implementation)
9. [MeTTa Predicates](#metta-predicates)
10. [PathMap Schema](#pathmap-schema)

---

## Overview

Context injection prepares relevant background information for LLM prompts, enabling
the model to generate contextually appropriate responses. This involves:

1. **Token Budget Management** - Allocating limited tokens across components
2. **Dialogue History** - Summarizing and formatting conversation turns
3. **Entity Context** - Providing relevant entity information
4. **RAG Retrieval** - Injecting retrieved knowledge chunks
5. **System Instructions** - User preferences and agent personality

```
┌─────────────────────────────────────────────────────────────────────────┐
│                      CONTEXT INJECTION PIPELINE                          │
│                                                                          │
│  ┌─────────────────────────────────────────────────────────────────────┐│
│  │                     TOKEN BUDGET ALLOCATOR                          ││
│  │                                                                     ││
│  │   Total Budget: 4096 tokens                                         ││
│  │                                                                     ││
│  │   ┌──────────┐ ┌──────────┐ ┌──────────┐ ┌──────────┐ ┌──────────┐ ││
│  │   │ System   │ │ History  │ │ Entities │ │   RAG    │ │  Query   │ ││
│  │   │  500     │ │  1000    │ │   500    │ │  1500    │ │   596    │ ││
│  │   └────┬─────┘ └────┬─────┘ └────┬─────┘ └────┬─────┘ └────┬─────┘ ││
│  │        │            │            │            │            │        ││
│  └────────┼────────────┼────────────┼────────────┼────────────┼────────┘│
│           │            │            │            │            │         │
│  ┌────────▼────────────▼────────────▼────────────▼────────────▼────────┐│
│  │                      CONTEXT FORMATTERS                             ││
│  │                                                                     ││
│  │  ┌─────────────────┐  ┌─────────────────┐  ┌─────────────────┐     ││
│  │  │ DialogueState   │  │ EntityRegistry  │  │ VectorIndex     │     ││
│  │  │                 │  │                 │  │                 │     ││
│  │  │ • Recent turns  │  │ • Active ents   │  │ • Semantic      │     ││
│  │  │ • Summarize old │  │ • Attributes    │  │   search        │     ││
│  │  │ • Topics        │  │ • Relationships │  │ • Reranking     │     ││
│  │  └────────┬────────┘  └────────┬────────┘  └────────┬────────┘     ││
│  │           │                    │                    │               ││
│  └───────────┼────────────────────┼────────────────────┼───────────────┘│
│              │                    │                    │                │
│              ▼                    ▼                    ▼                │
│  ┌─────────────────────────────────────────────────────────────────────┐│
│  │                      PROMPT ASSEMBLER                               ││
│  │                                                                     ││
│  │  ┌─────────────────────────────────────────────────────────────┐   ││
│  │  │ [SYSTEM]                                                    │   ││
│  │  │ You are a helpful assistant...                              │   ││
│  │  │ User prefers: concise, professional                         │   ││
│  │  ├─────────────────────────────────────────────────────────────┤   ││
│  │  │ [CONTEXT]                                                   │   ││
│  │  │ Previous conversation summary...                            │   ││
│  │  │ Relevant entities: John Smith (Engineering)...              │   ││
│  │  ├─────────────────────────────────────────────────────────────┤   ││
│  │  │ [KNOWLEDGE]                                                 │   ││
│  │  │ Source: Email from John Smith (Dec 5)...                    │   ││
│  │  ├─────────────────────────────────────────────────────────────┤   ││
│  │  │ [USER]                                                      │   ││
│  │  │ Current query...                                            │   ││
│  │  └─────────────────────────────────────────────────────────────┘   ││
│  │                                                                     ││
│  └─────────────────────────────────────────────────────────────────────┘│
│                                                                          │
└─────────────────────────────────────────────────────────────────────────┘
```

---

## Token Budget Management

Effective context injection requires careful token budget allocation.

### Budget Allocation Strategy

```rust
/// Token budget manager
pub struct TokenBudgetManager {
    /// Total available tokens for context
    total_budget: usize,

    /// Tokenizer for counting
    tokenizer: Tokenizer,

    /// Allocation strategy
    strategy: AllocationStrategy,

    /// Configuration
    config: BudgetConfig,
}

/// Token budget allocation
pub struct TokenBudget {
    /// Budget for system instructions
    pub system: usize,

    /// Budget for dialogue history
    pub history: usize,

    /// Budget for entity context
    pub entities: usize,

    /// Budget for RAG chunks
    pub rag: usize,

    /// Budget for user query (reserved)
    pub query: usize,
}

/// Allocation strategy
pub enum AllocationStrategy {
    /// Fixed percentages
    Fixed {
        system_pct: f64,
        history_pct: f64,
        entities_pct: f64,
        rag_pct: f64,
        query_pct: f64,
    },

    /// Dynamic based on query complexity
    Dynamic,

    /// Prioritized allocation (fills in order until full)
    Prioritized {
        order: Vec<BudgetCategory>,
    },
}

impl Default for TokenBudget {
    fn default() -> Self {
        // For 4096 token model
        Self {
            system: 500,
            history: 1000,
            entities: 500,
            rag: 1500,
            query: 596,
        }
    }
}

impl TokenBudgetManager {
    /// Allocate tokens based on strategy and available content
    pub fn allocate(
        &self,
        query: &str,
        dialogue_state: &DialogueState,
        available_chunks: usize,
    ) -> TokenBudget {
        let query_tokens = self.tokenizer.count(query);

        match &self.strategy {
            AllocationStrategy::Fixed { .. } => {
                self.allocate_fixed(query_tokens)
            }

            AllocationStrategy::Dynamic => {
                self.allocate_dynamic(query, dialogue_state, available_chunks, query_tokens)
            }

            AllocationStrategy::Prioritized { order } => {
                self.allocate_prioritized(order, query_tokens)
            }
        }
    }

    /// Dynamic allocation based on context needs
    fn allocate_dynamic(
        &self,
        query: &str,
        dialogue_state: &DialogueState,
        available_chunks: usize,
        query_tokens: usize,
    ) -> TokenBudget {
        // Reserve query tokens
        let remaining = self.total_budget.saturating_sub(query_tokens + 100);

        // Calculate needs
        let history_turns = dialogue_state.turns.len();
        let entity_count = dialogue_state.entity_registry.active_count();

        // Base allocations
        let mut system = 400;
        let mut history;
        let mut entities;
        let mut rag;

        // Adjust based on conversation length
        if history_turns <= 3 {
            // Short conversation: more RAG, less history
            history = remaining * 15 / 100;
            entities = remaining * 15 / 100;
            rag = remaining * 60 / 100;
        } else if history_turns <= 10 {
            // Medium conversation: balanced
            history = remaining * 30 / 100;
            entities = remaining * 20 / 100;
            rag = remaining * 40 / 100;
        } else {
            // Long conversation: more history, less RAG
            history = remaining * 40 / 100;
            entities = remaining * 25 / 100;
            rag = remaining * 25 / 100;
        }

        // Adjust for entity count
        if entity_count > 10 {
            entities = (entities as f64 * 1.3) as usize;
            rag = remaining.saturating_sub(system + history + entities);
        }

        // Adjust for available RAG chunks
        if available_chunks == 0 {
            // No RAG available, redistribute
            let rag_excess = rag;
            rag = 0;
            history += rag_excess / 2;
            entities += rag_excess / 2;
        }

        // Add system overhead
        system = system.min(remaining.saturating_sub(history + entities + rag));

        TokenBudget {
            system,
            history,
            entities,
            rag,
            query: query_tokens + 100,
        }
    }
}
```

### Overflow Handling

```rust
impl TokenBudgetManager {
    /// Handle when content exceeds budget
    pub fn handle_overflow(
        &self,
        content: &mut ContextContent,
        budget: &TokenBudget,
    ) -> Result<(), BudgetError> {
        // Check each category
        if content.system_tokens > budget.system {
            content.system = self.truncate_system(&content.system, budget.system)?;
        }

        if content.history_tokens > budget.history {
            content.history = self.compress_history(&content.history, budget.history)?;
        }

        if content.entities_tokens > budget.entities {
            content.entities = self.prioritize_entities(&content.entities, budget.entities)?;
        }

        if content.rag_tokens > budget.rag {
            content.rag_chunks = self.select_rag_chunks(&content.rag_chunks, budget.rag)?;
        }

        Ok(())
    }

    /// Compress dialogue history to fit budget
    fn compress_history(
        &self,
        history: &FormattedHistory,
        max_tokens: usize,
    ) -> Result<FormattedHistory, BudgetError> {
        // Try different compression levels
        for level in &[CompressionLevel::Light, CompressionLevel::Medium, CompressionLevel::Heavy] {
            let compressed = self.compress_at_level(history, *level)?;
            let tokens = self.tokenizer.count(&compressed.text);

            if tokens <= max_tokens {
                return Ok(compressed);
            }
        }

        // Ultimate fallback: just keep last N turns
        self.keep_last_turns(history, max_tokens)
    }

    /// Prioritize entities within budget
    fn prioritize_entities(
        &self,
        entities: &[EntityContext],
        max_tokens: usize,
    ) -> Result<Vec<EntityContext>, BudgetError> {
        // Sort by relevance
        let mut sorted = entities.to_vec();
        sorted.sort_by(|a, b| b.relevance.partial_cmp(&a.relevance).unwrap());

        // Select within budget
        let mut selected = Vec::new();
        let mut total_tokens = 0;

        for entity in sorted {
            let entity_tokens = self.tokenizer.count(&entity.formatted);
            if total_tokens + entity_tokens <= max_tokens {
                selected.push(entity);
                total_tokens += entity_tokens;
            } else {
                // Try compressed version
                let compressed = self.compress_entity(&entity)?;
                let compressed_tokens = self.tokenizer.count(&compressed.formatted);
                if total_tokens + compressed_tokens <= max_tokens {
                    selected.push(compressed);
                    total_tokens += compressed_tokens;
                }
            }
        }

        Ok(selected)
    }
}
```

---

## Dialogue History Formatting

Dialogue history is formatted with summarization for longer conversations.

### History Formatter

```rust
/// Dialogue history formatter
pub struct HistoryFormatter {
    /// Summarization model
    summarizer: DialogueSummarizer,

    /// Tokenizer
    tokenizer: Tokenizer,

    /// Configuration
    config: HistoryFormatterConfig,
}

/// History formatter configuration
pub struct HistoryFormatterConfig {
    /// Number of turns to keep verbatim
    pub verbatim_turns: usize,

    /// Maximum summary length in tokens
    pub max_summary_tokens: usize,

    /// Include speaker labels
    pub include_speakers: bool,

    /// Include timestamps
    pub include_timestamps: bool,

    /// Format template
    pub template: HistoryTemplate,
}

/// Formatted dialogue history
pub struct FormattedHistory {
    /// Summary of older turns
    pub summary: Option<String>,

    /// Recent turns (verbatim)
    pub recent_turns: Vec<FormattedTurn>,

    /// Full formatted text
    pub text: String,

    /// Token count
    pub token_count: usize,
}

/// Single formatted turn
pub struct FormattedTurn {
    /// Turn ID
    pub turn_id: TurnId,

    /// Speaker label
    pub speaker: String,

    /// Turn content
    pub content: String,

    /// Formatted text
    pub formatted: String,
}

impl HistoryFormatter {
    /// Format dialogue history for context injection
    pub fn format(
        &self,
        dialogue_state: &DialogueState,
        max_tokens: usize,
    ) -> Result<FormattedHistory, FormattingError> {
        let turns: Vec<_> = dialogue_state.turns.iter().collect();

        if turns.is_empty() {
            return Ok(FormattedHistory {
                summary: None,
                recent_turns: Vec::new(),
                text: String::new(),
                token_count: 0,
            });
        }

        // Split into older and recent
        let split_point = turns.len().saturating_sub(self.config.verbatim_turns);
        let older_turns = &turns[..split_point];
        let recent_turns = &turns[split_point..];

        // Format recent turns verbatim
        let formatted_recent = self.format_recent(recent_turns)?;
        let recent_tokens = self.tokenizer.count(&formatted_recent.join("\n"));

        // Calculate remaining budget for summary
        let summary_budget = max_tokens.saturating_sub(recent_tokens + 50);

        // Summarize older turns
        let summary = if !older_turns.is_empty() && summary_budget > 50 {
            Some(self.summarize_turns(older_turns, summary_budget)?)
        } else {
            None
        };

        // Assemble full text
        let text = self.assemble_history(&summary, &formatted_recent)?;
        let token_count = self.tokenizer.count(&text);

        Ok(FormattedHistory {
            summary,
            recent_turns: self.create_formatted_turns(recent_turns)?,
            text,
            token_count,
        })
    }

    /// Format recent turns verbatim
    fn format_recent(&self, turns: &[&Turn]) -> Result<Vec<String>, FormattingError> {
        let mut formatted = Vec::new();

        for turn in turns {
            let speaker = self.format_speaker(&turn.speaker);
            let content = turn.corrected_text.as_ref()
                .unwrap_or(&turn.raw_text);

            let line = if self.config.include_timestamps {
                format!("[{}] {}: {}", turn.timestamp.format("%H:%M"), speaker, content)
            } else {
                format!("{}: {}", speaker, content)
            };

            formatted.push(line);
        }

        Ok(formatted)
    }

    /// Summarize older turns
    fn summarize_turns(
        &self,
        turns: &[&Turn],
        max_tokens: usize,
    ) -> Result<String, FormattingError> {
        // Extract key information for summarization
        let summary_input = self.prepare_for_summarization(turns)?;

        // Run summarization
        let summary = self.summarizer.summarize(&summary_input, max_tokens)?;

        // Format summary
        Ok(format!("[Conversation summary: {}]", summary))
    }

    /// Prepare turns for summarization
    fn prepare_for_summarization(
        &self,
        turns: &[&Turn],
    ) -> Result<String, FormattingError> {
        let mut lines = Vec::new();

        for turn in turns {
            let speaker = self.format_speaker(&turn.speaker);
            let content = turn.corrected_text.as_ref()
                .unwrap_or(&turn.raw_text);

            // Include key elements
            let line = format!("{}: {}", speaker, content);
            lines.push(line);

            // Add speech act context
            if let Some(speech_act) = &turn.speech_act {
                lines.push(format!("  ({})", speech_act.short_description()));
            }
        }

        Ok(lines.join("\n"))
    }

    /// Format speaker label
    fn format_speaker(&self, participant: &ParticipantId) -> String {
        match participant {
            ParticipantId::User => "User".to_string(),
            ParticipantId::Assistant => "Assistant".to_string(),
            ParticipantId::System => "System".to_string(),
            ParticipantId::Named(name) => name.clone(),
        }
    }

    /// Assemble full history text
    fn assemble_history(
        &self,
        summary: &Option<String>,
        recent: &[String],
    ) -> Result<String, FormattingError> {
        let mut parts = Vec::new();

        if let Some(summary) = summary {
            parts.push(summary.clone());
            parts.push(String::new());  // Blank line
        }

        if !recent.is_empty() {
            parts.push("Recent conversation:".to_string());
            parts.extend(recent.iter().cloned());
        }

        Ok(parts.join("\n"))
    }
}
```

---

## Entity Context Injection

Entity context provides relevant information about entities in the conversation.

### Entity Context Formatter

```rust
/// Entity context formatter
pub struct EntityContextFormatter {
    /// Entity registry reference
    entity_registry: Arc<RwLock<EntityRegistry>>,

    /// Tokenizer
    tokenizer: Tokenizer,

    /// Configuration
    config: EntityContextConfig,
}

/// Entity context configuration
pub struct EntityContextConfig {
    /// Maximum entities to include
    pub max_entities: usize,

    /// Minimum relevance threshold
    pub min_relevance: f64,

    /// Attributes to include per entity
    pub attributes_per_entity: usize,

    /// Include relationships
    pub include_relationships: bool,

    /// Format template
    pub template: EntityTemplate,
}

/// Formatted entity context
pub struct EntityContext {
    /// Entity ID
    pub entity_id: EntityId,

    /// Canonical name
    pub name: String,

    /// Entity type
    pub entity_type: String,

    /// Brief description
    pub description: String,

    /// Key attributes
    pub attributes: Vec<(String, String)>,

    /// Relationships to other entities
    pub relationships: Vec<EntityRelationship>,

    /// Relevance score
    pub relevance: f64,

    /// Formatted text
    pub formatted: String,

    /// Token count
    pub token_count: usize,
}

impl EntityContextFormatter {
    /// Format entity context for injection
    pub fn format(
        &self,
        dialogue_state: &DialogueState,
        resolved_entities: &[ResolvedEntity],
        max_tokens: usize,
    ) -> Result<Vec<EntityContext>, FormattingError> {
        // Collect entities to include
        let mut entities_to_format = Vec::new();

        // Start with resolved entities from current query
        for resolved in resolved_entities {
            if let Some(entity) = dialogue_state.entity_registry.get(&resolved.entity_id)? {
                entities_to_format.push((entity, resolved.confidence));
            }
        }

        // Add high-salience entities from dialogue
        let high_salience = dialogue_state.entity_registry
            .get_high_salience_entities(self.config.max_entities)?;

        for entity in high_salience {
            if !entities_to_format.iter().any(|(e, _)| e.id == entity.id) {
                let salience = dialogue_state.entity_registry.get_salience(&entity.id)?;
                entities_to_format.push((entity, salience * 0.7));  // Lower weight
            }
        }

        // Sort by relevance
        entities_to_format.sort_by(|a, b| b.1.partial_cmp(&a.1).unwrap());

        // Format within budget
        let mut formatted = Vec::new();
        let mut total_tokens = 0;

        for (entity, relevance) in entities_to_format {
            if relevance < self.config.min_relevance {
                continue;
            }

            let context = self.format_entity(&entity, relevance, dialogue_state)?;

            if total_tokens + context.token_count <= max_tokens {
                total_tokens += context.token_count;
                formatted.push(context);
            }

            if formatted.len() >= self.config.max_entities {
                break;
            }
        }

        Ok(formatted)
    }

    /// Format single entity
    fn format_entity(
        &self,
        entity: &Entity,
        relevance: f64,
        dialogue_state: &DialogueState,
    ) -> Result<EntityContext, FormattingError> {
        // Select key attributes
        let attributes = self.select_attributes(entity)?;

        // Get relationships if enabled
        let relationships = if self.config.include_relationships {
            self.get_relationships(entity, dialogue_state)?
        } else {
            Vec::new()
        };

        // Generate description
        let description = self.generate_description(entity, &attributes)?;

        // Format text
        let formatted = self.format_entity_text(
            &entity.canonical_name,
            &entity.entity_type,
            &description,
            &attributes,
            &relationships,
        )?;

        let token_count = self.tokenizer.count(&formatted);

        Ok(EntityContext {
            entity_id: entity.id.clone(),
            name: entity.canonical_name.clone(),
            entity_type: entity.entity_type.clone(),
            description,
            attributes,
            relationships,
            relevance,
            formatted,
            token_count,
        })
    }

    /// Select key attributes for entity
    fn select_attributes(
        &self,
        entity: &Entity,
    ) -> Result<Vec<(String, String)>, FormattingError> {
        // Prioritize common useful attributes
        let priority_attrs = ["email", "phone", "title", "department", "location"];

        let mut selected = Vec::new();

        // Add priority attributes first
        for attr_name in &priority_attrs {
            if let Some(value) = entity.get_attribute(attr_name)? {
                selected.push((attr_name.to_string(), value.value));
                if selected.len() >= self.config.attributes_per_entity {
                    return Ok(selected);
                }
            }
        }

        // Fill remaining slots with other attributes
        for (name, value) in entity.attributes.iter() {
            if !priority_attrs.contains(&name.as_str()) {
                selected.push((name.clone(), value.value.clone()));
                if selected.len() >= self.config.attributes_per_entity {
                    break;
                }
            }
        }

        Ok(selected)
    }

    /// Format entity as text
    fn format_entity_text(
        &self,
        name: &str,
        entity_type: &str,
        description: &str,
        attributes: &[(String, String)],
        relationships: &[EntityRelationship],
    ) -> Result<String, FormattingError> {
        let mut lines = Vec::new();

        // Name and type
        lines.push(format!("• {} ({})", name, entity_type));

        // Description
        if !description.is_empty() {
            lines.push(format!("  {}", description));
        }

        // Attributes
        for (attr_name, attr_value) in attributes {
            lines.push(format!("  {}: {}", attr_name, attr_value));
        }

        // Relationships
        if !relationships.is_empty() {
            let rel_str: Vec<_> = relationships
                .iter()
                .map(|r| format!("{} {}", r.relation, r.target_name))
                .collect();
            lines.push(format!("  Related: {}", rel_str.join(", ")));
        }

        Ok(lines.join("\n"))
    }
}
```

---

## RAG Integration

Retrieval-Augmented Generation (RAG) injects relevant knowledge from external sources.

### RAG System

```rust
/// RAG integration system
pub struct RAGSystem {
    /// Embedding model
    embedder: EmbeddingModel,

    /// Vector index
    vector_index: VectorIndex,

    /// Document store
    document_store: DocumentStore,

    /// Reranker
    reranker: CrossEncoderReranker,

    /// Tokenizer
    tokenizer: Tokenizer,

    /// Configuration
    config: RAGConfig,
}

/// RAG configuration
pub struct RAGConfig {
    /// Maximum chunks to retrieve initially
    pub initial_retrieval_count: usize,

    /// Maximum chunks after reranking
    pub final_chunk_count: usize,

    /// Minimum relevance threshold
    pub min_relevance: f64,

    /// Enable reranking
    pub enable_reranking: bool,

    /// Recency weight (0-1)
    pub recency_weight: f64,

    /// Entity overlap weight (0-1)
    pub entity_weight: f64,
}

/// Retrieved knowledge chunk
pub struct KnowledgeChunk {
    /// Chunk ID
    pub chunk_id: ChunkId,

    /// Source document
    pub source: DocumentSource,

    /// Chunk content
    pub content: String,

    /// Relevance score
    pub relevance: f64,

    /// Token count
    pub token_count: usize,

    /// Formatted for injection
    pub formatted: String,
}

/// Document source information
pub struct DocumentSource {
    /// Document ID
    pub doc_id: DocumentId,

    /// Document title
    pub title: String,

    /// Source URL (if applicable)
    pub url: Option<String>,

    /// Document date
    pub date: Option<DateTime<Utc>>,

    /// Document type
    pub doc_type: DocumentType,
}

impl RAGSystem {
    /// Retrieve relevant knowledge for query
    pub fn retrieve(
        &self,
        query: &str,
        entities: &[ResolvedEntity],
        max_tokens: usize,
    ) -> Result<Vec<KnowledgeChunk>, RAGError> {
        // Generate query embedding
        let query_embedding = self.embedder.embed(query)?;

        // Initial retrieval
        let candidates = self.vector_index.search(
            &query_embedding,
            self.config.initial_retrieval_count,
        )?;

        // Apply filters and boosts
        let filtered = self.apply_boosts(candidates, entities)?;

        // Rerank if enabled
        let ranked = if self.config.enable_reranking {
            self.reranker.rerank(query, filtered)?
        } else {
            filtered
        };

        // Filter by relevance threshold
        let relevant: Vec<_> = ranked
            .into_iter()
            .filter(|c| c.relevance >= self.config.min_relevance)
            .take(self.config.final_chunk_count)
            .collect();

        // Format and select within token budget
        self.select_within_budget(relevant, max_tokens)
    }

    /// Apply boosts for recency and entity overlap
    fn apply_boosts(
        &self,
        candidates: Vec<SearchResult>,
        entities: &[ResolvedEntity],
    ) -> Result<Vec<SearchResult>, RAGError> {
        let now = Utc::now();
        let entity_names: HashSet<_> = entities.iter()
            .map(|e| e.canonical_name.to_lowercase())
            .collect();

        let mut boosted = candidates;

        for candidate in &mut boosted {
            // Recency boost
            if let Some(date) = &candidate.document_date {
                let days_old = (now - *date).num_days() as f64;
                let recency_factor = (-days_old / 365.0).exp();  // Decay over year
                candidate.relevance += self.config.recency_weight * recency_factor * 0.2;
            }

            // Entity overlap boost
            let chunk = self.document_store.get_chunk(&candidate.chunk_id)?;
            let chunk_lower = chunk.content.to_lowercase();

            let overlap_count = entity_names
                .iter()
                .filter(|name| chunk_lower.contains(name.as_str()))
                .count();

            if overlap_count > 0 {
                let overlap_factor = (overlap_count as f64 / entity_names.len() as f64).min(1.0);
                candidate.relevance += self.config.entity_weight * overlap_factor * 0.3;
            }
        }

        // Re-sort by adjusted relevance
        boosted.sort_by(|a, b| b.relevance.partial_cmp(&a.relevance).unwrap());

        Ok(boosted)
    }

    /// Select chunks within token budget
    fn select_within_budget(
        &self,
        chunks: Vec<SearchResult>,
        max_tokens: usize,
    ) -> Result<Vec<KnowledgeChunk>, RAGError> {
        let mut selected = Vec::new();
        let mut total_tokens = 0;

        for result in chunks {
            let chunk = self.document_store.get_chunk(&result.chunk_id)?;
            let formatted = self.format_chunk(&chunk, &result.source)?;
            let token_count = self.tokenizer.count(&formatted);

            if total_tokens + token_count <= max_tokens {
                selected.push(KnowledgeChunk {
                    chunk_id: result.chunk_id,
                    source: result.source,
                    content: chunk.content,
                    relevance: result.relevance,
                    token_count,
                    formatted,
                });
                total_tokens += token_count;
            }
        }

        Ok(selected)
    }

    /// Format chunk for injection
    fn format_chunk(
        &self,
        chunk: &Chunk,
        source: &DocumentSource,
    ) -> Result<String, RAGError> {
        let mut lines = Vec::new();

        // Source header
        let mut header = format!("Source: {}", source.title);
        if let Some(date) = &source.date {
            header.push_str(&format!(" ({})", date.format("%Y-%m-%d")));
        }
        lines.push(header);

        // Separator
        lines.push("---".to_string());

        // Content
        lines.push(chunk.content.clone());

        // End separator
        lines.push("---".to_string());

        Ok(lines.join("\n"))
    }
}
```

### Knowledge Base Indexing

```rust
/// Knowledge base for RAG
pub struct KnowledgeBase {
    /// Document store
    document_store: DocumentStore,

    /// Vector index
    vector_index: VectorIndex,

    /// Embedding model
    embedder: EmbeddingModel,

    /// Chunking strategy
    chunker: DocumentChunker,
}

impl KnowledgeBase {
    /// Index a new document
    pub fn index_document(
        &mut self,
        document: Document,
    ) -> Result<DocumentId, KBError> {
        // Generate document ID
        let doc_id = DocumentId::new();

        // Chunk the document
        let chunks = self.chunker.chunk(&document)?;

        // Store document metadata
        self.document_store.store_document(&doc_id, &document)?;

        // Index each chunk
        for (idx, chunk) in chunks.iter().enumerate() {
            let chunk_id = ChunkId::new(&doc_id, idx);

            // Generate embedding
            let embedding = self.embedder.embed(&chunk.content)?;

            // Store chunk
            self.document_store.store_chunk(&chunk_id, chunk)?;

            // Add to vector index
            self.vector_index.add(&chunk_id, &embedding)?;
        }

        Ok(doc_id)
    }

    /// Update existing document
    pub fn update_document(
        &mut self,
        doc_id: &DocumentId,
        document: Document,
    ) -> Result<(), KBError> {
        // Remove old chunks
        self.remove_document_chunks(doc_id)?;

        // Re-index
        let chunks = self.chunker.chunk(&document)?;
        self.document_store.update_document(doc_id, &document)?;

        for (idx, chunk) in chunks.iter().enumerate() {
            let chunk_id = ChunkId::new(doc_id, idx);
            let embedding = self.embedder.embed(&chunk.content)?;
            self.document_store.store_chunk(&chunk_id, chunk)?;
            self.vector_index.add(&chunk_id, &embedding)?;
        }

        Ok(())
    }
}
```

---

## System Prompt Assembly

The system prompt sets the agent's behavior and incorporates user preferences.

### System Prompt Builder

```rust
/// System prompt builder
pub struct SystemPromptBuilder {
    /// Base system instructions
    base_instructions: String,

    /// User preferences
    user_preferences: Option<UserPreferences>,

    /// Agent personality
    agent_personality: AgentPersonality,

    /// Tokenizer
    tokenizer: Tokenizer,
}

/// User preferences for response style
pub struct UserPreferences {
    /// Communication style
    pub style: CommunicationStyle,

    /// Verbosity level
    pub verbosity: Verbosity,

    /// Technical level
    pub technical_level: TechnicalLevel,

    /// Formatting preferences
    pub formatting: FormattingPreferences,

    /// Custom instructions
    pub custom_instructions: Vec<String>,
}

/// Communication style
pub enum CommunicationStyle {
    Formal,
    Professional,
    Casual,
    Friendly,
}

/// Verbosity level
pub enum Verbosity {
    Concise,
    Moderate,
    Detailed,
}

/// Technical level
pub enum TechnicalLevel {
    Beginner,
    Intermediate,
    Expert,
}

/// Formatting preferences
pub struct FormattingPreferences {
    /// Use bullet points
    pub use_bullets: bool,

    /// Use numbered lists
    pub use_numbered_lists: bool,

    /// Include code blocks
    pub include_code_blocks: bool,

    /// Include links
    pub include_links: bool,
}

impl SystemPromptBuilder {
    /// Build system prompt
    pub fn build(&self, max_tokens: usize) -> Result<String, BuildError> {
        let mut parts = Vec::new();

        // Base instructions
        parts.push(self.base_instructions.clone());

        // Personality traits
        let personality = self.format_personality();
        parts.push(personality);

        // User preferences
        if let Some(prefs) = &self.user_preferences {
            let pref_text = self.format_preferences(prefs);
            parts.push(pref_text);
        }

        // Combine and check length
        let combined = parts.join("\n\n");
        let tokens = self.tokenizer.count(&combined);

        if tokens <= max_tokens {
            Ok(combined)
        } else {
            // Truncate preferences first
            self.truncate_system_prompt(&parts, max_tokens)
        }
    }

    /// Format agent personality
    fn format_personality(&self) -> String {
        match &self.agent_personality {
            AgentPersonality::Helpful => {
                "You are a helpful assistant. Be accurate, concise, and helpful.".to_string()
            }
            AgentPersonality::Expert { domain } => {
                format!(
                    "You are an expert assistant specializing in {}. \
                     Provide detailed, accurate information.",
                    domain
                )
            }
            AgentPersonality::Conversational => {
                "You are a friendly conversational assistant. \
                 Be engaging and natural in your responses.".to_string()
            }
            AgentPersonality::Custom { description } => description.clone(),
        }
    }

    /// Format user preferences
    fn format_preferences(&self, prefs: &UserPreferences) -> String {
        let mut instructions = Vec::new();

        // Communication style
        let style_instruction = match prefs.style {
            CommunicationStyle::Formal => "Use formal language.",
            CommunicationStyle::Professional => "Be professional and clear.",
            CommunicationStyle::Casual => "Use casual, conversational language.",
            CommunicationStyle::Friendly => "Be warm and friendly.",
        };
        instructions.push(style_instruction.to_string());

        // Verbosity
        let verbosity_instruction = match prefs.verbosity {
            Verbosity::Concise => "Keep responses brief and to the point.",
            Verbosity::Moderate => "Provide balanced, moderate-length responses.",
            Verbosity::Detailed => "Provide comprehensive, detailed responses.",
        };
        instructions.push(verbosity_instruction.to_string());

        // Technical level
        let tech_instruction = match prefs.technical_level {
            TechnicalLevel::Beginner => "Explain concepts simply, avoiding jargon.",
            TechnicalLevel::Intermediate => "Use appropriate technical terms with brief explanations.",
            TechnicalLevel::Expert => "Use technical language freely.",
        };
        instructions.push(tech_instruction.to_string());

        // Formatting
        if prefs.formatting.use_bullets {
            instructions.push("Use bullet points for lists.".to_string());
        }
        if prefs.formatting.use_numbered_lists {
            instructions.push("Use numbered lists for sequential steps.".to_string());
        }

        // Custom instructions
        instructions.extend(prefs.custom_instructions.iter().cloned());

        format!("User preferences:\n{}", instructions.join("\n"))
    }
}
```

---

## Dynamic Compression

When content exceeds the token budget, dynamic compression reduces it intelligently.

### Compression Strategies

```rust
/// Dynamic compression system
pub struct DynamicCompressor {
    /// Summarization model
    summarizer: Summarizer,

    /// Tokenizer
    tokenizer: Tokenizer,

    /// Configuration
    config: CompressionConfig,
}

/// Compression level
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum CompressionLevel {
    /// Light: Remove redundancy, keep most detail
    Light,

    /// Medium: Summarize older content
    Medium,

    /// Heavy: Aggressive summarization
    Heavy,

    /// Extreme: Only essential information
    Extreme,
}

impl DynamicCompressor {
    /// Compress content to fit token budget
    pub fn compress(
        &self,
        content: &ContextContent,
        target_tokens: usize,
    ) -> Result<ContextContent, CompressionError> {
        let current_tokens = content.total_tokens();

        if current_tokens <= target_tokens {
            return Ok(content.clone());
        }

        // Calculate required reduction
        let reduction_needed = current_tokens - target_tokens;
        let reduction_ratio = reduction_needed as f64 / current_tokens as f64;

        // Determine compression level
        let level = if reduction_ratio < 0.2 {
            CompressionLevel::Light
        } else if reduction_ratio < 0.4 {
            CompressionLevel::Medium
        } else if reduction_ratio < 0.6 {
            CompressionLevel::Heavy
        } else {
            CompressionLevel::Extreme
        };

        self.compress_at_level(content, level, target_tokens)
    }

    /// Compress at specific level
    fn compress_at_level(
        &self,
        content: &ContextContent,
        level: CompressionLevel,
        target_tokens: usize,
    ) -> Result<ContextContent, CompressionError> {
        let mut compressed = content.clone();

        match level {
            CompressionLevel::Light => {
                // Remove redundant whitespace, simplify formatting
                compressed.history = self.simplify_formatting(&compressed.history)?;
                compressed.rag_chunks = self.deduplicate_chunks(&compressed.rag_chunks)?;
            }

            CompressionLevel::Medium => {
                // Summarize older history turns
                compressed.history = self.summarize_older_turns(&compressed.history)?;

                // Reduce entity context
                compressed.entities = self.reduce_entity_detail(&compressed.entities)?;

                // Select fewer RAG chunks
                compressed.rag_chunks = self.select_top_chunks(&compressed.rag_chunks, 3)?;
            }

            CompressionLevel::Heavy => {
                // Aggressive summarization
                compressed.history = self.aggressive_summarize(&compressed.history)?;

                // Only most relevant entities
                compressed.entities = self.keep_top_entities(&compressed.entities, 3)?;

                // Minimal RAG
                compressed.rag_chunks = self.select_top_chunks(&compressed.rag_chunks, 2)?;
            }

            CompressionLevel::Extreme => {
                // Essential information only
                compressed.history = self.extract_essential(&compressed.history)?;
                compressed.entities = self.keep_top_entities(&compressed.entities, 1)?;
                compressed.rag_chunks = self.select_top_chunks(&compressed.rag_chunks, 1)?;
            }
        }

        // Verify we're within budget
        let new_tokens = compressed.total_tokens();
        if new_tokens > target_tokens && level < CompressionLevel::Extreme {
            // Recurse with higher compression
            let next_level = match level {
                CompressionLevel::Light => CompressionLevel::Medium,
                CompressionLevel::Medium => CompressionLevel::Heavy,
                CompressionLevel::Heavy => CompressionLevel::Extreme,
                CompressionLevel::Extreme => return Err(CompressionError::CannotCompress),
            };
            return self.compress_at_level(&compressed, next_level, target_tokens);
        }

        Ok(compressed)
    }

    /// Summarize older turns aggressively
    fn aggressive_summarize(
        &self,
        history: &FormattedHistory,
    ) -> Result<FormattedHistory, CompressionError> {
        // Keep only last turn verbatim
        let last_turn = history.recent_turns.last().cloned();

        // Summarize everything else into one line
        let summary_input = if let Some(existing_summary) = &history.summary {
            format!(
                "{}\n{}",
                existing_summary,
                history.recent_turns[..history.recent_turns.len() - 1]
                    .iter()
                    .map(|t| t.formatted.as_str())
                    .collect::<Vec<_>>()
                    .join("\n")
            )
        } else {
            history.recent_turns[..history.recent_turns.len() - 1]
                .iter()
                .map(|t| t.formatted.as_str())
                .collect::<Vec<_>>()
                .join("\n")
        };

        let summary = self.summarizer.summarize(&summary_input, 100)?;

        let text = if let Some(turn) = &last_turn {
            format!("[Summary: {}]\n\n{}", summary, turn.formatted)
        } else {
            format!("[Summary: {}]", summary)
        };

        let token_count = self.tokenizer.count(&text);

        Ok(FormattedHistory {
            summary: Some(summary),
            recent_turns: last_turn.into_iter().collect(),
            text,
            token_count,
        })
    }
}
```

---

## Implementation

### Full Context Injection Example

```rust
/// Example: Full context injection pipeline
pub async fn inject_context(
    query: &str,
    session: &Session,
    max_tokens: usize,
) -> Result<InjectedContext, Error> {
    // Get dialogue state
    let dialogue_state = session.dialogue_state.read().await;

    // Resolve entities from query
    let resolved_entities = session.entity_resolver.resolve(
        query,
        &dialogue_state,
    )?;

    // Initialize budget manager
    let budget_manager = TokenBudgetManager::new(
        max_tokens,
        session.tokenizer.clone(),
        AllocationStrategy::Dynamic,
    );

    // Calculate token budget
    let budget = budget_manager.allocate(
        query,
        &dialogue_state,
        session.rag_system.available_chunks(),
    );

    // Format dialogue history
    let history = session.history_formatter.format(
        &dialogue_state,
        budget.history,
    )?;

    // Format entity context
    let entities = session.entity_formatter.format(
        &dialogue_state,
        &resolved_entities,
        budget.entities,
    )?;

    // Retrieve RAG chunks
    let rag_chunks = session.rag_system.retrieve(
        query,
        &resolved_entities,
        budget.rag,
    )?;

    // Build system prompt
    let system_prompt = session.system_builder.build(budget.system)?;

    // Assemble full context
    let context_content = ContextContent {
        system: system_prompt,
        history,
        entities,
        rag_chunks,
    };

    // Compress if needed
    let final_content = if context_content.total_tokens() > max_tokens {
        session.compressor.compress(&context_content, max_tokens)?
    } else {
        context_content
    };

    // Format for prompt
    let formatted = session.prompt_formatter.format(&final_content)?;

    Ok(InjectedContext {
        content: final_content,
        formatted,
        token_count: session.tokenizer.count(&formatted),
    })
}
```

---

## MeTTa Predicates

```metta
; Core context injection predicates
(: inject-context (-> String DialogueState KnowledgeBase Int InjectedContext))
(: allocate-token-budget (-> String DialogueState Int TokenBudget))
(: format-dialogue-history (-> DialogueState Int FormattedHistory))
(: format-entity-context (-> DialogueState (List ResolvedEntity) Int (List EntityContext)))
(: retrieve-rag-chunks (-> String (List ResolvedEntity) Int (List KnowledgeChunk)))
(: build-system-prompt (-> UserPreferences AgentPersonality Int String))

; Token budget predicates
(: total-tokens (-> ContextContent Int))
(: handle-overflow (-> ContextContent TokenBudget ContextContent))
(: compress-content (-> ContextContent Int ContextContent))
(: compression-level (-> Float CompressionLevel))

; History formatting predicates
(: summarize-turns (-> (List Turn) Int String))
(: format-recent-turns (-> (List Turn) (List FormattedTurn)))
(: assemble-history (-> (Maybe String) (List FormattedTurn) String))

; Entity context predicates
(: select-entity-attributes (-> Entity Int (List (Pair String String))))
(: get-entity-relationships (-> Entity DialogueState (List EntityRelationship)))
(: format-entity (-> Entity Float (List (Pair String String)) EntityContext))

; RAG predicates
(: embed-query (-> String (List Float)))
(: search-vector-index (-> (List Float) Int (List SearchResult)))
(: apply-rag-boosts (-> (List SearchResult) (List ResolvedEntity) (List SearchResult)))
(: rerank-chunks (-> String (List SearchResult) (List SearchResult)))
(: format-chunk (-> Chunk DocumentSource String))

; System prompt predicates
(: format-personality (-> AgentPersonality String))
(: format-preferences (-> UserPreferences String))
(: truncate-system-prompt (-> (List String) Int String))

; Compression predicates
(: simplify-formatting (-> FormattedHistory FormattedHistory))
(: aggressive-summarize (-> FormattedHistory FormattedHistory))
(: reduce-entity-detail (-> (List EntityContext) (List EntityContext)))
(: select-top-chunks (-> (List KnowledgeChunk) Int (List KnowledgeChunk)))
```

---

## PathMap Schema

```
PathMap Key Structure:
=======================

/context/{session_id}/{turn_id}/
    /budget/
        total               → Total token budget
        system              → System prompt tokens
        history             → History tokens
        entities            → Entity context tokens
        rag                 → RAG tokens
        query               → Query tokens
        strategy            → Allocation strategy used

    /history/
        summary             → Summary text (if any)
        summary_tokens      → Summary token count
        verbatim_count      → Number of verbatim turns
        total_tokens        → Total history tokens
        compressed          → Whether compression applied
        compression_level   → Compression level (if applied)
        /turns/
            /{turn_idx}/
                turn_id     → Original turn ID
                speaker     → Speaker label
                content     → Turn content
                tokens      → Token count

    /entities/
        count               → Number of entities included
        total_tokens        → Total entity tokens
        /{entity_idx}/
            entity_id       → Entity ID
            name            → Canonical name
            type            → Entity type
            relevance       → Relevance score
            tokens          → Token count
            /attributes/    → Included attributes

    /rag/
        query_used          → Query used for retrieval
        chunks_retrieved    → Initial retrieval count
        chunks_selected     → Final selection count
        reranking_used      → Whether reranking applied
        total_tokens        → Total RAG tokens
        /chunks/
            /{chunk_idx}/
                chunk_id    → Chunk ID
                doc_title   → Source document title
                relevance   → Relevance score
                tokens      → Token count

    /system/
        base_instructions   → Base instruction text
        personality         → Agent personality type
        user_preferences    → Formatted user preferences
        total_tokens        → System prompt tokens

    /assembled/
        full_prompt         → Complete assembled prompt
        total_tokens        → Total tokens
        under_budget        → Whether within budget
```

---

## Related Documentation

- [LLM Integration Overview](./README.md) - Layer architecture
- [Prompt Preprocessing](./01-prompt-preprocessing.md) - Full preprocessing pipeline
- [Output Postprocessing](./02-output-postprocessing.md) - Response validation
- [Hallucination Detection](./03-hallucination-detection.md) - Detection algorithms
- [Dialogue Context](../dialogue/README.md) - Turn and entity tracking
- [Coreference Resolution](../dialogue/02-coreference-resolution.md) - Entity registry

---

## References

- Lewis, P. et al. (2020). "Retrieval-Augmented Generation for Knowledge-Intensive NLP Tasks"
- Guu, K. et al. (2020). "REALM: Retrieval-Augmented Language Model Pre-Training"
- Izacard, G. & Grave, E. (2021). "Leveraging Passage Retrieval with Generative Models"
- Karpukhin, V. et al. (2020). "Dense Passage Retrieval for Open-Domain QA"
- Borgeaud, S. et al. (2022). "Improving Language Models by Retrieving from Trillions of Tokens"
- Xu, P. et al. (2023). "Retrieval Meets Long Context Large Language Models"
