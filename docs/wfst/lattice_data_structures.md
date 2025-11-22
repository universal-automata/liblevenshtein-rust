# Lattice Data Structures: Technical Reference

## Table of Contents

1. [Overview](#overview)
2. [Core Data Structures](#core-data-structures)
3. [Graph Representation](#graph-representation)
4. [Chart Data Structures](#chart-data-structures)
5. [Parse Forest Representation](#parse-forest-representation)
6. [Memory Layout and Optimization](#memory-layout-and-optimization)
7. [Algorithms](#algorithms)
8. [API Reference](#api-reference)

---

## Overview

This document provides detailed technical specifications for the data structures used in lattice parsing within liblevenshtein-rust. It complements [lattice_parsing.md](./lattice_parsing.md) by focusing on implementation details rather than pedagogical exposition.

### Design Goals

1. **Memory efficiency**: Minimize memory overhead for large lattices (10K+ edges)
2. **Cache locality**: Optimize for CPU cache performance
3. **Zero-copy**: Avoid unnecessary cloning/copying
4. **Type safety**: Leverage Rust's type system for correctness
5. **Interoperability**: Seamless integration with FST and CFG layers

### Dependencies

```toml
[dependencies]
# Core data structures
indexmap = "2.0"        # Order-preserving hash maps
smallvec = "1.11"       # Stack-allocated small vectors
bitvec = "1.0"          # Compact bit vectors
ahash = "0.8"           # Fast hashing

# Optional: serialization
serde = { version = "1.0", optional = true, features = ["derive"] }
bincode = { version = "1.3", optional = true }
```

---

## Core Data Structures

### Lattice

The top-level lattice structure represents a weighted DAG of word transitions.

```rust
use std::sync::Arc;
use indexmap::IndexMap;
use smallvec::SmallVec;

/// Lattice: weighted DAG representing multiple candidate sentences
#[derive(Clone, Debug)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Lattice {
    /// Nodes: positions between words
    pub(crate) nodes: Vec<Node>,

    /// Edges: word transitions with weights
    pub(crate) edges: Vec<Edge>,

    /// Start node (unique source)
    pub(crate) start: NodeId,

    /// End node (unique sink)
    pub(crate) end: NodeId,

    /// Vocabulary: deduplicated word strings (Arc for sharing)
    pub(crate) vocab: IndexMap<Arc<str>, VocabId>,

    /// Metadata
    pub(crate) metadata: LatticeMetadata,
}

/// Metadata for lattice provenance and statistics
#[derive(Clone, Debug, Default)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct LatticeMetadata {
    /// Original input query
    pub input: String,

    /// Max Levenshtein distance used in FST
    pub max_distance: usize,

    /// Dictionary size
    pub dictionary_size: usize,

    /// Statistics
    pub path_count: Option<usize>,  // Cached path count (expensive to compute)
    pub avg_path_length: Option<f64>,
}

impl Lattice {
    /// Number of nodes
    #[inline]
    pub fn node_count(&self) -> usize {
        self.nodes.len()
    }

    /// Number of edges
    #[inline]
    pub fn edge_count(&self) -> usize {
        self.edges.len()
    }

    /// Get node by ID
    #[inline]
    pub fn node(&self, id: NodeId) -> &Node {
        &self.nodes[id.0]
    }

    /// Get edge by ID
    #[inline]
    pub fn edge(&self, id: EdgeId) -> &Edge {
        &self.edges[id.0]
    }

    /// Get word string from vocabulary ID
    #[inline]
    pub fn word(&self, vid: VocabId) -> &str {
        self.vocab.get_index(vid.0).unwrap().0
    }

    /// Iterator over all paths (lazy, depth-first)
    pub fn paths(&self) -> PathIterator<'_> {
        PathIterator::new(self)
    }

    /// Count total paths (dynamic programming, O(V+E))
    pub fn path_count(&mut self) -> usize {
        if let Some(count) = self.metadata.path_count {
            return count;
        }

        let count = algorithms::path_count_dp(self);
        self.metadata.path_count = Some(count);
        count
    }

    /// Topological ordering of nodes
    pub fn topological_order(&self) -> Vec<NodeId> {
        algorithms::topological_sort(self)
    }

    /// Check if lattice is acyclic (DAG property)
    pub fn is_acyclic(&self) -> bool {
        algorithms::is_acyclic(self)
    }
}
```

### Node

Represents a position between words in the lattice.

```rust
/// Node ID (newtype for type safety)
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct NodeId(pub usize);

/// Node: position in lattice with incoming/outgoing edges
#[derive(Clone, Debug)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Node {
    /// Unique identifier
    pub id: NodeId,

    /// Outgoing edges (typically 1-10 edges)
    /// SmallVec avoids heap allocation for common case
    pub outgoing: SmallVec<[EdgeId; 8]>,

    /// Incoming edges (typically 1-10 edges)
    pub incoming: SmallVec<[EdgeId; 8]>,

    /// Optional position hint in original input (for debugging)
    pub position: Option<usize>,
}

impl Node {
    /// Create new node with ID
    pub fn new(id: NodeId) -> Self {
        Self {
            id,
            outgoing: SmallVec::new(),
            incoming: SmallVec::new(),
            position: None,
        }
    }

    /// Add outgoing edge
    #[inline]
    pub fn add_outgoing(&mut self, edge: EdgeId) {
        self.outgoing.push(edge);
    }

    /// Add incoming edge
    #[inline]
    pub fn add_incoming(&mut self, edge: EdgeId) {
        self.incoming.push(edge);
    }

    /// Check if this is a source node (no incoming edges)
    #[inline]
    pub fn is_source(&self) -> bool {
        self.incoming.is_empty()
    }

    /// Check if this is a sink node (no outgoing edges)
    #[inline]
    pub fn is_sink(&self) -> bool {
        self.outgoing.is_empty()
    }

    /// Out-degree (number of outgoing edges)
    #[inline]
    pub fn out_degree(&self) -> usize {
        self.outgoing.len()
    }

    /// In-degree (number of incoming edges)
    #[inline]
    pub fn in_degree(&self) -> usize {
        self.incoming.len()
    }
}
```

### Edge

Represents a word transition between two nodes.

```rust
/// Edge ID (newtype for type safety)
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct EdgeId(pub usize);

/// Vocabulary ID (index into deduplicated vocabulary)
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct VocabId(pub usize);

/// Edge: word transition from source to target node
#[derive(Clone, Debug)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Edge {
    /// Unique identifier
    pub id: EdgeId,

    /// Source node
    pub source: NodeId,

    /// Target node
    pub target: NodeId,

    /// Word label (vocabulary ID for deduplication)
    pub label: VocabId,

    /// Weight/probability (for PCFG)
    /// Typically: 1.0 / (1.0 + levenshtein_distance)
    pub weight: f32,  // f32 for memory efficiency

    /// Optional metadata
    pub metadata: EdgeMetadata,
}

/// Edge metadata (optional information)
#[derive(Clone, Debug, Default)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct EdgeMetadata {
    /// Levenshtein distance from original token
    pub distance: Option<u8>,  // u8 sufficient for typical distances

    /// Was this edge from phonetic matching?
    pub is_phonetic: bool,

    /// FST rule that produced this correction (for debugging)
    pub rule_id: Option<usize>,
}

impl Edge {
    /// Create new edge
    pub fn new(
        id: EdgeId,
        source: NodeId,
        target: NodeId,
        label: VocabId,
        weight: f32,
    ) -> Self {
        Self {
            id,
            source,
            target,
            label,
            weight,
            metadata: EdgeMetadata::default(),
        }
    }

    /// Check if this is an epsilon (empty) edge
    #[inline]
    pub fn is_epsilon(&self, lattice: &Lattice) -> bool {
        lattice.word(self.label).is_empty()
    }
}
```

---

## Graph Representation

### Adjacency List

The lattice uses an **adjacency list** representation optimized for sparse graphs:

```
Memory layout:

nodes: [Node₀, Node₁, ..., Nodeₙ]
          ↓       ↓
       outgoing incoming
         [E₁,E₂] [E₃]

edges: [Edge₀, Edge₁, ..., Edgeₘ]
          ↓
       (src, tgt, label, weight)
```

**Space complexity**: O(|V| + |E|)

**Access patterns**:
- Forward traversal (following edges): O(1) via `node.outgoing`
- Backward traversal (predecessors): O(1) via `node.incoming`
- Random edge access: O(1) via `lattice.edge(edge_id)`

### Alternative: Adjacency Matrix

For dense lattices (not typical), adjacency matrix may be more efficient:

```rust
/// Dense lattice representation (not recommended for most use cases)
pub struct DenseLattice {
    /// Adjacency matrix: adj[i][j] = Some(edge_id) if edge exists
    adj: Vec<Vec<Option<EdgeId>>>,

    /// Edges (same as sparse representation)
    edges: Vec<Edge>,

    /// Vocabulary
    vocab: IndexMap<Arc<str>, VocabId>,
}
```

**Space complexity**: O(|V|²)

**Trade-offs**:
- Pro: O(1) edge existence check
- Con: Wasteful for sparse graphs (typical K=5-10 branching factor)
- Con: Poor cache locality

**Recommendation**: Use adjacency list (Lattice) unless |E| ≈ |V|² (very dense)

---

## Chart Data Structures

The Earley chart stores parse states indexed by `(node, position)` tuples.

### EarleyChart

```rust
use ahash::AHashMap as HashMap;
use std::collections::HashSet;

/// Earley chart: maps (node, position) to set of parse states
pub struct EarleyChart {
    /// Main chart storage
    /// Key: (current_node, dot_position)
    /// Value: set of Earley states at this chart position
    states: HashMap<(NodeId, usize), HashSet<EarleyState>>,

    /// Completed states cache (for Completer operation)
    /// Key: (lhs_non_terminal, start_node, end_node)
    /// Value: derivations for this non-terminal span
    completed: HashMap<(NonTerminal, NodeId, NodeId), Vec<Derivation>>,

    /// Statistics
    pub stats: ChartStatistics,
}

/// Chart statistics for profiling
#[derive(Clone, Debug, Default)]
pub struct ChartStatistics {
    /// Total states created
    pub states_created: usize,

    /// States reused from cache
    pub states_reused: usize,

    /// Predictor operations
    pub predictor_calls: usize,

    /// Scanner operations
    pub scanner_calls: usize,

    /// Completer operations
    pub completer_calls: usize,

    /// Peak memory usage (bytes)
    pub peak_memory: usize,
}

impl EarleyChart {
    /// Create new empty chart
    pub fn new() -> Self {
        Self {
            states: HashMap::default(),
            completed: HashMap::default(),
            stats: ChartStatistics::default(),
        }
    }

    /// Add state to chart
    pub fn add_state(&mut self, state: EarleyState) -> bool {
        let key = (state.current_node, state.dot_position);
        let inserted = self.states
            .entry(key)
            .or_insert_with(HashSet::new)
            .insert(state);

        if inserted {
            self.stats.states_created += 1;
        } else {
            self.stats.states_reused += 1;
        }

        inserted
    }

    /// Get all states at (node, position)
    pub fn states_at(&self, node: NodeId, position: usize) -> Option<&HashSet<EarleyState>> {
        self.states.get(&(node, position))
    }

    /// Get mutable states at (node, position)
    pub fn states_at_mut(&mut self, node: NodeId, position: usize)
        -> &mut HashSet<EarleyState>
    {
        self.states
            .entry((node, position))
            .or_insert_with(HashSet::new)
    }

    /// Cache completed derivation
    pub fn cache_completed(&mut self,
                           lhs: NonTerminal,
                           start: NodeId,
                           end: NodeId,
                           derivations: Vec<Derivation>) {
        self.completed.insert((lhs, start, end), derivations);
    }

    /// Get cached completed derivation
    pub fn get_completed(&self,
                         lhs: NonTerminal,
                         start: NodeId,
                         end: NodeId) -> Option<&Vec<Derivation>> {
        self.completed.get(&(lhs, start, end))
    }

    /// Check if chart contains accepting state
    pub fn accepts(&self, end_node: NodeId, grammar: &Grammar) -> bool {
        if let Some(states) = self.states_at(end_node, 0) {
            states.iter().any(|s|
                s.is_complete() &&
                s.lhs() == grammar.start_symbol() &&
                s.current_node == end_node
            )
        } else {
            false
        }
    }

    /// Estimate memory usage (bytes)
    pub fn memory_usage(&self) -> usize {
        let states_size = self.states.len() *
            (std::mem::size_of::<(NodeId, usize)>() +
             std::mem::size_of::<HashSet<EarleyState>>());

        let completed_size = self.completed.len() *
            std::mem::size_of::<(NonTerminal, NodeId, NodeId)>();

        states_size + completed_size
    }
}
```

### EarleyState

Represents a partially parsed production rule.

```rust
/// Earley state: [A → α • β, start_node, current_node]
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct EarleyState {
    /// Production rule being parsed
    pub rule: RuleId,

    /// Position of dot (•) in rule RHS
    pub dot_position: usize,

    /// Start node in lattice where this rule began
    pub start_node: NodeId,

    /// Current node in lattice
    pub current_node: NodeId,

    /// Backpointers for parse tree reconstruction
    pub backpointers: SmallVec<[BackPointer; 2]>,

    /// Probability (for PCFG)
    pub probability: f32,
}

/// Backpointer for parse tree reconstruction
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct BackPointer {
    /// Non-terminal that was completed
    pub non_terminal: NonTerminal,

    /// Node where this non-terminal started
    pub start_node: NodeId,

    /// Node where this non-terminal ended
    pub end_node: NodeId,
}

impl EarleyState {
    /// Create new state
    pub fn new(
        rule: RuleId,
        start_node: NodeId,
        current_node: NodeId,
    ) -> Self {
        Self {
            rule,
            dot_position: 0,
            start_node,
            current_node,
            backpointers: SmallVec::new(),
            probability: 1.0,
        }
    }

    /// Check if dot is at end (completed state)
    #[inline]
    pub fn is_complete(&self, grammar: &Grammar) -> bool {
        let rhs = grammar.rule(self.rule).rhs();
        self.dot_position >= rhs.len()
    }

    /// Get symbol after dot (• symbol)
    #[inline]
    pub fn next_symbol(&self, grammar: &Grammar) -> Option<Symbol> {
        let rhs = grammar.rule(self.rule).rhs();
        rhs.get(self.dot_position).copied()
    }

    /// Get LHS non-terminal of this rule
    #[inline]
    pub fn lhs(&self, grammar: &Grammar) -> NonTerminal {
        grammar.rule(self.rule).lhs()
    }

    /// Advance dot by one position
    pub fn advance(&self, target_node: NodeId) -> Self {
        Self {
            rule: self.rule,
            dot_position: self.dot_position + 1,
            start_node: self.start_node,
            current_node: target_node,
            backpointers: self.backpointers.clone(),
            probability: self.probability,
        }
    }

    /// Add backpointer
    pub fn with_backpointer(&self, bp: BackPointer) -> Self {
        let mut new_state = self.clone();
        new_state.backpointers.push(bp);
        new_state
    }
}
```

---

## Parse Forest Representation

Parse forests compactly represent multiple parse trees sharing common subtrees.

### ParseForest

```rust
/// Parse forest: packed representation of multiple parse trees
pub struct ParseForest {
    /// Forest nodes: (non_terminal, start_node, end_node) → derivations
    pub nodes: HashMap<ForestNodeId, ForestNode>,

    /// Root node(s)
    pub roots: Vec<ForestNodeId>,

    /// Grammar reference
    pub grammar: Arc<Grammar>,

    /// Lattice reference
    pub lattice: Arc<Lattice>,
}

/// Forest node ID
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct ForestNodeId {
    pub non_terminal: NonTerminal,
    pub start_node: NodeId,
    pub end_node: NodeId,
}

/// Forest node: alternative derivations for (NT, start, end)
pub struct ForestNode {
    /// Node identifier
    pub id: ForestNodeId,

    /// Alternative derivations (packed)
    pub alternatives: Vec<Derivation>,
}

/// Derivation: one way to derive this forest node
#[derive(Clone, Debug)]
pub struct Derivation {
    /// Production rule used
    pub rule: RuleId,

    /// Children (RHS symbols)
    pub children: Vec<ForestChild>,

    /// Probability (for PCFG)
    pub probability: f32,
}

/// Child in derivation
#[derive(Clone, Debug)]
pub enum ForestChild {
    /// Non-terminal child (reference to another forest node)
    NonTerminal(ForestNodeId),

    /// Terminal child (edge in lattice)
    Terminal(EdgeId),
}

impl ParseForest {
    /// Extract best parse (highest probability)
    pub fn best_parse(&self) -> Option<ParseTree> {
        if self.roots.is_empty() {
            return None;
        }

        // Use Viterbi algorithm to find highest-probability derivation
        Some(self.extract_best(&self.roots[0]))
    }

    /// Extract k-best parses
    pub fn k_best_parses(&self, k: usize) -> Vec<ParseTree> {
        // Use k-best algorithm (Huang & Chiang 2005)
        algorithms::k_best::extract(self, k)
    }

    /// Extract all parses (may be exponential!)
    pub fn all_parses(&self) -> Vec<ParseTree> {
        if self.roots.is_empty() {
            return Vec::new();
        }

        self.extract_all(&self.roots[0])
    }

    /// Count total parse trees (without enumerating)
    pub fn parse_count(&self) -> usize {
        if self.roots.is_empty() {
            return 0;
        }

        algorithms::parse_count_dp(self, &self.roots[0])
    }

    // Internal methods
    fn extract_best(&self, node_id: &ForestNodeId) -> ParseTree {
        // Viterbi: find highest-probability derivation
        // (Implementation details omitted for brevity)
        todo!()
    }

    fn extract_all(&self, node_id: &ForestNodeId) -> Vec<ParseTree> {
        // Enumerate all derivations (exponential!)
        // (Implementation details omitted for brevity)
        todo!()
    }
}

/// Parse tree: one concrete derivation
#[derive(Clone, Debug)]
pub struct ParseTree {
    /// Root rule
    pub rule: RuleId,

    /// Children
    pub children: Vec<ParseTreeChild>,

    /// Total probability
    pub probability: f32,
}

/// Child in parse tree
#[derive(Clone, Debug)]
pub enum ParseTreeChild {
    /// Non-terminal child (subtree)
    NonTerminal(Box<ParseTree>),

    /// Terminal child (word)
    Terminal(String),
}

impl ParseTree {
    /// Get sentence string
    pub fn sentence(&self) -> String {
        let mut words = Vec::new();
        self.collect_terminals(&mut words);
        words.join(" ")
    }

    fn collect_terminals(&self, words: &mut Vec<String>) {
        for child in &self.children {
            match child {
                ParseTreeChild::NonTerminal(subtree) => {
                    subtree.collect_terminals(words);
                }
                ParseTreeChild::Terminal(word) => {
                    words.push(word.clone());
                }
            }
        }
    }

    /// Pretty-print parse tree
    pub fn pretty_print(&self, grammar: &Grammar) -> String {
        let mut buffer = String::new();
        self.pretty_print_helper(grammar, &mut buffer, 0);
        buffer
    }

    fn pretty_print_helper(&self, grammar: &Grammar, buffer: &mut String, indent: usize) {
        let rule = grammar.rule(self.rule);
        buffer.push_str(&format!("{}({}\n", "  ".repeat(indent), rule.lhs()));

        for child in &self.children {
            match child {
                ParseTreeChild::NonTerminal(subtree) => {
                    subtree.pretty_print_helper(grammar, buffer, indent + 1);
                }
                ParseTreeChild::Terminal(word) => {
                    buffer.push_str(&format!("{}\"{}\"\n", "  ".repeat(indent + 1), word));
                }
            }
        }

        buffer.push_str(&format!("{})\n", "  ".repeat(indent)));
    }
}
```

---

## Memory Layout and Optimization

### Memory Breakdown

For a lattice with N nodes, E edges, K vocabulary size:

| Structure | Size per Element | Total Size |
|-----------|-----------------|------------|
| `Node` | 8 + 2×8×avg_degree ≈ 40 bytes | O(N × D) |
| `Edge` | 24 bytes (4×4 + metadata) | O(E) |
| `Vocabulary` | K × avg_word_len | O(K × L) |
| `Chart` | 16 + state_size × states | O(E × S) |

Where:
- D = average degree (typically 5-10)
- S = states per chart cell (typically 10-50)
- L = average word length (typically 5-8 bytes)

**Example**: Lattice with 100 nodes, 500 edges, 200 vocabulary:
- Nodes: 100 × 40 = 4 KB
- Edges: 500 × 24 = 12 KB
- Vocab: 200 × 6 = 1.2 KB
- Chart: 500 × 20 × 64 = 640 KB (dominates!)

**Optimization focus**: Chart size

### SmallVec Optimization

`Node.outgoing` and `Node.incoming` use `SmallVec<[EdgeId; 8]>`:

```rust
// Stack-allocated for ≤8 edges (common case)
pub outgoing: SmallVec<[EdgeId; 8]>,
```

**Benefit**: Avoids heap allocation for 99% of nodes (typical degree ≤8)

**Space savings**: 8 bytes (pointer) vs. 64 bytes (inline array) for small nodes

### Arc Sharing

Vocabulary strings use `Arc<str>` for deduplication:

```rust
pub vocab: IndexMap<Arc<str>, VocabId>,
```

**Benefit**: Multiple edges with same label share one allocation

**Example**: "the" appears 50× in lattice → 50 edges share 1 Arc<str>

### Bit Packing

Edge metadata uses compact types:

```rust
pub struct EdgeMetadata {
    pub distance: Option<u8>,  // 0-255 sufficient (not u32)
    pub is_phonetic: bool,     // 1 bit
    pub rule_id: Option<usize>,
}
```

**Space saving**: 2 bytes vs. 8 bytes (if using u32 for distance)

---

## Algorithms

Key algorithms operating on lattice data structures.

### Topological Sort (Kahn's Algorithm)

```rust
pub fn topological_sort(lattice: &Lattice) -> Vec<NodeId> {
    let mut in_degree: HashMap<NodeId, usize> = HashMap::default();
    let mut queue: VecDeque<NodeId> = VecDeque::new();
    let mut result: Vec<NodeId> = Vec::with_capacity(lattice.node_count());

    // Compute in-degrees
    for node in &lattice.nodes {
        in_degree.insert(node.id, node.in_degree());
        if node.is_source() {
            queue.push_back(node.id);
        }
    }

    // Process queue
    while let Some(node_id) = queue.pop_front() {
        result.push(node_id);

        for &edge_id in &lattice.node(node_id).outgoing {
            let edge = lattice.edge(edge_id);
            let target = edge.target;

            let deg = in_degree.get_mut(&target).unwrap();
            *deg -= 1;

            if *deg == 0 {
                queue.push_back(target);
            }
        }
    }

    assert_eq!(result.len(), lattice.node_count(), "Cycle detected in lattice!");
    result
}
```

**Complexity**: O(|V| + |E|)

### Path Counting (Dynamic Programming)

```rust
pub fn path_count_dp(lattice: &Lattice) -> usize {
    let mut count: HashMap<NodeId, usize> = HashMap::default();
    count.insert(lattice.start, 1);

    // Visit nodes in topological order
    for node_id in lattice.topological_order() {
        let node_count = *count.get(&node_id).unwrap_or(&0);

        // Propagate to successors
        for &edge_id in &lattice.node(node_id).outgoing {
            let target = lattice.edge(edge_id).target;
            *count.entry(target).or_insert(0) += node_count;
        }
    }

    *count.get(&lattice.end).unwrap_or(&0)
}
```

**Complexity**: O(|V| + |E|)

### Cycle Detection (DFS)

```rust
pub fn is_acyclic(lattice: &Lattice) -> bool {
    let mut visited: HashSet<NodeId> = HashSet::new();
    let mut rec_stack: HashSet<NodeId> = HashSet::new();

    fn dfs(
        lattice: &Lattice,
        node: NodeId,
        visited: &mut HashSet<NodeId>,
        rec_stack: &mut HashSet<NodeId>,
    ) -> bool {
        visited.insert(node);
        rec_stack.insert(node);

        for &edge_id in &lattice.node(node).outgoing {
            let target = lattice.edge(edge_id).target;

            if !visited.contains(&target) {
                if !dfs(lattice, target, visited, rec_stack) {
                    return false;  // Cycle detected
                }
            } else if rec_stack.contains(&target) {
                return false;  // Back edge = cycle
            }
        }

        rec_stack.remove(&node);
        true
    }

    for node in &lattice.nodes {
        if !visited.contains(&node.id) {
            if !dfs(lattice, node.id, &mut visited, &mut rec_stack) {
                return false;
            }
        }
    }

    true
}
```

**Complexity**: O(|V| + |E|)

---

## API Reference

### LatticeBuilder

Construct lattices incrementally from FST output.

```rust
pub struct LatticeBuilder {
    nodes: Vec<Node>,
    edges: Vec<Edge>,
    node_map: HashMap<usize, NodeId>,
    vocab: IndexMap<Arc<str>, VocabId>,
    next_node_id: usize,
    next_edge_id: usize,
}

impl LatticeBuilder {
    /// Create new builder
    pub fn new() -> Self {
        let mut builder = Self {
            nodes: Vec::new(),
            edges: Vec::new(),
            node_map: HashMap::default(),
            vocab: IndexMap::new(),
            next_node_id: 0,
            next_edge_id: 0,
        };

        // Create start node
        let start = builder.add_node_internal();
        builder.node_map.insert(0, start);

        builder
    }

    /// Add correction from position start_pos to end_pos
    pub fn add_correction(
        &mut self,
        start_pos: usize,
        end_pos: usize,
        word: impl Into<String>,
        weight: f32,
    ) -> &mut Self {
        let word: String = word.into();

        // Get or intern vocabulary
        let vocab_id = self.get_or_intern_vocab(word);

        // Get or create nodes
        let source = *self.node_map
            .entry(start_pos)
            .or_insert_with(|| self.add_node_internal());
        let target = *self.node_map
            .entry(end_pos)
            .or_insert_with(|| self.add_node_internal());

        // Add edge
        self.add_edge_internal(source, target, vocab_id, weight);

        self
    }

    /// Build final lattice
    pub fn build(mut self, end_pos: usize, metadata: LatticeMetadata) -> Lattice {
        // Ensure end node exists
        let end = *self.node_map
            .entry(end_pos)
            .or_insert_with(|| self.add_node_internal());

        Lattice {
            nodes: self.nodes,
            edges: self.edges,
            start: self.node_map[&0],
            end,
            vocab: self.vocab,
            metadata,
        }
    }

    // Internal helpers
    fn add_node_internal(&mut self) -> NodeId {
        let id = NodeId(self.next_node_id);
        self.next_node_id += 1;

        self.nodes.push(Node::new(id));
        id
    }

    fn add_edge_internal(
        &mut self,
        source: NodeId,
        target: NodeId,
        label: VocabId,
        weight: f32,
    ) -> EdgeId {
        let id = EdgeId(self.next_edge_id);
        self.next_edge_id += 1;

        self.edges.push(Edge::new(id, source, target, label, weight));

        self.nodes[source.0].add_outgoing(id);
        self.nodes[target.0].add_incoming(id);

        id
    }

    fn get_or_intern_vocab(&mut self, word: String) -> VocabId {
        let len = self.vocab.len();
        let (vid, _) = self.vocab
            .entry(Arc::from(word))
            .or_insert_with(|| VocabId(len));
        *vid
    }
}
```

### PathIterator

Lazy iterator over all paths (depth-first).

```rust
pub struct PathIterator<'a> {
    lattice: &'a Lattice,
    stack: Vec<PathState>,
}

struct PathState {
    node: NodeId,
    edge_index: usize,  // Index into node.outgoing
    path: Vec<EdgeId>,
}

impl<'a> PathIterator<'a> {
    pub fn new(lattice: &'a Lattice) -> Self {
        Self {
            lattice,
            stack: vec![PathState {
                node: lattice.start,
                edge_index: 0,
                path: Vec::new(),
            }],
        }
    }
}

impl<'a> Iterator for PathIterator<'a> {
    type Item = Path;

    fn next(&mut self) -> Option<Self::Item> {
        while let Some(mut state) = self.stack.pop() {
            let node = self.lattice.node(state.node);

            // If at end node, return path
            if node.id == self.lattice.end {
                return Some(Path {
                    edges: state.path,
                    lattice: self.lattice,
                });
            }

            // Otherwise, explore next edge
            if state.edge_index < node.outgoing.len() {
                let edge_id = node.outgoing[state.edge_index];
                let edge = self.lattice.edge(edge_id);

                // Push current state back (to explore remaining edges later)
                self.stack.push(PathState {
                    node: state.node,
                    edge_index: state.edge_index + 1,
                    path: state.path.clone(),
                });

                // Push next state
                let mut new_path = state.path;
                new_path.push(edge_id);
                self.stack.push(PathState {
                    node: edge.target,
                    edge_index: 0,
                    path: new_path,
                });
            }
        }

        None
    }
}

/// Path through lattice
pub struct Path {
    edges: Vec<EdgeId>,
    lattice: *const Lattice,  // Unsafe: lifetime tied to iterator
}

impl Path {
    /// Get sentence string for this path
    pub fn sentence(&self) -> String {
        let lattice = unsafe { &*self.lattice };
        self.edges.iter()
            .map(|&eid| {
                let edge = lattice.edge(eid);
                lattice.word(edge.label)
            })
            .collect::<Vec<_>>()
            .join(" ")
    }

    /// Get edges
    pub fn edges(&self) -> &[EdgeId] {
        &self.edges
    }
}
```

---

## Summary

This document specifies the core data structures for lattice parsing:

1. **Lattice**: Adjacency list DAG with deduplicated vocabulary
2. **Node**: Position with incoming/outgoing edges (SmallVec optimized)
3. **Edge**: Word transition with weight and metadata
4. **EarleyChart**: Parse state storage with memoization
5. **ParseForest**: Packed parse tree representation

**Key optimizations**:
- SmallVec for small vectors (avoid heap allocation)
- Arc<str> for vocabulary deduplication
- Bit packing for metadata
- Lazy path iteration (avoid exponential enumeration)
- Chart memoization (avoid redundant parsing)

**Memory efficiency**: O(K × n) space for K corrections over n words, vs. O(K^n) for string enumeration.

See [lattice_parsing.md](./lattice_parsing.md) for pedagogical explanation and [cfg_grammar_correction.md](./cfg_grammar_correction.md) for grammar integration.
