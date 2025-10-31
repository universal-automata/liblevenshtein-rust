//! Suffix automaton dictionary for approximate substring matching.
//!
//! This module implements a suffix automaton, which enables efficient approximate
//! matching of substrings anywhere within indexed text (not just prefixes like
//! traditional dictionaries).
//!
//! # Overview
//!
//! A **suffix automaton** is a minimal deterministic finite automaton (DFA) that
//! recognizes all suffixes of indexed text. Key properties:
//!
//! - **Substring Recognition**: Any path from root represents a substring
//! - **Minimality**: Typically ≤ 2n-1 states for n characters
//! - **Online Construction**: O(1) amortized per character
//! - **Endpos Equivalence**: States group substrings by ending positions
//!
//! # Use Cases
//!
//! ## Code Search
//!
//! ```rust,no_run
//! use liblevenshtein::dictionary::suffix_automaton::SuffixAutomaton;
//! use liblevenshtein::transducer::{Transducer, Algorithm};
//!
//! let code = r#"
//! fn calculate_total(items: &[Item]) -> f64 {
//!     items.iter().map(|i| i.price).sum()
//! }
//! "#;
//!
//! let dict = SuffixAutomaton::from_text(code);
//! let transducer = Transducer::new(dict, Algorithm::Standard);
//!
//! // Find "calculate" with typos
//! for term in transducer.query("calculat", 1) {
//!     println!("Found: {}", term);
//! }
//! ```
//!
//! ## Document Search
//!
//! ```rust,no_run
//! use liblevenshtein::dictionary::suffix_automaton::SuffixAutomaton;
//! use liblevenshtein::transducer::{Transducer, Algorithm};
//!
//! let docs = vec![
//!     "Levenshtein automata for approximate matching",
//!     "Suffix trees and suffix arrays for pattern search",
//! ];
//!
//! let dict = SuffixAutomaton::from_texts(docs);
//! let transducer = Transducer::new(dict.clone(), Algorithm::Standard);
//!
//! // Find "algorithm" even if misspelled
//! for candidate in transducer.query_ordered("algoritm", 2) {
//!     let positions = dict.match_positions(&candidate.term);
//!     for (doc_id, pos) in positions {
//!         println!("Doc {}, pos {}: {}", doc_id, pos, candidate.term);
//!     }
//! }
//! ```
//!
//! # Dynamic Updates
//!
//! ```rust,no_run
//! use liblevenshtein::dictionary::suffix_automaton::SuffixAutomaton;
//! use liblevenshtein::transducer::{Transducer, Algorithm};
//!
//! let dict = SuffixAutomaton::new();
//! let transducer = Transducer::new(dict.clone(), Algorithm::Standard);
//!
//! // Build index incrementally
//! dict.insert("testing the suffix automaton");
//! dict.insert("another test string");
//!
//! // Search
//! let results: Vec<_> = transducer.query("test", 0).collect();
//!
//! // Update index
//! dict.remove("another test string");
//! dict.insert("added new testing content");
//!
//! // Compact periodically
//! if dict.needs_compaction() {
//!     dict.compact();
//! }
//! ```
//!
//! # Comparison with Prefix Dictionaries
//!
//! | Feature | PathMap/DAWG | SuffixAutomaton |
//! |---------|--------------|-----------------|
//! | **Matching** | Prefix (whole words) | Substring (anywhere) |
//! | **Use Case** | Spell check, completion | Full-text search |
//! | **Space** | O(n) | O(n) states + edges |
//! | **Construction** | O(n) | O(n) online |
//! | **Dynamic** | Yes (DynamicDawg) | Yes |
//! | **Example** | "test" → "testing" | "test" → "contest" |
//!
//! # References
//!
//! - Blumer et al. (1985): "The smallest automaton recognizing the subwords of a text"
//! - Design document: `docs/SUFFIX_AUTOMATON_DESIGN.md`

use std::collections::HashMap;
use std::sync::{Arc, RwLock};

use crate::dictionary::{Dictionary, DictionaryNode, SyncStrategy};

/// A state in the suffix automaton.
///
/// Each state represents an equivalence class of substrings that have the same
/// set of ending positions (endpos). This minimizes the number of states while
/// maintaining the ability to recognize all substrings.
#[derive(Clone, Debug, PartialEq, Eq)]
#[cfg_attr(
    feature = "serialization",
    derive(serde::Serialize, serde::Deserialize)
)]
struct SuffixNode {
    /// Outgoing edges: (byte label, target state index).
    ///
    /// Kept sorted by byte for efficient binary search on large alphabets.
    edges: Vec<(u8, usize)>,

    /// Suffix link: points to state representing the longest proper suffix
    /// in a different endpos equivalence class.
    ///
    /// The suffix link forms a tree over states, enabling efficient construction
    /// and navigation through suffix relationships.
    suffix_link: Option<usize>,

    /// Length of the longest string in this equivalence class.
    ///
    /// All strings in this class have lengths in the range:
    /// [nodes[suffix_link].max_length + 1, max_length]
    max_length: usize,

    /// True if this state represents an end-of-string position.
    ///
    /// For generalized suffix automaton (multiple strings), this marks
    /// states where at least one indexed string ends.
    is_final: bool,

    /// Reference count for dynamic deletion (garbage collection).
    ///
    /// Tracks how many indexed strings pass through this state.
    /// Used during compaction to identify unreachable states.
    ref_count: usize,
}

impl SuffixNode {
    /// Create a new root node.
    fn root() -> Self {
        Self {
            edges: Vec::new(),
            suffix_link: None,
            max_length: 0,
            is_final: false,
            ref_count: 0,
        }
    }

    /// Create a new non-root node.
    fn new(max_length: usize) -> Self {
        Self {
            edges: Vec::new(),
            suffix_link: None,
            max_length,
            is_final: false,
            ref_count: 0,
        }
    }

    /// Find an edge by label.
    ///
    /// Uses linear search for small edge counts, binary search for larger.
    /// Threshold at 16 edges based on benchmarks from DAWG implementation.
    fn find_edge(&self, label: u8) -> Option<usize> {
        if self.edges.len() < 16 {
            self.edges
                .iter()
                .find(|(b, _)| *b == label)
                .map(|(_, t)| *t)
        } else {
            self.edges
                .binary_search_by_key(&label, |(b, _)| *b)
                .ok()
                .map(|idx| self.edges[idx].1)
        }
    }

    /// Add an edge, maintaining sorted order.
    fn add_edge(&mut self, label: u8, target: usize) {
        // Find insertion point to maintain sorted order
        match self.edges.binary_search_by_key(&label, |(b, _)| *b) {
            Ok(idx) => {
                // Edge already exists, update target
                self.edges[idx].1 = target;
            }
            Err(idx) => {
                // Insert at correct position
                self.edges.insert(idx, (label, target));
            }
        }
    }

    /// Update an existing edge target.
    fn update_edge(&mut self, label: u8, new_target: usize) -> bool {
        if let Some(idx) = self.edges.iter().position(|(b, _)| *b == label) {
            self.edges[idx].1 = new_target;
            true
        } else {
            false
        }
    }
}

/// Internal state of the suffix automaton.
///
/// This is wrapped in Arc<RwLock<...>> to provide thread-safe concurrent access
/// with dynamic mutation support.
#[derive(Debug)]
#[cfg_attr(
    feature = "serialization",
    derive(serde::Serialize, serde::Deserialize)
)]
struct SuffixAutomatonInner {
    /// Node storage (index-based graph).
    ///
    /// State 0 is always the root. States are added sequentially during
    /// construction, resulting in dense index space.
    nodes: Vec<SuffixNode>,

    /// Current state during online construction.
    ///
    /// Points to the last state added. New characters extend from here.
    /// Reset to 0 (root) when starting a new string in generalized automaton.
    last_state: usize,

    /// Total number of indexed strings.
    string_count: usize,

    /// Original source texts for serialization.
    ///
    /// Stored to enable proper deserialization since the automaton
    /// cannot be reconstructed from the graph structure alone.
    source_texts: Vec<String>,

    /// Position metadata: maps state IDs to (string_id, end_position).
    ///
    /// When a query matches at a final state, this map provides context
    /// about where the substring appears in the original texts.
    positions: HashMap<usize, Vec<(usize, usize)>>,

    /// Flag indicating compaction is recommended.
    ///
    /// Set to true when strings are removed, creating potentially unreachable
    /// states. Compaction performs garbage collection.
    needs_compaction: bool,
}

impl SuffixAutomatonInner {
    /// Create an empty suffix automaton with root state.
    fn new() -> Self {
        Self {
            nodes: vec![SuffixNode::root()],
            last_state: 0,
            string_count: 0,
            source_texts: Vec::new(),
            positions: HashMap::new(),
            needs_compaction: false,
        }
    }

    /// Extend the automaton with one character (online construction).
    ///
    /// This implements the algorithm from Blumer et al. (1985).
    ///
    /// # Complexity
    ///
    /// - Time: O(1) amortized per character
    /// - Space: Adds 1 state, possibly 1 clone
    ///
    /// # Algorithm Overview
    ///
    /// 1. Create new state for current character
    /// 2. Walk suffix links backward, adding transitions
    /// 3. Handle equivalence class splitting if necessary
    /// 4. Update last_state pointer
    ///
    /// # Note on is_final
    ///
    /// Unlike prefix tries where only complete words are final, in a suffix
    /// automaton EVERY state (except root) represents a valid substring.
    /// We mark all states as final to work with Transducer's matching logic.
    fn extend(&mut self, ch: u8) {
        let cur = self.nodes.len();
        let mut new_node = SuffixNode::new(self.nodes[self.last_state].max_length + 1);
        // Mark as final since every reachable state is a valid substring
        new_node.is_final = true;
        self.nodes.push(new_node);

        // Walk suffix links backward, adding transitions to new state
        let mut p = Some(self.last_state);
        while let Some(p_idx) = p {
            if self.nodes[p_idx].find_edge(ch).is_some() {
                break;
            }
            self.nodes[p_idx].add_edge(ch, cur);
            p = self.nodes[p_idx].suffix_link;
        }

        if let Some(p_idx) = p {
            let q = self.nodes[p_idx].find_edge(ch).unwrap();

            if self.nodes[p_idx].max_length + 1 == self.nodes[q].max_length {
                // Continuous transition - no split needed
                self.nodes[cur].suffix_link = Some(q);
            } else {
                // Split equivalence class by cloning state q
                let clone = self.nodes.len();
                let mut cloned_node = self.nodes[q].clone();
                cloned_node.max_length = self.nodes[p_idx].max_length + 1;
                cloned_node.is_final = true; // Cloned states are also valid substrings
                self.nodes.push(cloned_node);

                // Update suffix links
                self.nodes[cur].suffix_link = Some(clone);
                self.nodes[q].suffix_link = Some(clone);

                // Redirect transitions from states along suffix link path
                let mut p2 = Some(p_idx);
                while let Some(p2_idx) = p2 {
                    if let Some(target) = self.nodes[p2_idx].find_edge(ch) {
                        if target == q {
                            self.nodes[p2_idx].update_edge(ch, clone);
                            p2 = self.nodes[p2_idx].suffix_link;
                        } else {
                            break;
                        }
                    } else {
                        break;
                    }
                }
            }
        } else {
            // Reached root without finding transition - simple case
            self.nodes[cur].suffix_link = Some(0);
        }

        self.last_state = cur;
    }
}

/// Suffix automaton for approximate substring matching.
///
/// This dictionary type enables finding approximate matches anywhere within
/// indexed text, not just at word boundaries like prefix-based dictionaries.
///
/// # Thread Safety
///
/// Uses `Arc<RwLock<...>>` for safe concurrent access with dynamic updates.
/// Multiple readers can query simultaneously, with exclusive access for writes.
///
/// # Construction
///
/// - `new()` - Create empty automaton
/// - `from_text(s)` - Index single string
/// - `from_texts(iter)` - Index multiple strings
///
/// # Dynamic Operations
///
/// - `insert(text)` - Add a string
/// - `remove(text)` - Remove a string (may leave unreachable states)
/// - `compact()` - Garbage collect unreachable states
///
/// # Querying
///
/// Use with `Transducer` just like any other dictionary:
///
/// ```rust,no_run
/// use liblevenshtein::dictionary::suffix_automaton::SuffixAutomaton;
/// use liblevenshtein::transducer::{Transducer, Algorithm};
///
/// let dict = SuffixAutomaton::from_text("example text");
/// let transducer = Transducer::new(dict, Algorithm::Standard);
///
/// for term in transducer.query("exmple", 1) {
///     println!("Found: {}", term);
/// }
/// ```
#[derive(Clone, Debug)]
pub struct SuffixAutomaton {
    inner: Arc<RwLock<SuffixAutomatonInner>>,
}

impl SuffixAutomaton {
    /// Create an empty suffix automaton.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use liblevenshtein::dictionary::suffix_automaton::SuffixAutomaton;
    ///
    /// let dict = SuffixAutomaton::new();
    /// dict.insert("hello");
    /// dict.insert("world");
    /// ```
    pub fn new() -> Self {
        Self {
            inner: Arc::new(RwLock::new(SuffixAutomatonInner::new())),
        }
    }

    /// Get the number of states in the automaton (for debugging).
    pub fn state_count(&self) -> usize {
        self.inner.read().unwrap().nodes.len()
    }

    /// Debug: print automaton structure (for development).
    #[allow(dead_code)]
    pub fn debug_print(&self) {
        let inner = self.inner.read().unwrap();
        println!("Suffix Automaton with {} states:", inner.nodes.len());
        for (idx, node) in inner.nodes.iter().enumerate() {
            println!(
                "  State {}: is_final={}, max_len={}, edges={:?}, link={:?}",
                idx,
                node.is_final,
                node.max_length,
                node.edges
                    .iter()
                    .map(|(b, t)| (char::from(*b), t))
                    .collect::<Vec<_>>(),
                node.suffix_link
            );
        }
    }

    /// Build from a single text string.
    ///
    /// Indexes all suffixes of the input text, enabling substring search.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use liblevenshtein::dictionary::suffix_automaton::SuffixAutomaton;
    ///
    /// let code = "fn main() { println!(\"Hello\"); }";
    /// let dict = SuffixAutomaton::from_text(code);
    /// ```
    pub fn from_text(text: &str) -> Self {
        let dict = Self::new();
        dict.insert(text);
        dict
    }

    /// Build from multiple texts.
    ///
    /// Creates a generalized suffix automaton indexing all input strings.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use liblevenshtein::dictionary::suffix_automaton::SuffixAutomaton;
    ///
    /// let docs = vec![
    ///     "First document text",
    ///     "Second document text",
    ///     "Third document text",
    /// ];
    /// let dict = SuffixAutomaton::from_texts(docs);
    /// ```
    pub fn from_texts<I, S>(texts: I) -> Self
    where
        I: IntoIterator<Item = S>,
        S: AsRef<str>,
    {
        let dict = Self::new();
        for text in texts {
            dict.insert(text.as_ref());
        }
        dict
    }

    /// Insert a text string.
    ///
    /// Returns `true` if the operation succeeded (always true currently).
    ///
    /// # Examples
    ///
    /// ```rust
    /// use liblevenshtein::dictionary::suffix_automaton::SuffixAutomaton;
    ///
    /// let dict = SuffixAutomaton::new();
    /// dict.insert("testing insertion");
    /// ```
    pub fn insert(&self, text: &str) -> bool {
        let mut inner = self.inner.write().unwrap();
        let string_id = inner.string_count;

        // Store source text for serialization
        inner.source_texts.push(text.to_string());

        // Extend automaton with each character
        for ch in text.bytes() {
            inner.extend(ch);
        }

        // Record position metadata for the end-of-string state
        // Note: is_final is already set to true during extend()
        let last_state = inner.last_state;
        inner
            .positions
            .entry(last_state)
            .or_default()
            .push((string_id, text.len()));

        inner.string_count += 1;

        // Reset to root for next insertion (generalized automaton)
        inner.last_state = 0;

        true
    }

    /// Remove a text string.
    ///
    /// Returns `true` if removed, `false` if not found.
    ///
    /// **Note**: May leave unreachable states. Call `compact()` periodically
    /// to reclaim memory.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use liblevenshtein::dictionary::suffix_automaton::SuffixAutomaton;
    ///
    /// let dict = SuffixAutomaton::new();
    /// dict.insert("test string");
    /// assert!(dict.remove("test string"));
    /// assert!(!dict.remove("test string")); // Already removed
    /// ```
    pub fn remove(&self, text: &str) -> bool {
        let mut inner = self.inner.write().unwrap();

        // Navigate to end state for this text
        let mut state = 0;
        for ch in text.bytes() {
            match inner.nodes[state].find_edge(ch) {
                Some(next) => state = next,
                None => return false, // String not present
            }
        }

        // Check if this text's end position is recorded at this state
        let removed = if let Some(positions) = inner.positions.get_mut(&state) {
            let original_len = positions.len();
            positions.retain(|(_, end)| *end != text.len());
            positions.len() < original_len
        } else {
            false
        };

        if removed {
            // Remove from source_texts (mark as empty string to preserve indices)
            // We can't actually remove without reindexing, so we'll handle this in compact()
            // For now, we'll just track removal via positions metadata

            // Check if we need to remove the state from positions map
            let should_remove = inner
                .positions
                .get(&state)
                .map(|v| v.is_empty())
                .unwrap_or(false);

            if should_remove {
                // Note: We keep is_final=true because this state still represents
                // a valid substring (possibly from other indexed strings).
                // Only remove from positions map.
                inner.positions.remove(&state);
            }

            inner.needs_compaction = true;
            inner.string_count -= 1;
            true
        } else {
            false
        }
    }

    /// Clear all indexed text.
    ///
    /// Resets the automaton to empty state with only the root node.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use liblevenshtein::dictionary::suffix_automaton::SuffixAutomaton;
    ///
    /// let dict = SuffixAutomaton::new();
    /// dict.insert("test");
    /// dict.clear();
    /// assert_eq!(dict.string_count(), 0);
    /// ```
    pub fn clear(&self) {
        let mut inner = self.inner.write().unwrap();
        *inner = SuffixAutomatonInner::new();
    }

    /// Compact internal structure (garbage collection).
    ///
    /// Removes unreachable states after deletions. Recommended after batch
    /// deletions or when `needs_compaction()` returns true.
    ///
    /// # Complexity
    ///
    /// - Time: O(states + edges)
    /// - Space: O(states) temporary
    ///
    /// # Examples
    ///
    /// ```rust
    /// use liblevenshtein::dictionary::suffix_automaton::SuffixAutomaton;
    ///
    /// let dict = SuffixAutomaton::new();
    /// dict.insert("test1");
    /// dict.insert("test2");
    /// dict.remove("test1");
    ///
    /// if dict.needs_compaction() {
    ///     dict.compact();
    /// }
    /// ```
    pub fn compact(&self) {
        let mut inner = self.inner.write().unwrap();

        if !inner.needs_compaction {
            return;
        }

        // Mark-and-sweep garbage collection
        let mut reachable = vec![false; inner.nodes.len()];
        let mut stack = vec![0]; // Start from root

        while let Some(state) = stack.pop() {
            if reachable[state] {
                continue;
            }
            reachable[state] = true;

            for &(_, target) in &inner.nodes[state].edges {
                stack.push(target);
            }
        }

        // Build new node vector with only reachable states
        let mut new_nodes = Vec::new();
        let mut old_to_new = vec![0; inner.nodes.len()];

        for (old_idx, node) in inner.nodes.iter().enumerate() {
            if reachable[old_idx] {
                old_to_new[old_idx] = new_nodes.len();
                new_nodes.push(node.clone());
            }
        }

        // Remap all state indices
        for node in &mut new_nodes {
            for edge in &mut node.edges {
                edge.1 = old_to_new[edge.1];
            }
            if let Some(link) = node.suffix_link {
                node.suffix_link = Some(old_to_new[link]);
            }
        }

        // Update positions map
        let mut new_positions = HashMap::new();
        for (old_state, positions) in inner.positions.drain() {
            if reachable[old_state] {
                new_positions.insert(old_to_new[old_state], positions);
            }
        }

        inner.nodes = new_nodes;
        inner.positions = new_positions;
        inner.last_state = 0;
        inner.needs_compaction = false;
    }

    /// Get the number of indexed strings.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use liblevenshtein::dictionary::suffix_automaton::SuffixAutomaton;
    ///
    /// let dict = SuffixAutomaton::new();
    /// assert_eq!(dict.string_count(), 0);
    ///
    /// dict.insert("test");
    /// assert_eq!(dict.string_count(), 1);
    /// ```
    pub fn string_count(&self) -> usize {
        self.inner.read().unwrap().string_count
    }

    /// Check if compaction is recommended.
    ///
    /// Returns `true` if strings have been removed and unreachable states
    /// may exist.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use liblevenshtein::dictionary::suffix_automaton::SuffixAutomaton;
    ///
    /// let dict = SuffixAutomaton::new();
    /// dict.insert("test");
    /// dict.remove("test");
    ///
    /// if dict.needs_compaction() {
    ///     dict.compact();
    /// }
    /// ```
    pub fn needs_compaction(&self) -> bool {
        self.inner.read().unwrap().needs_compaction
    }

    /// Get match positions for a substring.
    ///
    /// Returns a list of (string_id, end_position) tuples indicating where
    /// the substring appears in the indexed texts.
    ///
    /// **Note**: Currently only returns positions if the substring matches
    /// at the end of an indexed string. Full position tracking for all
    /// substrings is a future enhancement.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use liblevenshtein::dictionary::suffix_automaton::SuffixAutomaton;
    ///
    /// let docs = vec!["testing", "test"];
    /// let dict = SuffixAutomaton::from_texts(docs);
    ///
    /// // Note: Position tracking is currently limited to final states
    /// // This is a placeholder for future enhancement
    /// let positions = dict.match_positions("test");
    /// // positions will contain entries for strings ending exactly with "test"
    /// ```
    pub fn match_positions(&self, substring: &str) -> Vec<(usize, usize)> {
        let inner = self.inner.read().unwrap();

        // Navigate to the state for this substring
        let mut state = 0;
        for byte in substring.as_bytes() {
            match inner.nodes[state].find_edge(*byte) {
                Some(next) => state = next,
                None => return Vec::new(), // Substring not found
            }
        }

        // Collect positions from this state and all reachable final states
        // via epsilon-like transitions (suffix links and forward edges)
        let mut result = Vec::new();

        // Add positions directly associated with this state
        if let Some(positions) = inner.positions.get(&state) {
            result.extend(positions.iter().copied());
        }

        // For a more complete implementation, we would need to traverse
        // all states reachable from here to find all occurrences.
        // This is left as a future enhancement for full position tracking.

        result
    }

    /// Get the original source texts used to build this automaton.
    ///
    /// Returns a vector of all texts that were indexed. This is useful
    /// for serialization, as the automaton can be reconstructed from
    /// these texts rather than extracting all possible substrings.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use liblevenshtein::dictionary::suffix_automaton::SuffixAutomaton;
    ///
    /// let texts = vec!["hello world", "test string"];
    /// let dict = SuffixAutomaton::from_texts(texts.clone());
    ///
    /// let sources = dict.source_texts();
    /// assert_eq!(sources.len(), 2);
    /// ```
    pub fn source_texts(&self) -> Vec<String> {
        let inner = self.inner.read().unwrap();
        inner.source_texts.clone()
    }
}

impl Default for SuffixAutomaton {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(feature = "serialization")]
impl serde::Serialize for SuffixAutomaton {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        // Extract the inner data by acquiring read lock
        let inner = self.inner.read().unwrap();
        inner.serialize(serializer)
    }
}

#[cfg(feature = "serialization")]
impl<'de> serde::Deserialize<'de> for SuffixAutomaton {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        let inner = SuffixAutomatonInner::deserialize(deserializer)?;
        Ok(SuffixAutomaton {
            inner: Arc::new(RwLock::new(inner)),
        })
    }
}

/// Handle for traversing the suffix automaton.
///
/// Implements `DictionaryNode` trait for compatibility with existing
/// `Transducer` and query infrastructure.
#[derive(Clone, Debug)]
pub struct SuffixNodeHandle {
    /// Reference to the automaton (for traversal).
    automaton: Arc<RwLock<SuffixAutomatonInner>>,

    /// Current state index.
    state_id: usize,
}

impl DictionaryNode for SuffixNodeHandle {
    type Unit = u8;

    fn is_final(&self) -> bool {
        let inner = self.automaton.read().unwrap();
        inner.nodes[self.state_id].is_final
    }

    fn transition(&self, label: u8) -> Option<Self> {
        let inner = self.automaton.read().unwrap();
        inner.nodes[self.state_id]
            .find_edge(label)
            .map(|target| Self {
                automaton: Arc::clone(&self.automaton),
                state_id: target,
            })
    }

    fn edges(&self) -> Box<dyn Iterator<Item = (u8, Self)> + '_> {
        // Clone edges to avoid holding lock during iteration
        let inner = self.automaton.read().unwrap();
        let edges = inner.nodes[self.state_id].edges.clone();
        drop(inner);

        Box::new(edges.into_iter().map(move |(label, target)| {
            (
                label,
                Self {
                    automaton: Arc::clone(&self.automaton),
                    state_id: target,
                },
            )
        }))
    }

    fn has_edge(&self, label: u8) -> bool {
        let inner = self.automaton.read().unwrap();
        inner.nodes[self.state_id].find_edge(label).is_some()
    }

    fn edge_count(&self) -> Option<usize> {
        let inner = self.automaton.read().unwrap();
        Some(inner.nodes[self.state_id].edges.len())
    }
}

impl Dictionary for SuffixAutomaton {
    type Node = SuffixNodeHandle;

    fn root(&self) -> Self::Node {
        SuffixNodeHandle {
            automaton: Arc::clone(&self.inner),
            state_id: 0,
        }
    }

    fn contains(&self, term: &str) -> bool {
        let mut node = self.root();
        for byte in term.as_bytes() {
            match node.transition(*byte) {
                Some(next) => node = next,
                None => return false,
            }
        }
        // For suffix automaton, we check substring existence, not finality
        // Any reachable state represents a valid substring
        true
    }

    fn len(&self) -> Option<usize> {
        Some(self.string_count())
    }

    fn sync_strategy(&self) -> SyncStrategy {
        SyncStrategy::ExternalSync // Uses RwLock
    }

    fn is_suffix_based(&self) -> bool {
        true // Suffix automaton performs substring matching
    }
}

#[cfg(feature = "serialization")]
impl crate::serialization::DictionaryFromTerms for SuffixAutomaton {
    /// Create a suffix automaton from texts.
    ///
    /// Note: For suffix automata, "terms" are treated as source texts
    /// to be indexed for substring matching.
    fn from_terms<I: IntoIterator<Item = String>>(terms: I) -> Self {
        Self::from_texts(terms)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_empty_automaton() {
        let dict = SuffixAutomaton::new();
        assert_eq!(dict.string_count(), 0);
        assert!(!dict.needs_compaction());
    }

    #[test]
    fn test_single_character() {
        let dict = SuffixAutomaton::from_text("a");
        assert_eq!(dict.string_count(), 1);
        assert!(dict.contains("a"));
        assert!(!dict.contains("b"));
    }

    #[test]
    fn test_simple_string() {
        let dict = SuffixAutomaton::from_text("abc");
        assert_eq!(dict.string_count(), 1);

        // All suffixes should be present
        assert!(dict.contains("abc"));
        assert!(dict.contains("bc"));
        assert!(dict.contains("c"));

        // All substrings should be present (suffix automaton recognizes all substrings)
        assert!(dict.contains("ab"));
        assert!(dict.contains("b"));
        assert!(dict.contains("a"));

        // Non-substrings should not be present
        assert!(!dict.contains("d"));
        assert!(!dict.contains("abcd"));
    }

    #[test]
    fn test_repeated_characters() {
        let dict = SuffixAutomaton::from_text("aaa");
        assert_eq!(dict.string_count(), 1);

        assert!(dict.contains("aaa"));
        assert!(dict.contains("aa"));
        assert!(dict.contains("a"));
    }

    #[test]
    fn test_complex_string() {
        let dict = SuffixAutomaton::from_text("abcbc");
        assert_eq!(dict.string_count(), 1);

        // All suffixes
        assert!(dict.contains("abcbc"));
        assert!(dict.contains("bcbc"));
        assert!(dict.contains("cbc"));
        assert!(dict.contains("bc"));
        assert!(dict.contains("c"));

        // Some substrings that should be present
        assert!(dict.contains("abc"));
        assert!(dict.contains("bcb"));
    }

    #[test]
    fn test_multiple_strings() {
        let dict = SuffixAutomaton::from_texts(vec!["abc", "def"]);
        assert_eq!(dict.string_count(), 2);

        // Substrings from first text
        assert!(dict.contains("abc"));
        assert!(dict.contains("bc"));
        assert!(dict.contains("c"));

        // Substrings from second text
        assert!(dict.contains("def"));
        assert!(dict.contains("ef"));
        assert!(dict.contains("f"));
    }

    #[test]
    fn test_insert_and_remove() {
        let dict = SuffixAutomaton::new();

        assert!(dict.insert("test"));
        assert_eq!(dict.string_count(), 1);
        assert!(dict.contains("test"));

        assert!(dict.remove("test"));
        assert_eq!(dict.string_count(), 0);
        assert!(dict.needs_compaction());

        assert!(!dict.remove("test")); // Already removed
    }

    #[test]
    fn test_clear() {
        let dict = SuffixAutomaton::from_texts(vec!["abc", "def", "ghi"]);
        assert_eq!(dict.string_count(), 3);

        dict.clear();
        assert_eq!(dict.string_count(), 0);
        assert!(!dict.contains("abc"));
    }

    #[test]
    fn test_compaction() {
        let dict = SuffixAutomaton::new();

        dict.insert("test1");
        dict.insert("test2");
        dict.insert("test3");
        assert_eq!(dict.string_count(), 3);

        dict.remove("test2");
        assert_eq!(dict.string_count(), 2);
        assert!(dict.needs_compaction());

        dict.compact();
        assert!(!dict.needs_compaction());
        assert_eq!(dict.string_count(), 2);

        // Verify remaining strings are still accessible
        assert!(dict.contains("test1"));
        assert!(dict.contains("test3"));
    }

    #[test]
    fn test_match_positions() {
        // Position tracking currently works for strings that end at final states
        let docs = vec!["hello", "world"];
        let dict = SuffixAutomaton::from_texts(docs);

        // "hello" and "world" are complete strings, so they end at final states
        let positions_hello = dict.match_positions("hello");
        assert!(!positions_hello.is_empty());
        assert_eq!(positions_hello[0].0, 0); // Document 0

        let positions_world = dict.match_positions("world");
        assert!(!positions_world.is_empty());
        assert_eq!(positions_world[0].0, 1); // Document 1

        // Suffixes also work (they reach the same final states)
        let positions_ello = dict.match_positions("ello");
        assert!(!positions_ello.is_empty());
    }

    #[test]
    fn test_dictionary_trait() {
        let dict = SuffixAutomaton::from_text("test");

        // Test Dictionary trait methods
        assert_eq!(dict.len(), Some(1));
        assert!(!dict.is_empty());
        assert_eq!(dict.sync_strategy(), SyncStrategy::ExternalSync);

        // Test node traversal
        let root = dict.root();
        assert!(root.has_edge(b't'));

        let node_t = root.transition(b't').unwrap();
        assert!(node_t.has_edge(b'e'));
    }

    #[test]
    fn test_node_edges() {
        let dict = SuffixAutomaton::from_text("ab");
        let root = dict.root();

        let edges: Vec<_> = root.edges().collect();
        assert!(!edges.is_empty());

        // Should have edges for suffixes "ab" and "b"
        let labels: Vec<_> = edges.iter().map(|(l, _)| *l).collect();
        assert!(labels.contains(&b'a') || labels.contains(&b'b'));
    }
}
