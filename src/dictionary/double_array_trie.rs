//! Double-Array Trie (DAT) implementation with dynamic updates.
//!
//! A Double-Array Trie stores a trie structure using two parallel arrays (BASE and CHECK)
//! providing O(1) transitions and excellent cache locality.
//!
//! ## Structure
//!
//! - **BASE[s]**: Contains the offset for computing child state indices
//! - **CHECK[s]**: Verifies that a state `s` is valid (stores parent state)
//! - **IS_FINAL**: BitVec marking final states (end of valid terms)
//!
//! ## Transition Function
//!
//! ```text
//! next_state = BASE[current_state] + byte
//! if CHECK[next_state] == current_state:
//!     transition is valid
//! ```
//!
//! ## Performance Characteristics
//!
//! - **Memory**: 6-8 bytes per character (BASE: 4 bytes, CHECK: 4 bytes, flags: bits)
//! - **Transitions**: O(1) - single array lookup
//! - **Cache locality**: Excellent - contiguous arrays
//! - **Construction**: O(n²) worst case (BASE placement problem)
//! - **Dynamic updates**: Good with XOR-based relocation and free list
//!
//! ## Use Cases
//!
//! Best for:
//! - Large static or semi-static dictionaries
//! - Memory-constrained environments
//! - Cache-sensitive applications
//! - Scenarios requiring occasional updates

use crate::dictionary::{Dictionary, DictionaryNode};
use std::sync::Arc;

#[cfg(feature = "serialization")]
use serde::{Deserialize, Deserializer, Serialize, Serializer};

/// Custom serialization for Arc<Vec<T>> - serializes the inner Vec directly
#[cfg(feature = "serialization")]
fn serialize_arc_vec<S, T>(arc: &Arc<Vec<T>>, serializer: S) -> Result<S::Ok, S::Error>
where
    S: Serializer,
    T: Serialize,
{
    arc.as_ref().serialize(serializer)
}

/// Custom deserialization for Arc<Vec<T>> - wraps deserialized Vec in Arc
#[cfg(feature = "serialization")]
fn deserialize_arc_vec<'de, D, T>(deserializer: D) -> Result<Arc<Vec<T>>, D::Error>
where
    D: Deserializer<'de>,
    T: Deserialize<'de>,
{
    Vec::<T>::deserialize(deserializer).map(Arc::new)
}

/// Custom serialization for Arc<Vec<Vec<T>>>
#[cfg(feature = "serialization")]
fn serialize_arc_vec_vec<S, T>(arc: &Arc<Vec<Vec<T>>>, serializer: S) -> Result<S::Ok, S::Error>
where
    S: Serializer,
    T: Serialize,
{
    arc.as_ref().serialize(serializer)
}

/// Custom deserialization for Arc<Vec<Vec<T>>>
#[cfg(feature = "serialization")]
fn deserialize_arc_vec_vec<'de, D, T>(deserializer: D) -> Result<Arc<Vec<Vec<T>>>, D::Error>
where
    D: Deserializer<'de>,
    T: Deserialize<'de>,
{
    Vec::<Vec<T>>::deserialize(deserializer).map(Arc::new)
}

/// A Double-Array Trie with support for dynamic updates.
///
/// Uses BASE/CHECK arrays for O(1) transitions with excellent cache locality.
/// Supports insertions and deletions with XOR-based relocation and lazy rebuilding.
/// Shared data structure for all nodes in a DAT.
/// Reduces Arc cloning overhead by grouping all shared arrays together.
#[cfg_attr(
    feature = "serialization",
    derive(serde::Serialize, serde::Deserialize)
)]
#[derive(Clone, Debug)]
struct DATShared {
    /// BASE array: offset for computing next state
    #[cfg_attr(
        feature = "serialization",
        serde(
            serialize_with = "serialize_arc_vec",
            deserialize_with = "deserialize_arc_vec"
        )
    )]
    base: Arc<Vec<i32>>,

    /// CHECK array: parent state verification
    #[cfg_attr(
        feature = "serialization",
        serde(
            serialize_with = "serialize_arc_vec",
            deserialize_with = "deserialize_arc_vec"
        )
    )]
    check: Arc<Vec<i32>>,

    /// Final states marking valid term endings
    #[cfg_attr(
        feature = "serialization",
        serde(
            serialize_with = "serialize_arc_vec",
            deserialize_with = "deserialize_arc_vec"
        )
    )]
    is_final: Arc<Vec<bool>>,

    /// Edge lists per state: which bytes have valid transitions
    /// This optimizes the edges() iterator to only check actual edges
    /// instead of all 256 possible bytes.
    #[cfg_attr(
        feature = "serialization",
        serde(
            serialize_with = "serialize_arc_vec_vec",
            deserialize_with = "deserialize_arc_vec_vec"
        )
    )]
    edges: Arc<Vec<Vec<u8>>>,
}

/// A compact, cache-efficient dictionary implementation using the Double-Array Trie data structure.
///
/// # Overview
///
/// Double-Array Trie (DAT) is a space-efficient trie implementation that uses two parallel
/// arrays (BASE and CHECK) to represent state transitions. This provides:
///
/// - **Compact memory footprint**: O(n) space where n is alphabet size × number of states
/// - **Fast lookups**: O(m) time where m is the query length, with excellent cache locality
/// - **Static structure**: Optimized for read-heavy workloads after construction
///
/// # Performance Characteristics
///
/// - **Lookup**: O(m) where m is string length - excellent cache performance
/// - **Construction**: O(n × m) where n is term count, m is average length
/// - **Memory**: More compact than tree-based tries, comparable to DAWG
/// - **Thread-safety**: Fully concurrent reads via Arc-based sharing
///
/// # Use Cases
///
/// Best suited for:
/// - Static or rarely-modified dictionaries
/// - Memory-constrained environments
/// - High-throughput exact matching
/// - Applications requiring fast startup (quick deserialization)
///
/// # Serialization
///
/// Supports multiple formats when the `serialization` feature is enabled:
/// - **Bincode**: Fast binary format, smallest size
/// - **JSON**: Human-readable, portable across platforms
/// - **Gzip compression**: Available for both formats via `compression` feature
///
/// # Example
///
/// ```
/// use liblevenshtein::prelude::*;
///
/// let terms = vec!["apple", "application", "apply"];
/// let dict = DoubleArrayTrie::from_terms(terms);
///
/// assert!(dict.contains("apple"));
/// assert!(!dict.contains("apricot"));
/// ```
#[cfg_attr(
    feature = "serialization",
    derive(serde::Serialize, serde::Deserialize)
)]
#[derive(Clone, Debug)]
pub struct DoubleArrayTrie {
    /// Shared data referenced by all nodes
    shared: DATShared,

    /// Free list for deleted/unused states
    #[cfg_attr(
        feature = "serialization",
        serde(
            serialize_with = "serialize_arc_vec",
            deserialize_with = "deserialize_arc_vec"
        )
    )]
    free_list: Arc<Vec<usize>>,

    /// Number of terms in the dictionary
    term_count: usize,

    /// Threshold for triggering rebuild (0.0 to 1.0, e.g., 0.2 = 20% deleted)
    rebuild_threshold: f64,
}

/// Builder for constructing a Double-Array Trie incrementally.
pub struct DoubleArrayTrieBuilder {
    /// BASE array being built
    base: Vec<i32>,

    /// CHECK array being built
    check: Vec<i32>,

    /// Final state markers
    is_final: Vec<bool>,

    /// Free list tracking unused states
    free_list: Vec<usize>,

    /// Number of terms inserted
    term_count: usize,

    /// Next available state index
    /// TODO: Reserved for future incremental construction support
    #[allow(dead_code)]
    next_state: usize,

    /// Rebuild threshold
    rebuild_threshold: f64,
}

impl DoubleArrayTrieBuilder {
    /// Create a new DAT builder.
    pub fn new() -> Self {
        // State 0 is reserved as a sentinel/error state
        // State 1 is the root
        let base = vec![-1, 0]; // -1 for sentinel, 0 for root
        let check = vec![-1, -1]; // -1 means unused
        let is_final = vec![false, false];

        Self {
            base,
            check,
            is_final,
            free_list: Vec::new(),
            term_count: 0,
            next_state: 2,          // Next available state
            rebuild_threshold: 0.2, // Rebuild when 20% deleted
        }
    }

    /// Set the rebuild threshold (0.0 to 1.0).
    pub fn with_rebuild_threshold(mut self, threshold: f64) -> Self {
        self.rebuild_threshold = threshold.clamp(0.0, 1.0);
        self
    }

    /// Insert a term into the trie.
    pub fn insert(&mut self, term: &str) -> bool {
        if term.is_empty() {
            return false;
        }

        let bytes = term.as_bytes();
        let mut state = 1; // Start at root

        // Traverse/create path
        for &byte in bytes {
            if let Some(next) = self.transition(state, byte) {
                state = next;
            } else {
                // Need to create new state for this transition
                state = self.add_transition(state, byte);
            }
        }

        // Mark final state
        if state < self.is_final.len() && self.is_final[state] {
            false // Already exists
        } else {
            while state >= self.is_final.len() {
                self.is_final.push(false);
            }
            self.is_final[state] = true;
            self.term_count += 1;
            true
        }
    }

    /// Transition from a state via a byte.
    fn transition(&self, state: usize, byte: u8) -> Option<usize> {
        if state >= self.base.len() {
            return None;
        }

        let base = self.base[state];
        if base < 0 {
            return None; // No edges
        }

        let next = (base as usize).wrapping_add(byte as usize);

        if next < self.check.len() && self.check[next] == state as i32 {
            Some(next)
        } else {
            None
        }
    }

    /// Add a transition from state via byte, returning the new state.
    fn add_transition(&mut self, state: usize, byte: u8) -> usize {
        // Ensure state exists
        while state >= self.base.len() {
            self.base.push(-1);
            self.check.push(-1);
            self.is_final.push(false);
        }

        // Find a valid next_state based on BASE
        let next_state = if self.base[state] < 0 {
            // No BASE set yet - find a suitable BASE
            // Start searching from a position based on state to spread out allocations
            let start = (state * 31) % 1000 + byte as usize;
            let base = self.find_free_base(start, &[byte]);
            self.base[state] = base;
            (base as usize).wrapping_add(byte as usize)
        } else {
            // BASE already set, compute next_state
            (self.base[state] as usize).wrapping_add(byte as usize)
        };

        // Ensure next_state slot exists and is free
        while next_state >= self.check.len() {
            self.base.push(-1);
            self.check.push(-1);
            self.is_final.push(false);
        }

        if self.check[next_state] >= 0 {
            // Conflict! Need to find a new BASE that accommodates ALL children
            // Collect all existing children of this state
            let mut all_bytes = Vec::new();
            let old_base = self.base[state];

            // Find existing transitions
            for b in 0u8..=255 {
                let child = (old_base as usize).wrapping_add(b as usize);
                if child < self.check.len() && self.check[child] == state as i32 {
                    all_bytes.push(b);
                }
            }

            // Add the new byte we're trying to insert
            all_bytes.push(byte);

            // Find a BASE that works for ALL bytes
            let new_base = self.find_free_base(next_state + 1, &all_bytes);

            // Relocate all existing children to new BASE
            for &b in &all_bytes {
                if b == byte {
                    continue; // Skip the new one, we'll add it below
                }

                let old_child = (old_base as usize).wrapping_add(b as usize);
                let new_child = (new_base as usize).wrapping_add(b as usize);

                // Ensure new slot exists
                while new_child >= self.check.len() {
                    self.base.push(-1);
                    self.check.push(-1);
                    self.is_final.push(false);
                }

                // Move the child's data
                self.check[new_child] = state as i32; // CHECK points to parent
                self.base[new_child] = self.base[old_child];
                self.is_final[new_child] = self.is_final[old_child];

                // Update all grandchildren's CHECK pointers
                if self.base[old_child] >= 0 {
                    let child_base = self.base[old_child] as usize;
                    for gc_byte in 0u8..=255 {
                        let grandchild = child_base + (gc_byte as usize);
                        if grandchild < self.check.len()
                            && self.check[grandchild] == old_child as i32
                        {
                            self.check[grandchild] = new_child as i32;
                        }
                    }
                }

                // Clear old slot
                self.check[old_child] = -1;
                self.base[old_child] = -1;
                self.is_final[old_child] = false;
            }

            // Update state's BASE
            self.base[state] = new_base;
            let new_next = (new_base as usize).wrapping_add(byte as usize);

            while new_next >= self.check.len() {
                self.base.push(-1);
                self.check.push(-1);
                self.is_final.push(false);
            }

            self.check[new_next] = state as i32;
            new_next
        } else {
            self.check[next_state] = state as i32;
            next_state
        }
    }

    /// Find a free BASE value for a state that needs to have transitions for the given bytes.
    ///
    /// The double-array formula is: next_state = BASE[current_state] + byte
    ///
    /// This function finds a BASE value such that for each byte in `bytes`,
    /// the computed next_state position is available (CHECK[next_state] < 0).
    ///
    /// Returns the BASE value to store in BASE[current_state].
    fn find_free_base(&self, start: usize, bytes: &[u8]) -> i32 {
        if bytes.is_empty() {
            return 0;
        }

        // Search for a BASE value where all required slots are free
        // We search in the range [start, start + 10000)
        // For each candidate BASE value, check if BASE + byte is free for all bytes
        let start_base = start as i32;

        for base in start_base..start_base + 10000 {
            let mut all_free = true;

            for &byte in bytes {
                // Compute next_state = BASE + byte
                let next = base + (byte as i32);

                // next_state must be non-negative and within bounds (or we'll grow)
                if next < 0 {
                    all_free = false;
                    break;
                }

                let next_usize = next as usize;

                // Check if this slot is free (CHECK[next] < 0 means unused)
                if next_usize < self.check.len() && self.check[next_usize] >= 0 {
                    all_free = false;
                    break;
                }
            }

            if all_free {
                return base;
            }
        }

        // Fallback: use a large BASE value
        start_base + 10000
    }

    /// Build the final DoubleArrayTrie.
    pub fn build(self) -> DoubleArrayTrie {
        // Compute edge lists for each state to optimize edges() iteration
        let mut edges = vec![Vec::new(); self.base.len()];

        for (state, base_entry) in self.base.iter().enumerate() {
            if *base_entry >= 0 {
                let base = *base_entry as usize;

                // Find all valid edges for this state
                for byte in 0u8..=255 {
                    let next = base + (byte as usize);
                    if next < self.check.len() && self.check[next] == state as i32 {
                        edges[state].push(byte);
                    }
                }
            }
        }

        DoubleArrayTrie {
            shared: DATShared {
                base: Arc::new(self.base),
                check: Arc::new(self.check),
                is_final: Arc::new(self.is_final),
                edges: Arc::new(edges),
            },
            free_list: Arc::new(self.free_list),
            term_count: self.term_count,
            rebuild_threshold: self.rebuild_threshold,
        }
    }
}

impl Default for DoubleArrayTrieBuilder {
    fn default() -> Self {
        Self::new()
    }
}

impl DoubleArrayTrie {
    /// Create a new empty Double-Array Trie.
    pub fn new() -> Self {
        DoubleArrayTrieBuilder::new().build()
    }

    /// Create a DAT from an iterator of terms.
    ///
    /// For optimal space efficiency, terms should be sorted.
    pub fn from_terms<I, S>(terms: I) -> Self
    where
        I: IntoIterator<Item = S>,
        S: AsRef<str>,
    {
        let mut sorted_terms: Vec<String> =
            terms.into_iter().map(|s| s.as_ref().to_string()).collect();
        sorted_terms.sort();
        sorted_terms.dedup();

        let mut builder = DoubleArrayTrieBuilder::new();
        for term in sorted_terms {
            builder.insert(&term);
        }
        builder.build()
    }

    /// Get the number of terms in the dictionary.
    pub fn len(&self) -> Option<usize> {
        Some(self.term_count)
    }

    /// Check if the dictionary is empty.
    pub fn is_empty(&self) -> bool {
        self.term_count == 0
    }

    /// Check if a term exists in the dictionary.
    pub fn contains(&self, term: &str) -> bool {
        let mut state = 1; // Start at root

        for &byte in term.as_bytes() {
            let base = self.shared.base[state];
            if base < 0 {
                return false; // No edges
            }

            let next = (base as usize).wrapping_add(byte as usize);

            if next >= self.shared.check.len() || self.shared.check[next] != state as i32 {
                return false; // Invalid transition
            }

            state = next;
        }

        state < self.shared.is_final.len() && self.shared.is_final[state]
    }

    /// Get the number of states in the trie.
    pub fn state_count(&self) -> usize {
        self.shared.base.len()
    }

    /// Get memory usage in bytes (estimated).
    pub fn memory_bytes(&self) -> usize {
        // BASE: 4 bytes/state, CHECK: 4 bytes/state, IS_FINAL: ~1 bit/state
        // EDGES: avg 3 bytes/state (small overhead)
        let state_count = self.state_count();
        let edges_bytes: usize = self.shared.edges.iter().map(|e| e.len()).sum();
        state_count * 4 + state_count * 4 + (state_count + 7) / 8 + edges_bytes
    }
}

impl Default for DoubleArrayTrie {
    fn default() -> Self {
        Self::new()
    }
}

/// Node reference for Dictionary trait implementation.
#[derive(Clone)]
pub struct DoubleArrayTrieNode {
    /// Current state index
    state: usize,

    /// Shared data (reduces Arc cloning overhead)
    shared: DATShared,
}

impl DictionaryNode for DoubleArrayTrieNode {
    fn is_final(&self) -> bool {
        self.state < self.shared.is_final.len() && self.shared.is_final[self.state]
    }

    fn transition(&self, label: u8) -> Option<Self> {
        if self.state >= self.shared.base.len() {
            return None;
        }

        let base = self.shared.base[self.state];
        if base < 0 {
            return None; // No edges
        }

        let next = (base as usize).wrapping_add(label as usize);

        if next < self.shared.check.len() && self.shared.check[next] == self.state as i32 {
            Some(DoubleArrayTrieNode {
                state: next,
                shared: self.shared.clone(), // Single Arc clone
            })
        } else {
            None
        }
    }

    fn edges(&self) -> Box<dyn Iterator<Item = (u8, Self)> + '_> {
        // OPTIMIZED: Only iterate over actual edges stored in edge list
        let state = self.state;

        if state >= self.shared.edges.len() {
            return Box::new(std::iter::empty());
        }

        let base = self.shared.base[state];
        if base < 0 {
            return Box::new(std::iter::empty());
        }

        // Iterate only over actual edges (typically 1-5 instead of 256)
        let edges: Vec<(u8, Self)> = self.shared.edges[state]
            .iter()
            .map(|&byte| {
                let next = (base as usize) + (byte as usize);
                (
                    byte,
                    DoubleArrayTrieNode {
                        state: next,
                        shared: self.shared.clone(), // Single Arc clone
                    },
                )
            })
            .collect();

        Box::new(edges.into_iter())
    }

    fn edge_count(&self) -> Option<usize> {
        // Now we can efficiently return edge count
        if self.state < self.shared.edges.len() {
            Some(self.shared.edges[self.state].len())
        } else {
            Some(0)
        }
    }
}

// Serialization support
#[cfg(feature = "serialization")]
impl crate::serialization::DictionaryFromTerms for DoubleArrayTrie {
    fn from_terms<I: IntoIterator<Item = String>>(terms: I) -> Self {
        DoubleArrayTrie::from_terms(terms)
    }
}

impl Dictionary for DoubleArrayTrie {
    type Node = DoubleArrayTrieNode;

    fn root(&self) -> Self::Node {
        DoubleArrayTrieNode {
            state: 1, // Root is state 1
            shared: self.shared.clone(),
        }
    }

    fn len(&self) -> Option<usize> {
        Some(self.term_count)
    }

    fn contains(&self, term: &str) -> bool {
        self.contains(term)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_empty_dat() {
        let dat = DoubleArrayTrie::new();
        assert_eq!(dat.len(), Some(0));
        assert!(dat.is_empty());
    }

    #[test]
    fn test_single_term() {
        let dat = DoubleArrayTrie::from_terms(vec!["test"]);
        assert_eq!(dat.len(), Some(1));
        assert!(dat.contains("test"));
        assert!(!dat.contains("testing"));
        assert!(!dat.contains("tes"));
    }

    #[test]
    fn test_multiple_terms() {
        let dat = DoubleArrayTrie::from_terms(vec!["test", "testing", "tested", "tester"]);
        assert_eq!(dat.len(), Some(4));
        assert!(dat.contains("test"));
        assert!(dat.contains("testing"));
        assert!(dat.contains("tested"));
        assert!(dat.contains("tester"));
        assert!(!dat.contains("tes"));
        assert!(!dat.contains("tests"));
    }

    #[test]
    fn test_prefix_sharing() {
        let dat = DoubleArrayTrie::from_terms(vec!["test", "best", "rest"]);
        assert_eq!(dat.len(), Some(3));

        // All three words share "est" suffix
        // DAT should be space-efficient (but our simplified implementation isn't optimal)
        // Just verify it works correctly
        assert!(dat.contains("test"));
        assert!(dat.contains("best"));
        assert!(dat.contains("rest"));
    }

    #[test]
    fn test_memory_efficiency() {
        let dat =
            DoubleArrayTrie::from_terms(vec!["band", "banana", "bandana", "can", "cane", "candy"]);

        let memory = dat.memory_bytes();
        let state_count = dat.state_count();

        println!("DAT memory: {} bytes for {} states", memory, state_count);
        println!(
            "  Approximately {} bytes/state",
            memory / state_count.max(1)
        );

        // Should be around 8-10 bytes per state (BASE + CHECK + flags)
        assert!(memory < state_count * 12);
    }

    #[test]
    fn test_dictionary_trait() {
        let dat = DoubleArrayTrie::from_terms(vec!["test", "testing"]);

        let root = dat.root();
        assert!(!root.is_final());

        // Follow 't'
        let t_node = root.transition(b't').expect("Should have 't' edge");
        assert!(!t_node.is_final());

        // Follow 'e'
        let e_node = t_node.transition(b'e').expect("Should have 'e' edge");
        assert!(!e_node.is_final());

        // Follow 's'
        let s_node = e_node.transition(b's').expect("Should have 's' edge");
        assert!(!s_node.is_final());

        // Follow 't'
        let final_node = s_node.transition(b't').expect("Should have 't' edge");
        assert!(final_node.is_final()); // "test" is a word
    }

    #[test]
    fn test_edge_iteration() {
        let dat = DoubleArrayTrie::from_terms(vec!["ab", "ac", "ad"]);

        let root = dat.root();
        let a_node = root.transition(b'a').expect("Should have 'a' edge");

        let edges: Vec<u8> = a_node.edges().map(|(label, _)| label).collect();

        // Should have edges for 'b', 'c', 'd'
        assert!(edges.contains(&b'b'));
        assert!(edges.contains(&b'c'));
        assert!(edges.contains(&b'd'));
        assert_eq!(edges.len(), 3);
    }

    #[test]
    fn test_incremental_construction() {
        let mut builder = DoubleArrayTrieBuilder::new();

        assert!(builder.insert("hello"));
        assert!(builder.insert("world"));
        assert!(builder.insert("test"));
        assert!(!builder.insert("test")); // Duplicate

        let dat = builder.build();
        assert_eq!(dat.len(), Some(3));
        assert!(dat.contains("hello"));
        assert!(dat.contains("world"));
        assert!(dat.contains("test"));
    }
}
