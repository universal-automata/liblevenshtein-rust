//! Dictionary abstractions for pluggable backends.
//!
//! This module provides traits that abstract over different dictionary
//! implementations (tries, DAWGs, etc.) for use with Levenshtein automata.

pub mod char_unit;
pub mod compressed_suffix_automaton;
pub mod dawg;
pub mod dawg_optimized;
pub mod dawg_query;
pub mod double_array_trie;
pub mod double_array_trie_char;
pub mod dynamic_dawg;
pub mod factory;
#[cfg(feature = "pathmap-backend")]
pub mod pathmap;
#[cfg(feature = "pathmap-backend")]
pub mod pathmap_char;
pub mod suffix_automaton;
pub mod value;

pub use char_unit::CharUnit;
pub use value::DictionaryValue;

/// Synchronization strategy for dictionary operations.
///
/// Different dictionary backends may have different thread-safety guarantees.
/// This trait allows backends to specify their synchronization requirements.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SyncStrategy {
    /// Backend requires external synchronization (e.g., RwLock).
    ///
    /// Use this for backends that use interior mutability without
    /// internal synchronization.
    ExternalSync,

    /// Backend is internally synchronized and safe for concurrent access.
    ///
    /// Use this for backends that use atomic operations, locks, or
    /// lock-free data structures internally.
    InternalSync,

    /// Backend is a persistent/immutable data structure.
    ///
    /// Mutations create new versions with structural sharing.
    /// Reads require no synchronization. Writes can use atomic swaps.
    Persistent,
}

/// Core dictionary abstraction for approximate string matching.
///
/// A dictionary represents a collection of terms that can be efficiently
/// traversed character-by-character via graph-like nodes. This trait
/// allows different backend implementations (trie, DAWG, double-array trie,
/// etc.) to be used interchangeably.
pub trait Dictionary {
    /// The node type used for dictionary traversal
    type Node: DictionaryNode;

    /// Get the root node of the dictionary
    fn root(&self) -> Self::Node;

    /// Check if a term exists in the dictionary
    fn contains(&self, term: &str) -> bool {
        let mut node = self.root();
        for unit in <Self::Node as DictionaryNode>::Unit::iter_str(term) {
            match node.transition(unit) {
                Some(next) => node = next,
                None => return false,
            }
        }
        node.is_final()
    }

    /// Get the total number of terms (if available efficiently)
    fn len(&self) -> Option<usize>;

    /// Check if the dictionary is empty
    fn is_empty(&self) -> bool {
        self.len().map(|n| n == 0).unwrap_or(false)
    }

    /// Get the synchronization strategy for this dictionary backend.
    ///
    /// This allows wrappers to optimize synchronization based on
    /// the backend's thread-safety guarantees.
    ///
    /// Default: `ExternalSync` (conservative, always safe)
    fn sync_strategy(&self) -> SyncStrategy {
        SyncStrategy::ExternalSync
    }

    /// Check if this dictionary uses suffix-based matching (substring search).
    ///
    /// Suffix-based dictionaries (like SuffixAutomaton) match substrings anywhere
    /// in the indexed text, whereas prefix-based dictionaries match complete words
    /// from the beginning.
    ///
    /// This affects how the Levenshtein automaton computes match distances:
    /// - Prefix-based: penalizes unmatched query suffix
    /// - Suffix-based: allows partial query matches without penalty
    ///
    /// Default: `false` (prefix-based matching)
    fn is_suffix_based(&self) -> bool {
        false
    }
}

/// Traversable dictionary node.
///
/// Nodes form a graph structure representing the dictionary, where edges
/// are labeled with character units (bytes or Unicode characters) and final
/// nodes mark valid terms.
///
/// # Type Parameters
///
/// The node is generic over [`CharUnit`], which can be:
/// - [`u8`] for byte-level matching (faster, ASCII-optimized)
/// - [`char`] for character-level matching (correct Unicode semantics)
pub trait DictionaryNode: Clone + Send + Sync {
    /// The character unit type for edge labels.
    ///
    /// Use `u8` for byte-level (existing behavior, fastest).
    /// Use `char` for character-level (proper Unicode support).
    type Unit: CharUnit;

    /// Check if this node marks the end of a valid term
    fn is_final(&self) -> bool;

    /// Transition to a child node via the given character unit
    ///
    /// Returns `None` if no such transition exists
    fn transition(&self, label: Self::Unit) -> Option<Self>;

    /// Iterate over all outgoing edges as (unit, child_node) pairs
    fn edges(&self) -> Box<dyn Iterator<Item = (Self::Unit, Self)> + '_>;

    /// Check if a specific edge exists
    fn has_edge(&self, label: Self::Unit) -> bool {
        self.transition(label).is_some()
    }

    /// Get the number of outgoing edges (if efficiently available)
    fn edge_count(&self) -> Option<usize> {
        None
    }
}

/// Extension trait for dictionaries that map terms to values.
///
/// This trait enables "fuzzy maps" - dictionaries that associate arbitrary values
/// with terms, allowing efficient filtered queries based on those values. This is
/// particularly useful for contextual code completion where terms are mapped to
/// scope IDs, categories, or other metadata.
///
/// # Examples
///
/// ```ignore
/// use liblevenshtein::prelude::*;
/// use liblevenshtein::dictionary::value::DictionaryValue;
///
/// // Implement for a dictionary backend that supports values
/// # struct MyDict;
/// # struct MyNode;
/// # impl Clone for MyNode { fn clone(&self) -> Self { MyNode } }
/// # impl DictionaryNode for MyNode {
/// #     fn is_final(&self) -> bool { false }
/// #     fn transition(&self, _label: u8) -> Option<Self> { None }
/// #     fn edges(&self) -> Box<dyn Iterator<Item = (u8, Self)> + '_> { Box::new(std::iter::empty()) }
/// # }
/// # impl Dictionary for MyDict {
/// #     type Node = MyNode;
/// #     fn root(&self) -> Self::Node { MyNode }
/// #     fn len(&self) -> Option<usize> { None }
/// # }
/// impl MappedDictionary for MyDict {
///     type Value = u32; // Map terms to scope IDs
///
///     fn get_value(&self, term: &str) -> Option<Self::Value> {
///         // Look up the value for this term
///         # None
///     }
/// }
/// ```
///
/// # Performance
///
/// Filtering during graph traversal (using values) provides 10-100x speedups
/// compared to post-filtering, especially when filters are highly selective.
pub trait MappedDictionary: Dictionary {
    /// The type of values associated with dictionary terms
    type Value: DictionaryValue;

    /// Get the value associated with a term
    ///
    /// Returns `None` if the term doesn't exist in the dictionary.
    fn get_value(&self, term: &str) -> Option<Self::Value> {
        // Default implementation: traverse to find the term, but return no value
        // (for backward compatibility with non-mapped dictionaries)
        if self.contains(term) {
            None
        } else {
            None
        }
    }

    /// Check if a term exists and its value matches a predicate
    ///
    /// This is more efficient than `get_value` + predicate test, as it can
    /// short-circuit early if the term doesn't exist.
    fn contains_with_value<F>(&self, term: &str, predicate: F) -> bool
    where
        F: Fn(&Self::Value) -> bool,
    {
        self.get_value(term).map_or(false, |v| predicate(&v))
    }
}

/// Extension trait for dictionary nodes that provide access to values.
///
/// This trait allows nodes to expose values during graph traversal, enabling
/// efficient filtering at query time without materializing all results first.
pub trait MappedDictionaryNode: DictionaryNode {
    /// The type of values associated with terms at this node
    type Value: DictionaryValue;

    /// Get the value at this node if it's a final node
    ///
    /// Returns `None` if this is not a final node, or if no value is associated.
    fn value(&self) -> Option<Self::Value>;
}
