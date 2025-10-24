//! Dictionary abstractions for pluggable backends.
//!
//! This module provides traits that abstract over different dictionary
//! implementations (tries, DAWGs, etc.) for use with Levenshtein automata.

pub mod pathmap;
pub mod dawg;

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
        for byte in term.as_bytes() {
            match node.transition(*byte) {
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
}

/// Traversable dictionary node.
///
/// Nodes form a graph structure representing the dictionary, where edges
/// are labeled with bytes (characters) and final nodes mark valid terms.
pub trait DictionaryNode: Clone + Send + Sync {
    /// Check if this node marks the end of a valid term
    fn is_final(&self) -> bool;

    /// Transition to a child node via the given byte
    ///
    /// Returns `None` if no such transition exists
    fn transition(&self, label: u8) -> Option<Self>;

    /// Iterate over all outgoing edges as (byte, child_node) pairs
    fn edges(&self) -> Box<dyn Iterator<Item = (u8, Self)> + '_>;

    /// Check if a specific edge exists
    fn has_edge(&self, label: u8) -> bool {
        self.transition(label).is_some()
    }

    /// Get the number of outgoing edges (if efficiently available)
    fn edge_count(&self) -> Option<usize> {
        None
    }
}
