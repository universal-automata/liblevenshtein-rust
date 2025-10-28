//! Intersection of dictionary traversal and automaton state.

use super::state::State;
use crate::dictionary::DictionaryNode;

/// Lightweight representation of path history.
///
/// Used to reconstruct the term path without storing full Intersection data.
/// This eliminates Arc overhead from dictionary node cloning in parent chains.
///
/// # Memory Efficiency
///
/// PathNode is ~16 bytes (label + pointer) vs ~50+ bytes for full Intersection.
/// For queries exploring 1000 paths, this saves ~34KB per query.
///
/// # Performance
///
/// Eliminates Arc::clone operations in parent chains, reducing query overhead
/// by an estimated 15-25% for DAWG dictionaries.
#[derive(Clone)]
pub struct PathNode {
    /// Edge label from parent
    label: u8,
    /// Parent in the path
    parent: Option<Box<PathNode>>,
}

impl PathNode {
    /// Create a new path node
    #[inline(always)]
    pub fn new(label: u8, parent: Option<Box<PathNode>>) -> Self {
        Self { label, parent }
    }

    /// Collect labels into vector (for term reconstruction)
    pub fn collect_labels(&self, labels: &mut Vec<u8>) {
        labels.push(self.label);
        if let Some(parent) = &self.parent {
            parent.collect_labels(labels);
        }
    }

    /// Get the depth (number of labels in the path)
    pub fn depth(&self) -> usize {
        match &self.parent {
            Some(parent) => 1 + parent.depth(),
            None => 1,
        }
    }
}

/// Intersection of dictionary node and Levenshtein automaton state.
///
/// Represents a point in the simultaneous traversal of both the dictionary
/// graph and the Levenshtein automaton. Each intersection tracks:
/// - The current dictionary node
/// - The current automaton state (positions)
/// - The edge label from the parent (for path reconstruction)
/// - A lightweight parent path (for backtracking)
///
/// # Performance Optimization
///
/// Uses PathNode for parent chain instead of full Intersection to eliminate
/// Arc cloning overhead. The parent chain only needs labels for path
/// reconstruction, not the full dictionary node.
pub struct Intersection<N: DictionaryNode> {
    /// Edge label from parent (character)
    pub label: Option<u8>,

    /// Current dictionary node
    pub node: N,

    /// Current automaton state
    pub state: State,

    /// Parent path (for path reconstruction) - lightweight, no node cloning
    pub parent: Option<Box<PathNode>>,
}

impl<N: DictionaryNode> Intersection<N> {
    /// Create a new intersection (root)
    pub fn new(node: N, state: State) -> Self {
        Self {
            label: None,
            node,
            state,
            parent: None,
        }
    }

    /// Create a child intersection with a parent path
    #[inline]
    pub fn with_parent(label: u8, node: N, state: State, parent: Option<Box<PathNode>>) -> Self {
        Self {
            label: Some(label),
            node,
            state,
            parent,
        }
    }

    /// Reconstruct the term (path) from root to this intersection
    pub fn term(&self) -> String {
        let mut bytes = Vec::new();

        // Collect current label
        if let Some(label) = self.label {
            bytes.push(label);
        }

        // Collect parent labels
        if let Some(parent) = &self.parent {
            parent.collect_labels(&mut bytes);
        }

        bytes.reverse();
        String::from_utf8_lossy(&bytes).into_owned()
    }

    /// Get the depth (length of path from root)
    pub fn depth(&self) -> usize {
        match &self.parent {
            Some(parent) => 1 + parent.depth(),
            None => {
                if self.label.is_some() {
                    1
                } else {
                    0
                }
            }
        }
    }

    /// Check if this intersection represents a complete match
    #[inline(always)]
    pub fn is_final(&self) -> bool {
        self.node.is_final()
    }

    /// Get the minimum distance at this intersection
    #[inline(always)]
    pub fn min_distance(&self) -> Option<usize> {
        self.state.min_distance()
    }
}

// Manual Clone implementation - clones PathNode parent (lightweight)
impl<N: DictionaryNode> Clone for Intersection<N> {
    fn clone(&self) -> Self {
        Self {
            label: self.label,
            node: self.node.clone(),
            state: self.state.clone(),
            // Clone PathNode parent (cheap - no dictionary node cloning)
            parent: self.parent.clone(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::dictionary::double_array_trie::DoubleArrayTrie;
    use crate::dictionary::Dictionary;
    use crate::transducer::Position;

    #[test]
    fn test_intersection_creation() {
        let dict = DoubleArrayTrie::from_terms(vec!["test"]);
        let root = dict.root();
        let state = State::single(Position::new(0, 0));

        let intersection = Intersection::new(root, state);
        assert_eq!(intersection.depth(), 0);
        assert_eq!(intersection.term(), "");
    }

    #[test]
    fn test_intersection_path_reconstruction() {
        let dict = DoubleArrayTrie::from_terms(vec!["test"]);
        let root = dict.root();

        // Build path: t -> e -> s using PathNode
        let t_node = root.transition(b't').unwrap();
        let i2 = Intersection::with_parent(
            b't',
            t_node.clone(),
            State::new(),
            None, // Root parent
        );

        let e_node = t_node.transition(b'e').unwrap();
        let i3 = Intersection::with_parent(
            b'e',
            e_node.clone(),
            State::new(),
            Some(Box::new(PathNode::new(b't', None))), // t -> root
        );

        let s_node = e_node.transition(b's').unwrap();
        let i4 = Intersection::with_parent(
            b's',
            s_node,
            State::new(),
            Some(Box::new(PathNode::new(
                b'e',
                Some(Box::new(PathNode::new(b't', None))),
            ))), // e -> t -> root
        );

        assert_eq!(i4.term(), "tes");
        assert_eq!(i4.depth(), 3);
    }
}
