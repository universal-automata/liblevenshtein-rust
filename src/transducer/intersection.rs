//! Intersection of dictionary traversal and automaton state.

use super::state::State;
use crate::dictionary::DictionaryNode;

/// Intersection of dictionary node and Levenshtein automaton state.
///
/// Represents a point in the simultaneous traversal of both the dictionary
/// graph and the Levenshtein automaton. Each intersection tracks:
/// - The current dictionary node
/// - The current automaton state (positions)
/// - The edge label from the parent (for path reconstruction)
/// - A link to the parent intersection (for backtracking)
pub struct Intersection<N: DictionaryNode> {
    /// Edge label from parent (character)
    pub label: Option<u8>,

    /// Current dictionary node
    pub node: N,

    /// Current automaton state
    pub state: State,

    /// Parent intersection (for path reconstruction)
    pub parent: Option<Box<Intersection<N>>>,
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

    /// Create a child intersection with a parent link
    pub fn with_parent(
        label: u8,
        node: N,
        state: State,
        parent: Box<Intersection<N>>,
    ) -> Self {
        Self {
            label: Some(label),
            node,
            state,
            parent: Some(parent),
        }
    }

    /// Reconstruct the term (path) from root to this intersection
    pub fn term(&self) -> String {
        let mut bytes = Vec::new();
        self.collect_path(&mut bytes);
        bytes.reverse();
        String::from_utf8_lossy(&bytes).into_owned()
    }

    /// Recursively collect path bytes
    fn collect_path(&self, bytes: &mut Vec<u8>) {
        if let Some(label) = self.label {
            bytes.push(label);
            if let Some(parent) = &self.parent {
                parent.collect_path(bytes);
            }
        }
    }

    /// Get the depth (length of path from root)
    pub fn depth(&self) -> usize {
        match &self.parent {
            Some(parent) => 1 + parent.depth(),
            None => 0,
        }
    }

    /// Check if this intersection represents a complete match
    pub fn is_final(&self) -> bool {
        self.node.is_final()
    }

    /// Get the minimum distance at this intersection
    pub fn min_distance(&self) -> Option<usize> {
        self.state.min_distance()
    }
}

// Manual Clone implementation - clones parent reference
impl<N: DictionaryNode> Clone for Intersection<N> {
    fn clone(&self) -> Self {
        Self {
            label: self.label,
            node: self.node.clone(),
            state: self.state.clone(),
            // Clone the parent box reference (shallow copy)
            parent: self.parent.clone(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::dictionary::pathmap::PathMapDictionary;
    use crate::dictionary::Dictionary;
    use crate::transducer::Position;

    #[test]
    fn test_intersection_creation() {
        let dict = PathMapDictionary::from_iter(vec!["test"]);
        let root = dict.root();
        let state = State::single(Position::new(0, 0));

        let intersection = Intersection::new(root, state);
        assert_eq!(intersection.depth(), 0);
        assert_eq!(intersection.term(), "");
    }

    #[test]
    fn test_intersection_path_reconstruction() {
        let dict = PathMapDictionary::from_iter(vec!["test"]);
        let root = dict.root();

        // Build path: t -> e -> s
        let i1 = Intersection::new(root.clone(), State::new());
        let t_node = root.transition(b't').unwrap();

        let i2 = Intersection::with_parent(
            b't',
            t_node.clone(),
            State::new(),
            Box::new(i1),
        );

        let e_node = t_node.transition(b'e').unwrap();
        let i3 = Intersection::with_parent(
            b'e',
            e_node.clone(),
            State::new(),
            Box::new(i2),
        );

        let s_node = e_node.transition(b's').unwrap();
        let i4 = Intersection::with_parent(
            b's',
            s_node,
            State::new(),
            Box::new(i3),
        );

        assert_eq!(i4.term(), "tes");
        assert_eq!(i4.depth(), 3);
    }
}
