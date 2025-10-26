//! DAWG-specific query iterator that eliminates Arc operations.
//!
//! This module provides an optimized query iterator for DawgDictionary
//! that works directly with node indices instead of DawgDictionaryNode,
//! eliminating Arc::clone operations during traversal.

use super::dawg::DawgNode;
use crate::transducer::transition::{initial_state, transition_state_pooled};
use crate::transducer::{Algorithm, PathNode, State, StatePool};
use std::collections::VecDeque;
use std::sync::Arc;

/// Intersection for DAWG traversal using node indices.
///
/// This eliminates Arc cloning by using indices instead of DawgDictionaryNode.
/// The shared Arc<Vec<DawgNode>> is stored at the iterator level.
struct DawgIntersection {
    /// Edge label from parent
    label: Option<u8>,
    /// Node index in the DAWG
    node_idx: usize,
    /// Current automaton state
    state: State,
    /// Parent path (for path reconstruction) - lightweight, no Arc
    parent: Option<Box<PathNode>>,
}

impl DawgIntersection {
    /// Create a new intersection (root)
    fn new(node_idx: usize, state: State) -> Self {
        Self {
            label: None,
            node_idx,
            state,
            parent: None,
        }
    }

    /// Create a child intersection with a parent path
    fn with_parent(
        label: u8,
        node_idx: usize,
        state: State,
        parent: Option<Box<PathNode>>,
    ) -> Self {
        Self {
            label: Some(label),
            node_idx,
            state,
            parent,
        }
    }

    /// Reconstruct the term (path) from root to this intersection
    fn term(&self) -> String {
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
}

/// Query result containing term and distance.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DawgCandidate {
    /// The matching term
    pub term: String,
    /// Edit distance from query
    pub distance: usize,
}

/// Optimized query iterator for DAWG dictionaries.
///
/// This iterator works directly with node indices instead of DawgDictionaryNode,
/// eliminating Arc::clone operations on every edge traversal. This provides
/// an estimated 10-15% performance improvement over the generic QueryIterator.
///
/// # Performance
///
/// - **Arc elimination**: No Arc clones during traversal
/// - **Cache efficiency**: Smaller intersection structures
/// - **Memory efficiency**: Single shared Arc for entire query
///
/// # Example
///
/// ```rust,ignore
/// use liblevenshtein::prelude::*;
///
/// let dawg = DawgDictionary::from_iter(vec!["test", "testing"]);
/// let iter = dawg.query_optimized("tset", 2, Algorithm::Standard);
///
/// for term in iter {
///     println!("Found: {}", term);
/// }
/// ```
pub struct DawgQueryIterator {
    /// Shared DAWG nodes (single Arc for entire query)
    nodes: Arc<Vec<DawgNode>>,
    /// Pending intersections to explore
    pending: VecDeque<Box<DawgIntersection>>,
    /// Query bytes
    query: Vec<u8>,
    /// Maximum edit distance
    max_distance: usize,
    /// Levenshtein algorithm
    algorithm: Algorithm,
    /// Whether iteration is finished
    finished: bool,
    /// State pool for allocation reuse
    state_pool: StatePool,
}

impl DawgQueryIterator {
    /// Create a new DAWG query iterator
    pub fn new(
        nodes: Arc<Vec<DawgNode>>,
        query: String,
        max_distance: usize,
        algorithm: Algorithm,
    ) -> Self {
        let query_bytes = query.into_bytes();
        let initial = initial_state(query_bytes.len(), max_distance);

        let mut pending = VecDeque::new();
        pending.push_back(Box::new(DawgIntersection::new(0, initial)));

        Self {
            nodes,
            pending,
            query: query_bytes,
            max_distance,
            algorithm,
            finished: false,
            state_pool: StatePool::new(),
        }
    }

    /// Advance to the next match
    fn advance(&mut self) -> Option<String> {
        while let Some(intersection) = self.pending.pop_front() {
            let node = &self.nodes[intersection.node_idx];

            // Check if this is a final match
            if node.is_final {
                // Infer the distance
                if let Some(distance) = intersection.state.infer_distance(self.query.len()) {
                    if distance <= self.max_distance {
                        let term = intersection.term();

                        // Queue children for further exploration
                        self.queue_children(&intersection);

                        return Some(term);
                    }
                }
            }

            // Queue children even if not final (continue exploring)
            if !node.is_final {
                self.queue_children(&intersection);
            }
        }

        self.finished = true;
        None
    }

    /// Queue child intersections for exploration
    fn queue_children(&mut self, intersection: &DawgIntersection) {
        let node = &self.nodes[intersection.node_idx];

        // ✅ Iterate edges using indices - NO Arc clone!
        for &(label, child_idx) in &node.edges {
            if let Some(next_state) = transition_state_pooled(
                &intersection.state,
                &mut self.state_pool,
                label,
                &self.query,
                self.max_distance,
                self.algorithm,
                false, // Exact matching (not prefix mode)
            ) {
                // Create lightweight PathNode (no Arc clone!)
                let parent_path = intersection.label.map(|current_label| {
                    Box::new(PathNode::new(
                        current_label,
                        intersection.parent.clone(), // Clone PathNode chain (cheap)
                    ))
                });

                let child = Box::new(DawgIntersection::with_parent(
                    label,
                    child_idx, // ← Index, not DawgDictionaryNode!
                    next_state,
                    parent_path,
                ));

                self.pending.push_back(child);
            }
        }
    }
}

impl Iterator for DawgQueryIterator {
    type Item = String;

    fn next(&mut self) -> Option<Self::Item> {
        if self.finished {
            None
        } else {
            self.advance()
        }
    }
}

/// Optimized candidate iterator for DAWG dictionaries.
///
/// Returns `DawgCandidate` structs with both term and distance.
pub struct DawgCandidateIterator {
    inner: DawgQueryIterator,
}

impl DawgCandidateIterator {
    /// Create a new DAWG candidate iterator
    pub fn new(
        nodes: Arc<Vec<DawgNode>>,
        query: String,
        max_distance: usize,
        algorithm: Algorithm,
    ) -> Self {
        Self {
            inner: DawgQueryIterator::new(nodes, query, max_distance, algorithm),
        }
    }
}

impl Iterator for DawgCandidateIterator {
    type Item = DawgCandidate;

    fn next(&mut self) -> Option<Self::Item> {
        // Get next term from inner iterator
        let term = self.inner.advance()?;

        // Recompute distance
        let distance = self.compute_distance(&term);

        Some(DawgCandidate { term, distance })
    }
}

impl DawgCandidateIterator {
    /// Compute edit distance between query and term.
    fn compute_distance(&self, term: &str) -> usize {
        let query = std::str::from_utf8(&self.inner.query).unwrap_or("");
        let query_chars: Vec<char> = query.chars().collect();
        let term_chars: Vec<char> = term.chars().collect();

        let m = query_chars.len();
        let n = term_chars.len();

        let mut dp = vec![vec![0; n + 1]; m + 1];

        // Initialize first row and column
        for i in 0..=m {
            dp[i][0] = i;
        }
        for j in 0..=n {
            dp[0][j] = j;
        }

        // Fill the DP table
        for i in 1..=m {
            for j in 1..=n {
                let cost = if query_chars[i - 1] == term_chars[j - 1] {
                    0
                } else {
                    1
                };

                dp[i][j] = (dp[i - 1][j] + 1) // deletion
                    .min(dp[i][j - 1] + 1) // insertion
                    .min(dp[i - 1][j - 1] + cost); // substitution
            }
        }

        dp[m][n]
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::dictionary::dawg::DawgDictionary;

    #[test]
    fn test_dawg_query_exact_match() {
        let dawg = DawgDictionary::from_iter(vec!["test"]);
        let iter =
            DawgQueryIterator::new(dawg.nodes_arc(), "test".to_string(), 0, Algorithm::Standard);

        let result: Vec<_> = iter.collect();
        assert_eq!(result, vec!["test"]);
    }

    #[test]
    fn test_dawg_query_with_distance() {
        let dawg = DawgDictionary::from_iter(vec!["test", "best", "rest", "testing"]);
        let iter =
            DawgQueryIterator::new(dawg.nodes_arc(), "test".to_string(), 1, Algorithm::Standard);

        let results: Vec<_> = iter.collect();
        assert!(results.contains(&"test".to_string()));
        assert!(results.contains(&"best".to_string()));
        assert!(results.contains(&"rest".to_string()));
    }

    #[test]
    fn test_dawg_candidate_iterator() {
        let dawg = DawgDictionary::from_iter(vec!["test", "best"]);
        let iter = DawgCandidateIterator::new(
            dawg.nodes_arc(),
            "test".to_string(),
            1,
            Algorithm::Standard,
        );

        let candidates: Vec<_> = iter.collect();
        assert!(candidates
            .iter()
            .any(|c| c.term == "test" && c.distance == 0));
        assert!(candidates
            .iter()
            .any(|c| c.term == "best" && c.distance == 1));
    }
}
