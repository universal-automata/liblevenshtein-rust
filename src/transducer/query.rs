//! Lazy query iterators for approximate string matching.

use super::transition::{initial_state, transition_state_pooled};
use super::{Algorithm, Intersection, StatePool};
use crate::dictionary::DictionaryNode;
use std::collections::VecDeque;

/// Query result containing term and distance.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Candidate {
    /// The matching term
    pub term: String,
    /// Edit distance from query
    pub distance: usize,
}

/// Lazy iterator over matching terms (strings only).
///
/// Iterates over all dictionary terms within `max_distance` edits
/// of the query term, yielding just the term strings.
///
/// # Performance
///
/// Uses StatePool to eliminate State cloning overhead during traversal.
/// The pool is created per-query and reuses State allocations across
/// all transitions, reducing memory allocation by 6-10% of runtime.
pub struct QueryIterator<N: DictionaryNode> {
    pending: VecDeque<Box<Intersection<N>>>,
    query: Vec<u8>,
    max_distance: usize,
    algorithm: Algorithm,
    finished: bool,
    state_pool: StatePool, // Pool for State allocation reuse
    substring_mode: bool,  // Enable substring matching (for suffix automata)
}

impl<N: DictionaryNode> QueryIterator<N> {
    /// Create a new query iterator
    pub fn new(root: N, query: String, max_distance: usize, algorithm: Algorithm) -> Self {
        Self::with_substring_mode(root, query, max_distance, algorithm, false)
    }

    /// Create a new query iterator with substring matching mode
    pub fn with_substring_mode(
        root: N,
        query: String,
        max_distance: usize,
        algorithm: Algorithm,
        substring_mode: bool,
    ) -> Self {
        let query_bytes = query.into_bytes();
        let initial = initial_state(query_bytes.len(), max_distance, algorithm);

        let mut pending = VecDeque::new();
        let root_intersection = Intersection::new(root.clone(), initial.clone());

        // Check if root node is final (handles empty string case)
        // Without this check, empty strings in the dictionary are never returned
        // because the root node has no outgoing edges to trigger the finality check
        // in the main loop. See: docs/CROSS_VALIDATION_BUG_REPORT.md
        if root_intersection.is_final() {
            let distance = if substring_mode {
                root_intersection.state.min_distance().unwrap_or(usize::MAX)
            } else {
                root_intersection
                    .state
                    .infer_distance(query_bytes.len())
                    .unwrap_or(usize::MAX)
            };

            if distance <= max_distance {
                // Root is final and within distance: prioritize empty string by adding to front
                pending.push_front(Box::new(root_intersection.clone()));
            }
        }

        pending.push_back(Box::new(Intersection::new(root, initial)));

        Self {
            pending,
            query: query_bytes,
            max_distance,
            algorithm,
            finished: false,
            state_pool: StatePool::new(), // Create pool for this query
            substring_mode,
        }
    }

    /// Advance to the next match
    fn advance(&mut self) -> Option<String> {
        while let Some(intersection) = self.pending.pop_front() {
            // Check if this is a final match
            if intersection.is_final() {
                // Infer the distance based on matching mode
                let distance = if self.substring_mode {
                    // Substring mode: don't penalize unmatched query suffix
                    intersection.state.min_distance().unwrap_or(usize::MAX)
                } else {
                    // Standard mode: penalize remaining query characters
                    intersection
                        .state
                        .infer_distance(self.query.len())
                        .unwrap_or(usize::MAX)
                };

                if distance <= self.max_distance {
                    let term = intersection.term();

                    // Queue children for further exploration
                    self.queue_children(&intersection);

                    return Some(term);
                } else {
                    // Even if this final node is too far, we must still explore its children
                    // Example: dict ["z", "za"], query "za" (dist=0)
                    // At 'z': is_final=true, distance=1 (too far), but we must explore 'a'
                    self.queue_children(&intersection);
                }
            } else {
                // Not final: queue children to continue exploring
                self.queue_children(&intersection);
            }
        }

        self.finished = true;
        None
    }

    /// Queue child intersections for exploration
    fn queue_children(&mut self, intersection: &Intersection<N>) {
        for (label, child_node) in intersection.node.edges() {
            if let Some(next_state) = transition_state_pooled(
                &intersection.state,
                &mut self.state_pool, // Use pool for State allocation reuse
                label,
                &self.query,
                self.max_distance,
                self.algorithm,
                self.substring_mode, // Use prefix_mode=true only for substring matching
            ) {
                // ✅ Create lightweight PathNode (no Arc clone!)
                // Only stores label and parent chain - dictionary node not needed in parent
                let parent_path = intersection.label.map(|current_label| {
                    Box::new(super::intersection::PathNode::new(
                        current_label,
                        intersection.parent.clone(), // Clone PathNode chain (cheap)
                    ))
                });

                let child = Box::new(Intersection::with_parent(
                    label,
                    child_node,
                    next_state,
                    parent_path, // ← Lightweight path, no node cloning!
                ));

                self.pending.push_back(child);
            }
        }
    }
}

impl<N: DictionaryNode> Iterator for QueryIterator<N> {
    type Item = String;

    fn next(&mut self) -> Option<Self::Item> {
        if self.finished {
            None
        } else {
            self.advance()
        }
    }
}

/// Lazy iterator over matching candidates (term + distance).
///
/// Iterates over all dictionary terms within `max_distance` edits
/// of the query term, yielding `Candidate` structs with both the
/// term and its computed edit distance.
pub struct CandidateIterator<N: DictionaryNode> {
    inner: QueryIterator<N>,
}

impl<N: DictionaryNode> CandidateIterator<N> {
    /// Create a new candidate iterator
    pub fn new(root: N, query: String, max_distance: usize, algorithm: Algorithm) -> Self {
        Self {
            inner: QueryIterator::new(root, query, max_distance, algorithm),
        }
    }
}

impl<N: DictionaryNode> Iterator for CandidateIterator<N> {
    type Item = Candidate;

    fn next(&mut self) -> Option<Self::Item> {
        // Get next term from inner iterator
        let term = self.inner.advance()?;

        // Recompute distance (could be optimized by caching)
        // For now, use simple character-level comparison
        let distance = self.compute_distance(&term);

        Some(Candidate { term, distance })
    }
}

impl<N: DictionaryNode> CandidateIterator<N> {
    /// Compute edit distance between query and term.
    ///
    /// This is a simplified implementation using dynamic programming.
    /// In production, you'd use the distance module implementations.
    fn compute_distance(&self, term: &str) -> usize {
        let query = std::str::from_utf8(&self.inner.query).unwrap_or("");
        let query_chars: Vec<char> = query.chars().collect();
        let term_chars: Vec<char> = term.chars().collect();

        let m = query_chars.len();
        let n = term_chars.len();

        let mut dp = vec![vec![0; n + 1]; m + 1];

        // Initialize first row and column
        for (i, row) in dp.iter_mut().enumerate().take(m + 1) {
            row[0] = i;
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
    use crate::dictionary::double_array_trie::DoubleArrayTrie;
    use crate::dictionary::Dictionary;

    #[test]
    fn test_query_exact_match() {
        let dict = DoubleArrayTrie::from_terms(vec!["test"]);
        let query = QueryIterator::new(dict.root(), "test".to_string(), 0, Algorithm::Standard);

        let result: Vec<_> = query.collect();
        assert_eq!(result, vec!["test"]);
    }

    #[test]
    fn test_query_with_distance() {
        let dict = DoubleArrayTrie::from_terms(vec!["test", "best", "rest", "testing"]);
        let query = QueryIterator::new(dict.root(), "test".to_string(), 1, Algorithm::Standard);

        let results: Vec<_> = query.collect();
        assert!(results.contains(&"test".to_string()));
        assert!(results.contains(&"best".to_string()));
        assert!(results.contains(&"rest".to_string()));
        // "testing" should not match with distance 1
    }

    #[test]
    fn test_candidate_iterator() {
        let dict = DoubleArrayTrie::from_terms(vec!["test", "best"]);
        let query = CandidateIterator::new(dict.root(), "test".to_string(), 1, Algorithm::Standard);

        let candidates: Vec<_> = query.collect();
        assert!(candidates
            .iter()
            .any(|c| c.term == "test" && c.distance == 0));
        assert!(candidates
            .iter()
            .any(|c| c.term == "best" && c.distance == 1));
    }

    #[test]
    fn test_empty_query() {
        let dict = DoubleArrayTrie::from_terms(vec!["test"]);
        let query = QueryIterator::new(dict.root(), "".to_string(), 0, Algorithm::Standard);

        let results: Vec<_> = query.collect();
        // Empty query with distance 0 should match nothing unless dict has empty string
        assert!(results.is_empty() || results.contains(&"".to_string()));
    }
}
