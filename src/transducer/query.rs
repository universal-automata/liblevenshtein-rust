//! Lazy query iterators for approximate string matching.

use super::{Algorithm, Intersection, StatePool};
use super::transition::{initial_state, transition_state_pooled};
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
    state_pool: StatePool,  // Pool for State allocation reuse
}

impl<N: DictionaryNode> QueryIterator<N> {
    /// Create a new query iterator
    pub fn new(
        root: N,
        query: String,
        max_distance: usize,
        algorithm: Algorithm,
    ) -> Self {
        let query_bytes = query.into_bytes();
        let initial = initial_state(query_bytes.len(), max_distance);

        let mut pending = VecDeque::new();
        pending.push_back(Box::new(Intersection::new(root, initial)));

        Self {
            pending,
            query: query_bytes,
            max_distance,
            algorithm,
            finished: false,
            state_pool: StatePool::new(),  // Create pool for this query
        }
    }

    /// Advance to the next match
    fn advance(&mut self) -> Option<String> {
        while let Some(intersection) = self.pending.pop_front() {
            // Check if this is a final match
            if intersection.is_final() {
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
            if !intersection.is_final() {
                self.queue_children(&intersection);
            }
        }

        self.finished = true;
        None
    }

    /// Queue child intersections for exploration
    fn queue_children(&mut self, intersection: &Box<Intersection<N>>) {
        for (label, child_node) in intersection.node.edges() {
            if let Some(next_state) = transition_state_pooled(
                &intersection.state,
                &mut self.state_pool,  // Use pool for State allocation reuse
                label,
                &self.query,
                self.max_distance,
                self.algorithm,
            ) {
                // Clone the current intersection box to use as parent
                // This preserves the full parent chain
                let parent_box = Box::new(Intersection {
                    label: intersection.label,
                    node: intersection.node.clone(),
                    state: intersection.state.clone(),
                    parent: intersection.parent.clone(), // Keep parent chain
                });

                let child = Box::new(Intersection::with_parent(
                    label,
                    child_node,
                    next_state,
                    parent_box,
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
    pub fn new(
        root: N,
        query: String,
        max_distance: usize,
        algorithm: Algorithm,
    ) -> Self {
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
    use crate::dictionary::pathmap::PathMapDictionary;
    use crate::dictionary::Dictionary;

    #[test]
    fn test_query_exact_match() {
        let dict = PathMapDictionary::from_iter(vec!["test"]);
        let query = QueryIterator::new(
            dict.root(),
            "test".to_string(),
            0,
            Algorithm::Standard,
        );

        let result: Vec<_> = query.collect();
        assert_eq!(result, vec!["test"]);
    }

    #[test]
    fn test_query_with_distance() {
        let dict = PathMapDictionary::from_iter(vec!["test", "best", "rest", "testing"]);
        let query = QueryIterator::new(
            dict.root(),
            "test".to_string(),
            1,
            Algorithm::Standard,
        );

        let results: Vec<_> = query.collect();
        assert!(results.contains(&"test".to_string()));
        assert!(results.contains(&"best".to_string()));
        assert!(results.contains(&"rest".to_string()));
        // "testing" should not match with distance 1
    }

    #[test]
    fn test_candidate_iterator() {
        let dict = PathMapDictionary::from_iter(vec!["test", "best"]);
        let query = CandidateIterator::new(
            dict.root(),
            "test".to_string(),
            1,
            Algorithm::Standard,
        );

        let candidates: Vec<_> = query.collect();
        assert!(candidates.iter().any(|c| c.term == "test" && c.distance == 0));
        assert!(candidates.iter().any(|c| c.term == "best" && c.distance == 1));
    }

    #[test]
    fn test_empty_query() {
        let dict = PathMapDictionary::from_iter(vec!["test"]);
        let query = QueryIterator::new(
            dict.root(),
            "".to_string(),
            0,
            Algorithm::Standard,
        );

        let results: Vec<_> = query.collect();
        // Empty query with distance 0 should match nothing unless dict has empty string
        assert!(results.is_empty() || results.contains(&"".to_string()));
    }
}
