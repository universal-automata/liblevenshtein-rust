//! Ordered query iterators that return results by distance, then lexicographically.
//!
//! This module provides iterators that yield spelling candidates in a specific order:
//! 1. Primary: Ascending edit distance (0, 1, 2, ...)
//! 2. Secondary: Lexicographic (alphabetical)
//!
//! This ordering enables efficient "top-k" queries and take-while patterns.

use super::{Algorithm, Intersection, PathNode, StatePool};
use super::transition::{initial_state, transition_state_pooled};
use crate::dictionary::DictionaryNode;
use std::collections::VecDeque;

/// Query result containing term and distance.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct OrderedCandidate {
    /// Edit distance from query (primary sort key)
    pub distance: usize,
    /// The matching term (secondary sort key - lexicographic)
    pub term: String,
}

/// Lazy iterator that returns candidates in distance-first, lexicographic order.
///
/// This iterator yields all distance=0 matches first (exact matches), then all
/// distance=1 matches (alphabetically), then distance=2, etc. This ordering
/// enables efficient "top-k" queries using `take(n)` and distance-bounded
/// queries using `take_while`.
///
/// # Ordering Guarantees
///
/// 1. **Primary:** Results are ordered by ascending edit distance
/// 2. **Secondary:** Within each distance, results are lexicographically ordered
///
/// # Performance
///
/// - Explores the search space in distance layers (BFS-like)
/// - Uses StatePool for allocation reuse
/// - Leverages pre-sorted DAWG edges for lexicographic ordering
/// - Truly lazy - can stop early with `take(n)` or `take_while`
///
/// # Example
///
/// ```rust,ignore
/// use liblevenshtein::prelude::*;
///
/// let dict = PathMapDictionary::from_iter(vec!["test", "best", "rest", "testing"]);
/// let transducer = Transducer::new(dict, Algorithm::Standard);
///
/// // Get first 3 closest matches
/// for candidate in transducer.query_ordered("tset", 2).take(3) {
///     println!("{}: {}", candidate.term, candidate.distance);
/// }
/// // Output (in order):
/// // test: 0
/// // best: 1
/// // rest: 1
///
/// // Get all matches within distance 1
/// for candidate in transducer.query_ordered("tset", 2).take_while(|c| c.distance <= 1) {
///     println!("{}", candidate.term);
/// }
/// ```
pub struct OrderedQueryIterator<N: DictionaryNode> {
    /// Pending intersections grouped by minimum distance
    pending_by_distance: Vec<VecDeque<Box<Intersection<N>>>>,
    /// Current distance level being explored
    current_distance: usize,
    /// Maximum distance to explore
    max_distance: usize,
    /// Query bytes
    query: Vec<u8>,
    /// Levenshtein algorithm
    algorithm: Algorithm,
    /// State pool for allocation reuse
    state_pool: StatePool,
}

impl<N: DictionaryNode> OrderedQueryIterator<N> {
    /// Create a new ordered query iterator
    pub fn new(
        root: N,
        query: String,
        max_distance: usize,
        algorithm: Algorithm,
    ) -> Self {
        let query_bytes = query.into_bytes();
        let initial = initial_state(query_bytes.len(), max_distance);

        // Create buckets for each distance level (0..=max_distance)
        let mut pending_by_distance = vec![VecDeque::new(); max_distance + 1];

        // Start with root at distance 0
        pending_by_distance[0].push_back(Box::new(Intersection::new(root, initial)));

        Self {
            pending_by_distance,
            current_distance: 0,
            max_distance,
            query: query_bytes,
            algorithm,
            state_pool: StatePool::new(),
        }
    }

    /// Advance to the next match in order
    fn advance(&mut self) -> Option<OrderedCandidate> {
        // Explore distance levels in ascending order
        while self.current_distance <= self.max_distance {
            // Try to get next intersection from current distance level
            if let Some(intersection) = self.pending_by_distance[self.current_distance].pop_front() {
                // Check if this is a final match
                if intersection.is_final() {
                    if let Some(distance) = intersection.state.infer_distance(self.query.len()) {
                        if distance <= self.max_distance && distance == self.current_distance {
                            let term = intersection.term();

                            // Queue children for further exploration
                            self.queue_children(&intersection);

                            return Some(OrderedCandidate { distance, term });
                        }
                    }
                }

                // Queue children even if not final (continue exploring)
                if !intersection.is_final() {
                    self.queue_children(&intersection);
                }
            } else {
                // Current distance level exhausted, move to next
                self.current_distance += 1;
            }
        }

        None
    }

    /// Queue child intersections into appropriate distance buckets
    fn queue_children(&mut self, intersection: &Box<Intersection<N>>) {
        // Edges are iterated in sorted order (lexicographic) thanks to DAWG construction
        for (label, child_node) in intersection.node.edges() {
            if let Some(next_state) = transition_state_pooled(
                &intersection.state,
                &mut self.state_pool,
                label,
                &self.query,
                self.max_distance,
                self.algorithm,
            ) {
                // Determine minimum possible distance from this state
                if let Some(min_dist) = next_state.min_distance() {
                    if min_dist <= self.max_distance {
                        // Create lightweight PathNode for parent chain
                        let parent_path = if let Some(current_label) = intersection.label {
                            Some(Box::new(PathNode::new(
                                current_label,
                                intersection.parent.clone(),
                            )))
                        } else {
                            None
                        };

                        let child = Box::new(Intersection::with_parent(
                            label,
                            child_node,
                            next_state,
                            parent_path,
                        ));

                        // Add to the appropriate distance bucket
                        self.pending_by_distance[min_dist].push_back(child);
                    }
                }
            }
        }
    }
}

impl<N: DictionaryNode> Iterator for OrderedQueryIterator<N> {
    type Item = OrderedCandidate;

    fn next(&mut self) -> Option<Self::Item> {
        self.advance()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::dictionary::pathmap::PathMapDictionary;
    use crate::dictionary::Dictionary;

    #[test]
    fn test_ordered_exact_match() {
        let dict = PathMapDictionary::from_iter(vec!["test"]);
        let query = OrderedQueryIterator::new(
            dict.root(),
            "test".to_string(),
            0,
            Algorithm::Standard,
        );

        let results: Vec<_> = query.collect();
        assert_eq!(results.len(), 1);
        assert_eq!(results[0].term, "test");
        assert_eq!(results[0].distance, 0);
    }

    #[test]
    fn test_ordered_distance_first() {
        let dict = PathMapDictionary::from_iter(vec![
            "test",    // distance 0
            "best",    // distance 1
            "rest",    // distance 1
            "testing", // distance 3
            "nest",    // distance 1
        ]);

        let query = OrderedQueryIterator::new(
            dict.root(),
            "test".to_string(),
            3,
            Algorithm::Standard,
        );

        let results: Vec<_> = query.collect();

        // Verify distance ordering
        for i in 1..results.len() {
            assert!(
                results[i - 1].distance <= results[i].distance,
                "Distance ordering violated: {} (d={}) should come before {} (d={})",
                results[i - 1].term,
                results[i - 1].distance,
                results[i].term,
                results[i].distance
            );
        }

        // Verify exact match comes first
        assert_eq!(results[0].term, "test");
        assert_eq!(results[0].distance, 0);
    }

    #[test]
    fn test_ordered_lexicographic_within_distance() {
        let dict = PathMapDictionary::from_iter(vec![
            "test", "best", "fest", "nest", "rest", "west", "zest",
        ]);

        let query = OrderedQueryIterator::new(
            dict.root(),
            "test".to_string(),
            1,
            Algorithm::Standard,
        );

        let results: Vec<_> = query.collect();

        // Group by distance
        let mut by_distance: Vec<Vec<String>> = vec![Vec::new(); 2];
        for candidate in results {
            by_distance[candidate.distance].push(candidate.term);
        }

        // Verify distance 0
        assert_eq!(by_distance[0], vec!["test"]);

        // Verify distance 1 is lexicographically sorted
        let dist1 = &by_distance[1];
        for i in 1..dist1.len() {
            assert!(
                dist1[i - 1] <= dist1[i],
                "Lexicographic ordering violated: {} should come before {}",
                dist1[i - 1],
                dist1[i]
            );
        }
    }

    #[test]
    fn test_ordered_take() {
        let dict = PathMapDictionary::from_iter(vec![
            "test", "best", "rest", "nest", "testing", "resting",
        ]);

        let query = OrderedQueryIterator::new(
            dict.root(),
            "test".to_string(),
            3,
            Algorithm::Standard,
        );

        // Take only first 3 results
        let results: Vec<_> = query.take(3).collect();
        assert_eq!(results.len(), 3);

        // First should be exact match
        assert_eq!(results[0].distance, 0);
        assert_eq!(results[0].term, "test");

        // Next two should be distance 1
        assert_eq!(results[1].distance, 1);
        assert_eq!(results[2].distance, 1);
    }

    #[test]
    fn test_ordered_take_while() {
        let dict = PathMapDictionary::from_iter(vec![
            "test", "best", "rest", "nest", "testing", "resting",
        ]);

        let query = OrderedQueryIterator::new(
            dict.root(),
            "test".to_string(),
            3,
            Algorithm::Standard,
        );

        // Take while distance <= 1
        let results: Vec<_> = query.take_while(|c| c.distance <= 1).collect();

        // All results should have distance <= 1
        for candidate in &results {
            assert!(candidate.distance <= 1);
        }

        // Should include exact match
        assert!(results.iter().any(|c| c.term == "test" && c.distance == 0));

        // Should not include distance 3 results
        assert!(!results.iter().any(|c| c.term == "testing"));
        assert!(!results.iter().any(|c| c.term == "resting"));
    }

    #[test]
    fn test_ordered_empty_query() {
        let dict = PathMapDictionary::from_iter(vec!["test", "best"]);

        let query = OrderedQueryIterator::new(
            dict.root(),
            "xyz".to_string(),
            0,
            Algorithm::Standard,
        );

        let results: Vec<_> = query.collect();
        assert_eq!(results.len(), 0);
    }

    #[test]
    fn test_ordered_consistency_with_unordered() {
        // Verify ordered iterator returns same results as unordered, just in different order
        use crate::transducer::query::QueryIterator;

        let dict = PathMapDictionary::from_iter(vec![
            "test", "best", "rest", "nest", "fest", "testing",
        ]);

        let ordered = OrderedQueryIterator::new(
            dict.root(),
            "test".to_string(),
            2,
            Algorithm::Standard,
        );

        let unordered = QueryIterator::new(
            dict.root(),
            "test".to_string(),
            2,
            Algorithm::Standard,
        );

        let mut ordered_terms: Vec<_> = ordered.map(|c| c.term).collect();
        let mut unordered_terms: Vec<_> = unordered.collect();

        ordered_terms.sort();
        unordered_terms.sort();

        assert_eq!(ordered_terms, unordered_terms);
    }
}
