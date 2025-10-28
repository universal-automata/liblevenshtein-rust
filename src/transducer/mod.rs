//! Levenshtein automata for approximate string matching.
//!
//! This module implements Universal Levenshtein Automata for efficient
//! fuzzy string matching against dictionaries.

mod algorithm;
pub mod builder;
mod builder_api;
mod intersection;
mod ordered_query;
mod pool;
mod position;
mod query;
mod state;
pub mod transition;

pub use algorithm::Algorithm;
pub use builder::{BuilderError, TransducerBuilder};
pub use builder_api::QueryBuilder;
pub use intersection::{Intersection, PathNode};
pub use ordered_query::{OrderedCandidate, OrderedQueryIterator};
pub use pool::StatePool;
pub use position::Position;
pub use query::{Candidate, CandidateIterator, QueryIterator};
pub use state::State;

use crate::dictionary::Dictionary;

/// Main transducer for approximate string matching.
///
/// The transducer combines a dictionary with a Levenshtein automaton
/// to efficiently find all terms within a given edit distance of a query.
///
/// # Example
///
/// ```rust,ignore
/// use liblevenshtein::prelude::*;
///
/// let dict = DoubleArrayTrie::from_terms(vec!["test", "testing"]);
/// let transducer = Transducer::new(dict, Algorithm::Standard);
///
/// for term in transducer.query("tset", 2) {
///     println!("Found: {}", term);
/// }
/// ```
#[derive(Clone, Debug)]
pub struct Transducer<D: Dictionary> {
    dictionary: D,
    algorithm: Algorithm,
}

impl<D: Dictionary> Transducer<D> {
    /// Create a new transducer with the given dictionary and algorithm
    pub fn new(dictionary: D, algorithm: Algorithm) -> Self {
        Self {
            dictionary,
            algorithm,
        }
    }

    /// Query for terms within `max_distance` edits of `term`
    ///
    /// Returns an iterator over matching terms (strings only)
    pub fn query(&self, term: &str, max_distance: usize) -> QueryIterator<D::Node> {
        QueryIterator::with_substring_mode(
            self.dictionary.root(),
            term.to_string(),
            max_distance,
            self.algorithm,
            self.dictionary.is_suffix_based(),
        )
    }

    /// Query for terms with their edit distances
    ///
    /// Returns an iterator over `Candidate` structs containing both
    /// the matching term and its computed distance
    pub fn query_with_distance(
        &self,
        term: &str,
        max_distance: usize,
    ) -> CandidateIterator<D::Node> {
        CandidateIterator::new(
            self.dictionary.root(),
            term.to_string(),
            max_distance,
            self.algorithm,
        )
    }

    /// Query for terms in distance-first, lexicographic order
    ///
    /// Returns an iterator that yields results ordered by:
    /// 1. Primary: Ascending edit distance (0, 1, 2, ...)
    /// 2. Secondary: Lexicographic (alphabetical)
    ///
    /// This ordering enables efficient "top-k" queries and take-while patterns.
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// use liblevenshtein::prelude::*;
    ///
    /// let dict = DoubleArrayTrie::from_terms(vec!["test", "best", "rest"]);
    /// let transducer = Transducer::new(dict, Algorithm::Standard);
    ///
    /// // Get first 3 closest matches
    /// for candidate in transducer.query_ordered("tset", 2).take(3) {
    ///     println!("{}: {}", candidate.term, candidate.distance);
    /// }
    ///
    /// // Get all matches within distance 1
    /// for candidate in transducer.query_ordered("tset", 2)
    ///     .take_while(|c| c.distance <= 1)
    /// {
    ///     println!("{}", candidate.term);
    /// }
    /// ```
    pub fn query_ordered(&self, term: &str, max_distance: usize) -> OrderedQueryIterator<D::Node> {
        OrderedQueryIterator::with_substring_mode(
            self.dictionary.root(),
            term.to_string(),
            max_distance,
            self.algorithm,
            self.dictionary.is_suffix_based(),
        )
    }

    /// Get the algorithm used by this transducer
    pub fn algorithm(&self) -> Algorithm {
        self.algorithm
    }

    /// Get a reference to the underlying dictionary
    pub fn dictionary(&self) -> &D {
        &self.dictionary
    }

    /// Create a fluent query builder
    ///
    /// Provides a more ergonomic, self-documenting API for querying.
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// use liblevenshtein::prelude::*;
    ///
    /// let dict = DawgDictionary::from_iter(vec!["test", "testing"]);
    /// let transducer = Transducer::new(dict, Algorithm::Standard);
    ///
    /// // Fluent API
    /// let results: Vec<_> = transducer
    ///     .query_builder("tset")
    ///     .max_distance(2)
    ///     .prefix_mode(true)
    ///     .limit(10)
    ///     .collect();
    ///
    /// // Ordered results
    /// let top_matches: Vec<_> = transducer
    ///     .query_builder("test")
    ///     .max_distance(2)
    ///     .ordered()
    ///     .take(5)
    ///     .map(|c| c.term)
    ///     .collect();
    /// ```
    pub fn query_builder(&self, term: impl Into<String>) -> QueryBuilder<'_, D> {
        QueryBuilder::new(&self.dictionary, term, 2, self.algorithm)
    }
}
