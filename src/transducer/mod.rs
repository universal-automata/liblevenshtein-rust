//! Levenshtein automata for approximate string matching.
//!
//! This module implements Universal Levenshtein Automata for efficient
//! fuzzy string matching against dictionaries.

mod algorithm;
mod automaton_zipper;
pub mod builder;
mod builder_api;
pub mod helpers;
mod intersection;
pub mod intersection_zipper;
mod ordered_query;
mod pool;
mod position;
mod query;
mod query_result;
mod state;
pub mod transition;
mod value_filtered_query;
mod zipper_query_iterator;

#[cfg(feature = "simd")]
pub mod simd;

pub use algorithm::Algorithm;
pub use automaton_zipper::AutomatonZipper;
pub use builder::{BuilderError, TransducerBuilder};
pub use builder_api::QueryBuilder;
pub use intersection::{Intersection, PathNode};
pub use intersection_zipper::IntersectionZipper;
pub use ordered_query::{OrderedCandidate, OrderedQueryIterator};
pub use pool::StatePool;
pub use position::Position;
pub use query::{Candidate, CandidateIterator, QueryIterator, StringQueryIterator};
pub use query_result::QueryResult;
pub use state::State;
pub use value_filtered_query::{ValueFilteredQueryIterator, ValueSetFilteredQueryIterator};
pub use zipper_query_iterator::ZipperQueryIterator;

use crate::dictionary::{Dictionary, MappedDictionary, MappedDictionaryNode};
use std::collections::HashSet;

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

    /// Create a transducer with the Standard algorithm.
    ///
    /// This is a convenience constructor for the most common use case.
    /// The Standard algorithm supports insert, delete, and substitute operations.
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// use liblevenshtein::prelude::*;
    ///
    /// let dict = DoubleArrayTrie::from_terms(vec!["test", "testing"]);
    /// let transducer = Transducer::standard(dict);
    /// // Equivalent to: Transducer::new(dict, Algorithm::Standard)
    /// ```
    pub fn standard(dictionary: D) -> Self {
        Self::new(dictionary, Algorithm::Standard)
    }

    /// Create a transducer with the Transposition algorithm.
    ///
    /// The Transposition algorithm adds support for swapping adjacent characters,
    /// useful for catching common typos like "teh" → "the".
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// use liblevenshtein::prelude::*;
    ///
    /// let dict = DoubleArrayTrie::from_terms(vec!["the", "quick"]);
    /// let transducer = Transducer::with_transposition(dict);
    /// // Will match "teh" to "the" with distance 1
    /// ```
    pub fn with_transposition(dictionary: D) -> Self {
        Self::new(dictionary, Algorithm::Transposition)
    }

    /// Create a transducer with the MergeAndSplit algorithm.
    ///
    /// The MergeAndSplit algorithm adds support for merge and split operations,
    /// useful for catching spacing errors like "every one" ↔ "everyone".
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// use liblevenshtein::prelude::*;
    ///
    /// let dict = DoubleArrayTrie::from_terms(vec!["everyone", "someone"]);
    /// let transducer = Transducer::with_merge_split(dict);
    /// // Will match "every one" to "everyone" with distance 1
    /// ```
    pub fn with_merge_split(dictionary: D) -> Self {
        Self::new(dictionary, Algorithm::MergeAndSplit)
    }

    /// Query for terms within `max_distance` edits of `term`
    ///
    /// Returns an iterator over matching terms (strings only)
    pub fn query(&self, term: &str, max_distance: usize) -> QueryIterator<D::Node, String> {
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
    /// the matching term and its edit distance computed from automaton states
    pub fn query_with_distance(
        &self,
        term: &str,
        max_distance: usize,
    ) -> QueryIterator<D::Node, Candidate> {
        QueryIterator::with_substring_mode(
            self.dictionary.root(),
            term.to_string(),
            max_distance,
            self.algorithm,
            self.dictionary.is_suffix_based(),
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

    /// Extract the underlying dictionary, consuming the transducer.
    ///
    /// This is useful when you need to:
    /// - Serialize the dictionary independently
    /// - Perform maintenance operations outside the transducer context
    /// - Reuse the dictionary in another transducer or engine
    ///
    /// # Examples
    ///
    /// ```rust
    /// # #[cfg(feature = "pathmap-backend")]
    /// # {
    /// use liblevenshtein::prelude::*;
    /// use liblevenshtein::dictionary::pathmap::PathMapDictionary;
    /// use liblevenshtein::transducer::Algorithm;
    ///
    /// let dict: PathMapDictionary = PathMapDictionary::from_terms(["test", "testing"]);
    /// let transducer = Transducer::new(dict, Algorithm::Standard);
    ///
    /// // Extract the dictionary
    /// let dict = transducer.into_inner();
    /// assert_eq!(dict.len(), Some(2));
    /// # }
    /// ```
    #[inline]
    pub fn into_inner(self) -> D {
        self.dictionary
    }

    /// Alias for `into_inner()` - extracts the underlying dictionary.
    ///
    /// Provided for semantic clarity when specifically working with dictionaries.
    #[inline]
    pub fn into_dictionary(self) -> D {
        self.dictionary
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

    /// Alias for [`query`](Self::query) - returns matching term strings.
    ///
    /// This is a more descriptive name that makes it clear the method returns
    /// just the term strings without distance information.
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// use liblevenshtein::prelude::*;
    ///
    /// let dict = DoubleArrayTrie::from_terms(vec!["test", "testing"]);
    /// let transducer = Transducer::standard(dict);
    ///
    /// for term in transducer.query_terms("tset", 2) {
    ///     println!("Match: {}", term);
    /// }
    /// ```
    pub fn query_terms(&self, term: &str, max_distance: usize) -> QueryIterator<D::Node, String> {
        self.query(term, max_distance)
    }

    /// Alias for [`query_with_distance`](Self::query_with_distance) - returns candidates with distances.
    ///
    /// This is a more concise name for getting both terms and their edit distances.
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// use liblevenshtein::prelude::*;
    ///
    /// let dict = DoubleArrayTrie::from_terms(vec!["test", "best", "rest"]);
    /// let transducer = Transducer::standard(dict);
    ///
    /// for candidate in transducer.query_candidates("test", 1) {
    ///     println!("{}: distance {}", candidate.term, candidate.distance);
    /// }
    /// ```
    pub fn query_candidates(
        &self,
        term: &str,
        max_distance: usize,
    ) -> QueryIterator<D::Node, Candidate> {
        self.query_with_distance(term, max_distance)
    }

    /// Alias for [`query_ordered`](Self::query_ordered) - returns ranked results by distance.
    ///
    /// This name emphasizes that results are returned in ranked order
    /// (closest matches first).
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// use liblevenshtein::prelude::*;
    ///
    /// let dict = DoubleArrayTrie::from_terms(vec!["test", "best", "rest"]);
    /// let transducer = Transducer::standard(dict);
    ///
    /// // Get top 5 closest matches
    /// for candidate in transducer.query_ranked("test", 2).take(5) {
    ///     println!("{}: distance {}", candidate.term, candidate.distance);
    /// }
    /// ```
    pub fn query_ranked(&self, term: &str, max_distance: usize) -> OrderedQueryIterator<D::Node> {
        self.query_ordered(term, max_distance)
    }
}

// Value-aware query methods (only available for MappedDictionary)
impl<D> Transducer<D>
where
    D: MappedDictionary,
    D::Node: MappedDictionaryNode<Value = D::Value>,
{
    /// Query with value-based filtering during traversal.
    ///
    /// This method filters candidates based on their associated values **during**
    /// graph traversal, providing 10-100x speedup compared to post-filtering for
    /// selective predicates.
    ///
    /// # Performance
    ///
    /// - **Post-filtering**: Explores 100% of matches, filters afterwards
    /// - **Value-filtered**: Only explores branches matching the predicate
    ///
    /// For a query matching 1000 terms where only 10 are in the target scope:
    /// - Post-filtering: Explores 1000 terms, returns 10 (slow)
    /// - Value-filtered: Explores ~10-50 terms, returns 10 (fast!)
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// use liblevenshtein::prelude::*;
    /// use liblevenshtein::dictionary::pathmap::PathMapDictionary;
    ///
    /// // Dictionary with scope IDs
    /// let dict: PathMapDictionary<u32> = PathMapDictionary::from_terms_with_values(vec![
    ///     ("println", 1),    // std scope
    ///     ("my_func", 2),    // local scope
    ///     ("other_func", 3), // other scope
    /// ]);
    ///
    /// let transducer = Transducer::new(dict, Algorithm::Standard);
    ///
    /// // Query for "func" in local scope only
    /// let matches: Vec<_> = transducer
    ///     .query_filtered("func", 2, |scope_id| *scope_id == 2)
    ///     .collect();
    ///
    /// // Returns: [("my_func", 2)] - other_func is never explored!
    /// ```
    ///
    /// # Use Cases
    ///
    /// - **Code completion**: Filter by lexical scope ID
    /// - **Tagged search**: Filter by category, tag, or metadata
    /// - **Access control**: Filter by permission level
    /// - **Multi-tenancy**: Filter by tenant ID
    pub fn query_filtered<F>(
        &self,
        term: &str,
        max_distance: usize,
        filter: F,
    ) -> ValueFilteredQueryIterator<D::Node, F>
    where
        F: Fn(&D::Value) -> bool,
    {
        ValueFilteredQueryIterator::new(
            self.dictionary.root(),
            term.to_string(),
            max_distance,
            self.algorithm,
            filter,
        )
    }

    /// Query with value set membership filtering.
    ///
    /// Optimized for the common case of checking if a value is in a set.
    /// This is particularly useful for hierarchical scope queries where you
    /// want to match terms visible from multiple nested scopes.
    ///
    /// # Example: Hierarchical Lexical Scope
    ///
    /// ```rust,ignore
    /// use std::collections::HashSet;
    /// use liblevenshtein::prelude::*;
    /// use liblevenshtein::dictionary::pathmap::PathMapDictionary;
    ///
    /// let dict: PathMapDictionary<u32> = PathMapDictionary::from_terms_with_values(vec![
    ///     ("println", 1),    // global scope
    ///     ("format", 1),     // global scope
    ///     ("my_func", 2),    // module scope
    ///     ("helper", 3),     // function scope
    ///     ("local_var", 4),  // block scope
    /// ]);
    ///
    /// let transducer = Transducer::new(dict, Algorithm::Standard);
    ///
    /// // In block scope 4, can see: global(1), module(2), function(3), block(4)
    /// let visible_scopes: HashSet<u32> = [1, 2, 3, 4].iter().cloned().collect();
    ///
    /// let matches: Vec<_> = transducer
    ///     .query_by_value_set("func", 2, &visible_scopes)
    ///     .map(|c| c.term)
    ///     .collect();
    ///
    /// // Returns: ["my_func", "helper"] - only from visible scopes
    /// // Does NOT return items from other modules/files
    /// ```
    ///
    /// # Performance
    ///
    /// For a 10,000-term dictionary where 100 terms are in visible scopes:
    /// - Post-filtering: ~10ms (explores all 10,000 terms)
    /// - Value-filtered: ~0.1ms (explores ~100-500 terms)
    /// - **100x speedup!**
    pub fn query_by_value_set(
        &self,
        term: &str,
        max_distance: usize,
        value_set: &HashSet<D::Value>,
    ) -> ValueSetFilteredQueryIterator<D::Node, D::Value>
    where
        D::Value: Eq + std::hash::Hash + Clone,
    {
        ValueSetFilteredQueryIterator::new(
            self.dictionary.root(),
            term.to_string(),
            max_distance,
            self.algorithm,
            value_set.clone(),
        )
    }
}
