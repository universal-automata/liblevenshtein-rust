//! Fluent builder API for constructing queries
//!
//! This module provides a more ergonomic, self-documenting API for querying
//! dictionaries with various options.

use super::{Algorithm, OrderedQueryIterator, QueryIterator};
use crate::dictionary::Dictionary;

/// Fluent builder for constructing Levenshtein queries
///
/// # Examples
///
/// ```rust,ignore
/// use liblevenshtein::prelude::*;
///
/// let dict = DawgDictionary::from_iter(vec!["test", "testing", "tested"]);
/// let transducer = Transducer::new(dict, Algorithm::Standard);
///
/// // Simple query
/// let results: Vec<_> = transducer
///     .query_builder("tset")
///     .max_distance(2)
///     .execute()
///     .collect();
///
/// // Ordered query with prefix matching
/// let results: Vec<_> = transducer
///     .query_builder("te")
///     .max_distance(1)
///     .prefix_mode(true)
///     .ordered()
///     .take(10)
///     .collect();
/// ```
pub struct QueryBuilder<'a, D: Dictionary> {
    dictionary: &'a D,
    term: String,
    max_distance: usize,
    algorithm: Algorithm,
    prefix: bool,
}

impl<'a, D: Dictionary> QueryBuilder<'a, D> {
    /// Create a new query builder
    pub(crate) fn new(
        dictionary: &'a D,
        term: impl Into<String>,
        default_distance: usize,
        algorithm: Algorithm,
    ) -> Self {
        Self {
            dictionary,
            term: term.into(),
            max_distance: default_distance,
            algorithm,
            prefix: false,
        }
    }

    /// Set the maximum edit distance
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// let results = transducer
    ///     .query_builder("test")
    ///     .max_distance(2)  // Allow up to 2 edits
    ///     .execute();
    /// ```
    pub fn max_distance(mut self, distance: usize) -> Self {
        self.max_distance = distance;
        self
    }

    /// Set the Levenshtein algorithm
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// let results = transducer
    ///     .query_builder("test")
    ///     .algorithm(Algorithm::Transposition)
    ///     .execute();
    /// ```
    pub fn algorithm(mut self, algorithm: Algorithm) -> Self {
        self.algorithm = algorithm;
        self
    }

    /// Enable or disable prefix matching mode
    ///
    /// When enabled, matches terms that start with the query term
    /// (within the specified edit distance).
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// // Find all terms starting with "te" (within 1 edit)
    /// let results = transducer
    ///     .query_builder("te")
    ///     .prefix_mode(true)
    ///     .max_distance(1)
    ///     .execute();
    /// ```
    pub fn prefix_mode(mut self, enabled: bool) -> Self {
        self.prefix = enabled;
        self
    }

    /// Execute the query and return an iterator over matching terms
    ///
    /// Returns terms in arbitrary order as they are found during traversal.
    ///
    /// Note: Prefix mode is not yet implemented in the underlying query iterator.
    /// The `prefix` field will be used when prefix support is added.
    pub fn execute(self) -> QueryIterator<D::Node> {
        if self.prefix {
            // TODO: Once prefix mode is implemented in QueryIterator, pass it here
            eprintln!("Warning: prefix mode not yet implemented, ignoring");
        }
        QueryIterator::new(
            self.dictionary.root(),
            self.term,
            self.max_distance,
            self.algorithm,
        )
    }

    /// Execute the query with ordered results
    ///
    /// Returns an ordered iterator that yields results sorted by:
    /// 1. Edit distance (ascending)
    /// 2. Lexicographic order (for ties)
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// let results: Vec<_> = transducer
    ///     .query_builder("test")
    ///     .max_distance(2)
    ///     .ordered()
    ///     .take(5)  // Get top 5 closest matches
    ///     .collect();
    /// ```
    ///
    /// Note: Prefix mode is not yet implemented in the underlying query iterator.
    pub fn ordered(self) -> OrderedQueryIterator<D::Node> {
        if self.prefix {
            // TODO: Once prefix mode is implemented in OrderedQueryIterator, pass it here
            eprintln!("Warning: prefix mode not yet implemented, ignoring");
        }
        OrderedQueryIterator::new(
            self.dictionary.root(),
            self.term,
            self.max_distance,
            self.algorithm,
        )
    }

    /// Execute and collect results into a vector
    ///
    /// Convenience method for common use case of collecting all results.
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// let results = transducer
    ///     .query_builder("test")
    ///     .max_distance(1)
    ///     .collect_vec();
    /// ```
    pub fn collect_vec(self) -> Vec<String> {
        self.execute().collect()
    }

    /// Execute with a limit on the number of results
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// let results = transducer
    ///     .query_builder("test")
    ///     .max_distance(2)
    ///     .limit(10);
    /// ```
    pub fn limit(self, n: usize) -> impl Iterator<Item = String> {
        self.execute().take(n)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::dictionary::dawg::DawgDictionary;
    use crate::dictionary::Dictionary;
    use crate::transducer::{Algorithm, Transducer};

    #[test]
    fn test_query_builder_basic() {
        let dict = DawgDictionary::from_iter(vec!["test", "testing", "tested"]);
        let transducer = Transducer::new(dict, Algorithm::Standard);

        let results: Vec<_> = transducer
            .query_builder("test")
            .max_distance(0)
            .execute()
            .collect();

        assert_eq!(results, vec!["test"]);
    }

    #[test]
    fn test_query_builder_with_distance() {
        let dict = DawgDictionary::from_iter(vec!["test", "best", "rest"]);
        let transducer = Transducer::new(dict, Algorithm::Standard);

        let results: Vec<_> = transducer
            .query_builder("test")
            .max_distance(1)
            .execute()
            .collect();

        assert!(results.contains(&"test".to_string()));
        assert!(results.contains(&"best".to_string()));
        assert!(results.contains(&"rest".to_string()));
    }

    #[test]
    #[ignore] // TODO: Enable once prefix mode is implemented in QueryIterator
    fn test_query_builder_prefix_mode() {
        let dict = DawgDictionary::from_iter(vec!["test", "testing", "tested", "best"]);
        let transducer = Transducer::new(dict, Algorithm::Standard);

        let results: Vec<_> = transducer
            .query_builder("tes")
            .prefix_mode(true)
            .max_distance(0)
            .execute()
            .collect();

        assert!(results.contains(&"test".to_string()));
        assert!(results.contains(&"testing".to_string()));
        assert!(results.contains(&"tested".to_string()));
        assert!(!results.contains(&"best".to_string()));
    }

    #[test]
    fn test_query_builder_ordered() {
        let dict = DawgDictionary::from_iter(vec!["test", "best", "rest", "testing"]);
        let transducer = Transducer::new(dict, Algorithm::Standard);

        let results: Vec<_> = transducer
            .query_builder("test")
            .max_distance(2)
            .ordered()
            .take(3)
            .map(|c| c.term)
            .collect();

        // Exact match should come first
        assert_eq!(results[0], "test");
    }

    #[test]
    fn test_query_builder_collect_vec() {
        let dict = DawgDictionary::from_iter(vec!["test", "best"]);
        let transducer = Transducer::new(dict, Algorithm::Standard);

        let results = transducer
            .query_builder("test")
            .max_distance(1)
            .collect_vec();

        assert_eq!(results.len(), 2);
    }

    #[test]
    fn test_query_builder_limit() {
        let dict = DawgDictionary::from_iter(vec!["test", "best", "rest", "nest"]);
        let transducer = Transducer::new(dict, Algorithm::Standard);

        let results: Vec<_> = transducer
            .query_builder("test")
            .max_distance(1)
            .limit(2)
            .collect();

        assert_eq!(results.len(), 2);
    }
}
