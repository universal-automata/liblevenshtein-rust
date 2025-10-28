//! Builder pattern for creating Transducer instances.
//!
//! The `TransducerBuilder` provides a fluent API for constructing
//! `Transducer` instances with optional configuration and validation.

use crate::dictionary::Dictionary;
use crate::transducer::{Algorithm, Transducer};

/// Builder for constructing a `Transducer` with a fluent API.
///
/// # Example
///
/// ```rust,ignore
/// use liblevenshtein::prelude::*;
///
/// let dict = DoubleArrayTrie::from_terms(vec!["test", "testing"]);
/// let transducer = TransducerBuilder::new()
///     .dictionary(dict)
///     .algorithm(Algorithm::Transposition)
///     .build()?;
/// ```
pub struct TransducerBuilder<D: Dictionary> {
    dictionary: Option<D>,
    algorithm: Option<Algorithm>,
}

/// Error type for builder validation failures.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub enum BuilderError {
    /// No dictionary was provided
    #[error("Dictionary is required. Use .dictionary() to set it.")]
    MissingDictionary,
    /// No algorithm was provided
    #[error("Algorithm is required. Use .algorithm() to set it.")]
    MissingAlgorithm,
}

impl<D: Dictionary> TransducerBuilder<D> {
    /// Create a new empty builder.
    pub fn new() -> Self {
        TransducerBuilder {
            dictionary: None,
            algorithm: None,
        }
    }

    /// Set the dictionary to use for approximate string matching.
    ///
    /// # Arguments
    ///
    /// * `dictionary` - The dictionary containing the terms to match against
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// let dict = DoubleArrayTrie::from_terms(vec!["test"]);
    /// let builder = TransducerBuilder::new()
    ///     .dictionary(dict);
    /// ```
    pub fn dictionary(mut self, dictionary: D) -> Self {
        self.dictionary = Some(dictionary);
        self
    }

    /// Set the Levenshtein distance algorithm to use.
    ///
    /// # Arguments
    ///
    /// * `algorithm` - The distance algorithm (Standard, Transposition, or MergeAndSplit)
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// let builder = TransducerBuilder::new()
    ///     .algorithm(Algorithm::Transposition);
    /// ```
    pub fn algorithm(mut self, algorithm: Algorithm) -> Self {
        self.algorithm = Some(algorithm);
        self
    }

    /// Build the `Transducer`.
    ///
    /// # Returns
    ///
    /// * `Ok(Transducer)` if all required fields are set
    /// * `Err(BuilderError)` if any required fields are missing
    ///
    /// # Errors
    ///
    /// Returns an error if:
    /// - Dictionary was not set (use `.dictionary()`)
    /// - Algorithm was not set (use `.algorithm()`)
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// let transducer = TransducerBuilder::new()
    ///     .dictionary(dict)
    ///     .algorithm(Algorithm::Standard)
    ///     .build()?;
    /// ```
    pub fn build(self) -> Result<Transducer<D>, BuilderError> {
        let dictionary = self.dictionary.ok_or(BuilderError::MissingDictionary)?;
        let algorithm = self.algorithm.ok_or(BuilderError::MissingAlgorithm)?;

        Ok(Transducer::new(dictionary, algorithm))
    }
}

impl<D: Dictionary> Default for TransducerBuilder<D> {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::dictionary::double_array_trie::DoubleArrayTrie;

    #[test]
    fn test_builder_complete() {
        let dict = DoubleArrayTrie::from_terms(vec!["test", "testing"]);
        let transducer = TransducerBuilder::new()
            .dictionary(dict)
            .algorithm(Algorithm::Standard)
            .build()
            .unwrap();

        assert_eq!(transducer.algorithm(), Algorithm::Standard);
        assert_eq!(transducer.dictionary().len(), Some(2));
    }

    #[test]
    fn test_builder_missing_dictionary() {
        let result: Result<Transducer<DoubleArrayTrie>, _> = TransducerBuilder::new()
            .algorithm(Algorithm::Standard)
            .build();

        assert!(result.is_err());
        assert_eq!(result.unwrap_err(), BuilderError::MissingDictionary);
    }

    #[test]
    fn test_builder_missing_algorithm() {
        let dict = DoubleArrayTrie::from_terms(vec!["test"]);
        let result = TransducerBuilder::new().dictionary(dict).build();

        assert!(result.is_err());
        assert_eq!(result.unwrap_err(), BuilderError::MissingAlgorithm);
    }

    #[test]
    fn test_builder_order_independence() {
        let dict1 = DoubleArrayTrie::from_terms(vec!["test"]);
        let dict2 = DoubleArrayTrie::from_terms(vec!["test"]);

        // Algorithm first
        let t1 = TransducerBuilder::new()
            .algorithm(Algorithm::Transposition)
            .dictionary(dict1)
            .build()
            .unwrap();

        // Dictionary first
        let t2 = TransducerBuilder::new()
            .dictionary(dict2)
            .algorithm(Algorithm::Transposition)
            .build()
            .unwrap();

        assert_eq!(t1.algorithm(), t2.algorithm());
    }

    #[test]
    fn test_builder_all_algorithms() {
        for algo in [
            Algorithm::Standard,
            Algorithm::Transposition,
            Algorithm::MergeAndSplit,
        ] {
            let dict = DoubleArrayTrie::from_terms(vec!["test"]);
            let transducer = TransducerBuilder::new()
                .dictionary(dict)
                .algorithm(algo)
                .build()
                .unwrap();

            assert_eq!(transducer.algorithm(), algo);
        }
    }

    #[test]
    fn test_builder_with_dawg() {
        use crate::dictionary::dawg::DawgDictionary;

        let dict = DawgDictionary::from_iter(vec!["test", "testing"]);
        let transducer = TransducerBuilder::new()
            .dictionary(dict)
            .algorithm(Algorithm::Standard)
            .build()
            .unwrap();

        let results: Vec<_> = transducer.query("test", 0).collect();
        assert_eq!(results.len(), 1);
        assert_eq!(results[0], "test");
    }

    #[test]
    fn test_builder_error_display() {
        let err1 = BuilderError::MissingDictionary;
        let err2 = BuilderError::MissingAlgorithm;

        assert!(err1.to_string().contains("Dictionary"));
        assert!(err2.to_string().contains("Algorithm"));
    }
}
