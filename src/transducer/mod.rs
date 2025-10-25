//! Levenshtein automata for approximate string matching.
//!
//! This module implements Universal Levenshtein Automata for efficient
//! fuzzy string matching against dictionaries.

mod algorithm;
mod position;
mod state;
mod pool;
mod intersection;
mod query;
pub mod transition;
pub mod builder;

pub use algorithm::Algorithm;
pub use position::Position;
pub use state::State;
pub use pool::StatePool;
pub use intersection::{Intersection, PathNode};
pub use query::{QueryIterator, CandidateIterator, Candidate};
pub use builder::{TransducerBuilder, BuilderError};

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
/// let dict = PathMapDictionary::from_iter(vec!["test", "testing"]);
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
        QueryIterator::new(
            self.dictionary.root(),
            term.to_string(),
            max_distance,
            self.algorithm,
        )
    }

    /// Query for terms with their edit distances
    ///
    /// Returns an iterator over `Candidate` structs containing both
    /// the matching term and its computed distance
    pub fn query_with_distance(&self, term: &str, max_distance: usize) -> CandidateIterator<D::Node> {
        CandidateIterator::new(
            self.dictionary.root(),
            term.to_string(),
            max_distance,
            self.algorithm,
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
}
