//! # liblevenshtein
//!
//! Fast approximate string matching using Levenshtein automata.
//!
//! This library provides efficient fuzzy string matching against dictionaries
//! using Universal Levenshtein Automata, based on the algorithm described in:
//!
//! > Schulz, Klaus U., and Stoyan Mihov. "Fast string correction with
//! > Levenshtein automata." International Journal on Document Analysis and
//! > Recognition 5.1 (2002): 67-85.
//!
//! ## Example
//!
//! ```rust,ignore
//! use liblevenshtein::prelude::*;
//!
//! let terms = vec!["test", "testing", "tested"];
//! let dict = PathMapDictionary::from_terms(terms);
//! let transducer = Transducer::new(dict, Algorithm::Standard);
//!
//! for term in transducer.query("tset", 2) {
//!     println!("Match: {}", term);
//! }
//! ```

#![warn(missing_docs)]
#![warn(clippy::all)]

pub mod commands;
pub mod dictionary;
pub mod distance;
pub mod transducer;

#[cfg(feature = "serialization")]
pub mod serialization;

/// Fuzzy cache with composable eviction strategies
#[cfg(feature = "pathmap-backend")]
pub mod cache;

/// Interactive REPL for exploring Levenshtein dictionaries
#[cfg(feature = "cli")]
pub mod repl;

/// CLI interface and utilities
#[cfg(feature = "cli")]
pub mod cli;

/// Common imports for convenient usage
pub mod prelude {
    pub use crate::dictionary::compressed_suffix_automaton::CompressedSuffixAutomaton;
    pub use crate::dictionary::dawg::DawgDictionary;
    pub use crate::dictionary::dawg_optimized::OptimizedDawg;
    pub use crate::dictionary::double_array_trie::DoubleArrayTrie;
    pub use crate::dictionary::dynamic_dawg::DynamicDawg;
    pub use crate::dictionary::factory::{
        DictionaryBackend, DictionaryContainer, DictionaryFactory,
    };
    #[cfg(feature = "pathmap-backend")]
    pub use crate::dictionary::pathmap::PathMapDictionary;
    pub use crate::dictionary::suffix_automaton::SuffixAutomaton;
    pub use crate::dictionary::{Dictionary, DictionaryNode, SyncStrategy};
    pub use crate::transducer::{
        Algorithm, Candidate, QueryBuilder, Transducer, TransducerBuilder,
    };

    #[cfg(feature = "serialization")]
    pub use crate::serialization::{
        BincodeSerializer, DictionaryFromTerms, DictionarySerializer, JsonSerializer,
        PlainTextSerializer,
    };

    #[cfg(feature = "protobuf")]
    pub use crate::serialization::{
        DatProtobufSerializer, OptimizedProtobufSerializer, ProtobufSerializer,
        SuffixAutomatonProtobufSerializer,
    };

    #[cfg(feature = "compression")]
    pub use crate::serialization::GzipSerializer;

    #[cfg(feature = "pathmap-backend")]
    pub use crate::cache::eviction;
}
