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
//! let dict = PathMapDictionary::from_iter(terms);
//! let transducer = Transducer::new(dict, Algorithm::Standard);
//!
//! for term in transducer.query("tset", 2) {
//!     println!("Match: {}", term);
//! }
//! ```

#![warn(missing_docs)]
#![warn(clippy::all)]

pub mod dictionary;
pub mod transducer;
pub mod distance;

#[cfg(feature = "serialization")]
pub mod serialization;

/// Common imports for convenient usage
pub mod prelude {
    pub use crate::dictionary::{Dictionary, DictionaryNode, SyncStrategy};
    pub use crate::dictionary::pathmap::PathMapDictionary;
    pub use crate::dictionary::dawg::DawgDictionary;
    pub use crate::transducer::{Transducer, Algorithm, Candidate, TransducerBuilder};

    #[cfg(feature = "serialization")]
    pub use crate::serialization::{
        DictionarySerializer, DictionaryFromTerms,
        BincodeSerializer, JsonSerializer
    };
}
