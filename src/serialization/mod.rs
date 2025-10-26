//! Dictionary serialization support.
//!
//! This module provides serialization and deserialization of dictionaries
//! using various formats (bincode, JSON, protobuf) with optional compression.
//!
//! # Example
//!
//! ```rust,ignore
//! use liblevenshtein::prelude::*;
//! use liblevenshtein::serialization::{BincodeSerializer, DictionarySerializer};
//! use std::fs::File;
//!
//! // Create and populate dictionary
//! let dict = PathMapDictionary::from_iter(vec!["test", "testing"]);
//!
//! // Serialize to file
//! let file = File::create("dict.bin")?;
//! BincodeSerializer::serialize(&dict, file)?;
//!
//! // Deserialize from file
//! let file = File::open("dict.bin")?;
//! let loaded_dict: PathMapDictionary = BincodeSerializer::deserialize(file)?;
//! ```

use crate::dictionary::{Dictionary, DictionaryNode};
use std::io::{Read, Write};

// Serializer implementations
mod bincode_impl;
mod json_impl;

#[cfg(feature = "protobuf")]
pub mod protobuf_impl;

#[cfg(feature = "compression")]
mod compression_impl;

// Re-exports
pub use self::bincode_impl::BincodeSerializer;
pub use self::json_impl::JsonSerializer;

#[cfg(feature = "protobuf")]
pub use self::protobuf_impl::{OptimizedProtobufSerializer, ProtobufSerializer};

#[cfg(feature = "compression")]
pub use self::compression_impl::GzipSerializer;

/// Trait for serializing and deserializing dictionaries.
pub trait DictionarySerializer {
    /// Serialize a dictionary to a writer.
    ///
    /// # Arguments
    ///
    /// * `dict` - The dictionary to serialize
    /// * `writer` - Where to write the serialized data
    ///
    /// # Errors
    ///
    /// Returns an error if serialization fails or writing fails.
    fn serialize<D, W>(dict: &D, writer: W) -> Result<(), SerializationError>
    where
        D: Dictionary,
        W: Write;

    /// Deserialize a dictionary from a reader.
    ///
    /// # Arguments
    ///
    /// * `reader` - Where to read the serialized data from
    ///
    /// # Errors
    ///
    /// Returns an error if deserialization fails or reading fails.
    fn deserialize<D, R>(reader: R) -> Result<D, SerializationError>
    where
        D: DictionaryFromTerms,
        R: Read;
}

/// Trait for dictionaries that can be constructed from a list of terms.
///
/// This is used by the serialization system to reconstruct dictionaries
/// after deserialization.
pub trait DictionaryFromTerms: Sized {
    /// Create a dictionary from an iterator of terms.
    fn from_terms<I: IntoIterator<Item = String>>(terms: I) -> Self;
}

/// Errors that can occur during serialization/deserialization.
#[derive(Debug, thiserror::Error)]
pub enum SerializationError {
    /// Error during bincode serialization
    #[error("Bincode error")]
    Bincode(#[from] bincode::Error),
    /// Error during JSON serialization
    #[error("JSON error")]
    Json(#[from] serde_json::Error),
    /// Error during protobuf serialization
    #[cfg(feature = "protobuf")]
    #[error("Protobuf error")]
    Protobuf(#[from] prost::DecodeError),
    /// I/O error
    #[error("I/O error")]
    Io(#[from] std::io::Error),
    /// Dictionary iteration error
    #[error("Dictionary error: {0}")]
    DictionaryError(String),
}

/// Helper to extract all terms from a dictionary.
///
/// This performs a depth-first traversal of the dictionary trie
/// to collect all valid terms.
pub fn extract_terms<D: Dictionary>(dict: &D) -> Vec<String> {
    // Pre-allocate with estimated capacity
    let est_size = dict.len().unwrap_or(100);
    let mut terms = Vec::with_capacity(est_size);
    let mut current_term = Vec::with_capacity(32); // Most words < 32 bytes

    fn dfs<N: DictionaryNode>(node: &N, current_term: &mut Vec<u8>, terms: &mut Vec<String>) {
        if node.is_final() {
            // SAFETY: Dictionary implementations maintain the invariant that
            // all terms are valid UTF-8. We avoid the clone by using
            // from_utf8_unchecked, which is safe because:
            // 1. Dictionaries are constructed from valid UTF-8 strings
            // 2. We only traverse edges that were part of valid UTF-8 terms
            // 3. The byte sequence is validated during dictionary construction
            //
            // Fallback: If somehow invalid UTF-8 is encountered (shouldn't happen),
            // we use from_utf8_lossy which replaces invalid sequences with �
            match std::str::from_utf8(current_term) {
                Ok(s) => terms.push(s.to_string()),
                Err(_) => {
                    // Defensive: shouldn't happen with proper dictionary implementations
                    terms.push(String::from_utf8_lossy(current_term).into_owned());
                }
            }
        }

        // Explore all edges
        for (byte, child) in node.edges() {
            current_term.push(byte);
            dfs(&child, current_term, terms);
            current_term.pop();
        }
    }

    let root = dict.root();
    dfs(&root, &mut current_term, &mut terms);

    terms
}

// Tests
#[cfg(test)]
mod tests {
    use super::*;
    use crate::dictionary::pathmap::PathMapDictionary;

    #[test]
    fn test_bincode_roundtrip() {
        let dict = PathMapDictionary::from_iter(vec!["hello", "world", "test"]);
        let mut buffer = Vec::new();

        BincodeSerializer::serialize(&dict, &mut buffer).unwrap();
        let loaded: PathMapDictionary = BincodeSerializer::deserialize(&buffer[..]).unwrap();

        assert!(loaded.contains("hello"));
        assert!(loaded.contains("world"));
        assert!(loaded.contains("test"));
        assert!(!loaded.contains("missing"));
    }

    #[test]
    fn test_json_roundtrip() {
        let dict = PathMapDictionary::from_iter(vec!["alpha", "beta", "gamma"]);
        let mut buffer = Vec::new();

        JsonSerializer::serialize(&dict, &mut buffer).unwrap();
        let loaded: PathMapDictionary = JsonSerializer::deserialize(&buffer[..]).unwrap();

        assert!(loaded.contains("alpha"));
        assert!(loaded.contains("beta"));
        assert!(loaded.contains("gamma"));
        assert!(!loaded.contains("delta"));
    }

    #[test]
    fn test_extract_terms() {
        let dict = PathMapDictionary::from_iter(vec!["apple", "apply", "application"]);
        let terms = extract_terms(&dict);

        assert_eq!(terms.len(), 3);
        assert!(terms.contains(&"apple".to_string()));
        assert!(terms.contains(&"apply".to_string()));
        assert!(terms.contains(&"application".to_string()));
    }
}
