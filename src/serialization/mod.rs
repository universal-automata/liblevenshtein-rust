//! Dictionary serialization support.
//!
//! This module provides serialization and deserialization of dictionaries
//! using various formats (bincode, JSON, etc.).
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

use std::io::{Read, Write};
use crate::dictionary::{Dictionary, DictionaryNode};

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
#[derive(Debug)]
pub enum SerializationError {
    /// Error during bincode serialization
    Bincode(bincode::Error),
    /// Error during JSON serialization
    Json(serde_json::Error),
    /// I/O error
    Io(std::io::Error),
    /// Dictionary iteration error
    DictionaryError(String),
}

impl std::fmt::Display for SerializationError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            SerializationError::Bincode(e) => write!(f, "Bincode error: {}", e),
            SerializationError::Json(e) => write!(f, "JSON error: {}", e),
            SerializationError::Io(e) => write!(f, "I/O error: {}", e),
            SerializationError::DictionaryError(msg) => write!(f, "Dictionary error: {}", msg),
        }
    }
}

impl std::error::Error for SerializationError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            SerializationError::Bincode(e) => Some(e),
            SerializationError::Json(e) => Some(e),
            SerializationError::Io(e) => Some(e),
            SerializationError::DictionaryError(_) => None,
        }
    }
}

impl From<bincode::Error> for SerializationError {
    fn from(err: bincode::Error) -> Self {
        SerializationError::Bincode(err)
    }
}

impl From<serde_json::Error> for SerializationError {
    fn from(err: serde_json::Error) -> Self {
        SerializationError::Json(err)
    }
}

impl From<std::io::Error> for SerializationError {
    fn from(err: std::io::Error) -> Self {
        SerializationError::Io(err)
    }
}

/// Helper to extract all terms from a dictionary.
///
/// This performs a depth-first traversal of the dictionary trie
/// to collect all valid terms.
pub fn extract_terms<D: Dictionary>(dict: &D) -> Vec<String> {
    let mut terms = Vec::new();
    let mut current_term = Vec::new();

    fn dfs<N: DictionaryNode>(
        node: &N,
        current_term: &mut Vec<u8>,
        terms: &mut Vec<String>
    ) {
        if node.is_final() {
            // Convert current path to string
            if let Ok(term) = String::from_utf8(current_term.clone()) {
                terms.push(term);
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

/// Bincode serializer for compact binary format.
///
/// This serializer uses bincode for fast, space-efficient serialization.
/// It's ideal for production use where storage space and load time matter.
pub struct BincodeSerializer;

impl DictionarySerializer for BincodeSerializer {
    fn serialize<D, W>(dict: &D, mut writer: W) -> Result<(), SerializationError>
    where
        D: Dictionary,
        W: Write,
    {
        let terms = extract_terms(dict);
        bincode::serialize_into(&mut writer, &terms)?;
        Ok(())
    }

    fn deserialize<D, R>(mut reader: R) -> Result<D, SerializationError>
    where
        D: DictionaryFromTerms,
        R: Read,
    {
        let terms: Vec<String> = bincode::deserialize_from(&mut reader)?;
        Ok(D::from_terms(terms))
    }
}

/// JSON serializer for human-readable format.
///
/// This serializer uses JSON for easy debugging and manual inspection.
/// It's less efficient than bincode but useful for development.
pub struct JsonSerializer;

impl DictionarySerializer for JsonSerializer {
    fn serialize<D, W>(dict: &D, mut writer: W) -> Result<(), SerializationError>
    where
        D: Dictionary,
        W: Write,
    {
        let terms = extract_terms(dict);
        serde_json::to_writer_pretty(&mut writer, &terms)?;
        Ok(())
    }

    fn deserialize<D, R>(mut reader: R) -> Result<D, SerializationError>
    where
        D: DictionaryFromTerms,
        R: Read,
    {
        let terms: Vec<String> = serde_json::from_reader(&mut reader)?;
        Ok(D::from_terms(terms))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::dictionary::pathmap::PathMapDictionary;

    #[test]
    fn test_extract_terms() {
        let dict = PathMapDictionary::from_iter(vec!["test", "testing", "tested"]);
        let mut terms = extract_terms(&dict);
        terms.sort(); // Dictionary order may vary

        assert_eq!(terms, vec!["test", "tested", "testing"]);
    }

    #[test]
    fn test_bincode_roundtrip() {
        let dict = PathMapDictionary::from_iter(vec!["hello", "world", "test"]);

        // Serialize
        let mut buffer = Vec::new();
        BincodeSerializer::serialize(&dict, &mut buffer).unwrap();

        // Deserialize
        let loaded_dict: PathMapDictionary =
            BincodeSerializer::deserialize(&buffer[..]).unwrap();

        // Verify
        assert_eq!(loaded_dict.len(), Some(3));
        assert!(loaded_dict.contains("hello"));
        assert!(loaded_dict.contains("world"));
        assert!(loaded_dict.contains("test"));
    }

    #[test]
    fn test_json_roundtrip() {
        let dict = PathMapDictionary::from_iter(vec!["foo", "bar", "baz"]);

        // Serialize
        let mut buffer = Vec::new();
        JsonSerializer::serialize(&dict, &mut buffer).unwrap();

        // Verify JSON is readable
        let json_str = String::from_utf8(buffer.clone()).unwrap();
        assert!(json_str.contains("foo"));
        assert!(json_str.contains("bar"));
        assert!(json_str.contains("baz"));

        // Deserialize
        let loaded_dict: PathMapDictionary =
            JsonSerializer::deserialize(&buffer[..]).unwrap();

        // Verify
        assert_eq!(loaded_dict.len(), Some(3));
        assert!(loaded_dict.contains("foo"));
        assert!(loaded_dict.contains("bar"));
        assert!(loaded_dict.contains("baz"));
    }

    #[test]
    fn test_empty_dictionary() {
        let dict = PathMapDictionary::new();

        let mut buffer = Vec::new();
        BincodeSerializer::serialize(&dict, &mut buffer).unwrap();

        let loaded_dict: PathMapDictionary =
            BincodeSerializer::deserialize(&buffer[..]).unwrap();

        assert_eq!(loaded_dict.len(), Some(0));
    }

    #[test]
    fn test_large_dictionary() {
        // Create dictionary with 1000 terms
        let terms: Vec<String> = (0..1000)
            .map(|i| format!("term{:04}", i))
            .collect();
        let dict = PathMapDictionary::from_iter(terms.clone());

        // Serialize
        let mut buffer = Vec::new();
        BincodeSerializer::serialize(&dict, &mut buffer).unwrap();

        // Deserialize
        let loaded_dict: PathMapDictionary =
            BincodeSerializer::deserialize(&buffer[..]).unwrap();

        // Verify all terms present
        assert_eq!(loaded_dict.len(), Some(1000));
        for term in &terms {
            assert!(loaded_dict.contains(term));
        }
    }
}
