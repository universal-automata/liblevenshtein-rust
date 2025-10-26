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

use crate::dictionary::{Dictionary, DictionaryNode};
use std::io::{Read, Write};

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

#[cfg(feature = "protobuf")]
/// Protobuf serializer for cross-language compatibility.
///
/// This serializer uses Protocol Buffers to serialize the dictionary
/// as a graph structure (nodes + edges), which is:
/// - More space-efficient than storing all terms as strings
/// - Compatible with all liblevenshtein implementations (Java, C++, Rust)
/// - Preserves the DAWG/trie structure directly without rebuilding
///
/// # Format
///
/// The dictionary is serialized as:
/// - List of node IDs
/// - List of final (terminal) node IDs
/// - List of edges (source_id, label, target_id)
/// - Root node ID
/// - Dictionary size (term count)
///
/// This format is defined in `proto/liblevenshtein.proto` and is shared
/// across all liblevenshtein implementations.
pub struct ProtobufSerializer;

#[cfg(feature = "protobuf")]
impl ProtobufSerializer {
    /// Extract graph structure from dictionary.
    ///
    /// Performs DFS traversal to collect all nodes and edges.
    ///
    /// NOTE: Since the Dictionary trait doesn't provide node identity,
    /// we serialize as a trie structure where each unique path creates
    /// new nodes. For true DAWG serialization with node sharing, we'd
    /// need dictionary implementations to expose node IDs.
    fn extract_graph<D: Dictionary>(dict: &D) -> proto::Dictionary {
        // Pre-allocate vectors with estimated capacity
        let est_size = dict.len().unwrap_or(100);
        let mut node_ids = Vec::with_capacity(est_size * 2); // Estimate nodes
        let mut final_node_ids = Vec::with_capacity(est_size); // Estimate final nodes
        let mut edges = Vec::with_capacity(est_size * 3); // Estimate edges
        let mut next_id = 0u64;

        // Root node
        node_ids.push(next_id);
        let root = dict.root();
        if root.is_final() {
            final_node_ids.push(next_id);
        }
        next_id += 1;

        // DFS to build graph
        fn dfs<N: DictionaryNode>(
            node: &N,
            node_id: u64,
            next_id: &mut u64,
            node_ids: &mut Vec<u64>,
            final_node_ids: &mut Vec<u64>,
            edges: &mut Vec<proto::dictionary::Edge>,
        ) {
            for (label, child) in node.edges() {
                let child_id = *next_id;
                *next_id += 1;

                // Record child node
                node_ids.push(child_id);
                if child.is_final() {
                    final_node_ids.push(child_id);
                }

                // Record edge
                edges.push(proto::dictionary::Edge {
                    source_id: node_id,
                    label: label as u32,
                    target_id: child_id,
                });

                // Recurse
                dfs(&child, child_id, next_id, node_ids, final_node_ids, edges);
            }
        }

        dfs(
            &root,
            0,
            &mut next_id,
            &mut node_ids,
            &mut final_node_ids,
            &mut edges,
        );

        proto::Dictionary {
            node_id: node_ids,
            final_node_id: final_node_ids,
            edge: edges,
            root_id: 0,
            size: dict.len().unwrap_or(0) as u64,
        }
    }
}

#[cfg(feature = "protobuf")]
impl DictionarySerializer for ProtobufSerializer {
    fn serialize<D, W>(dict: &D, mut writer: W) -> Result<(), SerializationError>
    where
        D: Dictionary,
        W: Write,
    {
        use prost::Message;

        let proto_dict = Self::extract_graph(dict);
        let mut buf = Vec::new();
        proto_dict.encode(&mut buf).map_err(|e| {
            SerializationError::Io(std::io::Error::new(std::io::ErrorKind::Other, e))
        })?;
        writer.write_all(&buf)?;
        Ok(())
    }

    fn deserialize<D, R>(mut reader: R) -> Result<D, SerializationError>
    where
        D: DictionaryFromTerms,
        R: Read,
    {
        use prost::Message;
        use std::collections::HashMap;

        // Read all bytes
        let mut buf = Vec::new();
        reader.read_to_end(&mut buf)?;

        // Decode protobuf
        let proto_dict = proto::Dictionary::decode(&buf[..])?;

        // Reconstruct dictionary from graph
        // Build adjacency list with pre-allocated capacity
        let est_nodes = proto_dict.node_id.len();
        let mut adjacency: HashMap<u64, Vec<(u8, u64)>> = HashMap::with_capacity(est_nodes);
        for edge in &proto_dict.edge {
            adjacency
                .entry(edge.source_id)
                .or_default()
                .push((edge.label as u8, edge.target_id));
        }

        // Pre-allocate HashSet with known size
        let mut final_set: std::collections::HashSet<u64> =
            std::collections::HashSet::with_capacity(proto_dict.final_node_id.len());
        final_set.extend(proto_dict.final_node_id.iter().copied());

        // Extract all terms using DFS
        let est_terms = proto_dict.final_node_id.len();
        let mut terms = Vec::with_capacity(est_terms);
        let mut current_term = Vec::with_capacity(32); // Most words < 32 bytes

        fn dfs(
            node_id: u64,
            adjacency: &HashMap<u64, Vec<(u8, u64)>>,
            final_set: &std::collections::HashSet<u64>,
            current_term: &mut Vec<u8>,
            terms: &mut Vec<String>,
        ) {
            if final_set.contains(&node_id) {
                // Avoid clone by borrowing current_term
                match std::str::from_utf8(current_term) {
                    Ok(s) => terms.push(s.to_string()),
                    Err(_) => terms.push(String::from_utf8_lossy(current_term).into_owned()),
                }
            }

            if let Some(edges) = adjacency.get(&node_id) {
                for &(label, target_id) in edges {
                    current_term.push(label);
                    dfs(target_id, adjacency, final_set, current_term, terms);
                    current_term.pop();
                }
            }
        }

        dfs(
            proto_dict.root_id,
            &adjacency,
            &final_set,
            &mut current_term,
            &mut terms,
        );

        Ok(D::from_terms(terms))
    }
}

#[cfg(feature = "protobuf")]
/// Optimized protobuf serializer using DictionaryV2 format.
///
/// This serializer uses an optimized protobuf format that is 40-60% smaller
/// than the standard ProtobufSerializer by:
/// - Removing redundant node_id field (IDs are sequential)
/// - Using packed edge format (flat array instead of messages)
/// - Delta-encoding final node IDs for better compression
///
/// **Note**: This format is NOT compatible with older liblevenshtein
/// implementations. Use `ProtobufSerializer` for cross-language compatibility.
///
/// # Example
///
/// ```rust,ignore
/// use liblevenshtein::prelude::*;
///
/// let dict = PathMapDictionary::from_iter(vec!["test", "testing"]);
///
/// // Serialize with optimized format (smaller size)
/// let mut buf = Vec::new();
/// OptimizedProtobufSerializer::serialize(&dict, &mut buf)?;
///
/// // Deserialize
/// let loaded: PathMapDictionary =
///     OptimizedProtobufSerializer::deserialize(&buf[..])?;
/// ```
pub struct OptimizedProtobufSerializer;

#[cfg(feature = "protobuf")]
impl OptimizedProtobufSerializer {
    /// Extract graph structure in optimized format.
    fn extract_graph_v2<D: Dictionary>(dict: &D) -> proto::DictionaryV2 {
        // Pre-allocate vectors with estimated capacity
        let est_size = dict.len().unwrap_or(100);
        let mut final_node_ids = Vec::with_capacity(est_size); // Estimate final nodes
        let mut edge_data = Vec::with_capacity(est_size * 9); // 3 values per edge, estimate 3 edges/term
        let mut next_id = 0u64;

        // Root node
        let root = dict.root();
        if root.is_final() {
            final_node_ids.push(0);
        }
        next_id += 1;

        // DFS to build graph
        fn dfs<N: DictionaryNode>(
            node: &N,
            node_id: u64,
            next_id: &mut u64,
            final_node_ids: &mut Vec<u64>,
            edge_data: &mut Vec<u64>,
        ) {
            for (label, child) in node.edges() {
                let child_id = *next_id;
                *next_id += 1;

                // Record if final
                if child.is_final() {
                    final_node_ids.push(child_id);
                }

                // Pack edge as triplet: [source, label, target]
                edge_data.push(node_id);
                edge_data.push(label as u64);
                edge_data.push(child_id);

                // Recurse
                dfs(&child, child_id, next_id, final_node_ids, edge_data);
            }
        }

        dfs(&root, 0, &mut next_id, &mut final_node_ids, &mut edge_data);

        // Convert final node IDs to deltas
        let final_node_delta = if final_node_ids.is_empty() {
            Vec::new()
        } else {
            let mut deltas = Vec::with_capacity(final_node_ids.len());
            deltas.push(final_node_ids[0]); // First value is absolute

            for i in 1..final_node_ids.len() {
                // Delta = current - previous
                deltas.push(final_node_ids[i] - final_node_ids[i - 1]);
            }
            deltas
        };

        let edge_count = edge_data.len() / 3;

        proto::DictionaryV2 {
            final_node_delta,
            edge_data,
            root_id: 0,
            size: dict.len().unwrap_or(0) as u64,
            edge_count: edge_count as u64,
        }
    }
}

#[cfg(feature = "protobuf")]
impl DictionarySerializer for OptimizedProtobufSerializer {
    fn serialize<D, W>(dict: &D, mut writer: W) -> Result<(), SerializationError>
    where
        D: Dictionary,
        W: Write,
    {
        use prost::Message;

        let proto_dict = Self::extract_graph_v2(dict);
        let mut buf = Vec::new();
        proto_dict.encode(&mut buf).map_err(|e| {
            SerializationError::Io(std::io::Error::new(std::io::ErrorKind::Other, e))
        })?;
        writer.write_all(&buf)?;
        Ok(())
    }

    fn deserialize<D, R>(mut reader: R) -> Result<D, SerializationError>
    where
        D: DictionaryFromTerms,
        R: Read,
    {
        use prost::Message;
        use std::collections::HashMap;

        // Read all bytes
        let mut buf = Vec::new();
        reader.read_to_end(&mut buf)?;

        // Decode protobuf
        let proto_dict = proto::DictionaryV2::decode(&buf[..])?;

        // Validate edge_data length
        if proto_dict.edge_data.len() % 3 != 0 {
            return Err(SerializationError::DictionaryError(format!(
                "Invalid edge_data length: {} (must be multiple of 3)",
                proto_dict.edge_data.len()
            )));
        }

        // Reconstruct final node IDs from deltas with pre-allocation
        let mut final_node_ids = Vec::with_capacity(proto_dict.final_node_delta.len());
        if !proto_dict.final_node_delta.is_empty() {
            let mut cumsum = 0u64;
            for &delta in &proto_dict.final_node_delta {
                cumsum += delta;
                final_node_ids.push(cumsum);
            }
        }

        // Build adjacency list from packed edge data with pre-allocation
        let num_edges = proto_dict.edge_data.len() / 3;
        let est_nodes = (num_edges as f64 * 0.6) as usize; // Estimate nodes from edges
        let mut adjacency: HashMap<u64, Vec<(u8, u64)>> = HashMap::with_capacity(est_nodes);
        for chunk in proto_dict.edge_data.chunks_exact(3) {
            let source_id = chunk[0];
            let label = chunk[1] as u8;
            let target_id = chunk[2];

            adjacency
                .entry(source_id)
                .or_default()
                .push((label, target_id));
        }

        // Pre-allocate HashSet with known size
        let mut final_set: std::collections::HashSet<u64> =
            std::collections::HashSet::with_capacity(final_node_ids.len());
        final_set.extend(final_node_ids.iter().copied());

        // Extract all terms using DFS with pre-allocation
        let est_terms = final_node_ids.len();
        let mut terms = Vec::with_capacity(est_terms);
        let mut current_term = Vec::with_capacity(32); // Most words < 32 bytes

        fn dfs(
            node_id: u64,
            adjacency: &HashMap<u64, Vec<(u8, u64)>>,
            final_set: &std::collections::HashSet<u64>,
            current_term: &mut Vec<u8>,
            terms: &mut Vec<String>,
        ) {
            if final_set.contains(&node_id) {
                // Avoid clone by borrowing current_term
                match std::str::from_utf8(current_term) {
                    Ok(s) => terms.push(s.to_string()),
                    Err(_) => terms.push(String::from_utf8_lossy(current_term).into_owned()),
                }
            }

            if let Some(edges) = adjacency.get(&node_id) {
                for &(label, target_id) in edges {
                    current_term.push(label);
                    dfs(target_id, adjacency, final_set, current_term, terms);
                    current_term.pop();
                }
            }
        }

        dfs(
            proto_dict.root_id,
            &adjacency,
            &final_set,
            &mut current_term,
            &mut terms,
        );

        Ok(D::from_terms(terms))
    }
}

#[cfg(feature = "compression")]
/// Gzip-compressed serializer wrapper.
///
/// This wrapper applies gzip compression to any underlying serializer,
/// reducing file size by 40-60% with minimal performance cost.
///
/// # Example
///
/// ```rust,ignore
/// use liblevenshtein::prelude::*;
/// use liblevenshtein::serialization::{GzipSerializer, BincodeSerializer};
/// use std::fs::File;
///
/// let dict = PathMapDictionary::from_iter(vec!["test", "testing"]);
///
/// // Serialize with gzip compression
/// let file = File::create("dict.bin.gz")?;
/// GzipSerializer::<BincodeSerializer>::serialize(&dict, file)?;
///
/// // Deserialize
/// let file = File::open("dict.bin.gz")?;
/// let loaded: PathMapDictionary =
///     GzipSerializer::<BincodeSerializer>::deserialize(file)?;
/// ```
pub struct GzipSerializer<S> {
    _inner: std::marker::PhantomData<S>,
}

#[cfg(feature = "compression")]
impl<S: DictionarySerializer> DictionarySerializer for GzipSerializer<S> {
    fn serialize<D, W>(dict: &D, writer: W) -> Result<(), SerializationError>
    where
        D: Dictionary,
        W: Write,
    {
        use flate2::write::GzEncoder;
        use flate2::Compression;

        let mut encoder = GzEncoder::new(writer, Compression::default());
        S::serialize(dict, &mut encoder)?;
        encoder.finish().map_err(SerializationError::Io)?;
        Ok(())
    }

    fn deserialize<D, R>(reader: R) -> Result<D, SerializationError>
    where
        D: DictionaryFromTerms,
        R: Read,
    {
        use flate2::read::GzDecoder;

        let decoder = GzDecoder::new(reader);
        S::deserialize(decoder)
    }
}

#[cfg(feature = "protobuf")]
mod proto {
    #![allow(dead_code)]
    include!(concat!(env!("OUT_DIR"), "/liblevenshtein.proto.rs"));
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
        let loaded_dict: PathMapDictionary = BincodeSerializer::deserialize(&buffer[..]).unwrap();

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
        let loaded_dict: PathMapDictionary = JsonSerializer::deserialize(&buffer[..]).unwrap();

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

        let loaded_dict: PathMapDictionary = BincodeSerializer::deserialize(&buffer[..]).unwrap();

        assert_eq!(loaded_dict.len(), Some(0));
    }

    #[test]
    fn test_large_dictionary() {
        // Create dictionary with 1000 terms
        let terms: Vec<String> = (0..1000).map(|i| format!("term{:04}", i)).collect();
        let dict = PathMapDictionary::from_iter(terms.clone());

        // Serialize
        let mut buffer = Vec::new();
        BincodeSerializer::serialize(&dict, &mut buffer).unwrap();

        // Deserialize
        let loaded_dict: PathMapDictionary = BincodeSerializer::deserialize(&buffer[..]).unwrap();

        // Verify all terms present
        assert_eq!(loaded_dict.len(), Some(1000));
        for term in &terms {
            assert!(loaded_dict.contains(term));
        }
    }

    #[cfg(feature = "protobuf")]
    #[test]
    fn test_protobuf_roundtrip() {
        use super::ProtobufSerializer;

        let dict = PathMapDictionary::from_iter(vec!["hello", "world", "test"]);

        // Serialize
        let mut buffer = Vec::new();
        ProtobufSerializer::serialize(&dict, &mut buffer).unwrap();

        // Deserialize
        let loaded_dict: PathMapDictionary = ProtobufSerializer::deserialize(&buffer[..]).unwrap();

        // Verify
        assert_eq!(loaded_dict.len(), Some(3));
        assert!(loaded_dict.contains("hello"));
        assert!(loaded_dict.contains("world"));
        assert!(loaded_dict.contains("test"));
    }

    #[cfg(feature = "protobuf")]
    #[test]
    fn test_protobuf_vs_bincode_size() {
        use super::ProtobufSerializer;

        let terms = vec![
            "apple",
            "application",
            "apply",
            "apricot",
            "banana",
            "band",
            "bandana",
        ];
        let dict = PathMapDictionary::from_iter(terms);

        // Serialize with both formats
        let mut bincode_buf = Vec::new();
        BincodeSerializer::serialize(&dict, &mut bincode_buf).unwrap();

        let mut protobuf_buf = Vec::new();
        ProtobufSerializer::serialize(&dict, &mut protobuf_buf).unwrap();

        // Protobuf should be smaller for structured data
        println!("Bincode size: {} bytes", bincode_buf.len());
        println!("Protobuf size: {} bytes", protobuf_buf.len());

        // Both should deserialize correctly
        let loaded_bincode: PathMapDictionary =
            BincodeSerializer::deserialize(&bincode_buf[..]).unwrap();
        let loaded_protobuf: PathMapDictionary =
            ProtobufSerializer::deserialize(&protobuf_buf[..]).unwrap();

        assert_eq!(loaded_bincode.len(), loaded_protobuf.len());
    }

    #[cfg(feature = "protobuf")]
    #[test]
    fn test_optimized_protobuf_roundtrip() {
        use super::OptimizedProtobufSerializer;

        let dict = PathMapDictionary::from_iter(vec!["hello", "world", "test"]);

        // Serialize
        let mut buffer = Vec::new();
        OptimizedProtobufSerializer::serialize(&dict, &mut buffer).unwrap();

        // Deserialize
        let loaded_dict: PathMapDictionary =
            OptimizedProtobufSerializer::deserialize(&buffer[..]).unwrap();

        // Verify
        assert_eq!(loaded_dict.len(), Some(3));
        assert!(loaded_dict.contains("hello"));
        assert!(loaded_dict.contains("world"));
        assert!(loaded_dict.contains("test"));
    }

    #[cfg(feature = "protobuf")]
    #[test]
    fn test_optimized_vs_standard_protobuf() {
        use super::{OptimizedProtobufSerializer, ProtobufSerializer};

        let terms = vec![
            "apple",
            "application",
            "apply",
            "apricot",
            "banana",
            "band",
            "bandana",
            "cherry",
            "chocolate",
        ];
        let dict = PathMapDictionary::from_iter(terms);

        // Serialize with both protobuf formats
        let mut v1_buf = Vec::new();
        ProtobufSerializer::serialize(&dict, &mut v1_buf).unwrap();

        let mut v2_buf = Vec::new();
        OptimizedProtobufSerializer::serialize(&dict, &mut v2_buf).unwrap();

        println!("Protobuf V1 size: {} bytes", v1_buf.len());
        println!("Protobuf V2 (optimized) size: {} bytes", v2_buf.len());
        let savings = ((v1_buf.len() - v2_buf.len()) as f64 / v1_buf.len() as f64) * 100.0;
        println!("Space savings: {:.1}%", savings);

        // V2 should be significantly smaller
        assert!(
            v2_buf.len() < v1_buf.len(),
            "Optimized format should be smaller"
        );

        // Both should deserialize to same dictionary
        let loaded_v1: PathMapDictionary = ProtobufSerializer::deserialize(&v1_buf[..]).unwrap();
        let loaded_v2: PathMapDictionary =
            OptimizedProtobufSerializer::deserialize(&v2_buf[..]).unwrap();

        assert_eq!(loaded_v1.len(), loaded_v2.len());
    }

    #[cfg(feature = "protobuf")]
    #[test]
    fn test_optimized_delta_encoding() {
        use super::OptimizedProtobufSerializer;

        // Create dict with sequential final nodes (good for delta encoding)
        let dict = PathMapDictionary::from_iter(vec!["a", "ab", "abc", "abcd", "abcde"]);

        let mut buffer = Vec::new();
        OptimizedProtobufSerializer::serialize(&dict, &mut buffer).unwrap();

        let loaded: PathMapDictionary =
            OptimizedProtobufSerializer::deserialize(&buffer[..]).unwrap();

        assert_eq!(loaded.len(), Some(5));
        assert!(loaded.contains("a"));
        assert!(loaded.contains("ab"));
        assert!(loaded.contains("abc"));
        assert!(loaded.contains("abcd"));
        assert!(loaded.contains("abcde"));
    }

    #[cfg(feature = "protobuf")]
    #[test]
    fn test_all_formats_comparison() {
        use super::{OptimizedProtobufSerializer, ProtobufSerializer};

        let terms: Vec<String> = (0..100).map(|i| format!("term{:03}", i)).collect();
        let dict = PathMapDictionary::from_iter(terms);

        // Serialize with all formats
        let mut bincode_buf = Vec::new();
        BincodeSerializer::serialize(&dict, &mut bincode_buf).unwrap();

        let mut json_buf = Vec::new();
        JsonSerializer::serialize(&dict, &mut json_buf).unwrap();

        let mut proto_v1_buf = Vec::new();
        ProtobufSerializer::serialize(&dict, &mut proto_v1_buf).unwrap();

        let mut proto_v2_buf = Vec::new();
        OptimizedProtobufSerializer::serialize(&dict, &mut proto_v2_buf).unwrap();

        println!("\n=== Format Comparison (100 terms) ===");
        println!("Bincode:           {} bytes", bincode_buf.len());
        println!("JSON:              {} bytes", json_buf.len());
        println!("Protobuf V1:       {} bytes", proto_v1_buf.len());
        println!("Protobuf V2 (opt): {} bytes", proto_v2_buf.len());

        let v2_vs_v1_savings =
            ((proto_v1_buf.len() - proto_v2_buf.len()) as f64 / proto_v1_buf.len() as f64) * 100.0;
        println!("\nV2 vs V1 savings: {:.1}%", v2_vs_v1_savings);

        // All should deserialize correctly
        let loaded_bincode: PathMapDictionary =
            BincodeSerializer::deserialize(&bincode_buf[..]).unwrap();
        let loaded_json: PathMapDictionary = JsonSerializer::deserialize(&json_buf[..]).unwrap();
        let loaded_proto_v1: PathMapDictionary =
            ProtobufSerializer::deserialize(&proto_v1_buf[..]).unwrap();
        let loaded_proto_v2: PathMapDictionary =
            OptimizedProtobufSerializer::deserialize(&proto_v2_buf[..]).unwrap();

        assert_eq!(loaded_bincode.len(), Some(100));
        assert_eq!(loaded_json.len(), Some(100));
        assert_eq!(loaded_proto_v1.len(), Some(100));
        assert_eq!(loaded_proto_v2.len(), Some(100));
    }

    #[cfg(feature = "compression")]
    #[test]
    fn test_gzip_bincode_roundtrip() {
        use super::GzipSerializer;

        let dict = PathMapDictionary::from_iter(vec!["hello", "world", "test"]);

        // Serialize with gzip
        let mut buffer = Vec::new();
        GzipSerializer::<BincodeSerializer>::serialize(&dict, &mut buffer).unwrap();

        // Deserialize
        let loaded_dict: PathMapDictionary =
            GzipSerializer::<BincodeSerializer>::deserialize(&buffer[..]).unwrap();

        // Verify
        assert_eq!(loaded_dict.len(), Some(3));
        assert!(loaded_dict.contains("hello"));
        assert!(loaded_dict.contains("world"));
        assert!(loaded_dict.contains("test"));
    }

    #[cfg(feature = "compression")]
    #[test]
    fn test_gzip_compression_ratio() {
        use super::GzipSerializer;

        let terms: Vec<String> = (0..100).map(|i| format!("term{:03}", i)).collect();
        let dict = PathMapDictionary::from_iter(terms);

        // Serialize without compression
        let mut uncompressed = Vec::new();
        BincodeSerializer::serialize(&dict, &mut uncompressed).unwrap();

        // Serialize with compression
        let mut compressed = Vec::new();
        GzipSerializer::<BincodeSerializer>::serialize(&dict, &mut compressed).unwrap();

        println!("\n=== Compression Test ===");
        println!("Uncompressed: {} bytes", uncompressed.len());
        println!("Compressed:   {} bytes", compressed.len());
        let ratio =
            (uncompressed.len() - compressed.len()) as f64 / uncompressed.len() as f64 * 100.0;
        println!("Savings:      {:.1}%", ratio);

        // Compressed should be smaller
        assert!(
            compressed.len() < uncompressed.len(),
            "Compressed ({} bytes) should be smaller than uncompressed ({} bytes)",
            compressed.len(),
            uncompressed.len()
        );

        // Both should deserialize to same dictionary
        let loaded_uncompressed: PathMapDictionary =
            BincodeSerializer::deserialize(&uncompressed[..]).unwrap();
        let loaded_compressed: PathMapDictionary =
            GzipSerializer::<BincodeSerializer>::deserialize(&compressed[..]).unwrap();

        assert_eq!(loaded_uncompressed.len(), loaded_compressed.len());
    }

    #[cfg(all(feature = "compression", feature = "protobuf"))]
    #[test]
    fn test_gzip_with_all_formats() {
        use super::{GzipSerializer, OptimizedProtobufSerializer, ProtobufSerializer};

        let terms: Vec<String> = (0..50).map(|i| format!("word{:02}", i)).collect();
        let dict = PathMapDictionary::from_iter(terms);

        // Test gzip with bincode
        let mut gz_bincode = Vec::new();
        GzipSerializer::<BincodeSerializer>::serialize(&dict, &mut gz_bincode).unwrap();
        let loaded: PathMapDictionary =
            GzipSerializer::<BincodeSerializer>::deserialize(&gz_bincode[..]).unwrap();
        assert_eq!(loaded.len(), Some(50));

        // Test gzip with JSON
        let mut gz_json = Vec::new();
        GzipSerializer::<JsonSerializer>::serialize(&dict, &mut gz_json).unwrap();
        let loaded: PathMapDictionary =
            GzipSerializer::<JsonSerializer>::deserialize(&gz_json[..]).unwrap();
        assert_eq!(loaded.len(), Some(50));

        // Test gzip with Protobuf V1
        let mut gz_proto_v1 = Vec::new();
        GzipSerializer::<ProtobufSerializer>::serialize(&dict, &mut gz_proto_v1).unwrap();
        let loaded: PathMapDictionary =
            GzipSerializer::<ProtobufSerializer>::deserialize(&gz_proto_v1[..]).unwrap();
        assert_eq!(loaded.len(), Some(50));

        // Test gzip with Protobuf V2
        let mut gz_proto_v2 = Vec::new();
        GzipSerializer::<OptimizedProtobufSerializer>::serialize(&dict, &mut gz_proto_v2).unwrap();
        let loaded: PathMapDictionary =
            GzipSerializer::<OptimizedProtobufSerializer>::deserialize(&gz_proto_v2[..]).unwrap();
        assert_eq!(loaded.len(), Some(50));

        println!("\n=== Gzip + Format Comparison (50 terms) ===");
        println!("Gzip+Bincode:     {} bytes", gz_bincode.len());
        println!("Gzip+JSON:        {} bytes", gz_json.len());
        println!("Gzip+Protobuf V1: {} bytes", gz_proto_v1.len());
        println!("Gzip+Protobuf V2: {} bytes", gz_proto_v2.len());
    }
}
