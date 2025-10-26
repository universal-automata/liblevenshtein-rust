//! REPL state management
//!
//! Manages the dictionary backend, algorithm selection, and query parameters.

use crate::cli::args::SerializationFormat;
use crate::dictionary::dawg::DawgDictionary;
use crate::dictionary::dynamic_dawg::DynamicDawg;
use crate::dictionary::pathmap::PathMapDictionary;
use crate::dictionary::{Dictionary, DictionaryNode};
use crate::transducer::{Algorithm, Transducer};
use anyhow::Result;
use std::path::Path;

/// Helper to extract all terms from any dictionary using DFS
fn extract_terms<D: Dictionary>(dict: &D) -> Vec<String> {
    let est_size = dict.len().unwrap_or(100);
    let mut terms = Vec::with_capacity(est_size);
    let mut current_term = Vec::with_capacity(32);

    fn dfs<N: DictionaryNode>(node: &N, current_term: &mut Vec<u8>, terms: &mut Vec<String>) {
        if node.is_final() {
            if let Ok(term) = String::from_utf8(current_term.clone()) {
                terms.push(term);
            }
        }

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

/// Dictionary backend type
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(
    feature = "cli",
    derive(clap::ValueEnum, serde::Serialize, serde::Deserialize)
)]
pub enum DictionaryBackend {
    /// PathMap-based trie (default, fast insertion/deletion)
    PathMap,
    /// Static DAWG (read-only, compressed)
    Dawg,
    /// Dynamic DAWG (supports modifications, compressed)
    DynamicDawg,
}

impl std::fmt::Display for DictionaryBackend {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::PathMap => write!(f, "path-map"),
            Self::Dawg => write!(f, "dawg"),
            Self::DynamicDawg => write!(f, "dynamic-dawg"),
        }
    }
}

impl std::str::FromStr for DictionaryBackend {
    type Err = anyhow::Error;

    fn from_str(s: &str) -> Result<Self> {
        match s.to_lowercase().as_str() {
            "pathmap" => Ok(Self::PathMap),
            "dawg" => Ok(Self::Dawg),
            "dynamic-dawg" | "dynamicdawg" => Ok(Self::DynamicDawg),
            _ => Err(anyhow::anyhow!(
                "Unknown backend: {}. Valid options: pathmap, dawg, dynamic-dawg",
                s
            )),
        }
    }
}

/// Unified dictionary container
pub enum DictContainer {
    /// PathMap-based trie dictionary
    PathMap(PathMapDictionary),
    /// Static DAWG dictionary
    Dawg(DawgDictionary),
    /// Dynamic DAWG dictionary
    DynamicDawg(DynamicDawg),
}

impl DictContainer {
    /// Get the backend type
    pub fn backend(&self) -> DictionaryBackend {
        match self {
            Self::PathMap(_) => DictionaryBackend::PathMap,
            Self::Dawg(_) => DictionaryBackend::Dawg,
            Self::DynamicDawg(_) => DictionaryBackend::DynamicDawg,
        }
    }

    /// Check if term exists
    pub fn contains(&self, term: &str) -> bool {
        match self {
            Self::PathMap(d) => d.contains(term),
            Self::Dawg(d) => d.contains(term),
            Self::DynamicDawg(d) => d.contains(term),
        }
    }

    /// Insert a term (only for mutable backends)
    pub fn insert(&mut self, term: &str) -> Result<bool> {
        match self {
            Self::PathMap(d) => Ok(d.insert(term)),
            Self::Dawg(_) => Err(anyhow::anyhow!("DAWG dictionary is read-only. Use 'backend dynamic-dawg' or 'backend pathmap' for modifications.")),
            Self::DynamicDawg(d) => Ok(d.insert(term)),
        }
    }

    /// Remove a term (only for mutable backends)
    pub fn remove(&mut self, term: &str) -> Result<bool> {
        match self {
            Self::PathMap(d) => Ok(d.remove(term)),
            Self::Dawg(_) => Err(anyhow::anyhow!("DAWG dictionary is read-only. Use 'backend dynamic-dawg' or 'backend pathmap' for modifications.")),
            Self::DynamicDawg(d) => Ok(d.remove(term)),
        }
    }

    /// Get term count
    pub fn len(&self) -> usize {
        match self {
            Self::PathMap(d) => d.len().unwrap_or(0),
            Self::Dawg(d) => d.len().unwrap_or(0),
            Self::DynamicDawg(d) => d.len().unwrap_or(0),
        }
    }

    /// Check if empty
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Collect all terms
    pub fn terms(&self) -> Vec<String> {
        match self {
            Self::PathMap(d) => extract_terms(d),
            Self::Dawg(d) => extract_terms(d),
            Self::DynamicDawg(d) => extract_terms(d),
        }
    }

    /// Migrate to a different backend
    pub fn migrate_to(&self, backend: DictionaryBackend) -> Result<Self> {
        let terms: Vec<String> = self.terms();

        let new_dict = match backend {
            DictionaryBackend::PathMap => {
                let dict = PathMapDictionary::from_iter(terms.iter().map(|s| s.as_str()));
                Self::PathMap(dict)
            }
            DictionaryBackend::Dawg => {
                let dict = DawgDictionary::from_iter(terms.iter().map(|s| s.as_str()));
                Self::Dawg(dict)
            }
            DictionaryBackend::DynamicDawg => {
                let dict = DynamicDawg::new();
                for term in &terms {
                    dict.insert(term);
                }
                Self::DynamicDawg(dict)
            }
        };

        Ok(new_dict)
    }

    /// Clear all terms (only for mutable backends)
    pub fn clear(&mut self) -> Result<()> {
        match self {
            Self::PathMap(d) => {
                d.clear();
                Ok(())
            }
            Self::Dawg(_) => Err(anyhow::anyhow!("DAWG dictionary is read-only")),
            Self::DynamicDawg(_) => {
                // Replace with new empty DynamicDawg
                *self = Self::DynamicDawg(DynamicDawg::new());
                Ok(())
            }
        }
    }

    /// Compact/minimize (for dynamic backends)
    pub fn compact(&mut self) -> Result<()> {
        match self {
            Self::PathMap(_) => {
                // PathMap doesn't need compaction
                Ok(())
            }
            Self::Dawg(_) => Err(anyhow::anyhow!("DAWG dictionary is already minimized")),
            Self::DynamicDawg(d) => {
                d.minimize();
                Ok(())
            }
        }
    }
}

/// REPL state
pub struct ReplState {
    /// Dictionary container
    pub dictionary: DictContainer,
    /// Current backend type
    pub backend: DictionaryBackend,
    /// Serialization format for save/load operations
    pub serialization_format: SerializationFormat,
    /// Levenshtein algorithm
    pub algorithm: Algorithm,
    /// Maximum edit distance
    pub max_distance: usize,
    /// Whether to show distances in query results
    pub show_distances: bool,
    /// Whether to use prefix matching by default
    pub prefix_mode: bool,
    /// Result limit for queries
    pub result_limit: Option<usize>,
    /// Whether to auto-save after modifications
    pub auto_sync: bool,
    /// Path for auto-sync operations
    pub auto_sync_path: Option<std::path::PathBuf>,
    /// Custom config file path
    pub config_file_path: Option<std::path::PathBuf>,
}

impl ReplState {
    /// Create new REPL state with empty PathMap dictionary
    pub fn new() -> Self {
        // Default to Protobuf if available, otherwise Bincode
        #[cfg(feature = "protobuf")]
        let default_format = SerializationFormat::Protobuf;
        #[cfg(not(feature = "protobuf"))]
        let default_format = SerializationFormat::Bincode;

        Self {
            dictionary: DictContainer::PathMap(PathMapDictionary::new()),
            backend: DictionaryBackend::PathMap,
            serialization_format: default_format,
            algorithm: Algorithm::Standard,
            max_distance: 2,
            show_distances: false,
            prefix_mode: false,
            result_limit: None,
            auto_sync: false,
            auto_sync_path: None,
            config_file_path: None,
        }
    }

    /// Load dictionary from file
    pub fn load_from_file(&mut self, path: &Path, backend: DictionaryBackend) -> Result<usize> {
        #[cfg(feature = "cli")]
        {
            use crate::cli::commands::load_dictionary;
            use crate::cli::detect::detect_format;

            // Detect format
            let detection = detect_format(path, Some(backend), None)?;

            // Update serialization format based on detection
            self.serialization_format = detection.format.format;

            // Load dictionary using CLI function
            self.dictionary = load_dictionary(path, detection.format)?;
            self.backend = detection.format.backend;

            let count = self.dictionary.len();
            Ok(count)
        }

        #[cfg(not(feature = "cli"))]
        {
            // Fallback to plain text loading if CLI feature is not enabled
            let contents = std::fs::read_to_string(path)
                .with_context(|| format!("Failed to read dictionary file: {}", path.display()))?;

            let terms: Vec<&str> = contents
                .lines()
                .map(|line| line.trim())
                .filter(|line| !line.is_empty() && !line.starts_with('#'))
                .collect();

            if terms.is_empty() {
                return Err(anyhow::anyhow!("Dictionary file is empty"));
            }

            let term_count = terms.len();

            self.dictionary = match backend {
                DictionaryBackend::PathMap => {
                    DictContainer::PathMap(PathMapDictionary::from_iter(terms))
                }
                DictionaryBackend::Dawg => DictContainer::Dawg(DawgDictionary::from_iter(terms)),
                DictionaryBackend::DynamicDawg => {
                    let dict = DynamicDawg::new();
                    for term in &terms {
                        dict.insert(term);
                    }
                    DictContainer::DynamicDawg(dict)
                }
            };

            self.backend = backend;
            Ok(term_count)
        }
    }

    /// Save dictionary to file
    pub fn save_to_file(&self, path: &Path) -> Result<usize> {
        #[cfg(feature = "cli")]
        {
            use crate::cli::commands::save_dictionary;

            let count = self.dictionary.len();
            save_dictionary(&self.dictionary, path, self.serialization_format)?;
            Ok(count)
        }

        #[cfg(not(feature = "cli"))]
        {
            // Fallback to plain text saving if CLI feature is not enabled
            let terms = self.dictionary.terms();
            let content = terms.join("\n");

            std::fs::write(path, content)
                .with_context(|| format!("Failed to write dictionary file: {}", path.display()))?;

            Ok(terms.len())
        }
    }

    /// Change backend (migrates data)
    pub fn change_backend(&mut self, backend: DictionaryBackend) -> Result<()> {
        if self.backend == backend {
            return Ok(()); // Already using this backend
        }

        self.dictionary = self.dictionary.migrate_to(backend)?;
        self.backend = backend;
        Ok(())
    }

    /// Query the dictionary
    pub fn query(&self, term: &str) -> Vec<(String, usize)> {
        let mut results: Vec<_> = match &self.dictionary {
            DictContainer::PathMap(d) => {
                let transducer = Transducer::new(d.clone(), self.algorithm);
                if self.prefix_mode {
                    transducer
                        .query_ordered(term, self.max_distance)
                        .prefix()
                        .map(|c| (c.term, c.distance))
                        .collect()
                } else {
                    transducer
                        .query_ordered(term, self.max_distance)
                        .map(|c| (c.term, c.distance))
                        .collect()
                }
            }
            DictContainer::Dawg(d) => {
                let transducer = Transducer::new(d.clone(), self.algorithm);
                if self.prefix_mode {
                    transducer
                        .query_ordered(term, self.max_distance)
                        .prefix()
                        .map(|c| (c.term, c.distance))
                        .collect()
                } else {
                    transducer
                        .query_ordered(term, self.max_distance)
                        .map(|c| (c.term, c.distance))
                        .collect()
                }
            }
            DictContainer::DynamicDawg(d) => {
                let transducer = Transducer::new(d.clone(), self.algorithm);
                if self.prefix_mode {
                    transducer
                        .query_ordered(term, self.max_distance)
                        .prefix()
                        .map(|c| (c.term, c.distance))
                        .collect()
                } else {
                    transducer
                        .query_ordered(term, self.max_distance)
                        .map(|c| (c.term, c.distance))
                        .collect()
                }
            }
        };

        if let Some(limit) = self.result_limit {
            results.truncate(limit);
        }

        results
    }

    /// Get dictionary statistics
    pub fn stats(&self) -> DictStats {
        DictStats {
            backend: self.backend,
            term_count: self.dictionary.len(),
            node_count: self.node_count(),
        }
    }

    fn node_count(&self) -> Option<usize> {
        match &self.dictionary {
            DictContainer::Dawg(d) => Some(d.node_count()),
            DictContainer::DynamicDawg(d) => Some(d.node_count()),
            DictContainer::PathMap(_) => None,
        }
    }
}

impl Default for ReplState {
    fn default() -> Self {
        Self::new()
    }
}

/// Dictionary statistics
#[derive(Debug)]
pub struct DictStats {
    /// Dictionary backend type
    pub backend: DictionaryBackend,
    /// Number of terms in the dictionary
    pub term_count: usize,
    /// Number of nodes (if available)
    pub node_count: Option<usize>,
}

impl std::fmt::Display for DictStats {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "Backend:    {}", self.backend)?;
        writeln!(f, "Terms:      {}", self.term_count)?;
        if let Some(nodes) = self.node_count {
            writeln!(f, "Nodes:      {}", nodes)?;
            if self.term_count > 0 {
                let ratio = nodes as f64 / self.term_count as f64;
                writeln!(f, "Compression: {:.2}x (nodes/terms)", ratio)?;
            }
        }
        Ok(())
    }
}
