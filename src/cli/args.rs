//! CLI argument definitions

use clap::{Parser, Subcommand, ValueEnum};
use std::path::PathBuf;
use crate::transducer::Algorithm;
use crate::repl::state::DictionaryBackend;

#[derive(Parser)]
#[command(name = "liblevenshtein")]
#[command(about = "Fast fuzzy string matching with Levenshtein automata")]
#[command(version)]
pub struct Cli {
    /// Custom configuration file path
    #[arg(short = 'c', long, global = true)]
    pub config: Option<PathBuf>,

    #[command(subcommand)]
    pub command: Commands,
}

#[derive(Subcommand)]
pub enum Commands {
    /// Launch interactive REPL
    Repl {
        /// Dictionary file to load
        #[arg(short, long)]
        dict: Option<PathBuf>,

        /// Dictionary backend (auto-detected if not specified)
        #[arg(short, long)]
        backend: Option<DictionaryBackend>,

        /// Serialization format (auto-detected if not specified)
        #[arg(short = 'f', long)]
        format: Option<SerializationFormat>,

        /// Levenshtein algorithm
        #[arg(short, long, default_value = "standard")]
        algorithm: Algorithm,

        /// Maximum edit distance
        #[arg(short = 'm', long, default_value = "2")]
        max_distance: usize,

        /// Enable prefix matching mode
        #[arg(short, long)]
        prefix: bool,

        /// Show distances in query results
        #[arg(short = 's', long)]
        show_distances: bool,

        /// Result limit
        #[arg(short, long)]
        limit: Option<usize>,

        /// Enable auto-sync (save after every modification)
        #[arg(long)]
        auto_sync: bool,
    },

    /// Query dictionary for fuzzy matches
    Query {
        /// Query term
        term: String,

        /// Dictionary file
        #[arg(short, long)]
        dict: Option<PathBuf>,

        /// Dictionary backend (auto-detected if not specified)
        #[arg(short, long)]
        backend: Option<DictionaryBackend>,

        /// Serialization format (auto-detected if not specified)
        #[arg(short = 'f', long)]
        format: Option<SerializationFormat>,

        /// Maximum edit distance
        #[arg(short = 'm', long, default_value = "2")]
        max_distance: usize,

        /// Levenshtein algorithm
        #[arg(short, long, default_value = "standard")]
        algorithm: Algorithm,

        /// Enable prefix matching
        #[arg(short, long)]
        prefix: bool,

        /// Show distances
        #[arg(short = 's', long)]
        show_distances: bool,

        /// Limit results
        #[arg(short, long)]
        limit: Option<usize>,
    },

    /// Display dictionary information
    Info {
        /// Dictionary file
        dict: Option<PathBuf>,
    },

    /// Convert dictionary between formats
    Convert {
        /// Input dictionary file
        input: PathBuf,

        /// Output dictionary file
        output: PathBuf,

        /// Input backend (auto-detected if not specified)
        #[arg(long)]
        from_backend: Option<DictionaryBackend>,

        /// Output backend
        #[arg(long, default_value = "pathmap")]
        to_backend: DictionaryBackend,

        /// Input format (auto-detected if not specified)
        #[arg(long)]
        from_format: Option<SerializationFormat>,

        /// Output format
        #[arg(long, default_value = "bincode")]
        to_format: SerializationFormat,
    },

    /// Insert terms into dictionary
    Insert {
        /// Terms to insert
        terms: Vec<String>,

        /// Dictionary file
        #[arg(short, long)]
        dict: Option<PathBuf>,

        /// Dictionary backend (auto-detected if not specified)
        #[arg(short, long)]
        backend: Option<DictionaryBackend>,

        /// Serialization format (auto-detected if not specified)
        #[arg(short = 'f', long)]
        format: Option<SerializationFormat>,
    },

    /// Delete terms from dictionary
    Delete {
        /// Terms to delete
        terms: Vec<String>,

        /// Dictionary file
        #[arg(short, long)]
        dict: Option<PathBuf>,

        /// Dictionary backend (auto-detected if not specified)
        #[arg(short, long)]
        backend: Option<DictionaryBackend>,

        /// Serialization format (auto-detected if not specified)
        #[arg(short = 'f', long)]
        format: Option<SerializationFormat>,
    },

    /// Clear all terms from dictionary
    Clear {
        /// Dictionary file
        #[arg(short, long)]
        dict: Option<PathBuf>,

        /// Dictionary backend (auto-detected if not specified)
        #[arg(short, long)]
        backend: Option<DictionaryBackend>,

        /// Serialization format (auto-detected if not specified)
        #[arg(short = 'f', long)]
        format: Option<SerializationFormat>,
    },

    /// Minimize/compact dictionary (for DynamicDawg)
    Minimize {
        /// Dictionary file
        #[arg(short, long)]
        dict: Option<PathBuf>,

        /// Dictionary backend (auto-detected if not specified)
        #[arg(short, long)]
        backend: Option<DictionaryBackend>,

        /// Serialization format (auto-detected if not specified)
        #[arg(short = 'f', long)]
        format: Option<SerializationFormat>,
    },

    /// Show or update user settings
    Settings {
        /// Set default dictionary path
        #[arg(long)]
        set_dict: Option<PathBuf>,

        /// Set default backend
        #[arg(long)]
        set_backend: Option<DictionaryBackend>,

        /// Set default format
        #[arg(long)]
        set_format: Option<SerializationFormat>,

        /// Set default algorithm
        #[arg(long)]
        set_algorithm: Option<Algorithm>,

        /// Set default max distance
        #[arg(long)]
        set_max_distance: Option<usize>,

        /// Reset configuration to defaults
        #[arg(long)]
        reset: bool,
    },

    /// Manage config file location
    Config {
        /// Switch to a different config file (updates app config)
        #[arg(long)]
        switch: Option<PathBuf>,

        /// Show current config file path
        #[arg(long)]
        show: bool,
    },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, ValueEnum, serde::Serialize, serde::Deserialize)]
pub enum SerializationFormat {
    /// Plain text (one term per line)
    Text,
    /// Bincode binary format
    Bincode,
    /// JSON format
    Json,
    /// Protocol Buffers format
    #[cfg(feature = "protobuf")]
    Protobuf,
    /// Gzip-compressed Bincode format
    #[cfg(feature = "compression")]
    #[value(name = "bincode-gz")]
    BincodeGzip,
    /// Gzip-compressed JSON format
    #[cfg(feature = "compression")]
    #[value(name = "json-gz")]
    JsonGzip,
    /// Gzip-compressed Protocol Buffers format
    #[cfg(all(feature = "protobuf", feature = "compression"))]
    #[value(name = "protobuf-gz")]
    ProtobufGzip,
    /// PathMap's native .paths compressed format (PathMap backend only)
    #[value(name = "paths")]
    PathsNative,
}

impl std::fmt::Display for SerializationFormat {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Text => write!(f, "text"),
            Self::Bincode => write!(f, "bincode"),
            Self::Json => write!(f, "json"),
            #[cfg(feature = "protobuf")]
            Self::Protobuf => write!(f, "protobuf"),
            #[cfg(feature = "compression")]
            Self::BincodeGzip => write!(f, "bincode-gz"),
            #[cfg(feature = "compression")]
            Self::JsonGzip => write!(f, "json-gz"),
            #[cfg(all(feature = "protobuf", feature = "compression"))]
            Self::ProtobufGzip => write!(f, "protobuf-gz"),
            Self::PathsNative => write!(f, "paths"),
        }
    }
}
