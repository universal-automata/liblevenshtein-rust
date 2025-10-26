//! Core command definitions and types shared between CLI and REPL

use crate::transducer::Algorithm;
use std::path::PathBuf;

/// Query parameters used by both CLI and REPL
#[derive(Debug, Clone)]
pub struct QueryParams {
    /// The term to search for
    pub term: String,
    /// Maximum edit distance
    pub max_distance: usize,
    /// Levenshtein algorithm to use
    pub algorithm: Algorithm,
    /// Enable prefix matching mode
    pub prefix: bool,
    /// Show distances in results
    pub show_distances: bool,
    /// Limit number of results
    pub limit: Option<usize>,
}

/// Dictionary modification operations
#[derive(Debug, Clone)]
pub enum ModifyOp {
    /// Insert terms into the dictionary
    Insert {
        /// Terms to insert
        terms: Vec<String>,
    },
    /// Delete terms from the dictionary
    Delete {
        /// Terms to delete
        terms: Vec<String>,
    },
    /// Clear all terms from the dictionary
    Clear,
}

/// Dictionary I/O operations
#[derive(Debug, Clone)]
pub enum IoOp {
    /// Load dictionary from file
    Load {
        /// Path to dictionary file
        path: PathBuf,
    },
    /// Save dictionary to file
    Save {
        /// Path to save to
        path: PathBuf,
    },
    /// Display dictionary information
    Info {
        /// Optional path (use current dict if None)
        path: Option<PathBuf>,
    },
}

/// Result of command execution
#[derive(Debug)]
pub struct CommandResult {
    /// Output message to display
    pub output: String,
    /// Whether the dictionary was modified
    pub modified: bool,
    /// Whether to exit (for REPL)
    pub should_exit: bool,
}

impl CommandResult {
    /// Create a successful result with output
    pub fn success(output: impl Into<String>) -> Self {
        Self {
            output: output.into(),
            modified: false,
            should_exit: false,
        }
    }

    /// Create a result indicating modification
    pub fn modified(output: impl Into<String>) -> Self {
        Self {
            output: output.into(),
            modified: true,
            should_exit: false,
        }
    }

    /// Create a result that signals exit
    pub fn exit(output: impl Into<String>) -> Self {
        Self {
            output: output.into(),
            modified: false,
            should_exit: true,
        }
    }
}
