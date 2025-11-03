//! Contextual completion engine for incremental fuzzy matching.
//!
//! This module provides components for building contextual code completion
//! systems with support for draft text, hierarchical scopes, and efficient
//! incremental updates as the user types.

mod checkpoint;
mod completion;
mod context_tree;
mod draft_buffer;
mod engine;
pub mod error;

pub use checkpoint::{Checkpoint, CheckpointStack};
pub use completion::Completion;
pub use context_tree::{ContextId, ContextTree};
pub use draft_buffer::DraftBuffer;
pub use engine::ContextualCompletionEngine;
pub use error::{ContextError, Result};
