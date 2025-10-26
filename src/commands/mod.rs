//! Shared command logic for CLI and REPL
//!
//! This module contains the core command execution logic that is shared
//! between the CLI and REPL interfaces. By centralizing this logic, we:
//!
//! - Eliminate code duplication (~800 lines)
//! - Ensure consistent behavior between CLI and REPL
//! - Make testing easier (test once, works everywhere)
//! - Simplify maintenance (change once, applies everywhere)

pub mod core;
pub mod handlers;

// Re-export commonly used types
pub use core::{CommandResult, IoOp, ModifyOp, QueryParams};
