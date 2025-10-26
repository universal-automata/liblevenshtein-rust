# Refactoring Plan: Shared Commands and Module Splitting

This document provides a detailed implementation plan for the remaining architectural improvements identified in `ARCHITECTURE.md`.

## Overview

The goal is to eliminate code duplication between CLI and REPL by extracting shared command logic, which will naturally reduce the size of both modules.

## Current State

- `src/cli/commands.rs`: 1061 lines - CLI command handlers (mostly duplicated logic)
- `src/repl/command.rs`: 1371 lines - REPL command parser + handlers (mostly duplicated logic)
- `src/serialization/mod.rs`: 1080 lines - All serialization formats in one file
- **Duplication**: ~800 lines of similar query/modify/IO logic between CLI and REPL

## Target State

After refactoring:
- `src/commands/`: 950 lines - Shared command handlers (eliminates duplication)
- `src/cli/`: 200 lines - Thin wrapper dispatching to shared handlers
- `src/repl/`: 750 lines - Enum + parser + thin executor using shared handlers
- `src/serialization/`: ~650 lines - Split across format-specific files

**Net savings**: ~530 lines + eliminated duplication + improved testability

## Phase 1: Extract and Split Shared Command Module (Priority 1)

### Goal
Create a shared command execution layer with all handler logic that both CLI and REPL can use. This is the main refactoring task - once complete, CLI and REPL naturally become thin wrappers.

### Implementation Steps

#### 1.1 Create Commands Module Structure

```bash
mkdir -p src/commands
touch src/commands/mod.rs
touch src/commands/core.rs
touch src/commands/query.rs
touch src/commands/modify.rs
touch src/commands/io.rs
```

#### 1.2 Define Core Command Types (`src/commands/core.rs`)

```rust
//! Core command definitions shared between CLI and REPL

use crate::dictionary::Dictionary;
use crate::transducer::Algorithm;
use anyhow::Result;
use std::path::PathBuf;

/// Query parameters used by both CLI and REPL
#[derive(Debug, Clone)]
pub struct QueryParams {
    pub term: String,
    pub max_distance: usize,
    pub algorithm: Algorithm,
    pub prefix: bool,
    pub show_distances: bool,
    pub limit: Option<usize>,
}

/// Dictionary modification operations
#[derive(Debug, Clone)]
pub enum ModifyOp {
    Insert { terms: Vec<String> },
    Delete { terms: Vec<String> },
    Clear,
}

/// Dictionary I/O operations
#[derive(Debug, Clone)]
pub enum IoOp {
    Load { path: PathBuf },
    Save { path: PathBuf },
    Info { path: PathBuf },
}

/// Result type for command execution
pub struct CommandResult {
    pub output: String,
    pub modified: bool,
}
```

#### 1.3 Implement Query Handler (`src/commands/query.rs`)

```rust
//! Shared query command implementation

use super::core::{CommandResult, QueryParams};
use crate::dictionary::Dictionary;
use crate::transducer::Transducer;
use anyhow::Result;

pub fn execute_query<D: Dictionary>(
    dict: &D,
    params: QueryParams,
) -> Result<CommandResult> {
    let transducer = Transducer::new(dict, params.algorithm);

    let mut results = if params.show_distances {
        let candidates: Vec<_> = transducer
            .query_with_distance(&params.term, params.max_distance)
            .take(params.limit.unwrap_or(usize::MAX))
            .collect();

        format_results_with_distances(candidates)
    } else {
        let terms: Vec<_> = transducer
            .query(&params.term, params.max_distance)
            .take(params.limit.unwrap_or(usize::MAX))
            .collect();

        format_results(terms)
    };

    Ok(CommandResult {
        output: results,
        modified: false,
    })
}

fn format_results(terms: Vec<String>) -> String {
    if terms.is_empty() {
        "No matches found".to_string()
    } else {
        terms.join("\n")
    }
}

fn format_results_with_distances(
    candidates: Vec<crate::transducer::Candidate>
) -> String {
    if candidates.is_empty() {
        "No matches found".to_string()
    } else {
        candidates
            .iter()
            .map(|c| format!("{} (distance: {})", c.term, c.distance))
            .collect::<Vec<_>>()
            .join("\n")
    }
}
```

#### 1.4 Update CLI to Use Shared Commands

In `src/cli/commands.rs`, replace the implementation:

```rust
use crate::commands::core::QueryParams;
use crate::commands::query::execute_query;

fn cmd_query(...) -> Result<()> {
    // Load dictionary (existing code)
    let dict = load_dictionary(...)?;

    // Create params
    let params = QueryParams {
        term: term.to_string(),
        max_distance,
        algorithm,
        prefix,
        show_distances,
        limit,
    };

    // Execute shared command
    let result = execute_query(&dict, params)?;
    println!("{}", result.output);

    Ok(())
}
```

#### 1.5 Update REPL to Use Shared Commands

In `src/repl/command.rs`, update the execute method:

```rust
use crate::commands::core::QueryParams;
use crate::commands::query::execute_query;

impl Command {
    pub fn execute(&self, state: &mut ReplState) -> Result<CommandResult> {
        match self {
            Command::Query { term, distance, prefix, limit } => {
                let params = QueryParams {
                    term: term.clone(),
                    max_distance: distance.unwrap_or(state.max_distance),
                    algorithm: state.algorithm,
                    prefix: *prefix,
                    show_distances: state.show_distances,
                    limit: *limit,
                };

                match &state.dict {
                    Some(container) => {
                        // Call shared implementation
                        execute_query_on_container(container, params)
                    }
                    None => bail!("No dictionary loaded"),
                }
            }
            // ... other commands
        }
    }
}
```

### Testing Strategy

1. Run existing CLI tests: `cargo test --features cli`
2. Run existing REPL tests: `cargo test --lib repl`
3. Verify no regressions in functionality
4. Add integration tests for shared commands

## Phase 2: Refactor REPL to Use Shared Commands (Priority 2)

### Goal
Update REPL to use shared command handlers from Phase 1. This naturally reduces REPL from 1371 lines to ~750 lines.

### Target Structure

```
src/repl/
├── mod.rs
├── command.rs       (~150 lines: Command enum + CommandResult)
├── parser.rs        (~400 lines: Parse user input into Command)
├── executor.rs      (~200 lines: Map Command to shared handlers)
├── state.rs         (existing)
├── helper.rs        (existing)
└── highlighter.rs   (existing)
```

### Key Insight
Most of the 1371 lines are handlers - these move to `src/commands/` in Phase 1. What remains is just the REPL-specific parsing and thin execution wrappers.

### Implementation Steps

#### 2.1 Extract Command Enum

Keep only the enum definition in `command.rs`:

```rust
//! REPL command definitions

#[derive(Debug, Clone)]
pub enum Command {
    Query { ... },
    Insert { ... },
    // ... all variants
}

pub enum CommandResult {
    Success(String),
    Continue,
    Exit,
}
```

#### 2.2 Move Parsing Logic

Create `parser.rs` with all parsing functions:

```rust
//! Command parsing from user input

use super::command::Command;
use anyhow::Result;

pub fn parse(input: &str) -> Result<Command> {
    // All existing parsing logic
}

fn parse_query(args: &[&str]) -> Result<Command> { ... }
fn parse_insert(args: &[&str]) -> Result<Command> { ... }
// ... other parsers
```

#### 2.3 Create Handler Modules

Each handler implements execution for related commands:

```rust
// src/repl/handlers/query.rs
use crate::repl::{Command, CommandResult, ReplState};
use anyhow::Result;

pub fn handle_query(
    state: &mut ReplState,
    term: &str,
    distance: Option<usize>,
    prefix: bool,
    limit: Option<usize>,
) -> Result<CommandResult> {
    // Use shared command from Phase 1
    // ...
}
```

## Phase 3: Extract Serialization Formats (Priority 3)

### Goal
Split `src/serialization/mod.rs` (1080 lines) into format-specific modules.

### Target Structure

```
src/serialization/
├── mod.rs          (~150 lines: traits + core)
├── bincode.rs      (~100 lines)
├── json.rs         (~100 lines)
├── protobuf.rs     (~400 lines: v1 + v2)
└── compression.rs  (~100 lines)
```

### Implementation Steps

#### 3.1 Keep Core in mod.rs

```rust
//! Dictionary serialization support

pub mod bincode;
pub mod json;
#[cfg(feature = "protobuf")]
pub mod protobuf;
#[cfg(feature = "compression")]
pub mod compression;

// Re-export main types
pub use self::bincode::BincodeSerializer;
pub use self::json::JsonSerializer;
// ... etc

pub trait DictionarySerializer { ... }
pub trait DictionaryFromTerms { ... }
pub fn extract_terms<D: Dictionary>(dict: &D) -> Vec<String> { ... }
```

#### 3.2 Move Bincode Implementation

```rust
// src/serialization/bincode.rs
//! Bincode serializer for compact binary format

use super::{DictionarySerializer, SerializationError, extract_terms};
use crate::dictionary::Dictionary;
use std::io::{Read, Write};

pub struct BincodeSerializer;

impl DictionarySerializer for BincodeSerializer {
    // ... implementation
}

#[cfg(test)]
mod tests {
    // Bincode-specific tests
}
```

#### 3.3 Move Other Formats Similarly

- `json.rs` - JSON serializer
- `protobuf.rs` - Both ProtobufSerializer and OptimizedProtobufSerializer
- `compression.rs` - GzipSerializer wrapper

## Phase 4: Refactor CLI to Use Shared Commands (Priority 4)

### Goal
Update CLI to use shared command handlers from Phase 1. This reduces CLI from 1061 lines to ~200 lines of dispatch logic.

### Target Structure

```
src/cli/
├── mod.rs
├── args.rs         (~250 lines: clap definitions - unchanged)
├── commands.rs     (~200 lines: dispatch to shared handlers)
├── detect.rs       (existing)
└── paths.rs        (existing)
```

### Key Insight
No need for separate handler files - the logic is in `src/commands/`. CLI just needs to parse args and call shared handlers.

### Implementation

CLI becomes a thin facade over shared commands:

```rust
// src/cli/handlers/query.rs
use crate::commands::core::QueryParams;
use crate::commands::query::execute_query;
use anyhow::Result;

pub fn handle_query(...) -> Result<()> {
    let dict = load_dictionary(...)?;
    let params = QueryParams { ... };
    let result = execute_query(&dict, params)?;
    println!("{}", result.output);
    Ok(())
}
```

## Migration Strategy

### Incremental Approach

1. **Commit after each phase** to maintain working state
2. **Run full test suite** after each change
3. **Keep both old and new code** temporarily with feature flags if needed
4. **Update documentation** as you go

### Testing Checklist

After each phase:
- [ ] `cargo test --all-features --lib`
- [ ] `cargo test --all-features --test '*'`
- [ ] `cargo clippy --all-features`
- [ ] `cargo build --all-features`
- [ ] Manual REPL testing for interactive commands
- [ ] Manual CLI testing for command-line operations

### Rollback Plan

If a phase causes issues:
1. Revert the commit for that phase
2. Identify the problem
3. Fix and retry
4. Each phase is independent, so reverting one doesn't affect others

## Benefits After Completion

1. **Reduced duplication**: ~800 lines of duplicated query/modify logic eliminated
2. **Easier testing**: Shared commands can be unit tested independently
3. **Better maintainability**: Each module has a single, clear responsibility
4. **Improved readability**: Files are 100-400 lines instead of 1000+
5. **Faster development**: Changes to query logic only need to be made once

## Timeline Estimate

- Phase 1 (Extract & split shared commands): 6-8 hours ← Main work
- Phase 2 (Refactor REPL wrapper): 1-2 hours ← Quick update
- Phase 3 (Split serialization): 2-3 hours
- Phase 4 (Refactor CLI wrapper): 1 hour ← Quick update

**Total**: ~10-14 hours of focused work

**Note**: Phase 1 is the bulk of the work. Once it's done, Phases 2 and 4 are straightforward refactorings that mostly involve deleting code and adding delegation calls.

## Questions to Consider

1. Should shared commands be in `src/commands/` or `src/core/commands/`?
2. Do we want a `CommandExecutor` trait for dependency injection?
3. Should handlers return structured results or formatted strings?
4. Do we need a command builder pattern for complex commands?

## Next Steps

1. Review this plan
2. Start with Phase 1 (shared commands)
3. Create a feature branch for the work
4. Commit frequently
5. Open a PR when complete
