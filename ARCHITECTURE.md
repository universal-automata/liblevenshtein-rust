# liblevenshtein-rust Architecture Guide

This document outlines the current architecture and provides detailed plans for recommended improvements.

## Current Architecture

### Module Organization

```
src/
├── lib.rs                    # Public API and prelude
├── dictionary/               # Dictionary backends
│   ├── mod.rs               # Dictionary traits
│   ├── dawg.rs              # Static DAWG (529 lines)
│   ├── dynamic_dawg.rs      # Mutable DAWG (1031 lines)
│   ├── dawg_query.rs        # Optimized DAWG queries (345 lines)
│   └── pathmap.rs           # PathMap wrapper (451 lines)
├── transducer/              # Levenshtein automata
│   ├── mod.rs               # Transducer main struct
│   ├── algorithm.rs         # Algorithm types
│   ├── state.rs             # Automaton state (293 lines)
│   ├── transition.rs        # State transitions (485 lines)
│   ├── query.rs             # Unordered queries (254 lines)
│   ├── ordered_query.rs     # Ordered queries (754 lines)
│   ├── intersection.rs      # Dictionary-automaton intersection
│   ├── pool.rs              # State pooling (294 lines)
│   ├── position.rs          # Position in automaton
│   └── builder.rs           # Transducer builder (231 lines)
├── serialization/           # Dictionary persistence
│   └── mod.rs               # All formats (1080 lines) ⚠️
├── cli/                     # Command-line interface
│   ├── mod.rs
│   ├── args.rs              # Clap definitions (285 lines)
│   ├── commands.rs          # Command handlers (1061 lines) ⚠️
│   ├── detect.rs            # Format detection (261 lines)
│   └── paths.rs             # Path utilities (300 lines)
├── repl/                    # Interactive REPL
│   ├── mod.rs
│   ├── command.rs           # Commands + parsing + execution (1371 lines) ⚠️
│   ├── state.rs             # REPL state (455 lines)
│   ├── helper.rs            # Rustyline integration
│   └── highlighter.rs       # Syntax highlighting
└── distance/                # Distance calculations
    └── mod.rs

⚠️ = Files that need splitting
```

## Recommended Improvements

### 1. Split REPL Command Module ⭐ HIGH PRIORITY

**Problem:** `src/repl/command.rs` (1371 lines) contains command types, parsing, and ALL execution logic.

**Solution:**

```
src/repl/
├── mod.rs
├── state.rs
├── helper.rs
├── highlighter.rs
└── command/
    ├── mod.rs               # Command enum + CommandResult
    ├── parser.rs            # Command::parse() and parse_* methods
    ├── executor.rs          # Command::execute() dispatch
    └── handlers/
        ├── mod.rs
        ├── query.rs         # Query command implementation
        ├── dictionary.rs    # Insert, Delete, Contains, Load, Save
        ├── file_ops.rs      # InsertFrom, RemoveFrom, ReplaceWith
        ├── config.rs        # Backend, Algorithm, Distance, Prefix, etc.
        └── utility.rs       # Help, Stats, Dump, Settings, Config
```

**Implementation Steps:**

1. **Create `command/mod.rs`:**
```rust
//! REPL command definitions and execution

mod parser;
mod executor;
mod handlers;

pub use self::executor::CommandResult;

/// REPL command
#[derive(Debug, Clone)]
pub enum Command {
    Query { term: String, distance: Option<usize>, prefix: bool, limit: Option<usize> },
    Insert { terms: Vec<String> },
    // ... other variants
}

impl Command {
    /// Parse command from input string
    pub fn parse(input: &str) -> anyhow::Result<Self> {
        parser::parse(input)
    }

    /// Execute command against REPL state
    pub fn execute(&self, state: &mut super::ReplState) -> anyhow::Result<CommandResult> {
        executor::execute(self, state)
    }
}
```

2. **Create `command/parser.rs`:**
```rust
use super::Command;
use anyhow::Result;

pub fn parse(input: &str) -> Result<Command> {
    let input = input.trim();
    if input.is_empty() {
        return Err(anyhow::anyhow!("Empty command"));
    }

    let parts: Vec<&str> = input.split_whitespace().collect();
    let cmd = parts[0].to_lowercase();

    match cmd.as_str() {
        "query" | "q" => parse_query(&parts[1..]),
        "insert" | "add" => parse_insert(&parts[1..]),
        // ... dispatch to parse_* functions
        _ => Err(anyhow::anyhow!("Unknown command: '{}'", cmd)),
    }
}

fn parse_query(args: &[&str]) -> Result<Command> {
    // Move parse logic here
}

fn parse_insert(args: &[&str]) -> Result<Command> {
    // Move parse logic here
}
// ... other parse_* functions
```

3. **Create `command/executor.rs`:**
```rust
use super::Command;
use crate::repl::ReplState;
use anyhow::Result;

pub enum CommandResult {
    Continue(String),
    Exit,
    Silent,
}

pub fn execute(command: &Command, state: &mut ReplState) -> Result<CommandResult> {
    match command {
        Command::Query { .. } => handlers::query::execute(command, state),
        Command::Insert { .. } => handlers::dictionary::execute_insert(command, state),
        // ... dispatch to handlers
    }
}
```

4. **Create `command/handlers/query.rs`:**
```rust
use crate::repl::command::{Command, CommandResult};
use crate::repl::ReplState;
use anyhow::Result;

pub fn execute(command: &Command, state: &mut ReplState) -> Result<CommandResult> {
    let Command::Query { term, distance, prefix, limit } = command else {
        unreachable!()
    };

    // Move query execution logic here
    let results = state.query(term);
    let output = format_results(&results, state.show_distances);
    Ok(CommandResult::Continue(output))
}

fn format_results(results: &[String], show_distances: bool) -> String {
    // Move formatting logic here
}
```

**Benefits:**
- Each handler is 50-100 lines (easy to understand)
- Independent testing per handler
- Clear separation of parsing vs execution
- Easy to add new commands

---

### 2. Extract Serialization Formats ⭐ HIGH PRIORITY

**Problem:** `src/serialization/mod.rs` (1080 lines) contains all format implementations.

**Solution:**

```
src/serialization/
├── mod.rs                   # Traits, common types, and re-exports
├── formats/
│   ├── mod.rs
│   ├── bincode.rs           # BincodeSerializer
│   ├── json.rs              # JsonSerializer
│   ├── protobuf.rs          # ProtobufSerializer + OptimizedProtobufSerializer
│   └── text.rs              # Plain text format
├── compression/
│   ├── mod.rs
│   └── gzip.rs              # GzipSerializer wrapper
└── proto/
    └── mod.rs               # Generated protobuf code
```

**Implementation:**

1. **Update `mod.rs`:**
```rust
//! Dictionary serialization support

mod formats;
#[cfg(feature = "compression")]
mod compression;

pub use formats::bincode::BincodeSerializer;
pub use formats::json::JsonSerializer;
pub use formats::text::TextSerializer;

#[cfg(feature = "protobuf")]
pub use formats::protobuf::{ProtobufSerializer, OptimizedProtobufSerializer};

#[cfg(feature = "compression")]
pub use compression::gzip::GzipSerializer;

// Traits stay here
pub trait DictionarySerializer {
    fn serialize<D, W>(&self, dictionary: &D, writer: W) -> Result<(), SerializationError>
    where
        D: Dictionary,
        W: Write;

    fn deserialize<D, R>(&self, reader: R) -> Result<D, SerializationError>
    where
        D: DictionaryFromTerms,
        R: Read;
}

pub trait DictionaryFromTerms: Sized {
    fn from_terms<I: IntoIterator<Item = String>>(terms: I) -> Self;
}
```

2. **Create `formats/bincode.rs`:**
```rust
use super::super::{DictionaryFromTerms, DictionarySerializer, SerializationError};
use crate::dictionary::Dictionary;
use std::io::{Read, Write};

pub struct BincodeSerializer;

impl DictionarySerializer for BincodeSerializer {
    fn serialize<D, W>(&self, dictionary: &D, writer: W) -> Result<(), SerializationError>
    where
        D: Dictionary,
        W: Write,
    {
        // Move bincode serialization logic here
    }

    fn deserialize<D, R>(&self, reader: R) -> Result<D, SerializationError>
    where
        D: DictionaryFromTerms,
        R: Read,
    {
        // Move bincode deserialization logic here
    }
}
```

**Benefits:**
- Feature gates are cleaner
- Each format is self-contained
- Easy to add new formats
- Reduces compilation time when features disabled

---

### 3. Implement Query Builder Pattern ⭐ MEDIUM PRIORITY

**Problem:** Current API `transducer.query("test", 2)` is not self-documenting.

**Solution:** Add fluent builder API (already implemented in `builder_api.rs`)

**Integration:**

1. **Add to `transducer/mod.rs`:**
```rust
mod builder_api;
pub use builder_api::QueryBuilder;

impl<D: Dictionary> Transducer<D> {
    /// Create a fluent query builder
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// let results: Vec<_> = transducer
    ///     .query_builder("test")
    ///     .max_distance(2)
    ///     .prefix_mode(true)
    ///     .execute()
    ///     .collect();
    /// ```
    pub fn query_builder(&self, term: impl Into<String>) -> QueryBuilder<D> {
        QueryBuilder::new(&self.dictionary, term, 2, self.algorithm)
    }
}
```

2. **Update prelude:**
```rust
pub mod prelude {
    // ... existing exports
    pub use crate::transducer::QueryBuilder;
}
```

**Benefits:**
- Self-documenting API
- Type-safe configuration
- Backwards compatible (existing `query()` still works)
- Better IDE autocomplete

---

### 4. Add Dedicated Error Types 🔧 MEDIUM PRIORITY

**Problem:** Using `anyhow::Error` everywhere loses type information.

**Solution:**

1. **Add `thiserror` dependency:**
```toml
[dependencies]
thiserror = "1.0"
```

2. **Create `src/error.rs`:**
```rust
//! Error types for liblevenshtein

use std::io;

/// Main library error type
#[derive(Debug, thiserror::Error)]
pub enum Error {
    #[error("Dictionary error: {0}")]
    Dictionary(#[from] DictionaryError),

    #[error("Serialization error: {0}")]
    Serialization(#[from] SerializationError),

    #[error("Query error: {0}")]
    Query(String),

    #[error("Invalid algorithm: {0}")]
    InvalidAlgorithm(String),

    #[error("IO error: {0}")]
    Io(#[from] io::Error),

    #[error("{0}")]
    Other(String),
}

/// Dictionary-specific errors
#[derive(Debug, thiserror::Error)]
pub enum DictionaryError {
    #[error("Term not found: {0}")]
    NotFound(String),

    #[error("Operation {operation} not supported by {backend} backend")]
    UnsupportedOperation {
        backend: String,
        operation: String,
    },

    #[error("Invalid dictionary format: {0}")]
    InvalidFormat(String),

    #[error("Dictionary is read-only")]
    ReadOnly,
}

/// Serialization-specific errors
#[derive(Debug, thiserror::Error)]
pub enum SerializationError {
    #[error("Unsupported format: {0}")]
    UnsupportedFormat(String),

    #[error("Serialization failed: {0}")]
    SerializationFailed(String),

    #[error("Deserialization failed: {0}")]
    DeserializationFailed(String),

    #[error("Compression error: {0}")]
    Compression(String),

    #[error("IO error: {0}")]
    Io(#[from] io::Error),
}

pub type Result<T> = std::result::Result<T, Error>;
```

3. **Update `src/lib.rs`:**
```rust
pub mod error;
pub use error::{Error, Result};
```

4. **Gradually migrate from `anyhow::Error` to `crate::Error`**

**Benefits:**
- Type-safe error handling
- Better error messages
- Easier error recovery
- Self-documenting error cases

---

### 5. Split CLI Commands ⭐ MEDIUM PRIORITY

**Problem:** `src/cli/commands.rs` (1061 lines) contains all command handlers.

**Solution:**

```
src/cli/
├── mod.rs
├── args.rs
├── detect.rs
├── paths.rs
└── commands/
    ├── mod.rs               # Re-exports and dispatch
    ├── query.rs             # Query command
    ├── info.rs              # Info command
    ├── convert.rs           # Convert command
    ├── dictionary.rs        # Insert, Delete, Clear
    ├── minimize.rs          # Minimize command
    └── settings.rs          # Settings, Config commands
```

**Implementation:**

1. **Create `commands/mod.rs`:**
```rust
mod query;
mod info;
mod convert;
mod dictionary;
mod minimize;
mod settings;

use crate::cli::args::Commands;
use anyhow::Result;

pub fn execute(command: &Commands) -> Result<()> {
    match command {
        Commands::Query { .. } => query::execute(command),
        Commands::Info { .. } => info::execute(command),
        Commands::Convert { .. } => convert::execute(command),
        Commands::Insert { .. } => dictionary::execute_insert(command),
        Commands::Delete { .. } => dictionary::execute_delete(command),
        // ... etc
    }
}
```

2. **Create individual handler files following REPL pattern**

---

### 6. Add Dictionary Factory 🔧 LOW PRIORITY

**Problem:** Dictionary creation is scattered across codebase.

**Solution:**

1. **Create `src/dictionary/factory.rs`:**
```rust
//! Dictionary factory for creating dictionary instances

use super::{DawgDictionary, DictionaryBackend, DynamicDawg};
use crate::dictionary::pathmap::PathMapDictionary;
use crate::error::{DictionaryError, Result};
use std::path::Path;

pub struct DictionaryFactory;

impl DictionaryFactory {
    /// Create a new dictionary with the specified backend
    pub fn create<I>(backend: DictionaryBackend, terms: I) -> Result<Box<dyn Dictionary>>
    where
        I: IntoIterator<Item = String>,
    {
        match backend {
            DictionaryBackend::PathMap => {
                Ok(Box::new(PathMapDictionary::from_iter(terms)))
            }
            DictionaryBackend::Dawg => {
                Ok(Box::new(DawgDictionary::from_iter(terms)))
            }
            DictionaryBackend::DynamicDawg => {
                Ok(Box::new(DynamicDawg::from_iter(terms)))
            }
        }
    }

    /// Load a dictionary from a file, auto-detecting format and backend
    pub fn load(
        path: &Path,
        backend: Option<DictionaryBackend>,
        format: Option<SerializationFormat>,
    ) -> Result<Box<dyn Dictionary>> {
        // Auto-detection and loading logic
        let detected = if format.is_none() || backend.is_none() {
            detect_format(path)?
        } else {
            DictFormat {
                backend: backend.unwrap(),
                format: format.unwrap(),
            }
        };

        // Load using appropriate serializer
        // ... implementation
    }

    /// Save a dictionary to a file
    pub fn save(
        dictionary: &dyn Dictionary,
        path: &Path,
        format: SerializationFormat,
    ) -> Result<()> {
        // Save using appropriate serializer
        // ... implementation
    }
}
```

2. **Update dictionary mod.rs:**
```rust
mod factory;
pub use factory::DictionaryFactory;
```

**Benefits:**
- Centralized creation logic
- Consistent error handling
- Easy to add new backends
- Simplifies CLI/REPL code

---

## Migration Guide

### Phase 1: Foundation (Week 1)
1. Add error types (`error.rs`)
2. Add Query Builder (`builder_api.rs` - already done!)
3. Add Dictionary Factory (`dictionary/factory.rs`)

### Phase 2: REPL Split (Week 2)
1. Create `repl/command/` directory structure
2. Move Command enum to `mod.rs`
3. Extract parser to `parser.rs`
4. Extract executor to `executor.rs`
5. Create handler modules
6. Run tests after each step

### Phase 3: Serialization Split (Week 3)
1. Create `serialization/formats/` directory
2. Extract each format to its own file
3. Update feature gates
4. Test each format independently

### Phase 4: CLI Split (Week 4)
1. Create `cli/commands/` directory
2. Extract each command handler
3. Follow REPL pattern
4. Update tests

### Phase 5: Polish (Week 5)
1. Update all documentation
2. Add migration guide for users
3. Update examples to use new APIs
4. Performance testing

## Testing Strategy

- **Unit tests:** Each handler module has its own tests
- **Integration tests:** Test command parsing and execution together
- **Backwards compatibility:** Keep old APIs working with `#[deprecated]`
- **Property tests:** Use `quickcheck` for query invariants

## Performance Considerations

- **No performance regression:** All changes are structural, not algorithmic
- **Compilation time:** Modular structure may improve incremental compilation
- **Binary size:** No change expected (same code, different organization)

## Backwards Compatibility

- Keep existing public APIs with `#[deprecated]` for 1-2 versions
- Provide migration examples
- Use semantic versioning: 0.2.0 → 0.3.0 (minor breaking changes)

## Future Enhancements

### Async Support (v0.4.0)
```rust
pub trait AsyncDictionary {
    async fn query(&self, term: &str, distance: usize)
        -> impl Stream<Item = String>;
}
```

### Metrics/Telemetry (v0.5.0)
```rust
pub trait QueryMetrics {
    fn record_query(
        &self,
        term: &str,
        distance: usize,
        result_count: usize,
        duration: Duration,
    );
}
```

### Plugin System (v0.6.0)
- Custom dictionary backends
- Custom serialization formats
- Custom distance metrics

---

## Summary

This architecture guide provides a clear roadmap for improving the codebase structure while maintaining quality and backwards compatibility. Each improvement is independent and can be implemented incrementally.

**Priority Order:**
1. ⭐ Split REPL commands (immediate maintainability win)
2. ⭐ Extract serialization formats (cleaner feature gates)
3. 🔧 Query Builder (better DX - already implemented!)
4. 🔧 Error types (better error handling)
5. 🔧 Split CLI commands (consistency)
6. 🔧 Dictionary Factory (convenience)

All improvements maintain backwards compatibility and follow Rust best practices.
