//! Command handler implementations

pub mod query;

// Note: Modification operations (insert/delete/clear) are backend-specific
// and handled directly by dictionary containers (REPL's DictContainer, etc.)
// They don't fit into a shared handler pattern since the Dictionary trait
// is immutable.

// TODO: Implement I/O handler for serialization/deserialization
