//! Generalized Levenshtein Automata with Runtime-Configurable Operations
//!
//! This module provides `GeneralizedAutomaton`, a Levenshtein automaton that accepts
//! runtime-configurable operations via `OperationSet`. This enables:
//! - Phonetic corrections (ph↔f, ch↔k, etc.)
//! - Custom edit distance metrics
//! - Weighted operations (future)
//! - Multi-character operations (future)
//!
//! # Design Philosophy
//!
//! `GeneralizedAutomaton` complements `UniversalAutomaton` by trading compile-time
//! specialization for runtime flexibility:
//!
//! - **UniversalAutomaton**: Compile-time operations (Standard, Transposition, MergeAndSplit)
//!   - Zero runtime overhead
//!   - Fixed operation sets
//!   - Perfect for standard Levenshtein variants
//!
//! - **GeneralizedAutomaton**: Runtime operations via `OperationSet`
//!   - Small runtime overhead (+10-20%)
//!   - Custom operation sets
//!   - Perfect for phonetic corrections and custom metrics
//!
//! # Example
//!
//! ```ignore
//! use liblevenshtein::transducer::{GeneralizedAutomaton, OperationSet};
//! use liblevenshtein::transducer::phonetic::phonetic_english_basic;
//!
//! // Standard operations
//! let ops = OperationSet::standard();
//! let automaton = GeneralizedAutomaton::new(2, ops);
//!
//! // Phonetic operations
//! let ops = phonetic_english_basic();
//! let automaton = GeneralizedAutomaton::new(2, ops);
//! ```
//!
//! # Implementation Status
//!
//! **Phase 1 (Current):**
//! - ✅ GeneralizedPosition (no PositionVariant generic)
//! - 🔄 GeneralizedState (in progress)
//! - 🔄 GeneralizedAutomaton (in progress)
//! - ⏳ Basic accepts() functionality
//!
//! **Phase 2 (Future):**
//! - Multi-character operations (⟨m,n,w⟩ where m>1 or n>1)
//! - Weighted operations (fractional costs)
//! - Performance optimizations
//!
//! See: `docs/design/generalized-automaton.md`

pub mod position;
mod automaton;
mod bit_vector;
mod state;
mod subsumption;

pub use automaton::GeneralizedAutomaton;
pub use position::{GeneralizedPosition, PositionError};
pub use state::GeneralizedState;
pub(crate) use bit_vector::CharacteristicVector;
