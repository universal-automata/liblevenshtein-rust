//! Phonetic rewrite rules for approximate string matching.
//!
//! This module implements verified phonetic transformation rules based on
//! Zompist's English spelling rules, with formal correctness guarantees from
//! Coq/Rocq proofs.
//!
//! # Formal Verification
//!
//! All algorithms in this module are proven correct in Coq/Rocq. The proofs
//! establish five critical properties:
//!
//! 1. **Well-formedness** (Theorem 1, `docs/verification/phonetic/zompist_rules.v:285`)
//!    - All rules satisfy structural constraints
//!    - Pattern and replacement sequences are valid
//!    - Context specifications are well-formed
//!
//! 2. **Bounded Expansion** (Theorem 2, `docs/verification/phonetic/zompist_rules.v:425`)
//!    - String length growth is bounded by a constant factor
//!    - Maximum expansion: `length(output) ≤ length(input) + 20`
//!    - Prevents unbounded memory growth
//!
//! 3. **Non-Confluence** (Theorem 3, `docs/verification/phonetic/zompist_rules.v:491`)
//!    - Rule application order matters
//!    - Different orders can produce different results
//!    - Sequential application is the canonical approach
//!
//! 4. **Termination** (Theorem 4, `docs/verification/phonetic/zompist_rules.v:569`)
//!    - Sequential application always terminates
//!    - No infinite rewrite loops
//!    - Guaranteed to reach a fixed point
//!
//! 5. **Idempotence** (Theorem 5, `docs/verification/phonetic/zompist_rules.v:615`)
//!    - Fixed points remain unchanged
//!    - Applying rules to the output produces the same output
//!    - Stable transformation semantics
//!
//! # Usage
//!
//! ```rust,ignore
//! use liblevenshtein::phonetic::{apply_rules_seq, ORTHOGRAPHY_RULES};
//!
//! let input = "enough";
//! let phonetic = apply_rules_seq(&ORTHOGRAPHY_RULES, input);
//! assert_eq!(phonetic, "enuf");
//! ```
//!
//! # Rule Sets
//!
//! Three rule sets are provided:
//!
//! - [`ORTHOGRAPHY_RULES`] - Simplifies English spelling (e.g., "gh" → "f")
//! - [`PHONETIC_RULES`] - Maps to phonetic representations
//! - [`TEST_RULES`] - Example rules for testing and validation
//!
//! # Implementation Note
//!
//! Following the existing codebase pattern, this module provides both
//! byte-level (`u8`) and character-level (`char`) implementations:
//!
//! - Byte-level types (`Phone`, `Context`, `RewriteRule`) for ASCII text
//! - Character-level types (`PhoneChar`, `ContextChar`, `RewriteRuleChar`) for Unicode
//!
//! Byte-level operations are ~5% faster and use ~4× less memory for edge labels,
//! but character-level operations correctly handle accented characters, CJK, emoji, etc.
//!
//! # See Also
//!
//! - Original specification: <https://zompist.com/spell.html>
//! - Verification proofs: `docs/verification/phonetic/`
//! - Architecture documentation: `docs/verification/ARCHITECTURE.md`

pub mod application;
pub mod matching;
pub mod rules;
pub mod types;

// #[cfg(test)]
// mod tests;

// Re-export main types (byte-level)
pub use application::{apply_rule_at, apply_rules_seq, MAX_EXPANSION_FACTOR};
pub use matching::{context_matches, pattern_matches_at, phone_eq};
pub use rules::{orthography_rules, phonetic_rules, test_rules, zompist_rules};
pub use types::{Context, Phone, RewriteRule};

// Re-export character-level types
pub use application::{apply_rule_at_char, apply_rules_seq_char};
pub use matching::{context_matches_char, pattern_matches_at_char, phone_eq_char};
pub use rules::{
    orthography_rules_char, phonetic_rules_char, test_rules_char, zompist_rules_char,
};
pub use types::{ContextChar, PhoneChar, RewriteRuleChar};
