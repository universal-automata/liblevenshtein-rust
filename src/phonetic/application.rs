//! Rule application for phonetic rewrite systems.
//!
//! This module implements the rule application logic for phonetic rewrite rules,
//! directly translated from the Coq/Rocq verification in
//! `docs/verification/phonetic/rewrite_rules.v`.
//!
//! # Functions
//!
//! - [`apply_rule_at`] / [`apply_rule_at_char`] - Apply a rule at a specific position
//! - [`find_first_match`] / [`find_first_match_char`] - Find first matching position
//! - [`apply_rules_seq`] / [`apply_rules_seq_char`] - Sequential rule application
//!
//! # Constants
//!
//! - [`MAX_EXPANSION_FACTOR`] - Maximum string expansion (from Theorem 2)
//!
//! # Formal Guarantees
//!
//! These functions implement algorithms with proven properties:
//!
//! - **Bounded Expansion** (Theorem 2, `zompist_rules.v:425`):
//!   Output length ≤ input length + [`MAX_EXPANSION_FACTOR`]
//!
//! - **Termination** (Theorem 4, `zompist_rules.v:569`):
//!   Sequential application always terminates with sufficient fuel
//!
//! - **Idempotence** (Theorem 5, `zompist_rules.v:615`):
//!   Fixed points remain unchanged under further application

use super::matching::{context_matches, context_matches_char, pattern_matches_at, pattern_matches_at_char};
use super::types::{Phone, PhoneChar, RewriteRule, RewriteRuleChar};

#[cfg(feature = "perf-instrumentation")]
use std::sync::atomic::{AtomicUsize, Ordering};

#[cfg(feature = "perf-instrumentation")]
static BYTES_COPIED: AtomicUsize = AtomicUsize::new(0);

#[cfg(feature = "perf-instrumentation")]
static ALLOCATIONS: AtomicUsize = AtomicUsize::new(0);

#[cfg(feature = "perf-instrumentation")]
pub fn get_perf_stats() -> (usize, usize) {
    (
        BYTES_COPIED.load(Ordering::Relaxed),
        ALLOCATIONS.load(Ordering::Relaxed),
    )
}

#[cfg(feature = "perf-instrumentation")]
pub fn reset_perf_stats() {
    BYTES_COPIED.store(0, Ordering::Relaxed);
    ALLOCATIONS.store(0, Ordering::Relaxed);
}

/// Maximum expansion factor for phonetic rewrite rules.
///
/// **Formal Specification**: Theorem 2, `docs/verification/phonetic/zompist_rules.v:425`
///
/// This constant bounds the maximum string growth from any single rule application.
/// For all well-formed rules in the zompist rule set:
///
/// ```text
/// length(output) ≤ length(input) + MAX_EXPANSION_FACTOR
/// ```
///
/// The value 20 is proven sufficient for all 56 zompist rules.
pub const MAX_EXPANSION_FACTOR: usize = 20;

// ============================================================================
// Position-dependent context checks (for position skipping optimization)
// ============================================================================

/// Check if any rules have position-dependent contexts (byte-level).
///
/// **Formal Specification**: `docs/verification/phonetic/position_skipping_proof.v:3453`
///
/// Returns `true` if position skipping is UNSAFE (any rule uses `Context::Final`).
/// Returns `false` if position skipping is SAFE.
///
/// # Position Skipping Safety
///
/// Position skipping optimization starts the next rule search from the last match
/// position instead of position 0. This is SAFE when no rules use `Context::Final`
/// because:
///
/// - All other contexts (Initial, BeforeVowel, AfterConsonant, etc.) depend only
///   on local structure, not on the overall string length
/// - `Final` depends on `pos == s.len()`, which changes when the string is shortened
///
/// # Example
///
/// ```rust,ignore
/// use liblevenshtein::phonetic::{has_position_dependent_rules, orthography_rules, phonetic_rules};
///
/// // orthography_rules contains rule_silent_e_final with Context::Final
/// assert!(has_position_dependent_rules(&orthography_rules()));
///
/// // phonetic_rules has no Final context - safe for optimization
/// assert!(!has_position_dependent_rules(&phonetic_rules()));
/// ```
#[inline]
pub fn has_position_dependent_rules(rules: &[RewriteRule]) -> bool {
    rules.iter().any(|r| r.context.is_position_dependent())
}

/// Check if any rules have position-dependent contexts (character-level).
///
/// **Formal Specification**: `docs/verification/phonetic/position_skipping_proof.v:3453`
///
/// Character-level variant of [`has_position_dependent_rules`].
#[inline]
pub fn has_position_dependent_rules_char(rules: &[RewriteRuleChar]) -> bool {
    rules.iter().any(|r| r.context.is_position_dependent())
}

// ============================================================================
// Rule application (byte-level)
// ============================================================================

/// Check if a rewrite rule can be applied at a specific position (byte-level).
///
/// **Performance Optimization**: This function checks rule applicability without
/// allocating a result vector, making it much faster for position scanning.
///
/// # Arguments
///
/// - `rule` - The rewrite rule to check
/// - `s` - The phonetic string
/// - `pos` - The position to check
///
/// # Returns
///
/// - `true` if the rule can be applied at the position
/// - `false` otherwise
#[inline]
pub fn can_apply_at(rule: &RewriteRule, s: &[Phone], pos: usize) -> bool {
    // Check context matches
    if !context_matches(&rule.context, s, pos) {
        return false;
    }

    // Check pattern matches
    if !pattern_matches_at(&rule.pattern, s, pos) {
        return false;
    }

    true
}

/// Apply a rewrite rule at a specific position if possible (byte-level).
///
/// **Formal Specification**: `docs/verification/phonetic/rewrite_rules.v:177-187`
///
/// Attempts to apply a rule at the given position in the phonetic string.
/// Returns `Some(new_string)` if the rule applies, `None` otherwise.
///
/// # Algorithm
///
/// 1. Check if the context is satisfied at the position
/// 2. Check if the pattern matches at the position
/// 3. If both conditions hold, replace the pattern with the replacement
///
/// # Arguments
///
/// - `rule` - The rewrite rule to apply
/// - `s` - The phonetic string
/// - `pos` - The position to attempt application
///
/// # Returns
///
/// - `Some(new_string)` if the rule applies at the position
/// - `None` if the rule does not apply
///
/// # Examples
///
/// ```rust,ignore
/// use liblevenshtein::phonetic::{apply_rule_at, Phone, Context, RewriteRule};
///
/// let rule = RewriteRule {
///     rule_id: 1,
///     rule_name: "gh → f".to_string(),
///     pattern: vec![Phone::Consonant(b'g'), Phone::Consonant(b'h')],
///     replacement: vec![Phone::Consonant(b'f')],
///     context: Context::Anywhere,
///     weight: 0.15,
/// };
///
/// let s = vec![
///     Phone::Vowel(b'e'),
///     Phone::Consonant(b'g'),
///     Phone::Consonant(b'h'),
/// ];
///
/// let result = apply_rule_at(&rule, &s, 1);
/// assert_eq!(result, Some(vec![Phone::Vowel(b'e'), Phone::Consonant(b'f')]));
/// ```
pub fn apply_rule_at(rule: &RewriteRule, s: &[Phone], pos: usize) -> Option<Vec<Phone>> {
    // Check if rule can be applied (no allocation)
    if !can_apply_at(rule, s, pos) {
        return None;
    }

    // Build result: prefix + replacement + suffix
    let mut result = Vec::with_capacity(s.len() + MAX_EXPANSION_FACTOR);

    #[cfg(feature = "perf-instrumentation")]
    {
        ALLOCATIONS.fetch_add(1, Ordering::Relaxed);
        // Count bytes copied: prefix + replacement + suffix
        let bytes_copied = pos + rule.replacement.len() + (s.len() - pos - rule.pattern.len());
        BYTES_COPIED.fetch_add(bytes_copied, Ordering::Relaxed);
    }

    result.extend_from_slice(&s[..pos]);
    result.extend_from_slice(&rule.replacement);
    result.extend_from_slice(&s[(pos + rule.pattern.len())..]);

    Some(result)
}

/// Find the first position where a rule can be applied (byte-level).
///
/// **Formal Specification**: `docs/verification/phonetic/rewrite_rules.v:190-198`
///
/// Scans the string from left to right to find the first position where
/// the rule can be applied.
///
/// # Arguments
///
/// - `rule` - The rewrite rule to match
/// - `s` - The phonetic string
///
/// # Returns
///
/// - `Some(pos)` if the rule can be applied at position `pos`
/// - `None` if the rule cannot be applied anywhere
pub fn find_first_match(rule: &RewriteRule, s: &[Phone]) -> Option<usize> {
    find_first_match_from(rule, s, 0)
}

/// Find the first position where a rule can be applied, starting from a given position.
///
/// This is an optimization helper for sequential rule application.
///
/// # Arguments
///
/// - `rule` - The rewrite rule to match
/// - `s` - The phonetic string
/// - `start_pos` - The position to start scanning from (0-based)
///
/// # Returns
///
/// - `Some(pos)` if the rule can be applied at position `pos >= start_pos`
/// - `None` if the rule cannot be applied anywhere from `start_pos` onward
#[inline]
pub fn find_first_match_from(rule: &RewriteRule, s: &[Phone], start_pos: usize) -> Option<usize> {
    // Try each position from start_pos to s.len()
    // Optimization: use can_apply_at() to avoid allocating vectors during search
    for pos in start_pos..=s.len() {
        if can_apply_at(rule, s, pos) {
            return Some(pos);
        }
    }
    None
}

/// Apply a list of rules sequentially until fixed point or fuel exhausted (byte-level).
///
/// **Formal Specification**: `docs/verification/phonetic/rewrite_rules.v:203-227`
///
/// Applies rules in order, restarting from the first rule after each successful
/// application, until no rules can be applied or fuel is exhausted.
///
/// # Formal Guarantees
///
/// - **Termination** (Theorem 4, `zompist_rules.v:569`):
///   Always terminates with sufficient fuel
///
/// - **Idempotence** (Theorem 5, `zompist_rules.v:615`):
///   Result is a fixed point (applying rules again produces the same result)
///
/// # Algorithm
///
/// ```text
/// loop:
///   for each rule r in rules:
///     if r can be applied:
///       apply r
///       restart loop
///   no rules applied → return fixed point
/// ```
///
/// # Arguments
///
/// - `rules` - The list of rewrite rules to apply
/// - `s` - The phonetic string
/// - `fuel` - Maximum number of iterations (prevents infinite loops)
///
/// # Returns
///
/// - `Some(result)` with the transformed string
/// - `None` if fuel is exhausted (shouldn't happen with sufficient fuel)
///
/// # Fuel Calculation
///
/// Sufficient fuel is:
/// ```text
/// fuel >= length(s) * length(rules) * MAX_EXPANSION_FACTOR
/// ```
///
/// For practical use, `fuel = s.len() * rules.len() * 100` is recommended.
pub fn apply_rules_seq(rules: &[RewriteRule], s: &[Phone], fuel: usize) -> Option<Vec<Phone>> {
    let mut current = s.to_vec();

    #[cfg(feature = "perf-instrumentation")]
    {
        ALLOCATIONS.fetch_add(1, Ordering::Relaxed);
        BYTES_COPIED.fetch_add(s.len(), Ordering::Relaxed);
    }

    let mut remaining_fuel = fuel;

    loop {
        if remaining_fuel == 0 {
            // Out of fuel - return current state
            return Some(current);
        }

        let mut applied = false;

        // Try each rule in order
        for rule in rules {
            if let Some(pos) = find_first_match(rule, &current) {
                if let Some(new_s) = apply_rule_at(rule, &current, pos) {
                    current = new_s;
                    remaining_fuel -= 1;
                    applied = true;
                    break; // Restart from first rule
                }
            }
        }

        if !applied {
            // Fixed point reached - no rules can be applied
            return Some(current);
        }
    }
}

// ============================================================================
// Optimized rule application with conditional position skipping (byte-level)
// ============================================================================

/// Apply rules with position skipping optimization (byte-level).
///
/// **Formal Specification**: `docs/verification/phonetic/position_skipping_proof.v`
///
/// This function automatically determines whether position skipping is safe
/// based on whether any rules use `Context::Final`. If safe, it enables the
/// optimization; otherwise, it falls back to standard sequential application.
///
/// # Position Skipping Optimization
///
/// After applying a rule at position `last_pos`, the next search starts from
/// `last_pos` instead of 0. This is SAFE when no rules use `Context::Final`
/// because all other contexts depend only on local structure, not string length.
///
/// # When Optimization is Disabled
///
/// The optimization is disabled when any rule uses `Context::Final`, because:
/// - `Final` matches when `pos == s.len()` (depends on string length)
/// - When strings are shortened, positions that were non-final become final
/// - Counter-example: `[a,b,c]` → `[a,b]` causes position 2 to become final
///
/// # Arguments
///
/// - `rules` - The list of rewrite rules to apply
/// - `s` - The phonetic string
/// - `fuel` - Maximum number of iterations
///
/// # Returns
///
/// - `Some(result)` with the transformed string
/// - `None` if fuel is exhausted
pub fn apply_rules_seq_opt(rules: &[RewriteRule], s: &[Phone], fuel: usize) -> Option<Vec<Phone>> {
    if has_position_dependent_rules(rules) {
        // Fall back to standard sequential application (safe but slower)
        apply_rules_seq(rules, s, fuel)
    } else {
        // Use position skipping optimization (proven safe for this rule set)
        apply_rules_seq_optimized(rules, s, fuel)
    }
}

/// Apply rules with position skipping optimization enabled (byte-level).
///
/// **Formal Specification**: `docs/verification/phonetic/position_skipping_proof.v`
///
/// **SAFETY**: This function MUST only be called when no rules use `Context::Final`.
/// Use [`apply_rules_seq_opt`] for automatic safety checking, or verify with
/// [`has_position_dependent_rules`] before calling this function directly.
///
/// # Algorithm
///
/// ```text
/// last_pos = 0
/// loop:
///   for each rule r in rules:
///     if r can be applied at pos >= last_pos:
///       apply r at pos
///       last_pos = pos  // Key optimization: skip positions [0, last_pos)
///       restart loop
///   no rules applied → return fixed point
/// ```
///
/// # Performance
///
/// Position skipping reduces redundant position checks. When rules repeatedly
/// apply near the same position, this can significantly reduce iterations.
///
/// # Arguments
///
/// - `rules` - The list of rewrite rules (MUST NOT contain `Context::Final`)
/// - `s` - The phonetic string
/// - `fuel` - Maximum number of iterations
///
/// # Returns
///
/// - `Some(result)` with the transformed string
/// - `None` if fuel is exhausted
pub fn apply_rules_seq_optimized(
    rules: &[RewriteRule],
    s: &[Phone],
    fuel: usize,
) -> Option<Vec<Phone>> {
    debug_assert!(
        !has_position_dependent_rules(rules),
        "apply_rules_seq_optimized requires no position-dependent rules (Context::Final)"
    );

    let mut current = s.to_vec();

    #[cfg(feature = "perf-instrumentation")]
    {
        ALLOCATIONS.fetch_add(1, Ordering::Relaxed);
        BYTES_COPIED.fetch_add(s.len(), Ordering::Relaxed);
    }

    let mut remaining_fuel = fuel;
    let mut last_pos: usize = 0; // Position skipping: start from here

    loop {
        if remaining_fuel == 0 {
            // Out of fuel - return current state
            return Some(current);
        }

        let mut applied = false;

        // Try each rule in order, starting from last_pos
        for rule in rules {
            // Key optimization: search from last_pos instead of 0
            if let Some(pos) = find_first_match_from(rule, &current, last_pos) {
                if let Some(new_s) = apply_rule_at(rule, &current, pos) {
                    current = new_s;
                    remaining_fuel -= 1;
                    last_pos = pos; // Next iteration starts from here
                    applied = true;
                    break; // Restart from first rule
                }
            }
        }

        if !applied {
            // Fixed point reached - no rules can be applied
            return Some(current);
        }
    }
}

// ============================================================================
// Rule application (character-level)
// ============================================================================

/// Check if a rewrite rule can be applied at a specific position (character-level).
///
/// **Performance Optimization**: This function checks rule applicability without
/// allocating a result vector, making it much faster for position scanning.
///
/// # Arguments
///
/// - `rule` - The rewrite rule to check
/// - `s` - The phonetic string
/// - `pos` - The position to check
///
/// # Returns
///
/// - `true` if the rule can be applied at the position
/// - `false` otherwise
#[inline]
pub fn can_apply_at_char(rule: &RewriteRuleChar, s: &[PhoneChar], pos: usize) -> bool {
    // Check context matches
    if !context_matches_char(&rule.context, s, pos) {
        return false;
    }

    // Check pattern matches
    if !pattern_matches_at_char(&rule.pattern, s, pos) {
        return false;
    }

    true
}

/// Apply a rewrite rule at a specific position if possible (character-level).
///
/// **Formal Specification**: `docs/verification/phonetic/rewrite_rules.v:177-187`
///
/// This is the character-level variant of [`apply_rule_at`].
pub fn apply_rule_at_char(
    rule: &RewriteRuleChar,
    s: &[PhoneChar],
    pos: usize,
) -> Option<Vec<PhoneChar>> {
    // Check if rule can be applied (no allocation)
    if !can_apply_at_char(rule, s, pos) {
        return None;
    }

    // Build result: prefix + replacement + suffix
    let mut result = Vec::with_capacity(s.len() + MAX_EXPANSION_FACTOR);
    result.extend_from_slice(&s[..pos]);
    result.extend_from_slice(&rule.replacement);
    result.extend_from_slice(&s[(pos + rule.pattern.len())..]);

    Some(result)
}

/// Find the first position where a rule can be applied (character-level).
///
/// **Formal Specification**: `docs/verification/phonetic/rewrite_rules.v:190-198`
///
/// This is the character-level variant of [`find_first_match`].
pub fn find_first_match_char(rule: &RewriteRuleChar, s: &[PhoneChar]) -> Option<usize> {
    find_first_match_from_char(rule, s, 0)
}

/// Find the first position where a rule can be applied, starting from a given position (character-level).
///
/// This is the character-level variant of [`find_first_match_from`].
///
/// # Arguments
///
/// - `rule` - The rewrite rule to match
/// - `s` - The phonetic string
/// - `start_pos` - The position to start scanning from (0-based)
///
/// # Returns
///
/// - `Some(pos)` if the rule can be applied at position `pos >= start_pos`
/// - `None` if the rule cannot be applied anywhere from `start_pos` onward
#[inline]
pub fn find_first_match_from_char(
    rule: &RewriteRuleChar,
    s: &[PhoneChar],
    start_pos: usize,
) -> Option<usize> {
    // Optimization: use can_apply_at_char() to avoid allocating vectors during search
    for pos in start_pos..=s.len() {
        if can_apply_at_char(rule, s, pos) {
            return Some(pos);
        }
    }
    None
}

/// Apply a list of rules sequentially until fixed point or fuel exhausted (character-level).
///
/// **Formal Specification**: `docs/verification/phonetic/rewrite_rules.v:203-227`
///
/// This is the character-level variant of [`apply_rules_seq`].
pub fn apply_rules_seq_char(
    rules: &[RewriteRuleChar],
    s: &[PhoneChar],
    fuel: usize,
) -> Option<Vec<PhoneChar>> {
    let mut current = s.to_vec();
    let mut remaining_fuel = fuel;

    loop {
        if remaining_fuel == 0 {
            return Some(current);
        }

        let mut applied = false;

        for rule in rules {
            if let Some(pos) = find_first_match_char(rule, &current) {
                if let Some(new_s) = apply_rule_at_char(rule, &current, pos) {
                    current = new_s;
                    remaining_fuel -= 1;
                    applied = true;
                    break;
                }
            }
        }

        if !applied {
            return Some(current);
        }
    }
}

// ============================================================================
// Optimized rule application with conditional position skipping (character-level)
// ============================================================================

/// Apply rules with position skipping optimization (character-level).
///
/// **Formal Specification**: `docs/verification/phonetic/position_skipping_proof.v`
///
/// This is the character-level variant of [`apply_rules_seq_opt`].
/// See that function for detailed documentation on the position skipping optimization.
pub fn apply_rules_seq_opt_char(
    rules: &[RewriteRuleChar],
    s: &[PhoneChar],
    fuel: usize,
) -> Option<Vec<PhoneChar>> {
    if has_position_dependent_rules_char(rules) {
        // Fall back to standard sequential application (safe but slower)
        apply_rules_seq_char(rules, s, fuel)
    } else {
        // Use position skipping optimization (proven safe for this rule set)
        apply_rules_seq_optimized_char(rules, s, fuel)
    }
}

/// Apply rules with position skipping optimization enabled (character-level).
///
/// **Formal Specification**: `docs/verification/phonetic/position_skipping_proof.v`
///
/// This is the character-level variant of [`apply_rules_seq_optimized`].
/// See that function for detailed documentation.
///
/// **SAFETY**: This function MUST only be called when no rules use `ContextChar::Final`.
pub fn apply_rules_seq_optimized_char(
    rules: &[RewriteRuleChar],
    s: &[PhoneChar],
    fuel: usize,
) -> Option<Vec<PhoneChar>> {
    debug_assert!(
        !has_position_dependent_rules_char(rules),
        "apply_rules_seq_optimized_char requires no position-dependent rules (ContextChar::Final)"
    );

    let mut current = s.to_vec();
    let mut remaining_fuel = fuel;
    let mut last_pos: usize = 0; // Position skipping: start from here

    loop {
        if remaining_fuel == 0 {
            // Out of fuel - return current state
            return Some(current);
        }

        let mut applied = false;

        // Try each rule in order, starting from last_pos
        for rule in rules {
            // Key optimization: search from last_pos instead of 0
            if let Some(pos) = find_first_match_from_char(rule, &current, last_pos) {
                if let Some(new_s) = apply_rule_at_char(rule, &current, pos) {
                    current = new_s;
                    remaining_fuel -= 1;
                    last_pos = pos; // Next iteration starts from here
                    applied = true;
                    break; // Restart from first rule
                }
            }
        }

        if !applied {
            // Fixed point reached - no rules can be applied
            return Some(current);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::phonetic::types::{Context, ContextChar, Phone, PhoneChar};

    // ========================================================================
    // Byte-level tests
    // ========================================================================

    #[test]
    fn test_apply_rule_at_success() {
        let rule = RewriteRule {
            rule_id: 1,
            rule_name: "gh → f".to_string(),
            pattern: vec![Phone::Consonant(b'g'), Phone::Consonant(b'h')],
            replacement: vec![Phone::Consonant(b'f')],
            context: Context::Anywhere,
            weight: 0.15,
        };

        let s = vec![
            Phone::Vowel(b'e'),
            Phone::Consonant(b'g'),
            Phone::Consonant(b'h'),
        ];

        let result = apply_rule_at(&rule, &s, 1);
        assert_eq!(result, Some(vec![Phone::Vowel(b'e'), Phone::Consonant(b'f')]));
    }

    #[test]
    fn test_apply_rule_at_no_match() {
        let rule = RewriteRule {
            rule_id: 1,
            rule_name: "gh → f".to_string(),
            pattern: vec![Phone::Consonant(b'g'), Phone::Consonant(b'h')],
            replacement: vec![Phone::Consonant(b'f')],
            context: Context::Anywhere,
            weight: 0.15,
        };

        let s = vec![Phone::Vowel(b'e'), Phone::Consonant(b'k')];

        let result = apply_rule_at(&rule, &s, 0);
        assert_eq!(result, None);
    }

    #[test]
    fn test_apply_rule_at_context_fail() {
        let rule = RewriteRule {
            rule_id: 1,
            rule_name: "gh → f (initial only)".to_string(),
            pattern: vec![Phone::Consonant(b'g'), Phone::Consonant(b'h')],
            replacement: vec![Phone::Consonant(b'f')],
            context: Context::Initial,
            weight: 0.15,
        };

        let s = vec![
            Phone::Vowel(b'e'),
            Phone::Consonant(b'g'),
            Phone::Consonant(b'h'),
        ];

        // Should fail at pos=1 because not initial
        let result = apply_rule_at(&rule, &s, 1);
        assert_eq!(result, None);

        // Should succeed at pos=0 if pattern were there
        let s2 = vec![Phone::Consonant(b'g'), Phone::Consonant(b'h')];
        let result2 = apply_rule_at(&rule, &s2, 0);
        assert_eq!(result2, Some(vec![Phone::Consonant(b'f')]));
    }

    #[test]
    fn test_find_first_match() {
        let rule = RewriteRule {
            rule_id: 1,
            rule_name: "gh → f".to_string(),
            pattern: vec![Phone::Consonant(b'g'), Phone::Consonant(b'h')],
            replacement: vec![Phone::Consonant(b'f')],
            context: Context::Anywhere,
            weight: 0.15,
        };

        let s = vec![
            Phone::Vowel(b'e'),
            Phone::Consonant(b'g'),
            Phone::Consonant(b'h'),
            Phone::Vowel(b'o'),
        ];

        let pos = find_first_match(&rule, &s);
        assert_eq!(pos, Some(1));
    }

    #[test]
    fn test_find_first_match_none() {
        let rule = RewriteRule {
            rule_id: 1,
            rule_name: "gh → f".to_string(),
            pattern: vec![Phone::Consonant(b'g'), Phone::Consonant(b'h')],
            replacement: vec![Phone::Consonant(b'f')],
            context: Context::Anywhere,
            weight: 0.15,
        };

        let s = vec![Phone::Vowel(b'e'), Phone::Consonant(b'k')];

        let pos = find_first_match(&rule, &s);
        assert_eq!(pos, None);
    }

    #[test]
    fn test_apply_rules_seq_single_rule() {
        let rule = RewriteRule {
            rule_id: 1,
            rule_name: "gh → f".to_string(),
            pattern: vec![Phone::Consonant(b'g'), Phone::Consonant(b'h')],
            replacement: vec![Phone::Consonant(b'f')],
            context: Context::Anywhere,
            weight: 0.15,
        };

        let s = vec![
            Phone::Vowel(b'e'),
            Phone::Consonant(b'g'),
            Phone::Consonant(b'h'),
        ];

        let result = apply_rules_seq(&[rule], &s, 100);
        assert_eq!(result, Some(vec![Phone::Vowel(b'e'), Phone::Consonant(b'f')]));
    }

    #[test]
    fn test_apply_rules_seq_multiple_applications() {
        let rule = RewriteRule {
            rule_id: 1,
            rule_name: "gh → f".to_string(),
            pattern: vec![Phone::Consonant(b'g'), Phone::Consonant(b'h')],
            replacement: vec![Phone::Consonant(b'f')],
            context: Context::Anywhere,
            weight: 0.15,
        };

        // "ghgh" → "fgh" → "ff"
        let s = vec![
            Phone::Consonant(b'g'),
            Phone::Consonant(b'h'),
            Phone::Consonant(b'g'),
            Phone::Consonant(b'h'),
        ];

        let result = apply_rules_seq(&[rule], &s, 100);
        assert_eq!(
            result,
            Some(vec![Phone::Consonant(b'f'), Phone::Consonant(b'f')])
        );
    }

    #[test]
    fn test_apply_rules_seq_fixed_point() {
        let rule = RewriteRule {
            rule_id: 1,
            rule_name: "gh → f".to_string(),
            pattern: vec![Phone::Consonant(b'g'), Phone::Consonant(b'h')],
            replacement: vec![Phone::Consonant(b'f')],
            context: Context::Anywhere,
            weight: 0.15,
        };

        // Already a fixed point (no 'gh')
        let s = vec![Phone::Vowel(b'e'), Phone::Consonant(b'f')];

        let result = apply_rules_seq(&[rule], &s, 100);
        assert_eq!(result, Some(vec![Phone::Vowel(b'e'), Phone::Consonant(b'f')]));
    }

    // ========================================================================
    // Character-level tests
    // ========================================================================

    #[test]
    fn test_apply_rule_at_char_success() {
        let rule = RewriteRuleChar {
            rule_id: 1,
            rule_name: "gh → f".to_string(),
            pattern: vec![PhoneChar::Consonant('g'), PhoneChar::Consonant('h')],
            replacement: vec![PhoneChar::Consonant('f')],
            context: ContextChar::Anywhere,
            weight: 0.15,
        };

        let s = vec![
            PhoneChar::Vowel('e'),
            PhoneChar::Consonant('g'),
            PhoneChar::Consonant('h'),
        ];

        let result = apply_rule_at_char(&rule, &s, 1);
        assert_eq!(
            result,
            Some(vec![PhoneChar::Vowel('e'), PhoneChar::Consonant('f')])
        );
    }

    #[test]
    fn test_apply_rules_seq_char() {
        let rule = RewriteRuleChar {
            rule_id: 1,
            rule_name: "gh → f".to_string(),
            pattern: vec![PhoneChar::Consonant('g'), PhoneChar::Consonant('h')],
            replacement: vec![PhoneChar::Consonant('f')],
            context: ContextChar::Anywhere,
            weight: 0.15,
        };

        let s = vec![
            PhoneChar::Vowel('e'),
            PhoneChar::Consonant('g'),
            PhoneChar::Consonant('h'),
        ];

        let result = apply_rules_seq_char(&[rule], &s, 100);
        assert_eq!(
            result,
            Some(vec![PhoneChar::Vowel('e'), PhoneChar::Consonant('f')])
        );
    }

    // ========================================================================
    // Position skipping optimization tests (byte-level)
    // ========================================================================

    #[test]
    fn test_has_position_dependent_rules_empty() {
        let rules: Vec<RewriteRule> = vec![];
        assert!(!has_position_dependent_rules(&rules));
    }

    #[test]
    fn test_has_position_dependent_rules_no_final() {
        let rules = vec![
            RewriteRule {
                rule_id: 1,
                rule_name: "test".to_string(),
                pattern: vec![Phone::Consonant(b'g')],
                replacement: vec![Phone::Consonant(b'k')],
                context: Context::Anywhere,
                weight: 1.0,
            },
            RewriteRule {
                rule_id: 2,
                rule_name: "test2".to_string(),
                pattern: vec![Phone::Consonant(b'c')],
                replacement: vec![Phone::Consonant(b's')],
                context: Context::Initial,
                weight: 1.0,
            },
        ];
        assert!(!has_position_dependent_rules(&rules));
    }

    #[test]
    fn test_has_position_dependent_rules_with_final() {
        let rules = vec![
            RewriteRule {
                rule_id: 1,
                rule_name: "test".to_string(),
                pattern: vec![Phone::Consonant(b'g')],
                replacement: vec![Phone::Consonant(b'k')],
                context: Context::Anywhere,
                weight: 1.0,
            },
            RewriteRule {
                rule_id: 2,
                rule_name: "final_rule".to_string(),
                pattern: vec![Phone::Vowel(b'e')],
                replacement: vec![],
                context: Context::Final,
                weight: 1.0,
            },
        ];
        assert!(has_position_dependent_rules(&rules));
    }

    #[test]
    fn test_find_first_match_from_start() {
        let rule = RewriteRule {
            rule_id: 1,
            rule_name: "gh → f".to_string(),
            pattern: vec![Phone::Consonant(b'g'), Phone::Consonant(b'h')],
            replacement: vec![Phone::Consonant(b'f')],
            context: Context::Anywhere,
            weight: 0.15,
        };

        let s = vec![
            Phone::Vowel(b'e'),
            Phone::Consonant(b'g'),
            Phone::Consonant(b'h'),
            Phone::Vowel(b'o'),
        ];

        // Search from start
        assert_eq!(find_first_match_from(&rule, &s, 0), Some(1));
        // Search from position 1 (should still find it)
        assert_eq!(find_first_match_from(&rule, &s, 1), Some(1));
        // Search from position 2 (should not find it)
        assert_eq!(find_first_match_from(&rule, &s, 2), None);
    }

    #[test]
    fn test_find_first_match_from_multiple_occurrences() {
        let rule = RewriteRule {
            rule_id: 1,
            rule_name: "gh → f".to_string(),
            pattern: vec![Phone::Consonant(b'g'), Phone::Consonant(b'h')],
            replacement: vec![Phone::Consonant(b'f')],
            context: Context::Anywhere,
            weight: 0.15,
        };

        // "e gh o gh a"
        let s = vec![
            Phone::Vowel(b'e'),
            Phone::Consonant(b'g'),
            Phone::Consonant(b'h'),
            Phone::Vowel(b'o'),
            Phone::Consonant(b'g'),
            Phone::Consonant(b'h'),
            Phone::Vowel(b'a'),
        ];

        // Search from start finds first occurrence
        assert_eq!(find_first_match_from(&rule, &s, 0), Some(1));
        // Search from position 2 finds second occurrence
        assert_eq!(find_first_match_from(&rule, &s, 2), Some(4));
        // Search from position 5 finds nothing
        assert_eq!(find_first_match_from(&rule, &s, 5), None);
    }

    #[test]
    fn test_apply_rules_seq_opt_safe_rules() {
        // Test with safe rules (no Final context) - should use optimized path
        let rule = RewriteRule {
            rule_id: 1,
            rule_name: "gh → f".to_string(),
            pattern: vec![Phone::Consonant(b'g'), Phone::Consonant(b'h')],
            replacement: vec![Phone::Consonant(b'f')],
            context: Context::Anywhere,
            weight: 0.15,
        };

        let s = vec![
            Phone::Consonant(b'g'),
            Phone::Consonant(b'h'),
            Phone::Consonant(b'g'),
            Phone::Consonant(b'h'),
        ];

        let result = apply_rules_seq_opt(&[rule], &s, 100);
        assert_eq!(
            result,
            Some(vec![Phone::Consonant(b'f'), Phone::Consonant(b'f')])
        );
    }

    #[test]
    fn test_apply_rules_seq_optimized_produces_same_result() {
        // Verify optimized version produces same result as non-optimized
        let rule = RewriteRule {
            rule_id: 1,
            rule_name: "gh → f".to_string(),
            pattern: vec![Phone::Consonant(b'g'), Phone::Consonant(b'h')],
            replacement: vec![Phone::Consonant(b'f')],
            context: Context::Anywhere,
            weight: 0.15,
        };

        let s = vec![
            Phone::Vowel(b'e'),
            Phone::Consonant(b'g'),
            Phone::Consonant(b'h'),
            Phone::Vowel(b'o'),
            Phone::Consonant(b'g'),
            Phone::Consonant(b'h'),
        ];

        let standard_result = apply_rules_seq(&[rule.clone()], &s, 100);
        let optimized_result = apply_rules_seq_optimized(&[rule], &s, 100);

        assert_eq!(standard_result, optimized_result);
    }

    #[test]
    fn test_apply_rules_seq_optimized_fixed_point() {
        let rule = RewriteRule {
            rule_id: 1,
            rule_name: "gh → f".to_string(),
            pattern: vec![Phone::Consonant(b'g'), Phone::Consonant(b'h')],
            replacement: vec![Phone::Consonant(b'f')],
            context: Context::Anywhere,
            weight: 0.15,
        };

        // Already at fixed point
        let s = vec![Phone::Vowel(b'e'), Phone::Consonant(b'f')];

        let result = apply_rules_seq_optimized(&[rule], &s, 100);
        assert_eq!(result, Some(vec![Phone::Vowel(b'e'), Phone::Consonant(b'f')]));
    }

    // ========================================================================
    // Position skipping optimization tests (character-level)
    // ========================================================================

    #[test]
    fn test_has_position_dependent_rules_char_empty() {
        let rules: Vec<RewriteRuleChar> = vec![];
        assert!(!has_position_dependent_rules_char(&rules));
    }

    #[test]
    fn test_has_position_dependent_rules_char_no_final() {
        let rules = vec![RewriteRuleChar {
            rule_id: 1,
            rule_name: "test".to_string(),
            pattern: vec![PhoneChar::Consonant('g')],
            replacement: vec![PhoneChar::Consonant('k')],
            context: ContextChar::Anywhere,
            weight: 1.0,
        }];
        assert!(!has_position_dependent_rules_char(&rules));
    }

    #[test]
    fn test_has_position_dependent_rules_char_with_final() {
        let rules = vec![RewriteRuleChar {
            rule_id: 1,
            rule_name: "final_rule".to_string(),
            pattern: vec![PhoneChar::Vowel('e')],
            replacement: vec![],
            context: ContextChar::Final,
            weight: 1.0,
        }];
        assert!(has_position_dependent_rules_char(&rules));
    }

    #[test]
    fn test_find_first_match_from_char() {
        let rule = RewriteRuleChar {
            rule_id: 1,
            rule_name: "gh → f".to_string(),
            pattern: vec![PhoneChar::Consonant('g'), PhoneChar::Consonant('h')],
            replacement: vec![PhoneChar::Consonant('f')],
            context: ContextChar::Anywhere,
            weight: 0.15,
        };

        let s = vec![
            PhoneChar::Vowel('e'),
            PhoneChar::Consonant('g'),
            PhoneChar::Consonant('h'),
            PhoneChar::Vowel('o'),
        ];

        assert_eq!(find_first_match_from_char(&rule, &s, 0), Some(1));
        assert_eq!(find_first_match_from_char(&rule, &s, 1), Some(1));
        assert_eq!(find_first_match_from_char(&rule, &s, 2), None);
    }

    #[test]
    fn test_apply_rules_seq_opt_char_safe_rules() {
        let rule = RewriteRuleChar {
            rule_id: 1,
            rule_name: "gh → f".to_string(),
            pattern: vec![PhoneChar::Consonant('g'), PhoneChar::Consonant('h')],
            replacement: vec![PhoneChar::Consonant('f')],
            context: ContextChar::Anywhere,
            weight: 0.15,
        };

        let s = vec![
            PhoneChar::Consonant('g'),
            PhoneChar::Consonant('h'),
            PhoneChar::Consonant('g'),
            PhoneChar::Consonant('h'),
        ];

        let result = apply_rules_seq_opt_char(&[rule], &s, 100);
        assert_eq!(
            result,
            Some(vec![PhoneChar::Consonant('f'), PhoneChar::Consonant('f')])
        );
    }

    #[test]
    fn test_apply_rules_seq_optimized_char_produces_same_result() {
        let rule = RewriteRuleChar {
            rule_id: 1,
            rule_name: "gh → f".to_string(),
            pattern: vec![PhoneChar::Consonant('g'), PhoneChar::Consonant('h')],
            replacement: vec![PhoneChar::Consonant('f')],
            context: ContextChar::Anywhere,
            weight: 0.15,
        };

        let s = vec![
            PhoneChar::Vowel('e'),
            PhoneChar::Consonant('g'),
            PhoneChar::Consonant('h'),
            PhoneChar::Vowel('o'),
            PhoneChar::Consonant('g'),
            PhoneChar::Consonant('h'),
        ];

        let standard_result = apply_rules_seq_char(&[rule.clone()], &s, 100);
        let optimized_result = apply_rules_seq_optimized_char(&[rule], &s, 100);

        assert_eq!(standard_result, optimized_result);
    }
}
