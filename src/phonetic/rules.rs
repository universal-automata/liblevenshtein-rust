//! Concrete phonetic rewrite rule definitions.
//!
//! This module contains the actual rule definitions from the Zompist English
//! spelling-to-pronunciation system, directly translated from the Coq/Rocq
//! verification in `docs/verification/phonetic/zompist_rules.v`.
//!
//! # Rule Sets
//!
//! - [`orthography_rules()`] - Exact orthographic transformations (8 rules, weight=0.0)
//! - [`phonetic_rules()`] - Phonetic approximations (3 rules, weight=0.15)
//! - [`test_rules()`] - Test rules for non-commutativity (2 rules)
//! - [`zompist_rules()`] - Complete combined rule set (13 rules)
//!
//! # Rule Application Order
//!
//! Rules must be applied in the order defined in the rule set, as some rules
//! depend on transformations made by earlier rules (e.g., rule 21 "c → k" must
//! follow rule 20 "c → s before [ie]").
//!
//! # Formal Specification
//!
//! All rules are proven well-formed in `docs/verification/phonetic/zompist_rules.v`:
//! - Pattern is non-empty
//! - Weight is non-negative
//! - Bounded expansion property holds
//!
//! # Reference
//!
//! Original specification: <https://zompist.com/spell.html>

use super::types::{Context, ContextChar, Phone, PhoneChar, RewriteRule, RewriteRuleChar};

// ============================================================================
// Helper constants
// ============================================================================

/// Front vowels for velar softening (e, i)
const FRONT_VOWELS: &[u8] = &[b'e', b'i'];
const FRONT_VOWELS_CHAR: &[char] = &['e', 'i'];

// ============================================================================
// Orthography rules (byte-level) - weight = 0.0
// ============================================================================

/// Rule 1: ch → ç (digraph representation)
///
/// **Formal Specification**: `docs/verification/phonetic/zompist_rules.v:49-56`
///
/// Example: "church" → "çurç"
fn rule_ch_to_tsh() -> RewriteRule {
    RewriteRule {
        rule_id: 1,
        rule_name: "ch → ç (tsh sound)".to_string(),
        pattern: vec![Phone::Consonant(b'c'), Phone::Consonant(b'h')],
        replacement: vec![Phone::Digraph(b'c', b'h')],
        context: Context::Anywhere,
        weight: 0.0,
    }
}

/// Rule 2: sh → $ (digraph)
///
/// **Formal Specification**: `docs/verification/phonetic/zompist_rules.v:60-67`
fn rule_sh_to_sh() -> RewriteRule {
    RewriteRule {
        rule_id: 2,
        rule_name: "sh → $ (sh sound)".to_string(),
        pattern: vec![Phone::Consonant(b's'), Phone::Consonant(b'h')],
        replacement: vec![Phone::Digraph(b's', b'h')],
        context: Context::Anywhere,
        weight: 0.0,
    }
}

/// Rule 3: ph → f
///
/// **Formal Specification**: `docs/verification/phonetic/zompist_rules.v:71-78`
fn rule_ph_to_f() -> RewriteRule {
    RewriteRule {
        rule_id: 3,
        rule_name: "ph → f".to_string(),
        pattern: vec![Phone::Consonant(b'p'), Phone::Consonant(b'h')],
        replacement: vec![Phone::Consonant(b'f')],
        context: Context::Anywhere,
        weight: 0.0,
    }
}

/// Rule 20: c → s before front vowels (e, i)
///
/// **Formal Specification**: `docs/verification/phonetic/zompist_rules.v:84-91`
fn rule_c_to_s_before_front() -> RewriteRule {
    RewriteRule {
        rule_id: 20,
        rule_name: "c → s / _[ie]".to_string(),
        pattern: vec![Phone::Consonant(b'c')],
        replacement: vec![Phone::Consonant(b's')],
        context: Context::BeforeVowel(FRONT_VOWELS.to_vec()),
        weight: 0.0,
    }
}

/// Rule 21: c → k elsewhere
///
/// **Formal Specification**: `docs/verification/phonetic/zompist_rules.v:95-102`
fn rule_c_to_k_elsewhere() -> RewriteRule {
    RewriteRule {
        rule_id: 21,
        rule_name: "c → k (elsewhere)".to_string(),
        pattern: vec![Phone::Consonant(b'c')],
        replacement: vec![Phone::Consonant(b'k')],
        context: Context::Anywhere,
        weight: 0.0,
    }
}

/// Rule 22: g → j before front vowels
///
/// **Formal Specification**: `docs/verification/phonetic/zompist_rules.v:107-114`
fn rule_g_to_j_before_front() -> RewriteRule {
    RewriteRule {
        rule_id: 22,
        rule_name: "g → j / _[ie]".to_string(),
        pattern: vec![Phone::Consonant(b'g')],
        replacement: vec![Phone::Consonant(b'j')],
        context: Context::BeforeVowel(FRONT_VOWELS.to_vec()),
        weight: 0.0,
    }
}

/// Rule 33: Silent 'e' at end of word
///
/// **Formal Specification**: `docs/verification/phonetic/zompist_rules.v:121-128`
fn rule_silent_e_final() -> RewriteRule {
    RewriteRule {
        rule_id: 33,
        rule_name: "e → ∅ / _#".to_string(),
        pattern: vec![Phone::Vowel(b'e')],
        replacement: vec![Phone::Silent],
        context: Context::Final,
        weight: 0.0,
    }
}

/// Rule 34: gh → ∅ (silent)
///
/// **Formal Specification**: `docs/verification/phonetic/zompist_rules.v:132-139`
fn rule_gh_silent() -> RewriteRule {
    RewriteRule {
        rule_id: 34,
        rule_name: "gh → ∅".to_string(),
        pattern: vec![Phone::Consonant(b'g'), Phone::Consonant(b'h')],
        replacement: vec![Phone::Silent],
        context: Context::Anywhere,
        weight: 0.0,
    }
}

// ============================================================================
// Phonetic rules (byte-level) - weight = 0.15
// ============================================================================

/// Phonetic: th → t
///
/// **Formal Specification**: `docs/verification/phonetic/zompist_rules.v:147-154`
fn phonetic_th_to_t() -> RewriteRule {
    RewriteRule {
        rule_id: 100,
        rule_name: "th → t (phonetic)".to_string(),
        pattern: vec![Phone::Consonant(b't'), Phone::Consonant(b'h')],
        replacement: vec![Phone::Consonant(b't')],
        context: Context::Anywhere,
        weight: 0.15,
    }
}

/// Phonetic: qu → kw
///
/// **Formal Specification**: `docs/verification/phonetic/zompist_rules.v:158-165`
fn phonetic_qu_to_kw() -> RewriteRule {
    RewriteRule {
        rule_id: 101,
        rule_name: "qu → kw (phonetic)".to_string(),
        pattern: vec![Phone::Consonant(b'q'), Phone::Consonant(b'u')],
        replacement: vec![Phone::Consonant(b'k'), Phone::Consonant(b'w')],
        context: Context::Anywhere,
        weight: 0.15,
    }
}

/// Phonetic: kw → qu (reverse)
///
/// **Formal Specification**: `docs/verification/phonetic/zompist_rules.v:167-174`
fn phonetic_kw_to_qu() -> RewriteRule {
    RewriteRule {
        rule_id: 102,
        rule_name: "kw → qu (phonetic reverse)".to_string(),
        pattern: vec![Phone::Consonant(b'k'), Phone::Consonant(b'w')],
        replacement: vec![Phone::Consonant(b'q'), Phone::Consonant(b'u')],
        context: Context::Anywhere,
        weight: 0.15,
    }
}

// ============================================================================
// Test rules (byte-level) - for non-commutativity demonstration
// ============================================================================

/// Test Rule 200: x → yy (expansion)
///
/// **Formal Specification**: `docs/verification/phonetic/zompist_rules.v:187-194`
fn rule_x_expand() -> RewriteRule {
    RewriteRule {
        rule_id: 200,
        rule_name: "x → yy (expansion test)".to_string(),
        pattern: vec![Phone::Consonant(b'x')],
        replacement: vec![Phone::Consonant(b'y'), Phone::Consonant(b'y')],
        context: Context::Anywhere,
        weight: 0.0,
    }
}

/// Test Rule 201: y → z (transformation)
///
/// **Formal Specification**: `docs/verification/phonetic/zompist_rules.v:197-204`
fn rule_y_to_z() -> RewriteRule {
    RewriteRule {
        rule_id: 201,
        rule_name: "y → z (transformation test)".to_string(),
        pattern: vec![Phone::Consonant(b'y')],
        replacement: vec![Phone::Consonant(b'z')],
        context: Context::Anywhere,
        weight: 0.0,
    }
}

// ============================================================================
// Rule sets (byte-level)
// ============================================================================

/// Orthography rules: exact transformations (weight=0.0)
///
/// **Formal Specification**: `docs/verification/phonetic/zompist_rules.v:209-218`
///
/// Contains 8 rules for standard English orthography transformations.
pub fn orthography_rules() -> Vec<RewriteRule> {
    vec![
        rule_ch_to_tsh(),
        rule_sh_to_sh(),
        rule_ph_to_f(),
        rule_c_to_s_before_front(),
        rule_c_to_k_elsewhere(),
        rule_g_to_j_before_front(),
        rule_silent_e_final(),
        rule_gh_silent(),
    ]
}

/// Phonetic rules: approximate transformations (weight=0.15)
///
/// **Formal Specification**: `docs/verification/phonetic/zompist_rules.v:221-225`
///
/// Contains 3 rules for phonetic approximations.
pub fn phonetic_rules() -> Vec<RewriteRule> {
    vec![
        phonetic_th_to_t(),
        phonetic_qu_to_kw(),
        phonetic_kw_to_qu(),
    ]
}

/// Test rules: for demonstrating non-commutativity
///
/// **Formal Specification**: `docs/verification/phonetic/zompist_rules.v:228-231`
///
/// Contains 2 rules used in Theorem 3 (non-confluence proof).
pub fn test_rules() -> Vec<RewriteRule> {
    vec![rule_x_expand(), rule_y_to_z()]
}

/// Complete Zompist rule set: all 13 rules
///
/// **Formal Specification**: `docs/verification/phonetic/zompist_rules.v:234-235`
///
/// Combined set of orthography + phonetic + test rules.
pub fn zompist_rules() -> Vec<RewriteRule> {
    let mut rules = Vec::with_capacity(13);
    rules.extend(orthography_rules());
    rules.extend(phonetic_rules());
    rules.extend(test_rules());
    rules
}

// ============================================================================
// Character-level rules
// ============================================================================

fn rule_ch_to_tsh_char() -> RewriteRuleChar {
    RewriteRuleChar {
        rule_id: 1,
        rule_name: "ch → ç (tsh sound)".to_string(),
        pattern: vec![PhoneChar::Consonant('c'), PhoneChar::Consonant('h')],
        replacement: vec![PhoneChar::Digraph('c', 'h')],
        context: ContextChar::Anywhere,
        weight: 0.0,
    }
}

fn rule_sh_to_sh_char() -> RewriteRuleChar {
    RewriteRuleChar {
        rule_id: 2,
        rule_name: "sh → $ (sh sound)".to_string(),
        pattern: vec![PhoneChar::Consonant('s'), PhoneChar::Consonant('h')],
        replacement: vec![PhoneChar::Digraph('s', 'h')],
        context: ContextChar::Anywhere,
        weight: 0.0,
    }
}

fn rule_ph_to_f_char() -> RewriteRuleChar {
    RewriteRuleChar {
        rule_id: 3,
        rule_name: "ph → f".to_string(),
        pattern: vec![PhoneChar::Consonant('p'), PhoneChar::Consonant('h')],
        replacement: vec![PhoneChar::Consonant('f')],
        context: ContextChar::Anywhere,
        weight: 0.0,
    }
}

fn rule_c_to_s_before_front_char() -> RewriteRuleChar {
    RewriteRuleChar {
        rule_id: 20,
        rule_name: "c → s / _[ie]".to_string(),
        pattern: vec![PhoneChar::Consonant('c')],
        replacement: vec![PhoneChar::Consonant('s')],
        context: ContextChar::BeforeVowel(FRONT_VOWELS_CHAR.to_vec()),
        weight: 0.0,
    }
}

fn rule_c_to_k_elsewhere_char() -> RewriteRuleChar {
    RewriteRuleChar {
        rule_id: 21,
        rule_name: "c → k (elsewhere)".to_string(),
        pattern: vec![PhoneChar::Consonant('c')],
        replacement: vec![PhoneChar::Consonant('k')],
        context: ContextChar::Anywhere,
        weight: 0.0,
    }
}

fn rule_g_to_j_before_front_char() -> RewriteRuleChar {
    RewriteRuleChar {
        rule_id: 22,
        rule_name: "g → j / _[ie]".to_string(),
        pattern: vec![PhoneChar::Consonant('g')],
        replacement: vec![PhoneChar::Consonant('j')],
        context: ContextChar::BeforeVowel(FRONT_VOWELS_CHAR.to_vec()),
        weight: 0.0,
    }
}

fn rule_silent_e_final_char() -> RewriteRuleChar {
    RewriteRuleChar {
        rule_id: 33,
        rule_name: "e → ∅ / _#".to_string(),
        pattern: vec![PhoneChar::Vowel('e')],
        replacement: vec![PhoneChar::Silent],
        context: ContextChar::Final,
        weight: 0.0,
    }
}

fn rule_gh_silent_char() -> RewriteRuleChar {
    RewriteRuleChar {
        rule_id: 34,
        rule_name: "gh → ∅".to_string(),
        pattern: vec![PhoneChar::Consonant('g'), PhoneChar::Consonant('h')],
        replacement: vec![PhoneChar::Silent],
        context: ContextChar::Anywhere,
        weight: 0.0,
    }
}

fn phonetic_th_to_t_char() -> RewriteRuleChar {
    RewriteRuleChar {
        rule_id: 100,
        rule_name: "th → t (phonetic)".to_string(),
        pattern: vec![PhoneChar::Consonant('t'), PhoneChar::Consonant('h')],
        replacement: vec![PhoneChar::Consonant('t')],
        context: ContextChar::Anywhere,
        weight: 0.15,
    }
}

fn phonetic_qu_to_kw_char() -> RewriteRuleChar {
    RewriteRuleChar {
        rule_id: 101,
        rule_name: "qu → kw (phonetic)".to_string(),
        pattern: vec![PhoneChar::Consonant('q'), PhoneChar::Consonant('u')],
        replacement: vec![PhoneChar::Consonant('k'), PhoneChar::Consonant('w')],
        context: ContextChar::Anywhere,
        weight: 0.15,
    }
}

fn phonetic_kw_to_qu_char() -> RewriteRuleChar {
    RewriteRuleChar {
        rule_id: 102,
        rule_name: "kw → qu (phonetic reverse)".to_string(),
        pattern: vec![PhoneChar::Consonant('k'), PhoneChar::Consonant('w')],
        replacement: vec![PhoneChar::Consonant('q'), PhoneChar::Consonant('u')],
        context: ContextChar::Anywhere,
        weight: 0.15,
    }
}

fn rule_x_expand_char() -> RewriteRuleChar {
    RewriteRuleChar {
        rule_id: 200,
        rule_name: "x → yy (expansion test)".to_string(),
        pattern: vec![PhoneChar::Consonant('x')],
        replacement: vec![PhoneChar::Consonant('y'), PhoneChar::Consonant('y')],
        context: ContextChar::Anywhere,
        weight: 0.0,
    }
}

fn rule_y_to_z_char() -> RewriteRuleChar {
    RewriteRuleChar {
        rule_id: 201,
        rule_name: "y → z (transformation test)".to_string(),
        pattern: vec![PhoneChar::Consonant('y')],
        replacement: vec![PhoneChar::Consonant('z')],
        context: ContextChar::Anywhere,
        weight: 0.0,
    }
}

/// Character-level orthography rules
pub fn orthography_rules_char() -> Vec<RewriteRuleChar> {
    vec![
        rule_ch_to_tsh_char(),
        rule_sh_to_sh_char(),
        rule_ph_to_f_char(),
        rule_c_to_s_before_front_char(),
        rule_c_to_k_elsewhere_char(),
        rule_g_to_j_before_front_char(),
        rule_silent_e_final_char(),
        rule_gh_silent_char(),
    ]
}

/// Character-level phonetic rules
pub fn phonetic_rules_char() -> Vec<RewriteRuleChar> {
    vec![
        phonetic_th_to_t_char(),
        phonetic_qu_to_kw_char(),
        phonetic_kw_to_qu_char(),
    ]
}

/// Character-level test rules
pub fn test_rules_char() -> Vec<RewriteRuleChar> {
    vec![rule_x_expand_char(), rule_y_to_z_char()]
}

/// Character-level complete rule set
pub fn zompist_rules_char() -> Vec<RewriteRuleChar> {
    let mut rules = Vec::with_capacity(13);
    rules.extend(orthography_rules_char());
    rules.extend(phonetic_rules_char());
    rules.extend(test_rules_char());
    rules
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_orthography_rules_count() {
        assert_eq!(orthography_rules().len(), 8);
    }

    #[test]
    fn test_phonetic_rules_count() {
        assert_eq!(phonetic_rules().len(), 3);
    }

    #[test]
    fn test_test_rules_count() {
        assert_eq!(test_rules().len(), 2);
    }

    #[test]
    fn test_zompist_rules_count() {
        assert_eq!(zompist_rules().len(), 13);
    }

    #[test]
    fn test_rule_weights() {
        // Orthography rules should have weight 0.0
        for rule in orthography_rules().iter() {
            assert_eq!(
                rule.weight, 0.0,
                "Rule {} should have weight 0.0",
                rule.rule_name
            );
        }

        // Phonetic rules should have weight 0.15
        for rule in phonetic_rules().iter() {
            assert_eq!(
                rule.weight, 0.15,
                "Rule {} should have weight 0.15",
                rule.rule_name
            );
        }
    }

    #[test]
    fn test_char_rules_count() {
        assert_eq!(orthography_rules_char().len(), 8);
        assert_eq!(phonetic_rules_char().len(), 3);
        assert_eq!(test_rules_char().len(), 2);
        assert_eq!(zompist_rules_char().len(), 13);
    }
}
