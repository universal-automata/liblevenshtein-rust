//! Pattern and context matching for phonetic rewrite rules.
//!
//! This module implements the matching logic for phonetic rewrite rules,
//! directly translated from the Coq/Rocq verification in
//! `docs/verification/phonetic/rewrite_rules.v`.
//!
//! # Functions
//!
//! - [`phone_eq`] / [`phone_eq_char`] - Phone equality check
//! - [`context_matches`] / [`context_matches_char`] - Context satisfaction check
//! - [`pattern_matches_at`] / [`pattern_matches_at_char`] - Pattern matching at position
//!
//! # Formal Specification
//!
//! All functions are direct translations of Coq functions with proven properties.

use super::types::{Context, ContextChar, Phone, PhoneChar};

// ============================================================================
// Helper functions (byte-level)
// ============================================================================

/// Check if a character is a vowel (byte-level).
///
/// **Formal Specification**: `docs/verification/phonetic/rewrite_rules.v:72-76`
///
/// Checks if a byte represents one of the five English vowels: a, e, i, o, u.
#[inline]
pub fn is_vowel_char(c: u8) -> bool {
    matches!(c, b'a' | b'e' | b'i' | b'o' | b'u' | b'A' | b'E' | b'I' | b'O' | b'U')
}

/// Check if a phone is a vowel (byte-level).
///
/// **Formal Specification**: `docs/verification/phonetic/rewrite_rules.v:82-87`
#[inline]
pub fn is_vowel(p: &Phone) -> bool {
    matches!(p, Phone::Vowel(_))
}

/// Check if a phone is a consonant (byte-level).
///
/// **Formal Specification**: `docs/verification/phonetic/rewrite_rules.v:89-95`
///
/// Includes both `Consonant` and `Digraph` variants.
#[inline]
pub fn is_consonant(p: &Phone) -> bool {
    matches!(p, Phone::Consonant(_) | Phone::Digraph(_, _))
}

// ============================================================================
// Phone equality (byte-level)
// ============================================================================

/// Check if two phones are equal (byte-level).
///
/// **Formal Specification**: `docs/verification/phonetic/rewrite_rules.v:97-105`
///
/// # Examples
///
/// ```rust,ignore
/// use liblevenshtein::phonetic::{Phone, phone_eq};
///
/// assert!(phone_eq(&Phone::Vowel(b'a'), &Phone::Vowel(b'a')));
/// assert!(!phone_eq(&Phone::Vowel(b'a'), &Phone::Vowel(b'e')));
/// assert!(phone_eq(&Phone::Silent, &Phone::Silent));
/// ```
pub fn phone_eq(p1: &Phone, p2: &Phone) -> bool {
    match (p1, p2) {
        (Phone::Vowel(c1), Phone::Vowel(c2)) => c1 == c2,
        (Phone::Consonant(c1), Phone::Consonant(c2)) => c1 == c2,
        (Phone::Digraph(c1, c2), Phone::Digraph(c3, c4)) => c1 == c3 && c2 == c4,
        (Phone::Silent, Phone::Silent) => true,
        _ => false,
    }
}

// ============================================================================
// Context matching (byte-level)
// ============================================================================

/// Check if a context is satisfied at a position in a phonetic string.
///
/// **Formal Specification**: `docs/verification/phonetic/rewrite_rules.v:117-157`
///
/// # Arguments
///
/// - `ctx` - The context to check
/// - `s` - The phonetic string
/// - `pos` - The position in the string
///
/// # Returns
///
/// `true` if the context is satisfied at the given position, `false` otherwise.
///
/// # Examples
///
/// ```rust,ignore
/// use liblevenshtein::phonetic::{Context, Phone, context_matches};
///
/// let s = vec![Phone::Consonant(b'k'), Phone::Vowel(b'a'), Phone::Consonant(b't')];
/// assert!(context_matches(&Context::Initial, &s, 0));
/// assert!(context_matches(&Context::Final, &s, 3));
/// assert!(context_matches(&Context::Anywhere, &s, 1));
/// ```
pub fn context_matches(ctx: &Context, s: &[Phone], pos: usize) -> bool {
    match ctx {
        Context::Initial => pos == 0,
        Context::Final => pos == s.len(),
        Context::BeforeVowel(vowels) => {
            if let Some(Phone::Vowel(v)) = s.get(pos) {
                vowels.contains(v)
            } else {
                false
            }
        }
        Context::AfterConsonant(consonants) => {
            if pos == 0 {
                false
            } else if let Some(phone) = s.get(pos - 1) {
                match phone {
                    Phone::Consonant(c) => consonants.contains(c),
                    Phone::Digraph(c1, _) => consonants.contains(c1),
                    _ => false,
                }
            } else {
                false
            }
        }
        Context::BeforeConsonant(consonants) => {
            if let Some(phone) = s.get(pos) {
                match phone {
                    Phone::Consonant(c) => consonants.contains(c),
                    Phone::Digraph(c1, _) => consonants.contains(c1),
                    _ => false,
                }
            } else {
                false
            }
        }
        Context::AfterVowel(vowels) => {
            if pos == 0 {
                false
            } else if let Some(Phone::Vowel(v)) = s.get(pos - 1) {
                vowels.contains(v)
            } else {
                false
            }
        }
        Context::Anywhere => true,
    }
}

// ============================================================================
// Pattern matching (byte-level)
// ============================================================================

/// Check if a pattern matches at a specific position in a phonetic string.
///
/// **Formal Specification**: `docs/verification/phonetic/rewrite_rules.v:162-174`
///
/// # Arguments
///
/// - `pattern` - The pattern to match
/// - `s` - The phonetic string
/// - `pos` - The starting position
///
/// # Returns
///
/// `true` if the pattern matches at the given position, `false` otherwise.
///
/// # Examples
///
/// ```rust,ignore
/// use liblevenshtein::phonetic::{Phone, pattern_matches_at};
///
/// let pattern = vec![Phone::Consonant(b'c'), Phone::Consonant(b'h')];
/// let s = vec![Phone::Consonant(b'c'), Phone::Consonant(b'h'), Phone::Vowel(b'a')];
/// assert!(pattern_matches_at(&pattern, &s, 0));
/// assert!(!pattern_matches_at(&pattern, &s, 1));
/// ```
pub fn pattern_matches_at(pattern: &[Phone], s: &[Phone], pos: usize) -> bool {
    if pattern.is_empty() {
        return true;
    }

    for (i, p) in pattern.iter().enumerate() {
        if let Some(p_str) = s.get(pos + i) {
            if !phone_eq(p, p_str) {
                return false;
            }
        } else {
            return false;
        }
    }
    true
}

// ============================================================================
// Helper functions (character-level)
// ============================================================================

/// Check if a character is a vowel (character-level).
///
/// **Formal Specification**: `docs/verification/phonetic/rewrite_rules.v:72-76`
#[inline]
pub fn is_vowel_char_char(c: char) -> bool {
    matches!(c, 'a' | 'e' | 'i' | 'o' | 'u' | 'A' | 'E' | 'I' | 'O' | 'U')
}

/// Check if a phone is a vowel (character-level).
///
/// **Formal Specification**: `docs/verification/phonetic/rewrite_rules.v:82-87`
#[inline]
pub fn is_vowel_char_type(p: &PhoneChar) -> bool {
    matches!(p, PhoneChar::Vowel(_))
}

/// Check if a phone is a consonant (character-level).
///
/// **Formal Specification**: `docs/verification/phonetic/rewrite_rules.v:89-95`
#[inline]
pub fn is_consonant_char(p: &PhoneChar) -> bool {
    matches!(p, PhoneChar::Consonant(_) | PhoneChar::Digraph(_, _))
}

// ============================================================================
// Phone equality (character-level)
// ============================================================================

/// Check if two phones are equal (character-level).
///
/// **Formal Specification**: `docs/verification/phonetic/rewrite_rules.v:97-105`
pub fn phone_eq_char(p1: &PhoneChar, p2: &PhoneChar) -> bool {
    match (p1, p2) {
        (PhoneChar::Vowel(c1), PhoneChar::Vowel(c2)) => c1 == c2,
        (PhoneChar::Consonant(c1), PhoneChar::Consonant(c2)) => c1 == c2,
        (PhoneChar::Digraph(c1, c2), PhoneChar::Digraph(c3, c4)) => c1 == c3 && c2 == c4,
        (PhoneChar::Silent, PhoneChar::Silent) => true,
        _ => false,
    }
}

// ============================================================================
// Context matching (character-level)
// ============================================================================

/// Check if a context is satisfied at a position in a phonetic string (character-level).
///
/// **Formal Specification**: `docs/verification/phonetic/rewrite_rules.v:117-157`
pub fn context_matches_char(ctx: &ContextChar, s: &[PhoneChar], pos: usize) -> bool {
    match ctx {
        ContextChar::Initial => pos == 0,
        ContextChar::Final => pos == s.len(),
        ContextChar::BeforeVowel(vowels) => {
            if let Some(PhoneChar::Vowel(v)) = s.get(pos) {
                vowels.contains(v)
            } else {
                false
            }
        }
        ContextChar::AfterConsonant(consonants) => {
            if pos == 0 {
                false
            } else if let Some(phone) = s.get(pos - 1) {
                match phone {
                    PhoneChar::Consonant(c) => consonants.contains(c),
                    PhoneChar::Digraph(c1, _) => consonants.contains(c1),
                    _ => false,
                }
            } else {
                false
            }
        }
        ContextChar::BeforeConsonant(consonants) => {
            if let Some(phone) = s.get(pos) {
                match phone {
                    PhoneChar::Consonant(c) => consonants.contains(c),
                    PhoneChar::Digraph(c1, _) => consonants.contains(c1),
                    _ => false,
                }
            } else {
                false
            }
        }
        ContextChar::AfterVowel(vowels) => {
            if pos == 0 {
                false
            } else if let Some(PhoneChar::Vowel(v)) = s.get(pos - 1) {
                vowels.contains(v)
            } else {
                false
            }
        }
        ContextChar::Anywhere => true,
    }
}

// ============================================================================
// Pattern matching (character-level)
// ============================================================================

/// Check if a pattern matches at a specific position in a phonetic string (character-level).
///
/// **Formal Specification**: `docs/verification/phonetic/rewrite_rules.v:162-174`
pub fn pattern_matches_at_char(pattern: &[PhoneChar], s: &[PhoneChar], pos: usize) -> bool {
    if pattern.is_empty() {
        return true;
    }

    for (i, p) in pattern.iter().enumerate() {
        if let Some(p_str) = s.get(pos + i) {
            if !phone_eq_char(p, p_str) {
                return false;
            }
        } else {
            return false;
        }
    }
    true
}

#[cfg(test)]
mod tests {
    use super::*;

    // ========================================================================
    // Byte-level tests
    // ========================================================================

    #[test]
    fn test_is_vowel_char() {
        assert!(is_vowel_char(b'a'));
        assert!(is_vowel_char(b'e'));
        assert!(is_vowel_char(b'i'));
        assert!(is_vowel_char(b'o'));
        assert!(is_vowel_char(b'u'));
        assert!(!is_vowel_char(b'k'));
        assert!(!is_vowel_char(b'b'));
    }

    #[test]
    fn test_is_vowel() {
        assert!(is_vowel(&Phone::Vowel(b'a')));
        assert!(!is_vowel(&Phone::Consonant(b'k')));
        assert!(!is_vowel(&Phone::Silent));
    }

    #[test]
    fn test_is_consonant() {
        assert!(is_consonant(&Phone::Consonant(b'k')));
        assert!(is_consonant(&Phone::Digraph(b'c', b'h')));
        assert!(!is_consonant(&Phone::Vowel(b'a')));
        assert!(!is_consonant(&Phone::Silent));
    }

    #[test]
    fn test_phone_eq() {
        assert!(phone_eq(&Phone::Vowel(b'a'), &Phone::Vowel(b'a')));
        assert!(!phone_eq(&Phone::Vowel(b'a'), &Phone::Vowel(b'e')));
        assert!(phone_eq(&Phone::Silent, &Phone::Silent));
        assert!(phone_eq(
            &Phone::Digraph(b'c', b'h'),
            &Phone::Digraph(b'c', b'h')
        ));
        assert!(!phone_eq(
            &Phone::Digraph(b'c', b'h'),
            &Phone::Digraph(b's', b'h')
        ));
    }

    #[test]
    fn test_context_matches_initial() {
        let s = vec![Phone::Consonant(b'k'), Phone::Vowel(b'a')];
        assert!(context_matches(&Context::Initial, &s, 0));
        assert!(!context_matches(&Context::Initial, &s, 1));
    }

    #[test]
    fn test_context_matches_final() {
        let s = vec![Phone::Consonant(b'k'), Phone::Vowel(b'a')];
        assert!(context_matches(&Context::Final, &s, 2));
        assert!(!context_matches(&Context::Final, &s, 1));
    }

    #[test]
    fn test_context_matches_anywhere() {
        let s = vec![Phone::Consonant(b'k'), Phone::Vowel(b'a')];
        assert!(context_matches(&Context::Anywhere, &s, 0));
        assert!(context_matches(&Context::Anywhere, &s, 1));
        assert!(context_matches(&Context::Anywhere, &s, 2));
    }

    #[test]
    fn test_context_matches_before_vowel() {
        let s = vec![Phone::Consonant(b'k'), Phone::Vowel(b'a')];
        let ctx = Context::BeforeVowel(vec![b'a', b'e', b'i']);
        assert!(context_matches(&ctx, &s, 1));
        assert!(!context_matches(&ctx, &s, 0));
    }

    #[test]
    fn test_pattern_matches_at() {
        let pattern = vec![Phone::Consonant(b'c'), Phone::Consonant(b'h')];
        let s = vec![
            Phone::Consonant(b'c'),
            Phone::Consonant(b'h'),
            Phone::Vowel(b'a'),
        ];
        assert!(pattern_matches_at(&pattern, &s, 0));
        assert!(!pattern_matches_at(&pattern, &s, 1));
        assert!(!pattern_matches_at(&pattern, &s, 2));
    }

    #[test]
    fn test_pattern_matches_at_empty() {
        let pattern: Vec<Phone> = vec![];
        let s = vec![Phone::Vowel(b'a')];
        assert!(pattern_matches_at(&pattern, &s, 0));
    }

    // ========================================================================
    // Character-level tests
    // ========================================================================

    #[test]
    fn test_is_vowel_char_char() {
        assert!(is_vowel_char_char('a'));
        assert!(is_vowel_char_char('e'));
        assert!(!is_vowel_char_char('k'));
    }

    #[test]
    fn test_phone_eq_char() {
        assert!(phone_eq_char(
            &PhoneChar::Vowel('a'),
            &PhoneChar::Vowel('a')
        ));
        assert!(!phone_eq_char(
            &PhoneChar::Vowel('a'),
            &PhoneChar::Vowel('e')
        ));
        assert!(phone_eq_char(&PhoneChar::Silent, &PhoneChar::Silent));
    }

    #[test]
    fn test_context_matches_char_initial() {
        let s = vec![PhoneChar::Consonant('k'), PhoneChar::Vowel('a')];
        assert!(context_matches_char(&ContextChar::Initial, &s, 0));
        assert!(!context_matches_char(&ContextChar::Initial, &s, 1));
    }

    #[test]
    fn test_pattern_matches_at_char() {
        let pattern = vec![PhoneChar::Consonant('c'), PhoneChar::Consonant('h')];
        let s = vec![
            PhoneChar::Consonant('c'),
            PhoneChar::Consonant('h'),
            PhoneChar::Vowel('a'),
        ];
        assert!(pattern_matches_at_char(&pattern, &s, 0));
        assert!(!pattern_matches_at_char(&pattern, &s, 1));
    }
}
