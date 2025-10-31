//! Character unit abstraction for dictionary edges.
//!
//! This module provides the [`CharUnit`] trait, which abstracts over byte-level
//! (u8) and character-level (char) operations. This allows dictionaries to operate
//! at either granularity, trading performance for Unicode correctness.

/// Trait abstracting character unit types for dictionary edges.
///
/// This trait allows dictionaries to operate at byte-level ([`u8`]) for maximum
/// performance with ASCII/Latin-1 text, or character-level ([`char`]) for proper
/// Unicode support.
///
/// # Performance Trade-offs
///
/// - **Byte-level (u8)**: 1 byte per edge, fastest, but treats multi-byte UTF-8
///   sequences as multiple characters. Distance of 1 from "a" won't reach "é" (2 bytes).
///
/// - **Character-level (char)**: 4 bytes per edge, ~15% slower, but correct Unicode
///   semantics. Distance of 1 from "a" correctly reaches "é" (1 character).
///
/// # Example
///
/// ```rust,ignore
/// // Byte-level dictionary (existing behavior)
/// let dict_bytes: DoubleArrayTrie = DoubleArrayTrie::from_terms(vec!["café"]);
///
/// // Character-level dictionary (proper Unicode)
/// let dict_chars: DoubleArrayTrieChar = DoubleArrayTrieChar::from_terms(vec!["café"]);
/// ```
pub trait CharUnit:
    Copy + Clone + Eq + PartialEq + std::hash::Hash + std::fmt::Debug + Send + Sync + 'static
{
    /// Convert from a string slice to a vector of units.
    ///
    /// For `u8`, this extracts the UTF-8 bytes.
    /// For `char`, this extracts the Unicode scalar values.
    fn from_str(s: &str) -> Vec<Self>;

    /// Convert from a slice of units back to a string.
    ///
    /// For `u8`, this uses lossy UTF-8 decoding (invalid sequences become �).
    /// For `char`, this is lossless.
    fn to_string(units: &[Self]) -> String;

    /// Create an iterator over the units in a string.
    ///
    /// For `u8`, iterates over bytes.
    /// For `char`, iterates over Unicode scalar values.
    fn iter_str(s: &str) -> Box<dyn Iterator<Item = Self> + '_>;
}

/// Byte-level implementation (existing behavior).
///
/// This is the default and recommended for ASCII/Latin-1 content.
/// Provides best performance but treats multi-byte UTF-8 sequences as
/// multiple units.
impl CharUnit for u8 {
    #[inline]
    fn from_str(s: &str) -> Vec<Self> {
        s.as_bytes().to_vec()
    }

    #[inline]
    fn to_string(units: &[Self]) -> String {
        String::from_utf8_lossy(units).into_owned()
    }

    #[inline]
    fn iter_str(s: &str) -> Box<dyn Iterator<Item = Self> + '_> {
        Box::new(s.bytes())
    }
}

/// Character-level implementation (Unicode-aware).
///
/// This provides proper Unicode semantics where edit distance is measured in
/// characters rather than bytes. Use when working with non-ASCII text.
impl CharUnit for char {
    #[inline]
    fn from_str(s: &str) -> Vec<Self> {
        s.chars().collect()
    }

    #[inline]
    fn to_string(units: &[Self]) -> String {
        units.iter().collect()
    }

    #[inline]
    fn iter_str(s: &str) -> Box<dyn Iterator<Item = Self> + '_> {
        Box::new(s.chars())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_u8_ascii() {
        let s = "hello";
        let units = u8::from_str(s);
        assert_eq!(units, vec![b'h', b'e', b'l', b'l', b'o']);
        assert_eq!(<u8 as CharUnit>::to_string(&units), s);
    }

    #[test]
    fn test_u8_unicode() {
        let s = "café";
        let units = u8::from_str(s);
        // 'é' is 2 bytes in UTF-8: 0xC3 0xA9
        assert_eq!(units.len(), 5); // c, a, f, é (2 bytes)
        assert_eq!(<u8 as CharUnit>::to_string(&units), s);
    }

    #[test]
    fn test_char_ascii() {
        let s = "hello";
        let units = char::from_str(s);
        assert_eq!(units, vec!['h', 'e', 'l', 'l', 'o']);
        assert_eq!(<char as CharUnit>::to_string(&units), s);
    }

    #[test]
    fn test_char_unicode() {
        let s = "café";
        let units = char::from_str(s);
        // Proper character-level: 4 characters
        assert_eq!(units, vec!['c', 'a', 'f', 'é']);
        assert_eq!(units.len(), 4);
        assert_eq!(<char as CharUnit>::to_string(&units), s);
    }

    #[test]
    fn test_char_emoji() {
        let s = "hello 🎉 world";
        let units = char::from_str(s);
        assert_eq!(units.len(), 13); // 13 characters including emoji
        assert!(units.contains(&'🎉'));
        assert_eq!(<char as CharUnit>::to_string(&units), s);
    }

    #[test]
    fn test_char_cjk() {
        let s = "中文";
        let units = char::from_str(s);
        assert_eq!(units, vec!['中', '文']);
        assert_eq!(units.len(), 2);
        assert_eq!(<char as CharUnit>::to_string(&units), s);
    }

    #[test]
    fn test_iter_u8() {
        let s = "hi";
        let collected: Vec<u8> = u8::iter_str(s).collect();
        assert_eq!(collected, vec![b'h', b'i']);
    }

    #[test]
    fn test_iter_char() {
        let s = "café";
        let collected: Vec<char> = <char as CharUnit>::iter_str(s).collect();
        assert_eq!(collected, vec!['c', 'a', 'f', 'é']);
    }
}
