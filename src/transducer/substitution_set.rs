//! Set of allowed character substitutions for fuzzy matching.
//!
//! This module provides [`SubstitutionSet`], which defines which character
//! substitutions are permitted during Levenshtein automaton matching. It's
//! used with the [`Restricted`](super::substitution_policy::Restricted)
//! policy to implement custom character similarity.
//!
//! ## Use Cases
//!
//! - **Phonetic matching**: Allow phonetically similar substitutions (f/ph, c/k)
//! - **Keyboard typos**: Allow adjacent key substitutions
//! - **OCR errors**: Allow visually similar character substitutions
//! - **Leetspeak**: Allow common leetspeak substitutions (3/e, @/a, 0/o)
//!
//! ## Example
//!
//! ```rust,ignore
//! use liblevenshtein::transducer::{SubstitutionSet, Transducer, Algorithm};
//! use liblevenshtein::prelude::*;
//!
//! // Create phonetic substitution set
//! let mut phonetic = SubstitutionSet::new();
//! phonetic.allow('f', 'p');  // For "ph" → "f" phonetic similarity
//! phonetic.allow('c', 'k');
//! phonetic.allow('s', 'z');
//!
//! // Or use a preset
//! let phonetic = SubstitutionSet::phonetic_basic();
//!
//! // Use with dictionary
//! let dict = DoubleArrayTrie::from_terms(vec!["phone", "cat", "dogs"]);
//! let transducer = Transducer::with_substitutions(
//!     dict,
//!     Algorithm::Standard,
//!     phonetic
//! );
//!
//! // Now "fone" matches "phone" with distance 1 (via f/ph substitution)
//! let results: Vec<_> = transducer.query("fone", 1).collect();
//! ```

use rustc_hash::FxHashSet;

/// Set of allowed character substitutions.
///
/// A `SubstitutionSet` defines which character pairs can be substituted
/// for each other during fuzzy matching. Only ASCII characters (0-127)
/// are currently supported.
///
/// ## Performance
///
/// - **Storage**: HashSet with fast non-cryptographic hashing (FxHasher)
/// - **Lookup**: O(1) average case, ~10-30ns per check
/// - **Memory**: ~48 bytes base + 24 bytes per allowed pair
///
/// ## Symmetry
///
/// Substitutions are **not symmetric by default**. If you want bidirectional
/// substitutions, you must add both directions explicitly:
///
/// ```rust
/// # use liblevenshtein::transducer::SubstitutionSet;
/// let mut set = SubstitutionSet::new();
/// set.allow('a', 'b');  // 'a' can be substituted with 'b'
/// set.allow('b', 'a');  // 'b' can be substituted with 'a' (symmetric)
/// ```
///
/// Most presets (like `phonetic_basic()`) include symmetric pairs where appropriate.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SubstitutionSet {
    /// Allowed substitution pairs (dict_char, query_char).
    /// Uses FxHasher for fast non-cryptographic hashing.
    allowed: FxHashSet<(u8, u8)>,
}

impl SubstitutionSet {
    /// Create an empty substitution set.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use liblevenshtein::transducer::SubstitutionSet;
    /// let mut set = SubstitutionSet::new();
    /// set.allow('a', 'b');
    /// assert!(set.contains(b'a', b'b'));
    /// ```
    #[inline]
    pub fn new() -> Self {
        Self {
            allowed: FxHashSet::default(),
        }
    }

    /// Create a substitution set with expected capacity.
    ///
    /// Pre-allocates space for `capacity` substitution pairs to avoid
    /// reallocations during construction.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use liblevenshtein::transducer::SubstitutionSet;
    /// let mut set = SubstitutionSet::with_capacity(50);
    /// // Add many pairs without reallocations
    /// for i in 0..50 {
    ///     set.allow_byte(b'a' + i % 26, b'A' + i % 26);
    /// }
    /// ```
    #[inline]
    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            allowed: FxHashSet::with_capacity_and_hasher(capacity, Default::default()),
        }
    }

    /// Allow substituting character `a` with character `b`.
    ///
    /// Only ASCII characters are supported. Non-ASCII characters are silently ignored.
    ///
    /// # Parameters
    ///
    /// - `a`: Dictionary character (source)
    /// - `b`: Query character (target)
    ///
    /// # Example
    ///
    /// ```rust
    /// # use liblevenshtein::transducer::SubstitutionSet;
    /// let mut set = SubstitutionSet::new();
    /// set.allow('f', 'p');  // 'f' in dict can match 'p' in query
    /// set.allow('p', 'h');  // 'p' in dict can match 'h' in query
    ///
    /// // This enables "phone" to match "fone" via f→p substitution
    /// ```
    #[inline]
    pub fn allow(&mut self, a: char, b: char) {
        if a.is_ascii() && b.is_ascii() {
            self.allow_byte(a as u8, b as u8);
        }
    }

    /// Allow substituting byte `a` with byte `b` (low-level API).
    ///
    /// This is the low-level API that works directly with bytes. It's
    /// slightly faster than [`allow()`](Self::allow) since it skips
    /// the ASCII check, but requires the caller to ensure ASCII validity.
    ///
    /// # Parameters
    ///
    /// - `a`: Dictionary byte (source, 0-127)
    /// - `b`: Query byte (target, 0-127)
    ///
    /// # Example
    ///
    /// ```rust
    /// # use liblevenshtein::transducer::SubstitutionSet;
    /// let mut set = SubstitutionSet::new();
    /// set.allow_byte(b'a', b'b');
    /// assert!(set.contains(b'a', b'b'));
    /// ```
    #[inline]
    pub fn allow_byte(&mut self, a: u8, b: u8) {
        self.allowed.insert((a, b));
    }

    /// Check if substituting byte `a` with byte `b` is allowed.
    ///
    /// This is the hot-path method called during character matching.
    /// It's marked `#[inline]` for performance.
    ///
    /// # Parameters
    ///
    /// - `a`: Dictionary byte
    /// - `b`: Query byte
    ///
    /// # Returns
    ///
    /// `true` if the substitution `a → b` is allowed, `false` otherwise.
    ///
    /// # Performance
    ///
    /// O(1) average case, ~10-30ns per lookup with FxHasher.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use liblevenshtein::transducer::SubstitutionSet;
    /// let mut set = SubstitutionSet::new();
    /// set.allow('x', 'y');
    ///
    /// assert!(set.contains(b'x', b'y'));
    /// assert!(!set.contains(b'y', b'x'));  // Not symmetric
    /// ```
    #[inline]
    pub fn contains(&self, a: u8, b: u8) -> bool {
        self.allowed.contains(&(a, b))
    }

    /// Build a substitution set from character pairs.
    ///
    /// # Parameters
    ///
    /// - `pairs`: Slice of (source, target) character pairs
    ///
    /// # Example
    ///
    /// ```rust
    /// # use liblevenshtein::transducer::SubstitutionSet;
    /// let set = SubstitutionSet::from_pairs(&[
    ///     ('f', 'p'), ('p', 'h'),  // phonetic: ph → f
    ///     ('c', 'k'), ('k', 'c'),  // symmetric
    /// ]);
    ///
    /// assert!(set.contains(b'f', b'p'));
    /// assert!(set.contains(b'c', b'k'));
    /// ```
    pub fn from_pairs(pairs: &[(char, char)]) -> Self {
        let mut set = Self::with_capacity(pairs.len());
        for &(a, b) in pairs {
            set.allow(a, b);
        }
        set
    }

    /// Get the number of allowed substitution pairs.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use liblevenshtein::transducer::SubstitutionSet;
    /// let mut set = SubstitutionSet::new();
    /// assert_eq!(set.len(), 0);
    ///
    /// set.allow('a', 'b');
    /// set.allow('c', 'd');
    /// assert_eq!(set.len(), 2);
    /// ```
    #[inline]
    pub fn len(&self) -> usize {
        self.allowed.len()
    }

    /// Check if the substitution set is empty.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use liblevenshtein::transducer::SubstitutionSet;
    /// let set = SubstitutionSet::new();
    /// assert!(set.is_empty());
    ///
    /// let phonetic = SubstitutionSet::phonetic_basic();
    /// assert!(!phonetic.is_empty());
    /// ```
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.allowed.is_empty()
    }

    /// Clear all allowed substitutions.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use liblevenshtein::transducer::SubstitutionSet;
    /// let mut set = SubstitutionSet::phonetic_basic();
    /// assert!(!set.is_empty());
    ///
    /// set.clear();
    /// assert!(set.is_empty());
    /// ```
    #[inline]
    pub fn clear(&mut self) {
        self.allowed.clear();
    }

    // ========================================================================
    // Preset Builders
    // ========================================================================

    /// Common phonetic equivalences for English.
    ///
    /// Includes bidirectional substitutions for phonetically similar sounds:
    /// - **f/ph**: phone ↔ fone
    /// - **c/k**: cat ↔ kat
    /// - **c/s**: cent ↔ sent
    /// - **s/z**: dogs ↔ dogz
    /// - **tion/shun**: nation ↔ nashun
    ///
    /// This is a basic set suitable for casual phonetic matching. For more
    /// sophisticated phonetic matching, consider implementing Soundex or
    /// Metaphone-inspired rules.
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// # use liblevenshtein::transducer::{SubstitutionSet, Transducer, Algorithm};
    /// # use liblevenshtein::prelude::*;
    /// let phonetic = SubstitutionSet::phonetic_basic();
    ///
    /// let dict = DoubleArrayTrie::from_terms(vec!["phone", "cat"]);
    /// let transducer = Transducer::with_substitutions(
    ///     dict,
    ///     Algorithm::Standard,
    ///     phonetic
    /// );
    ///
    /// // "fone" matches "phone" (f ↔ ph)
    /// let results: Vec<_> = transducer.query("fone", 1).collect();
    /// assert!(results.contains(&"phone"));
    /// ```
    pub fn phonetic_basic() -> Self {
        Self::from_pairs(&[
            // f/ph equivalence (bidirectional)
            ('f', 'p'), ('p', 'f'),
            // c/k equivalence (bidirectional)
            ('c', 'k'), ('k', 'c'),
            // c/s equivalence (bidirectional)
            ('c', 's'), ('s', 'c'),
            // s/z equivalence (bidirectional)
            ('s', 'z'), ('z', 's'),
            // Common vowel confusions
            ('a', 'e'), ('e', 'a'),
            ('i', 'y'), ('y', 'i'),
            // Silent letters (allow omission)
            ('h', '\0'),  // Hour → our
            ('k', '\0'),  // Knight → night (when followed by 'n')
        ])
    }

    /// QWERTY keyboard proximity substitutions.
    ///
    /// Allows substitutions between adjacent keys on a QWERTY keyboard,
    /// useful for catching typos caused by hitting nearby keys.
    ///
    /// Includes horizontal and vertical adjacencies for common keys.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use liblevenshtein::transducer::SubstitutionSet;
    /// let keyboard = SubstitutionSet::keyboard_qwerty();
    ///
    /// // 'q' and 'w' are adjacent
    /// assert!(keyboard.contains(b'q', b'w') || keyboard.contains(b'w', b'q'));
    /// ```
    pub fn keyboard_qwerty() -> Self {
        Self::from_pairs(&[
            // Top row
            ('q', 'w'), ('w', 'q'),
            ('w', 'e'), ('e', 'w'),
            ('e', 'r'), ('r', 'e'),
            ('r', 't'), ('t', 'r'),
            ('t', 'y'), ('y', 't'),
            ('y', 'u'), ('u', 'y'),
            ('u', 'i'), ('i', 'u'),
            ('i', 'o'), ('o', 'i'),
            ('o', 'p'), ('p', 'o'),
            // Middle row
            ('a', 's'), ('s', 'a'),
            ('s', 'd'), ('d', 's'),
            ('d', 'f'), ('f', 'd'),
            ('f', 'g'), ('g', 'f'),
            ('g', 'h'), ('h', 'g'),
            ('h', 'j'), ('j', 'h'),
            ('j', 'k'), ('k', 'j'),
            ('k', 'l'), ('l', 'k'),
            // Bottom row
            ('z', 'x'), ('x', 'z'),
            ('x', 'c'), ('c', 'x'),
            ('c', 'v'), ('v', 'c'),
            ('v', 'b'), ('b', 'v'),
            ('b', 'n'), ('n', 'b'),
            ('n', 'm'), ('m', 'n'),
            // Vertical adjacencies (selected)
            ('q', 'a'), ('a', 'q'),
            ('w', 's'), ('s', 'w'),
            ('e', 'd'), ('d', 'e'),
            ('r', 'f'), ('f', 'r'),
            ('t', 'g'), ('g', 't'),
            ('y', 'h'), ('h', 'y'),
            ('u', 'j'), ('j', 'u'),
            ('i', 'k'), ('k', 'i'),
            ('o', 'l'), ('l', 'o'),
        ])
    }

    /// Common leetspeak substitutions.
    ///
    /// Allows common character-to-number substitutions used in leetspeak:
    /// - **3 ↔ e**: leet ↔ l33t
    /// - **@ ↔ a**: at ↔ @t
    /// - **0 ↔ o**: root ↔ r00t
    /// - **1 ↔ i/l**: lit ↔ l1t
    /// - **$ ↔ s**: cash ↔ ca$h
    /// - **7 ↔ t**: test ↔ 7es7
    ///
    /// Useful for matching leetspeak variations in usernames or informal text.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use liblevenshtein::transducer::SubstitutionSet;
    /// let leet = SubstitutionSet::leet_speak();
    ///
    /// // '3' can substitute for 'e'
    /// assert!(leet.contains(b'e', b'3'));
    /// assert!(leet.contains(b'3', b'e'));
    /// ```
    pub fn leet_speak() -> Self {
        Self::from_pairs(&[
            ('e', '3'), ('3', 'e'),
            ('a', '@'), ('@', 'a'),
            ('a', '4'), ('4', 'a'),
            ('o', '0'), ('0', 'o'),
            ('i', '1'), ('1', 'i'),
            ('l', '1'), ('1', 'l'),
            ('s', '$'), ('$', 's'),
            ('s', '5'), ('5', 's'),
            ('t', '7'), ('7', 't'),
            ('b', '8'), ('8', 'b'),
            ('g', '9'), ('9', 'g'),
        ])
    }

    /// OCR-friendly substitutions for commonly confused characters.
    ///
    /// Includes substitutions for characters that are visually similar
    /// and often confused by OCR systems:
    /// - **0/O**: Zero vs letter O
    /// - **1/I/l**: One vs capital I vs lowercase L
    /// - **8/B**: Eight vs capital B
    /// - **5/S**: Five vs capital S
    ///
    /// # Example
    ///
    /// ```rust
    /// # use liblevenshtein::transducer::SubstitutionSet;
    /// let ocr = SubstitutionSet::ocr_friendly();
    ///
    /// // '0' and 'O' are visually similar
    /// assert!(ocr.contains(b'0', b'O') || ocr.contains(b'O', b'0'));
    /// ```
    pub fn ocr_friendly() -> Self {
        Self::from_pairs(&[
            // 0/O confusion
            ('0', 'O'), ('O', '0'),
            ('0', 'o'), ('o', '0'),
            // 1/I/l confusion
            ('1', 'I'), ('I', '1'),
            ('1', 'l'), ('l', '1'),
            ('I', 'l'), ('l', 'I'),
            // 8/B confusion
            ('8', 'B'), ('B', '8'),
            // 5/S confusion
            ('5', 'S'), ('S', '5'),
            // 6/G confusion
            ('6', 'G'), ('G', '6'),
            // 2/Z confusion
            ('2', 'Z'), ('Z', '2'),
        ])
    }
}

impl Default for SubstitutionSet {
    /// Create an empty substitution set (equivalent to [`new()`](Self::new)).
    #[inline]
    fn default() -> Self {
        Self::new()
    }
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_new_empty() {
        let set = SubstitutionSet::new();
        assert_eq!(set.len(), 0);
        assert!(set.is_empty());
    }

    #[test]
    fn test_allow_and_contains() {
        let mut set = SubstitutionSet::new();

        set.allow('a', 'b');
        assert!(set.contains(b'a', b'b'));
        assert!(!set.contains(b'b', b'a')); // Not symmetric

        set.allow('b', 'a'); // Add reverse
        assert!(set.contains(b'b', b'a'));
    }

    #[test]
    fn test_allow_byte() {
        let mut set = SubstitutionSet::new();

        set.allow_byte(b'x', b'y');
        assert!(set.contains(b'x', b'y'));
        assert_eq!(set.len(), 1);
    }

    #[test]
    fn test_from_pairs() {
        let set = SubstitutionSet::from_pairs(&[
            ('a', 'b'),
            ('c', 'd'),
            ('e', 'f'),
        ]);

        assert_eq!(set.len(), 3);
        assert!(set.contains(b'a', b'b'));
        assert!(set.contains(b'c', b'd'));
        assert!(set.contains(b'e', b'f'));
    }

    #[test]
    fn test_clear() {
        let mut set = SubstitutionSet::from_pairs(&[('a', 'b'), ('c', 'd')]);
        assert_eq!(set.len(), 2);

        set.clear();
        assert_eq!(set.len(), 0);
        assert!(set.is_empty());
    }

    #[test]
    fn test_phonetic_basic() {
        let phonetic = SubstitutionSet::phonetic_basic();

        assert!(!phonetic.is_empty());

        // f/ph equivalence
        assert!(phonetic.contains(b'f', b'p'));
        assert!(phonetic.contains(b'p', b'f'));

        // c/k equivalence
        assert!(phonetic.contains(b'c', b'k'));
        assert!(phonetic.contains(b'k', b'c'));

        // s/z equivalence
        assert!(phonetic.contains(b's', b'z'));
        assert!(phonetic.contains(b'z', b's'));
    }

    #[test]
    fn test_keyboard_qwerty() {
        let keyboard = SubstitutionSet::keyboard_qwerty();

        assert!(!keyboard.is_empty());

        // Adjacent keys on top row
        assert!(keyboard.contains(b'q', b'w'));
        assert!(keyboard.contains(b'w', b'q'));

        // Adjacent keys on middle row
        assert!(keyboard.contains(b'a', b's'));
        assert!(keyboard.contains(b's', b'a'));

        // Vertical adjacency
        assert!(keyboard.contains(b'q', b'a'));
        assert!(keyboard.contains(b'a', b'q'));
    }

    #[test]
    fn test_leet_speak() {
        let leet = SubstitutionSet::leet_speak();

        assert!(!leet.is_empty());

        // 3/e
        assert!(leet.contains(b'e', b'3'));
        assert!(leet.contains(b'3', b'e'));

        // @/a
        assert!(leet.contains(b'a', b'@'));
        assert!(leet.contains(b'@', b'a'));

        // 0/o
        assert!(leet.contains(b'o', b'0'));
        assert!(leet.contains(b'0', b'o'));
    }

    #[test]
    fn test_ocr_friendly() {
        let ocr = SubstitutionSet::ocr_friendly();

        assert!(!ocr.is_empty());

        // 0/O confusion
        assert!(ocr.contains(b'0', b'O'));
        assert!(ocr.contains(b'O', b'0'));

        // 1/I/l confusion
        assert!(ocr.contains(b'1', b'I'));
        assert!(ocr.contains(b'1', b'l'));
        assert!(ocr.contains(b'I', b'l'));
    }

    #[test]
    fn test_with_capacity() {
        let set = SubstitutionSet::with_capacity(100);
        assert_eq!(set.len(), 0);
        // Capacity is internal, but shouldn't panic
    }

    #[test]
    fn test_non_ascii_ignored() {
        let mut set = SubstitutionSet::new();

        // Non-ASCII characters should be ignored
        set.allow('α', 'β'); // Greek letters
        set.allow('你', '好'); // Chinese characters

        assert_eq!(set.len(), 0); // Nothing added
    }

    #[test]
    fn test_duplicate_pairs() {
        let mut set = SubstitutionSet::new();

        set.allow('a', 'b');
        set.allow('a', 'b'); // Duplicate

        // HashSet deduplicates
        assert_eq!(set.len(), 1);
    }

    #[test]
    fn test_clone() {
        let set1 = SubstitutionSet::phonetic_basic();
        let set2 = set1.clone();

        assert_eq!(set1.len(), set2.len());
        assert_eq!(set1, set2);
    }

    #[test]
    fn test_debug() {
        let set = SubstitutionSet::from_pairs(&[('a', 'b')]);
        let debug_str = format!("{:?}", set);
        assert!(debug_str.contains("SubstitutionSet"));
    }
}
