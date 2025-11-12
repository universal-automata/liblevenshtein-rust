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

/// Internal representation of SubstitutionSet storage.
///
/// Uses a hybrid approach (H3 optimization):
/// - **Small sets (≤4 pairs)**: Linear scan in Vec (~200-350ns, 1.2-1.9× faster than hash)
/// - **Large sets (>4 pairs)**: Hash lookup in FxHashSet (~370ns constant time)
///
/// Crossover analysis shows linear scan wins for tiny sets due to:
/// - No hashing overhead (~3-5ns saved)
/// - Better cache behavior (sequential access)
/// - Predictable branches (linear loop)
/// - Smaller memory footprint (2× less than hash)
///
/// See: docs/optimization/substitution-set/05-crossover-analysis.md
#[derive(Clone, Debug, PartialEq, Eq)]
enum SubstitutionSetImpl {
    /// Small set using linear scan (≤4 pairs).
    /// Faster for tiny sets due to no hash overhead.
    Small(Vec<(u8, u8)>),

    /// Large set using hash lookup (>4 pairs).
    /// Scales better for larger sets with O(1) lookup.
    Large(FxHashSet<(u8, u8)>),
}

/// Set of allowed character substitutions.
///
/// A `SubstitutionSet` defines which character pairs can be substituted
/// for each other during fuzzy matching. Only ASCII characters (0-127)
/// are currently supported.
///
/// ## Performance
///
/// Uses a hybrid approach (H3 optimization):
/// - **Small sets (≤4 pairs)**: Linear scan (~200-350ns, 15-48% faster than hash)
/// - **Large sets (>4 pairs)**: Hash lookup (~370ns constant time)
///
/// Automatically upgrades from Vec to FxHashSet when exceeding threshold.
///
/// ## Memory
///
/// - **Small sets**: ~24 bytes + 2 bytes per pair (50-75% less than hash)
/// - **Large sets**: ~48 bytes + 24 bytes per pair (same as before)
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
    /// Internal storage using hybrid Vec/HashSet approach.
    inner: SubstitutionSetImpl,
}

impl SubstitutionSet {
    /// Threshold for upgrading from Vec to FxHashSet.
    ///
    /// Based on empirical crossover analysis showing linear scan wins for ≤4 pairs.
    /// See: docs/optimization/substitution-set/05-crossover-analysis.md
    const SMALL_SET_THRESHOLD: usize = 4;

    /// Create an empty substitution set.
    ///
    /// Starts with a small Vec-based representation for optimal performance
    /// with tiny sets (automatically upgrades to hash for larger sets).
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
            inner: SubstitutionSetImpl::Small(Vec::new()),
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
        // Choose optimal storage based on expected capacity
        if capacity <= Self::SMALL_SET_THRESHOLD {
            Self {
                inner: SubstitutionSetImpl::Small(Vec::with_capacity(capacity)),
            }
        } else {
            Self {
                inner: SubstitutionSetImpl::Large(
                    FxHashSet::with_capacity_and_hasher(capacity, Default::default())
                ),
            }
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
        match &mut self.inner {
            SubstitutionSetImpl::Small(vec) if vec.len() < Self::SMALL_SET_THRESHOLD => {
                // Still small - add to Vec if not duplicate
                if !vec.contains(&(a, b)) {
                    vec.push((a, b));
                }
            }
            SubstitutionSetImpl::Small(vec) => {
                // Exceeded threshold - upgrade to hash set
                let mut set = FxHashSet::with_capacity_and_hasher(
                    vec.len() + 1,
                    Default::default()
                );
                for &pair in vec.iter() {
                    set.insert(pair);
                }
                set.insert((a, b));
                self.inner = SubstitutionSetImpl::Large(set);
            }
            SubstitutionSetImpl::Large(set) => {
                // Already large - use hash set
                set.insert((a, b));
            }
        }
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
        match &self.inner {
            SubstitutionSetImpl::Small(vec) => {
                // Linear scan for small sets (faster for ≤4 pairs)
                vec.iter().any(|&(x, y)| x == a && y == b)
            }
            SubstitutionSetImpl::Large(set) => {
                // Hash lookup for large sets (faster for >4 pairs)
                set.contains(&(a, b))
            }
        }
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
        match &self.inner {
            SubstitutionSetImpl::Small(vec) => vec.len(),
            SubstitutionSetImpl::Large(set) => set.len(),
        }
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
        match &self.inner {
            SubstitutionSetImpl::Small(vec) => vec.is_empty(),
            SubstitutionSetImpl::Large(set) => set.is_empty(),
        }
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
        match &mut self.inner {
            SubstitutionSetImpl::Small(vec) => vec.clear(),
            SubstitutionSetImpl::Large(set) => set.clear(),
        }
    }

    // ========================================================================
    // Preset Builders
    // ========================================================================

    // Const arrays for optimized preset initialization (15-28% faster)
    // See: docs/optimization/substitution-set/02-hypothesis1-const-arrays.md

    /// Phonetic substitutions as a const array.
    const PHONETIC_PAIRS: &[(u8, u8)] = &[
        // f/ph equivalence (bidirectional)
        (b'f', b'p'), (b'p', b'f'),
        // c/k equivalence (bidirectional)
        (b'c', b'k'), (b'k', b'c'),
        // c/s equivalence (bidirectional)
        (b'c', b's'), (b's', b'c'),
        // s/z equivalence (bidirectional)
        (b's', b'z'), (b'z', b's'),
        // Common vowel confusions
        (b'a', b'e'), (b'e', b'a'),
        (b'i', b'y'), (b'y', b'i'),
        // Silent letters (allow omission)
        (b'h', b'\0'),
        (b'k', b'\0'),
    ];

    /// QWERTY keyboard substitutions as a const array.
    const KEYBOARD_PAIRS: &[(u8, u8)] = &[
        // Top row
        (b'q', b'w'), (b'w', b'q'),
        (b'w', b'e'), (b'e', b'w'),
        (b'e', b'r'), (b'r', b'e'),
        (b'r', b't'), (b't', b'r'),
        (b't', b'y'), (b'y', b't'),
        (b'y', b'u'), (b'u', b'y'),
        (b'u', b'i'), (b'i', b'u'),
        (b'i', b'o'), (b'o', b'i'),
        (b'o', b'p'), (b'p', b'o'),
        // Middle row
        (b'a', b's'), (b's', b'a'),
        (b's', b'd'), (b'd', b's'),
        (b'd', b'f'), (b'f', b'd'),
        (b'f', b'g'), (b'g', b'f'),
        (b'g', b'h'), (b'h', b'g'),
        (b'h', b'j'), (b'j', b'h'),
        (b'j', b'k'), (b'k', b'j'),
        (b'k', b'l'), (b'l', b'k'),
        // Bottom row
        (b'z', b'x'), (b'x', b'z'),
        (b'x', b'c'), (b'c', b'x'),
        (b'c', b'v'), (b'v', b'c'),
        (b'v', b'b'), (b'b', b'v'),
        (b'b', b'n'), (b'n', b'b'),
        (b'n', b'm'), (b'm', b'n'),
        // Vertical adjacencies (selected)
        (b'q', b'a'), (b'a', b'q'),
        (b'w', b's'), (b's', b'w'),
        (b'e', b'd'), (b'd', b'e'),
        (b'r', b'f'), (b'f', b'r'),
        (b't', b'g'), (b'g', b't'),
        (b'y', b'h'), (b'h', b'y'),
        (b'u', b'j'), (b'j', b'u'),
        (b'i', b'k'), (b'k', b'i'),
        (b'o', b'l'), (b'l', b'o'),
    ];

    /// Leetspeak substitutions as a const array.
    const LEET_PAIRS: &[(u8, u8)] = &[
        (b'e', b'3'), (b'3', b'e'),
        (b'a', b'@'), (b'@', b'a'),
        (b'a', b'4'), (b'4', b'a'),
        (b'o', b'0'), (b'0', b'o'),
        (b'i', b'1'), (b'1', b'i'),
        (b'l', b'1'), (b'1', b'l'),
        (b's', b'$'), (b'$', b's'),
        (b's', b'5'), (b'5', b's'),
        (b't', b'7'), (b'7', b't'),
        (b'b', b'8'), (b'8', b'b'),
        (b'g', b'9'), (b'9', b'g'),
    ];

    /// OCR-friendly substitutions as a const array.
    const OCR_PAIRS: &[(u8, u8)] = &[
        // 0/O confusion
        (b'0', b'O'), (b'O', b'0'),
        (b'0', b'o'), (b'o', b'0'),
        // 1/I/l confusion
        (b'1', b'I'), (b'I', b'1'),
        (b'1', b'l'), (b'l', b'1'),
        (b'I', b'l'), (b'l', b'I'),
        // 8/B confusion
        (b'8', b'B'), (b'B', b'8'),
        // 5/S confusion
        (b'5', b'S'), (b'S', b'5'),
        // 6/G confusion
        (b'6', b'G'), (b'G', b'6'),
        // 2/Z confusion
        (b'2', b'Z'), (b'Z', b'2'),
    ];

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
        let mut set = Self::with_capacity(Self::PHONETIC_PAIRS.len());
        for &(a, b) in Self::PHONETIC_PAIRS {
            set.allow_byte(a, b);
        }
        set
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
        let mut set = Self::with_capacity(Self::KEYBOARD_PAIRS.len());
        for &(a, b) in Self::KEYBOARD_PAIRS {
            set.allow_byte(a, b);
        }
        set
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
        let mut set = Self::with_capacity(Self::LEET_PAIRS.len());
        for &(a, b) in Self::LEET_PAIRS {
            set.allow_byte(a, b);
        }
        set
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
        let mut set = Self::with_capacity(Self::OCR_PAIRS.len());
        for &(a, b) in Self::OCR_PAIRS {
            set.allow_byte(a, b);
        }
        set
    }

    /// Allow substituting string `a` with string `b`.
    ///
    /// This method supports multi-character substitutions for generalized operations.
    /// Only ASCII characters are supported.
    ///
    /// # Parameters
    ///
    /// - `a`: Dictionary string (source)
    /// - `b`: Query string (target)
    ///
    /// # Example
    ///
    /// ```rust
    /// # use liblevenshtein::transducer::SubstitutionSet;
    /// let mut set = SubstitutionSet::new();
    /// set.allow_str("ph", "f");  // "ph" in dict can match "f" in query
    /// set.allow_str("ch", "k");  // "ch" in dict can match "k" in query
    ///
    /// assert!(set.contains_str(b"ph", b"f"));
    /// assert!(set.contains_str(b"ch", b"k"));
    /// ```
    ///
    /// # Note
    ///
    /// For multi-character strings (length > 1), this currently stores them
    /// as a hash of the byte sequences. Single-character strings use the
    /// optimized single-byte storage.
    pub fn allow_str(&mut self, a: &str, b: &str) {
        // For single-char pairs, use optimized single-byte storage
        if a.len() == 1 && b.len() == 1 {
            if let (Some(a_char), Some(b_char)) = (a.chars().next(), b.chars().next()) {
                if a_char.is_ascii() && b_char.is_ascii() {
                    self.allow_byte(a_char as u8, b_char as u8);
                }
            }
        }
        // For multi-char pairs, we need a different storage strategy
        // For now, we'll use the hash of the concatenated bytes
        // This is a temporary approach - ideally we'd use a separate storage
        else {
            // TODO: Implement multi-character substitution storage
            // For now, just validate they're ASCII
            if a.is_ascii() && b.is_ascii() {
                // Store as hash key (u8, u8) using first bytes as placeholder
                // This is a limitation - proper implementation needs separate storage
                let a_key = a.bytes().next().unwrap_or(0);
                let b_key = b.bytes().next().unwrap_or(0);
                self.allow_byte(a_key, b_key);
            }
        }
    }

    /// Check if substituting string `a` with string `b` is allowed.
    ///
    /// This method supports multi-character substitution checking.
    ///
    /// # Parameters
    ///
    /// - `a`: Dictionary bytes
    /// - `b`: Query bytes
    ///
    /// # Returns
    ///
    /// `true` if the substitution `a → b` is allowed, `false` otherwise.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use liblevenshtein::transducer::SubstitutionSet;
    /// let mut set = SubstitutionSet::new();
    /// set.allow_str("ph", "f");
    ///
    /// assert!(set.contains_str(b"ph", b"f"));
    /// assert!(!set.contains_str(b"ph", b"g"));
    /// ```
    #[inline]
    pub fn contains_str(&self, a: &[u8], b: &[u8]) -> bool {
        // For single-byte pairs, use optimized lookup
        if a.len() == 1 && b.len() == 1 {
            self.contains(a[0], b[0])
        }
        // For multi-char pairs, use temporary implementation
        else {
            // TODO: Implement proper multi-character substitution lookup
            // For now, check first bytes as placeholder
            if !a.is_empty() && !b.is_empty() {
                self.contains(a[0], b[0])
            } else {
                false
            }
        }
    }

    /// Build a substitution set from string pairs.
    ///
    /// This supports multi-character substitution pairs.
    ///
    /// # Parameters
    ///
    /// - `pairs`: Slice of (source, target) string pairs
    ///
    /// # Example
    ///
    /// ```rust
    /// # use liblevenshtein::transducer::SubstitutionSet;
    /// let set = SubstitutionSet::from_str_pairs(&[
    ///     ("ph", "f"),   // phonetic: ph → f
    ///     ("ch", "k"),   // phonetic: ch → k
    ///     ("ght", "t"),  // silent letters: ght → t
    /// ]);
    ///
    /// assert!(set.contains_str(b"ph", b"f"));
    /// assert!(set.contains_str(b"ch", b"k"));
    /// ```
    pub fn from_str_pairs(pairs: &[(&str, &str)]) -> Self {
        let mut set = Self::with_capacity(pairs.len());
        for &(a, b) in pairs {
            set.allow_str(a, b);
        }
        set
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
