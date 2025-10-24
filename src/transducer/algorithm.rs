//! Levenshtein distance algorithm variants.

/// Levenshtein distance algorithm type.
///
/// Different algorithms support different edit operations and are
/// suited for different use cases.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Algorithm {
    /// Standard Levenshtein distance.
    ///
    /// Supports three edit operations:
    /// - Insert: add a character
    /// - Delete: remove a character
    /// - Substitute: replace one character with another
    ///
    /// This is the classic edit distance metric.
    Standard,

    /// Levenshtein distance with transposition.
    ///
    /// Extends Standard with:
    /// - Transpose: swap two adjacent characters
    ///
    /// Useful for catching common typos where adjacent letters are swapped.
    Transposition,

    /// Levenshtein distance with merge and split operations.
    ///
    /// Extends Standard with:
    /// - Merge: combine two characters into one
    /// - Split: expand one character into two
    ///
    /// Useful for OCR errors and other character-level transformations.
    MergeAndSplit,
}

impl Algorithm {
    /// Get a human-readable name for this algorithm
    pub fn name(&self) -> &'static str {
        match self {
            Algorithm::Standard => "standard",
            Algorithm::Transposition => "transposition",
            Algorithm::MergeAndSplit => "merge-and-split",
        }
    }

    /// Check if this algorithm supports transposition operations
    pub fn supports_transposition(&self) -> bool {
        matches!(self, Algorithm::Transposition | Algorithm::MergeAndSplit)
    }

    /// Check if this algorithm supports merge/split operations
    pub fn supports_merge_split(&self) -> bool {
        matches!(self, Algorithm::MergeAndSplit)
    }
}

impl Default for Algorithm {
    fn default() -> Self {
        Algorithm::Standard
    }
}
