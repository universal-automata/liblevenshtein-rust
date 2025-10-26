//! Levenshtein distance algorithm variants.

/// Levenshtein distance algorithm type.
///
/// Different algorithms support different edit operations and are
/// suited for different use cases.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(
    feature = "serialization",
    derive(serde::Serialize, serde::Deserialize)
)]
#[derive(Default)]
pub enum Algorithm {
    /// Standard Levenshtein distance.
    ///
    /// Supports three edit operations:
    /// - Insert: add a character
    /// - Delete: remove a character
    /// - Substitute: replace one character with another
    ///
    /// This is the classic edit distance metric.
    #[default]
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

impl std::fmt::Display for Algorithm {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(self.name())
    }
}

impl std::str::FromStr for Algorithm {
    type Err = String;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s.to_lowercase().as_str() {
            "standard" => Ok(Algorithm::Standard),
            "transposition" | "trans" => Ok(Algorithm::Transposition),
            "merge-and-split" | "mergesplit" | "merge" => Ok(Algorithm::MergeAndSplit),
            _ => Err(format!(
                "Unknown algorithm: {}. Valid options: standard, transposition, merge-and-split",
                s
            )),
        }
    }
}
