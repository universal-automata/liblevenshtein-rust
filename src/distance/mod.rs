//! Distance metric implementations.
//!
//! This module provides various Levenshtein distance implementations
//! for direct distance computation between two strings.

/// Compute standard Levenshtein distance between two strings.
///
/// Uses dynamic programming to compute the minimum number of
/// single-character edits (insertions, deletions, substitutions)
/// required to transform `source` into `target`.
///
/// # Example
///
/// ```rust
/// use liblevenshtein::distance::standard_distance;
///
/// assert_eq!(standard_distance("kitten", "sitting"), 3);
/// assert_eq!(standard_distance("test", "test"), 0);
/// ```
pub fn standard_distance(source: &str, target: &str) -> usize {
    let source_chars: Vec<char> = source.chars().collect();
    let target_chars: Vec<char> = target.chars().collect();

    let m = source_chars.len();
    let n = target_chars.len();

    // Handle edge cases
    if m == 0 {
        return n;
    }
    if n == 0 {
        return m;
    }

    // Use space-optimized version (two rows instead of full matrix)
    let mut prev_row = vec![0; n + 1];
    let mut curr_row = vec![0; n + 1];

    // Initialize first row
    for j in 0..=n {
        prev_row[j] = j;
    }

    // Fill the matrix
    for i in 1..=m {
        curr_row[0] = i;

        for j in 1..=n {
            let cost = if source_chars[i - 1] == target_chars[j - 1] {
                0
            } else {
                1
            };

            curr_row[j] = (prev_row[j] + 1) // deletion
                .min(curr_row[j - 1] + 1) // insertion
                .min(prev_row[j - 1] + cost); // substitution
        }

        std::mem::swap(&mut prev_row, &mut curr_row);
    }

    prev_row[n]
}

/// Compute Levenshtein distance with transposition support.
///
/// Extends standard Levenshtein distance to also consider transposition
/// (swapping two adjacent characters) as a single edit operation.
/// This is also known as Damerau-Levenshtein distance.
///
/// # Example
///
/// ```rust
/// use liblevenshtein::distance::transposition_distance;
///
/// assert_eq!(transposition_distance("ab", "ba"), 1); // One transposition
/// assert_eq!(transposition_distance("test", "tset"), 1); // One transposition
/// ```
pub fn transposition_distance(source: &str, target: &str) -> usize {
    let source_chars: Vec<char> = source.chars().collect();
    let target_chars: Vec<char> = target.chars().collect();

    let m = source_chars.len();
    let n = target_chars.len();

    if m == 0 {
        return n;
    }
    if n == 0 {
        return m;
    }

    // Need three rows for transposition
    let mut two_ago = vec![0; n + 1];
    let mut prev_row = vec![0; n + 1];
    let mut curr_row = vec![0; n + 1];

    // Initialize first row
    for j in 0..=n {
        prev_row[j] = j;
    }

    // Fill the matrix
    for i in 1..=m {
        curr_row[0] = i;

        for j in 1..=n {
            let cost = if source_chars[i - 1] == target_chars[j - 1] {
                0
            } else {
                1
            };

            curr_row[j] = (prev_row[j] + 1) // deletion
                .min(curr_row[j - 1] + 1) // insertion
                .min(prev_row[j - 1] + cost); // substitution

            // Check for transposition
            if i > 1
                && j > 1
                && source_chars[i - 1] == target_chars[j - 2]
                && source_chars[i - 2] == target_chars[j - 1]
            {
                curr_row[j] = curr_row[j].min(two_ago[j - 2] + 1);
            }
        }

        // Rotate rows
        std::mem::swap(&mut two_ago, &mut prev_row);
        std::mem::swap(&mut prev_row, &mut curr_row);
    }

    prev_row[n]
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_standard_distance_identical() {
        assert_eq!(standard_distance("test", "test"), 0);
        assert_eq!(standard_distance("", ""), 0);
    }

    #[test]
    fn test_standard_distance_empty() {
        assert_eq!(standard_distance("", "test"), 4);
        assert_eq!(standard_distance("test", ""), 4);
    }

    #[test]
    fn test_standard_distance_basic() {
        assert_eq!(standard_distance("kitten", "sitting"), 3);
        assert_eq!(standard_distance("saturday", "sunday"), 3);
        assert_eq!(standard_distance("test", "best"), 1);
    }

    #[test]
    fn test_transposition_distance() {
        assert_eq!(transposition_distance("ab", "ba"), 1);
        assert_eq!(transposition_distance("test", "tset"), 1);
        assert_eq!(transposition_distance("abc", "acb"), 1);
    }

    #[test]
    fn test_transposition_vs_standard() {
        // Transposition should be cheaper than standard for swaps
        let trans_dist = transposition_distance("test", "tset");
        let std_dist = standard_distance("test", "tset");

        assert_eq!(trans_dist, 1);
        assert_eq!(std_dist, 2); // Standard requires 2 substitutions
    }
}
