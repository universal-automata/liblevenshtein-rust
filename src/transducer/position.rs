//! Position in the Levenshtein automaton.

use super::algorithm::Algorithm;
use std::cmp::Ordering;

/// A position in the Levenshtein automaton state.
///
/// A position represents a location `(term_index, num_errors)` in the
/// automaton, indicating we've consumed `term_index` characters from
/// the query term with `num_errors` accumulated errors.
///
/// The `is_special` flag is used by extended algorithms (Transposition,
/// MergeAndSplit) to track additional state.
///
/// # Performance
///
/// Position is `Copy` (17 bytes: 2 usizes + bool) to eliminate allocation
/// overhead when copying positions during state transitions. This reduces
/// the overhead of Position cloning from ~7.44% to minimal bitwise copies.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Position {
    /// Index into the query term (characters consumed)
    pub term_index: usize,

    /// Number of accumulated edit operations
    pub num_errors: usize,

    /// Special flag for extended algorithm states
    ///
    /// - For Transposition: indicates a transposition is in progress
    /// - For MergeAndSplit: indicates a merge/split operation
    pub is_special: bool,
}

impl Position {
    /// Create a new position
    #[inline(always)]
    pub fn new(term_index: usize, num_errors: usize) -> Self {
        Self {
            term_index,
            num_errors,
            is_special: false,
        }
    }

    /// Create a new special position (for extended algorithms)
    #[inline(always)]
    pub fn new_special(term_index: usize, num_errors: usize) -> Self {
        Self {
            term_index,
            num_errors,
            is_special: true,
        }
    }

    /// Check if this position subsumes another position.
    ///
    /// Position `p1` subsumes `p2` if all candidates reachable from `p2`
    /// are also reachable from `p1`. This allows pruning redundant states.
    ///
    /// The subsumption logic differs by algorithm:
    ///
    /// # Standard Algorithm
    /// `p1` at (i, e) subsumes `p2` at (j, f) if:
    /// - `|i - j| <= (f - e)`
    ///
    /// # Transposition Algorithm
    /// Complex logic considering special positions (transposition states):
    /// - If both special: must be at same position
    /// - If lhs special, rhs not: requires rhs at max distance and same position
    /// - If rhs special: adjusted index difference formula
    /// - Otherwise: standard formula
    ///
    /// # MergeAndSplit Algorithm
    /// - If lhs special but not rhs: cannot subsume
    /// - Otherwise: standard formula
    ///
    /// Based on C++ implementation in subsumes.cpp
    ///
    /// # Parameters
    /// - `query_length`: Length of the query term (n in C++/Java code)
    pub fn subsumes(&self, other: &Position, algorithm: Algorithm, query_length: usize) -> bool {
        let i = self.term_index;
        let e = self.num_errors;
        let s = self.is_special;

        let j = other.term_index;
        let f = other.num_errors;
        let t = other.is_special;

        // Must have fewer or equal errors to subsume
        if e > f {
            return false;
        }

        match algorithm {
            Algorithm::Standard => {
                // Standard algorithm: |i - j| <= (f - e)
                let index_diff = i.abs_diff(j);
                let error_diff = f - e;
                index_diff <= error_diff
            }

            Algorithm::Transposition => {
                // From C++ subsumes.cpp lines 15-39
                if s {
                    if t {
                        // Both special: must be at same position
                        return i == j;
                    }
                    // lhs special, rhs not: requires rhs at query length and same position
                    // The C++ checks (f == n) && (i == j), where n is query length
                    return (f == query_length) && (i == j);
                }

                if t {
                    // CRITICAL FIX: Special positions (transposition-in-progress) represent
                    // fundamentally different computational paths than normal positions.
                    // A normal position should NEVER subsume a special position, as this
                    // would prematurely terminate exploration of valid transposition paths.
                    //
                    // Example bug case: Query "ab", dict "ba"
                    //   (1,1,false) was incorrectly subsuming (0,1,true)
                    //   The special position is needed to complete the transposition!
                    //
                    // This appears to be a bug in the original Java/C++ implementations
                    // that was not caught by their test suites.
                    if !s {
                        // lhs is normal, rhs is special → cannot subsume
                        return false;
                    }

                    // Both are special: use adjusted formula
                    // rhs is special: adjusted formula
                    // ((j < i) ? (i - j - 1) : (j - i + 1)) <= (f - e)
                    let adjusted_diff = if j < i {
                        i.saturating_sub(j).saturating_sub(1)
                    } else {
                        j.saturating_sub(i) + 1
                    };
                    return adjusted_diff <= (f - e);
                }

                // Neither special: standard formula
                let index_diff = i.abs_diff(j);
                let error_diff = f - e;
                index_diff <= error_diff
            }

            Algorithm::MergeAndSplit => {
                // From C++ subsumes.cpp lines 41-56
                if s && !t {
                    // lhs special but not rhs: cannot subsume
                    return false;
                }

                // Otherwise: standard formula
                let index_diff = i.abs_diff(j);
                let error_diff = f - e;
                index_diff <= error_diff
            }
        }
    }

    /// Compare positions for sorting (lexicographic order)
    ///
    /// Order: term_index (asc), then num_errors (asc), then is_special (false < true)
    pub fn compare(&self, other: &Position) -> Ordering {
        self.term_index
            .cmp(&other.term_index)
            .then_with(|| self.num_errors.cmp(&other.num_errors))
            .then_with(|| self.is_special.cmp(&other.is_special))
    }
}

impl PartialOrd for Position {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Position {
    fn cmp(&self, other: &Self) -> Ordering {
        self.compare(other)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_position_creation() {
        let pos = Position::new(5, 2);
        assert_eq!(pos.term_index, 5);
        assert_eq!(pos.num_errors, 2);
        assert!(!pos.is_special);
    }

    #[test]
    fn test_position_special() {
        let pos = Position::new_special(3, 1);
        assert!(pos.is_special);
    }

    #[test]
    fn test_position_subsumption_standard() {
        // Standard algorithm subsumption: |i - j| <= (f - e)
        let max_distance = 3; // Max distance for tests

        // (5, 2) should subsume (5, 3) - same position, fewer errors
        // |5-5| = 0 <= (3-2) = 1 ✓
        let p1 = Position::new(5, 2);
        let p2 = Position::new(5, 3);
        assert!(
            p1.subsumes(&p2, Algorithm::Standard, max_distance),
            "p1(5,2) should subsume p2(5,3)"
        );

        // (5, 2) SHOULD subsume (4, 3) - |5-4| = 1 <= (3-2) = 1
        let p3 = Position::new(5, 2);
        let p4 = Position::new(4, 3);
        assert!(
            p3.subsumes(&p4, Algorithm::Standard, max_distance),
            "p3(5,2) should subsume p4(4,3) per C++ logic"
        );

        // (3, 2) should subsume (3, 2) - same position and errors
        let p5 = Position::new(3, 2);
        let p6 = Position::new(3, 2);
        assert!(
            p5.subsumes(&p6, Algorithm::Standard, max_distance),
            "p5(3,2) should subsume p6(3,2)"
        );

        // (3, 3) should NOT subsume (5, 2) - |3-5| = 2 > (2-3) = -1 (and e > f)
        let p7 = Position::new(3, 3);
        let p8 = Position::new(5, 2);
        assert!(
            !p7.subsumes(&p8, Algorithm::Standard, max_distance),
            "p7(3,3) should NOT subsume p8(5,2)"
        );
    }

    #[test]
    fn test_position_subsumption_transposition() {
        // Transposition subsumption tests
        let max_distance = 3; // Max distance for tests

        // Both special: must be at same position
        let p1 = Position::new_special(5, 2);
        let p2 = Position::new_special(5, 3);
        assert!(
            p1.subsumes(&p2, Algorithm::Transposition, max_distance),
            "special(5,2) should subsume special(5,3) - same position"
        );

        let p3 = Position::new_special(5, 2);
        let p4 = Position::new_special(6, 3);
        assert!(
            !p3.subsumes(&p4, Algorithm::Transposition, max_distance),
            "special(5,2) should NOT subsume special(6,3) - different position"
        );

        // lhs special, rhs not: same position check, requires f == max_distance
        let p5 = Position::new_special(5, 2);
        let p6 = Position::new(5, 3); // f=3, max_distance=3, i=j=5 → should subsume
        assert!(
            p5.subsumes(&p6, Algorithm::Transposition, max_distance),
            "special(5,2) should subsume normal(5,3) when f==max_distance"
        );

        // rhs special: adjusted formula - ((j < i) ? (i - j - 1) : (j - i + 1)) <= (f - e)
        let p7 = Position::new(5, 2);
        let p8 = Position::new_special(4, 3); // j=4, i=5: (5-4-1)=0 <= (3-2)=1 ✓
        assert!(
            p7.subsumes(&p8, Algorithm::Transposition, max_distance),
            "normal(5,2) should subsume special(4,3)"
        );

        let p9 = Position::new(5, 2);
        let p10 = Position::new_special(6, 3); // j=6, i=5: (6-5+1)=2 > (3-2)=1 ✗
        assert!(
            !p9.subsumes(&p10, Algorithm::Transposition, max_distance),
            "normal(5,2) should NOT subsume special(6,3)"
        );

        // Neither special: standard formula
        let p11 = Position::new(5, 2);
        let p12 = Position::new(4, 3);
        assert!(
            p11.subsumes(&p12, Algorithm::Transposition, max_distance),
            "normal(5,2) should subsume normal(4,3) - standard formula"
        );
    }

    #[test]
    fn test_position_subsumption_merge_split() {
        // MergeAndSplit subsumption tests
        let max_distance = 3; // Max distance for tests

        // lhs special but not rhs: cannot subsume
        let p1 = Position::new_special(5, 2);
        let p2 = Position::new(5, 3);
        assert!(
            !p1.subsumes(&p2, Algorithm::MergeAndSplit, max_distance),
            "special(5,2) should NOT subsume normal(5,3) for MergeAndSplit"
        );

        // Both special or both normal: standard formula
        let p3 = Position::new(5, 2);
        let p4 = Position::new(4, 3);
        assert!(
            p3.subsumes(&p4, Algorithm::MergeAndSplit, max_distance),
            "normal(5,2) should subsume normal(4,3)"
        );

        let p5 = Position::new_special(5, 2);
        let p6 = Position::new_special(5, 3);
        assert!(
            p5.subsumes(&p6, Algorithm::MergeAndSplit, max_distance),
            "special(5,2) should subsume special(5,3)"
        );
    }

    #[test]
    fn test_position_ordering() {
        let p1 = Position::new(3, 1);
        let p2 = Position::new(3, 2);
        let p3 = Position::new(4, 1);

        assert!(p1 < p2);
        assert!(p1 < p3);
        assert!(p2 < p3);
    }
}
