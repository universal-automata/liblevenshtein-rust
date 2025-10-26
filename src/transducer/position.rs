//! Position in the Levenshtein automaton.

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

    /// Check if this position could subsume another position.
    ///
    /// Position `p1` subsumes `p2` if all candidates reachable from `p2`
    /// are also reachable from `p1`. This allows pruning redundant states.
    ///
    /// For Standard algorithm: `p1` subsumes `p2` if:
    /// - `p1.term_index == p2.term_index` (same query position)
    /// - `p1.num_errors <= p2.num_errors` (fewer or equal errors)
    ///
    /// The previous rule (term_index >= other.term_index) was too aggressive
    /// and caused incorrect pruning. Positions at different query indices
    /// can match different dictionary characters.
    pub fn subsumes(&self, other: &Position) -> bool {
        // Only subsume if at the SAME query position with fewer/equal errors
        if self.term_index == other.term_index && self.num_errors <= other.num_errors {
            // Special positions handled differently by algorithm
            if self.is_special == other.is_special {
                return true;
            }
        }
        false
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
    fn test_position_subsumption() {
        // Corrected subsumption: only at SAME query position
        // (5, 2) should subsume (5, 3) - same position, fewer errors
        let p1 = Position::new(5, 2);
        let p2 = Position::new(5, 3);
        assert!(p1.subsumes(&p2), "p1(5,2) should subsume p2(5,3)");

        // (5, 2) should NOT subsume (4, 3) - different positions
        let p3 = Position::new(5, 2);
        let p4 = Position::new(4, 3);
        assert!(
            !p3.subsumes(&p4),
            "p3(5,2) should NOT subsume p4(4,3) - different positions"
        );

        // (3, 2) should subsume (3, 2) - same position and errors
        let p5 = Position::new(3, 2);
        let p6 = Position::new(3, 2);
        assert!(p5.subsumes(&p6), "p5(3,2) should subsume p6(3,2)");

        // (3, 3) should NOT subsume (5, 2) - different positions
        let p7 = Position::new(3, 3);
        let p8 = Position::new(5, 2);
        assert!(!p7.subsumes(&p8), "p7(3,3) should NOT subsume p8(5,2)");
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
