//! Automaton state (collection of positions).

use super::position::Position;
use std::collections::BTreeSet;

/// A state in the Levenshtein automaton.
///
/// A state is a collection of positions, maintained in sorted order.
/// Duplicate and subsumed positions are automatically removed to
/// minimize state space.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct State {
    /// Positions in this state, maintained in sorted order
    positions: Vec<Position>,
}

impl State {
    /// Create a new empty state
    pub fn new() -> Self {
        Self {
            positions: Vec::new(),
        }
    }

    /// Create a state with a single position
    pub fn single(position: Position) -> Self {
        Self {
            positions: vec![position],
        }
    }

    /// Create a state from a vector of positions
    ///
    /// Positions will be sorted and deduplicated
    pub fn from_positions(mut positions: Vec<Position>) -> Self {
        positions.sort();
        positions.dedup();
        Self { positions }
    }

    /// Add a position to this state
    ///
    /// Maintains sorted order and removes subsumed positions
    pub fn insert(&mut self, position: Position) {
        // Check if this position is subsumed by an existing one
        for existing in &self.positions {
            if existing.subsumes(&position) {
                return; // Already covered by existing position
            }
        }

        // Remove any positions that this new position subsumes
        self.positions.retain(|p| !position.subsumes(p));

        // Insert in sorted position
        let insert_pos = self
            .positions
            .binary_search(&position)
            .unwrap_or_else(|pos| pos);
        self.positions.insert(insert_pos, position);
    }

    /// Merge another state into this one
    pub fn merge(&mut self, other: &State) {
        for position in &other.positions {
            self.insert(*position);
        }
    }

    /// Get the head (first) position
    pub fn head(&self) -> Option<&Position> {
        self.positions.first()
    }

    /// Get all positions
    #[inline(always)]
    pub fn positions(&self) -> &[Position] {
        &self.positions
    }

    /// Check if this state is empty
    #[inline(always)]
    pub fn is_empty(&self) -> bool {
        self.positions.is_empty()
    }

    /// Get the number of positions
    #[inline(always)]
    pub fn len(&self) -> usize {
        self.positions.len()
    }

    /// Iterate over positions
    pub fn iter(&self) -> impl Iterator<Item = &Position> {
        self.positions.iter()
    }

    /// Clear all positions from this state.
    ///
    /// This keeps the underlying Vec allocation, making it efficient for reuse
    /// in a StatePool. After clearing, the state will be empty but retain its
    /// capacity.
    ///
    /// # Performance
    ///
    /// - Time: O(1) - just sets Vec length to 0
    /// - Memory: Vec capacity is preserved for reuse
    #[inline]
    pub fn clear(&mut self) {
        self.positions.clear();
    }

    /// Copy all positions from another state into this one.
    ///
    /// This clears the current state and then copies all positions from the
    /// source state. The source state is unchanged.
    ///
    /// # Performance
    ///
    /// - Time: O(n) where n is the number of positions in source
    /// - Memory: Reuses this state's Vec allocation if capacity is sufficient
    /// - Position is Copy, so this is a fast memcpy of the positions
    #[inline]
    pub fn copy_from(&mut self, other: &State) {
        self.positions.clear();
        self.positions.reserve(other.positions.len());
        for pos in &other.positions {
            self.positions.push(*pos); // Copy, not clone
        }
    }

    /// Get the minimum edit distance in this state
    ///
    /// Returns the smallest `num_errors` among all positions
    #[inline]
    pub fn min_distance(&self) -> Option<usize> {
        // Optimization: positions are sorted, and since we maintain subsumption,
        // the first position often has the minimum errors. Check it first.
        self.positions.first().map(|first| {
            // Fast path: if we only have one position, return it immediately
            if self.positions.len() == 1 {
                return first.num_errors;
            }

            // Otherwise, find the minimum
            self.positions.iter().map(|p| p.num_errors).min().unwrap()
        })
    }

    /// Infer the edit distance for a final state
    ///
    /// For a final state (at end of dictionary term), infer the
    /// distance based on remaining characters in query term
    #[inline]
    pub fn infer_distance(&self, query_length: usize) -> Option<usize> {
        // Fast path: single position (common case)
        if self.positions.len() == 1 {
            let p = &self.positions[0];
            let remaining = query_length.saturating_sub(p.term_index);
            return Some(p.num_errors + remaining);
        }

        // General case: find minimum across all positions
        self.positions
            .iter()
            .map(|p| {
                // Distance is errors already accumulated plus remaining chars
                let remaining = query_length.saturating_sub(p.term_index);
                p.num_errors + remaining
            })
            .min()
    }

    /// Infer the edit distance for prefix matching
    ///
    /// For prefix matching, we only care if we've consumed the entire query
    /// (allowing the dictionary term to be longer). Returns the minimum number
    /// of errors among positions that have consumed >= query_length characters.
    ///
    /// Returns None if no position has consumed the full query yet.
    #[inline]
    pub fn infer_prefix_distance(&self, query_length: usize) -> Option<usize> {
        // Fast path: single position
        if self.positions.len() == 1 {
            let p = &self.positions[0];
            return if p.term_index >= query_length {
                Some(p.num_errors)
            } else {
                None
            };
        }

        // General case: find minimum among positions that consumed the full query
        self.positions
            .iter()
            .filter(|p| p.term_index >= query_length)
            .map(|p| p.num_errors)
            .min()
    }
}

impl Default for State {
    fn default() -> Self {
        Self::new()
    }
}

impl FromIterator<Position> for State {
    fn from_iter<T: IntoIterator<Item = Position>>(iter: T) -> Self {
        let positions: BTreeSet<Position> = iter.into_iter().collect();
        Self::from_positions(positions.into_iter().collect())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_state_creation() {
        let state = State::new();
        assert!(state.is_empty());
        assert_eq!(state.len(), 0);
    }

    #[test]
    fn test_state_single_position() {
        let pos = Position::new(3, 1);
        let state = State::single(pos.clone());
        assert_eq!(state.len(), 1);
        assert_eq!(state.head(), Some(&pos));
    }

    #[test]
    fn test_state_insert_maintains_order() {
        let mut state = State::new();
        // Insert positions at different indices (won't subsume each other with corrected logic)
        state.insert(Position::new(2, 2));
        state.insert(Position::new(3, 1));
        state.insert(Position::new(4, 2));

        let positions: Vec<_> = state.positions().to_vec();
        // With corrected subsumption (same position only), all 3 remain
        assert_eq!(positions.len(), 3);
        assert!(positions[0] < positions[1]);
        assert!(positions[1] < positions[2]);
    }

    #[test]
    fn test_state_subsumption() {
        let mut state = State::new();
        state.insert(Position::new(5, 2));
        assert_eq!(state.len(), 1);

        // Try to insert a position at a different index (NOT subsumed with corrected logic)
        state.insert(Position::new(4, 3)); // Different position, so both kept
        assert_eq!(state.len(), 2, "Different positions should both be kept");

        // Insert a position at SAME index with fewer errors - should subsume
        state.insert(Position::new(5, 1)); // Subsumes (5,2) at same position
        assert_eq!(state.len(), 2, "Should have replaced (5,2) with (5,1)");

        // Verify (5,1) is in the state
        let pos_at_5 = state
            .positions()
            .iter()
            .find(|p| p.term_index == 5)
            .unwrap();
        assert_eq!(pos_at_5.num_errors, 1);
    }

    #[test]
    fn test_state_min_distance() {
        let mut state = State::new();
        state.insert(Position::new(3, 2));
        state.insert(Position::new(4, 1));
        state.insert(Position::new(5, 3));

        assert_eq!(state.min_distance(), Some(1));
    }

    #[test]
    fn test_state_infer_distance() {
        let mut state = State::new();
        state.insert(Position::new(3, 1)); // At position 3 with 1 error
        state.insert(Position::new(4, 2)); // At position 4 with 2 errors

        let query_length = 7;
        // Position (3,1): needs 4 more chars = 1+4=5 distance
        // Position (4,2): needs 3 more chars = 2+3=5 distance
        assert_eq!(state.infer_distance(query_length), Some(5));
    }
}
