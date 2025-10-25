//! State transition logic for Levenshtein automata.

use super::{Algorithm, Position, State, StatePool};
use smallvec::SmallVec;

/// Compute the characteristic vector for a position in the query.
///
/// The characteristic vector indicates which characters in a window
/// of the query term match the given dictionary character.
///
/// # Arguments
/// * `dict_char` - Character from the dictionary edge
/// * `query` - Query term bytes
/// * `window_size` - Size of the window (typically max_distance + 1)
/// * `offset` - Base offset in query
/// * `buffer` - Stack-allocated buffer to write results into
///
/// # Returns
/// Slice of booleans indicating matches at each position in window.
/// Uses stack-allocated array (max 8 elements) to avoid heap allocations.
#[inline]
fn characteristic_vector<'a>(
    dict_char: u8,
    query: &[u8],
    window_size: usize,
    offset: usize,
    buffer: &'a mut [bool; 8],
) -> &'a [bool] {
    // Most queries use max_distance ≤ 7, so window_size ≤ 8
    let len = window_size.min(8);
    for i in 0..len {
        let query_idx = offset + i;
        buffer[i] = query_idx < query.len() && query[query_idx] == dict_char;
    }
    &buffer[..len]
}

/// Transition a position given a characteristic vector.
///
/// Computes all possible next positions from the current position
/// after consuming a dictionary character, considering the query
/// term through the characteristic vector.
///
/// # Standard Algorithm
///
/// From position `(i, e)` (term_index=i, num_errors=e), we can reach:
/// - `(i+1, e)` if query[i] matches dict_char (no error)
/// - `(i+1, e+1)` via substitution (if different)
/// - `(i, e+1)` via insertion (dictionary char, no query advance)
/// - `(i+1, e+1)` via deletion (skip query char)
///
/// The characteristic vector tells us whether query[offset+k] matches
/// for k in [0..window_size).
///
/// # Prefix Mode
///
/// When `prefix_mode` is true, characters beyond query_length are treated
/// as free matches (no errors added), enabling autocomplete/prefix matching.
#[inline]
pub fn transition_position(
    position: &Position,
    characteristic_vector: &[bool],
    query_length: usize,
    max_distance: usize,
    algorithm: Algorithm,
    prefix_mode: bool,
) -> SmallVec<[Position; 4]> {
    match algorithm {
        Algorithm::Standard => transition_standard(position, characteristic_vector, query_length, max_distance, prefix_mode),
        Algorithm::Transposition => transition_transposition(position, characteristic_vector, query_length, max_distance, prefix_mode),
        Algorithm::MergeAndSplit => transition_merge_split(position, characteristic_vector, query_length, max_distance, prefix_mode),
    }
}

/// Standard algorithm transition (insert, delete, substitute)
///
/// Returns SmallVec to avoid heap allocations for small result sets.
/// Most transitions produce 2-3 positions, so we stack-allocate up to 4.
///
/// # Prefix Matching Support
///
/// When `prefix_mode` is true and term_index >= query_length, additional dictionary
/// characters are treated as free matches, keeping the position "stuck" at query_length
/// with the same error count.
fn transition_standard(
    position: &Position,
    cv: &[bool],
    query_length: usize,
    max_distance: usize,
    prefix_mode: bool,
) -> SmallVec<[Position; 4]> {
    let mut next = SmallVec::new();
    let i = position.term_index;
    let e = position.num_errors;

    // Prefix matching: if enabled and we've consumed the full query, treat any character as a free match
    if prefix_mode && i >= query_length {
        // Keep position at query_length, don't add errors
        next.push(Position::new(i, e));
        return next;
    }

    // Check cv[0] since the CV is already offset-adjusted
    // cv[0] corresponds to query[position.term_index]
    if !cv.is_empty() {
        if cv[0] {
            // Match: advance position without error
            next.push(Position::new(i + 1, e));
        } else if e < max_distance {
            // Substitution: advance position with error
            next.push(Position::new(i + 1, e + 1));
        }
    }

    // Insertion: consume dictionary char without advancing query position
    // This handles the case where the dictionary has an extra character
    if e < max_distance {
        next.push(Position::new(i, e + 1));
    }

    // NOTE: Deletion (skipping query characters) is handled by having multiple
    // positions in the state at different query indices, not during transition.
    // The previous implementation incorrectly added (i+1, e+1) here, which
    // duplicates the substitution operation above.

    next
}

/// Transposition algorithm transition (adds swap of adjacent chars)
fn transition_transposition(
    position: &Position,
    cv: &[bool],
    query_length: usize,
    max_distance: usize,
    prefix_mode: bool,
) -> SmallVec<[Position; 4]> {
    // Start with standard transitions
    let mut next = transition_standard(position, cv, query_length, max_distance, prefix_mode);

    let i = position.term_index;
    let e = position.num_errors;

    // Add transposition transitions
    // Transposition: if we previously saw a mismatch, we might be swapping
    // This is simplified - full implementation would track previous character
    if !position.is_special && e < max_distance && i + 1 < query_length {
        // Mark as special to indicate transposition in progress
        next.push(Position::new_special(i + 1, e + 1));
    }

    next
}

/// Merge and split algorithm transition
fn transition_merge_split(
    position: &Position,
    cv: &[bool],
    query_length: usize,
    max_distance: usize,
    prefix_mode: bool,
) -> SmallVec<[Position; 4]> {
    // Start with transposition transitions (which include standard)
    let mut next = transition_transposition(position, cv, query_length, max_distance, prefix_mode);

    let i = position.term_index;
    let e = position.num_errors;

    // Add merge/split operations
    if e < max_distance {
        // Merge: combine two query chars into one dict char
        if i + 1 < query_length {
            next.push(Position::new_special(i + 2, e + 1));
        }

        // Split: expand one query char into two dict chars
        // (represented as advancing without consuming query char)
        next.push(Position::new_special(i, e + 1));
    }

    next
}

/// Compute epsilon closure: add positions reachable by deletion (skipping query chars)
/// without consuming dictionary characters.
///
/// Optimized version that modifies the state in-place to avoid cloning.
fn epsilon_closure_mut(state: &mut State, query_length: usize, max_distance: usize) {
    // Track which positions we've already processed to avoid infinite loops
    let mut to_process: SmallVec<[Position; 8]> = SmallVec::new();

    // Start with current positions
    for pos in state.positions() {
        to_process.push(pos.clone());
    }

    let mut processed = 0;
    while processed < to_process.len() {
        let position = &to_process[processed];
        processed += 1;

        // Can we delete a query character (skip to next position)?
        if position.num_errors < max_distance && position.term_index < query_length {
            let deleted = Position::new(position.term_index + 1, position.num_errors + 1);

            // Check if this is a new position
            if !to_process.contains(&deleted) {
                state.insert(deleted.clone());
                to_process.push(deleted);
            }
        }
    }
}

/// Wrapper that creates a new state and applies epsilon closure
fn epsilon_closure(state: &State, query_length: usize, max_distance: usize) -> State {
    let mut result = state.clone();
    epsilon_closure_mut(&mut result, query_length, max_distance);
    result
}

/// Compute epsilon closure from source into target state (pool-friendly).
///
/// This function copies positions from the source state into the target state
/// and then applies epsilon closure in-place. The target state is cleared first.
///
/// # Performance
///
/// This is optimized for use with StatePool:
/// - Target state's Vec allocation is reused
/// - Position is Copy, so no clone overhead
/// - Eliminates one State::clone compared to epsilon_closure()
fn epsilon_closure_into(
    source: &State,
    target: &mut State,
    query_length: usize,
    max_distance: usize,
) {
    // Copy positions from source to target
    target.copy_from(source);

    // Apply epsilon closure in-place
    epsilon_closure_mut(target, query_length, max_distance);
}

/// Transition an entire state given a dictionary character.
///
/// Computes the next state by transitioning all positions in the
/// current state and merging the results.
pub fn transition_state(
    state: &State,
    dict_char: u8,
    query: &[u8],
    max_distance: usize,
    algorithm: Algorithm,
    prefix_mode: bool,
) -> Option<State> {
    let window_size = max_distance + 1;
    let query_length = query.len();

    // First, compute epsilon closure to handle deletions
    let expanded_state = epsilon_closure(state, query_length, max_distance);

    let mut next_state = State::new();

    // Stack-allocated buffer for characteristic vector (avoids heap allocations)
    let mut cv_buffer = [false; 8];

    for position in expanded_state.positions() {
        let offset = position.term_index;
        let cv = characteristic_vector(dict_char, query, window_size, offset, &mut cv_buffer);

        let next_positions = transition_position(position, cv, query_length, max_distance, algorithm, prefix_mode);

        for next_pos in next_positions {
            next_state.insert(next_pos);
        }
    }

    if next_state.is_empty() {
        None
    } else {
        Some(next_state)
    }
}

/// Transition a state using a StatePool for allocation reuse (optimized).
///
/// This is the pool-aware version of `transition_state` that eliminates
/// State cloning overhead by reusing allocations from the pool.
///
/// # Performance
///
/// Compared to `transition_state`:
/// - Eliminates Vec allocation for expanded_state (reuses from pool)
/// - Eliminates Vec allocation for next_state (reuses from pool)
/// - Reduces State::clone overhead by ~6-10% of total runtime
///
/// # Arguments
///
/// * `state` - Current automaton state
/// * `pool` - State pool for allocation reuse
/// * `dict_char` - Dictionary character to transition on
/// * `query` - Query term bytes
/// * `max_distance` - Maximum edit distance
/// * `algorithm` - Algorithm variant (Standard, Transposition, MergeAndSplit)
/// * `prefix_mode` - Enable prefix matching (characters beyond query treated as free matches)
///
/// # Returns
///
/// The next state after transitioning, or None if no valid transitions exist.
/// The returned state is acquired from the pool (caller should release it when done).
pub fn transition_state_pooled(
    state: &State,
    pool: &mut StatePool,
    dict_char: u8,
    query: &[u8],
    max_distance: usize,
    algorithm: Algorithm,
    prefix_mode: bool,
) -> Option<State> {
    let window_size = max_distance + 1;
    let query_length = query.len();

    // Acquire a state from pool for epsilon closure (reuses allocation!)
    let mut expanded_state = pool.acquire();

    // Compute epsilon closure into the pooled state (no clone!)
    epsilon_closure_into(state, &mut expanded_state, query_length, max_distance);

    // Acquire another state from pool for next state
    let mut next_state = pool.acquire();

    // Stack-allocated buffer for characteristic vector
    let mut cv_buffer = [false; 8];

    for position in expanded_state.positions() {
        let offset = position.term_index;
        let cv = characteristic_vector(dict_char, query, window_size, offset, &mut cv_buffer);

        let next_positions = transition_position(position, cv, query_length, max_distance, algorithm, prefix_mode);

        for next_pos in next_positions {
            next_state.insert(next_pos);
        }
    }

    // Return expanded_state to pool (no longer needed)
    pool.release(expanded_state);

    if next_state.is_empty() {
        // Return empty state to pool
        pool.release(next_state);
        None
    } else {
        Some(next_state)
    }
}

/// Create the initial state for a query.
///
/// The initial state contains positions representing all possible
/// ways to start matching (including initial errors via deletions/insertions).
pub fn initial_state(query_length: usize, max_distance: usize) -> State {
    let mut state = State::new();

    // Start at position (0, 0) - no errors, beginning of query
    state.insert(Position::new(0, 0));

    // Also add positions for initial deletions (skipping query chars)
    for i in 1..=max_distance.min(query_length) {
        state.insert(Position::new(i, i));
    }

    state
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_characteristic_vector() {
        let query = b"test";
        let mut buffer = [false; 8];

        let cv = characteristic_vector(b't', query, 3, 0, &mut buffer);
        assert_eq!(cv, &[true, false, false]);

        let cv = characteristic_vector(b'e', query, 3, 0, &mut buffer);
        assert_eq!(cv, &[false, true, false]);

        let cv = characteristic_vector(b's', query, 3, 1, &mut buffer);
        assert_eq!(cv, &[false, true, false]);
    }

    #[test]
    fn test_transition_standard_match() {
        let pos = Position::new(0, 0);
        let cv = vec![true, false, false]; // Matches at position 0
        let query_length = 4; // e.g., "test"
        let next = transition_standard(&pos, &cv, query_length, 2, false);

        // Should advance with no error on match
        assert!(next.contains(&Position::new(1, 0)));
    }

    #[test]
    fn test_transition_standard_operations() {
        let pos = Position::new(1, 0);
        let cv = vec![false, false, true]; // No match at position 1
        let query_length = 4; // e.g., "test"
        let next = transition_standard(&pos, &cv, query_length, 2, false);

        // Should include:
        // - Substitution: (2, 1)
        // - Insertion: (1, 1)
        // - Deletion: (2, 1)
        assert!(next.len() >= 2);
        assert!(next.contains(&Position::new(1, 1))); // Insertion
    }

    #[test]
    fn test_initial_state() {
        let state = initial_state(5, 2);

        // Should have positions: (0,0), (1,1), (2,2)
        assert!(state.positions().contains(&Position::new(0, 0)));
        assert!(state.positions().contains(&Position::new(1, 1)));
        assert!(state.positions().contains(&Position::new(2, 2)));
    }

    #[test]
    fn test_transition_state() {
        let query = b"test";
        let mut state = State::new();
        state.insert(Position::new(0, 0));

        let next = transition_state(&state, b't', query, 2, Algorithm::Standard, false);
        assert!(next.is_some());

        let next_state = next.unwrap();
        // Should have advanced after matching 't'
        assert!(next_state.positions().iter().any(|p| p.term_index > 0));
    }
}
