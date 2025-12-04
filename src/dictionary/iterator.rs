//! Generic dictionary iteration support.
//!
//! This module provides iterator types that work with any dictionary backend
//! via the zipper abstraction, enabling idiomatic Rust iteration:
//!
//! ```rust,ignore
//! use liblevenshtein::dictionary::double_array_trie::DoubleArrayTrie;
//!
//! let dict = DoubleArrayTrie::from_terms_with_values(vec![
//!     ("cat", 1), ("dog", 2), ("cats", 3)
//! ]);
//!
//! // Iterate with String keys
//! for (term, value) in dict.iter() {
//!     println!("{} -> {}", term, value);
//! }
//!
//! // Iterate with raw bytes (more efficient)
//! for (bytes, value) in dict.iter_bytes() {
//!     println!("{:?} -> {}", bytes, value);
//! }
//!
//! // IntoIterator support
//! for (bytes, value) in &dict {
//!     println!("{:?} -> {}", bytes, value);
//! }
//! ```
//!
//! # Performance
//!
//! The iterator uses lazy path reconstruction - paths are only built when
//! yielding final nodes, not during traversal. This gives O(n + m × d)
//! complexity where:
//! - n = total nodes visited
//! - m = number of terms yielded
//! - d = average term depth
//!
//! Since most nodes (~90%+) are not final, this is highly efficient.

use super::zipper::{DictZipper, ValuedDictZipper};

/// Iterator over dictionary entries yielding `(term, value)` pairs.
///
/// This iterator performs depth-first traversal of the dictionary structure,
/// yielding entries as `(Vec<Unit>, Value)` tuples where `Unit` is `u8` for
/// byte-level dictionaries or `char` for character-level dictionaries.
///
/// # Type Parameters
///
/// - `Z: ValuedDictZipper` - The underlying valued zipper type
///
/// # Examples
///
/// ```rust,ignore
/// use liblevenshtein::dictionary::double_array_trie::DoubleArrayTrie;
/// use liblevenshtein::dictionary::iterator::DictionaryIterator;
/// use liblevenshtein::dictionary::double_array_trie_zipper::DoubleArrayTrieZipper;
///
/// let dict = DoubleArrayTrie::from_terms_with_values(vec![("test", 42)]);
/// let zipper = DoubleArrayTrieZipper::new_from_dict(&dict);
/// let mut iter = DictionaryIterator::new(zipper);
///
/// let (term, value) = iter.next().unwrap();
/// assert_eq!(term, b"test".to_vec());
/// assert_eq!(value, 42);
/// ```
pub struct DictionaryIterator<Z: ValuedDictZipper> {
    /// DFS traversal stack containing zippers at each level.
    /// Pre-allocated with capacity 16 to cover typical tree depths.
    stack: Vec<Z>,
}

impl<Z: ValuedDictZipper> DictionaryIterator<Z> {
    /// Create a new dictionary iterator starting from the given root zipper.
    ///
    /// The zipper should be positioned at the root of the dictionary.
    ///
    /// # Arguments
    ///
    /// * `root_zipper` - Zipper positioned at the dictionary root
    ///
    /// # Examples
    ///
    /// ```rust,ignore
    /// use liblevenshtein::dictionary::double_array_trie::DoubleArrayTrie;
    /// use liblevenshtein::dictionary::double_array_trie_zipper::DoubleArrayTrieZipper;
    /// use liblevenshtein::dictionary::iterator::DictionaryIterator;
    ///
    /// let dict = DoubleArrayTrie::from_terms(vec!["hello", "world"]);
    /// let zipper = DoubleArrayTrieZipper::new_from_dict(&dict);
    /// let iter = DictionaryIterator::new(zipper);
    /// ```
    pub fn new(root_zipper: Z) -> Self {
        // Pre-allocate stack capacity to avoid reallocations during DFS traversal.
        // Capacity 16 covers typical tree depths (10-15) while avoiding excessive
        // over-allocation.
        let mut stack = Vec::with_capacity(16);
        stack.push(root_zipper);
        Self { stack }
    }
}

impl<Z: ValuedDictZipper> Iterator for DictionaryIterator<Z> {
    type Item = (Vec<Z::Unit>, Z::Value);

    fn next(&mut self) -> Option<Self::Item> {
        while let Some(zipper) = self.stack.pop() {
            // Push all children onto stack for continued DFS traversal.
            // No path work here - paths are reconstructed lazily only for final nodes.
            for (_unit, child) in zipper.children() {
                self.stack.push(child);
            }

            // If this is a final node, reconstruct path and yield with value.
            // Path reconstruction happens only for final nodes (~10% of total),
            // making iteration highly efficient.
            if zipper.is_final() {
                if let Some(value) = zipper.value() {
                    return Some((zipper.path(), value));
                }
                // For V=() dictionaries, value() returns Some(()) so this branch
                // handles edge cases where is_final() is true but no value exists.
            }
        }

        None
    }
}

/// Iterator over dictionary terms (without values).
///
/// This iterator yields only the terms (paths) in the dictionary, not values.
/// Use this for dictionaries created without associated values (e.g., via
/// `from_terms()` instead of `from_terms_with_values()`).
///
/// # Type Parameters
///
/// - `Z: DictZipper` - Any dictionary zipper type
///
/// # Examples
///
/// ```rust,ignore
/// use liblevenshtein::dictionary::double_array_trie::DoubleArrayTrie;
/// use liblevenshtein::dictionary::iterator::DictionaryTermIterator;
/// use liblevenshtein::dictionary::double_array_trie_zipper::DoubleArrayTrieZipper;
///
/// let dict = DoubleArrayTrie::from_terms(vec!["hello", "world"]);
/// let zipper = DoubleArrayTrieZipper::new_from_dict(&dict);
/// let iter = DictionaryTermIterator::new(zipper);
///
/// for term in iter {
///     println!("Term: {:?}", term);
/// }
/// ```
pub struct DictionaryTermIterator<Z: DictZipper> {
    /// DFS traversal stack containing zippers at each level.
    stack: Vec<Z>,
}

impl<Z: DictZipper> DictionaryTermIterator<Z> {
    /// Create a new term iterator starting from the given root zipper.
    pub fn new(root_zipper: Z) -> Self {
        let mut stack = Vec::with_capacity(16);
        stack.push(root_zipper);
        Self { stack }
    }
}

impl<Z: DictZipper> Iterator for DictionaryTermIterator<Z> {
    type Item = Vec<Z::Unit>;

    fn next(&mut self) -> Option<Self::Item> {
        while let Some(zipper) = self.stack.pop() {
            for (_unit, child) in zipper.children() {
                self.stack.push(child);
            }

            if zipper.is_final() {
                return Some(zipper.path());
            }
        }

        None
    }
}

#[cfg(test)]
mod tests {
    // Note: Actual dictionary tests are in tests/dictionary_iterator_tests.rs
}
