//! Zipper traits for navigating dictionary structures.
//!
//! This module provides trait abstractions for zipper-based dictionary navigation.
//! A zipper is a functional data structure that represents a position (focus) in a
//! tree-like structure along with the context needed to navigate back to the root.
//!
//! # Zipper Hierarchy
//!
//! This crate uses multiple zipper types for different purposes:
//!
//! * **`DictZipper`** - Navigate dictionary graph structures (this module)
//! * **`AutomatonZipper`** - Track Levenshtein automaton state (future)
//! * **`IntersectionZipper`** - Compose dictionary + automaton (future)
//! * **`ContextualZipper`** - Draft management for code completion (future)
//!
//! # Design Philosophy
//!
//! The zipper traits enable efficient navigation through dictionary structures without
//! requiring mutable references or extensive cloning. Each zipper implementation can
//! choose the most efficient representation for its backend (e.g., path-based for
//! PathMap, index-based for DoubleArrayTrie).
//!
//! # Examples
//!
//! ```ignore
//! use liblevenshtein::dictionary::DictZipper;
//! use liblevenshtein::dictionary::pathmap::PathMapDictionary;
//! use liblevenshtein::dictionary::pathmap_zipper::PathMapZipper;
//!
//! // Create a dictionary zipper
//! let dict = PathMapDictionary::<()>::new();
//! // Insert some terms...
//!
//! // Create zipper and navigate
//! let zipper = PathMapZipper::new_from_dict(&dict);
//! if let Some(child) = zipper.descend(b'a') {
//!     if child.is_final() {
//!         println!("Found a term ending at 'a'");
//!     }
//! }
//! ```

use crate::dictionary::value::DictionaryValue;
use crate::dictionary::CharUnit;

/// Core trait for dictionary navigation via zippers.
///
/// `DictZipper` is specifically for navigating the graph structure of dictionaries
/// (DAWG, PathMap, DoubleArrayTrie, etc.). Other zipper types (AutomatonZipper,
/// IntersectionZipper) handle different navigation concerns.
///
/// A `DictZipper` represents a cursor position in a dictionary structure,
/// providing methods to navigate through the tree and query properties at the
/// current position.
///
/// # Type Parameters
///
/// * `Unit` - The character unit type (typically `u8` or `char`)
///
/// # Navigation Model
///
/// Zippers use a functional navigation model:
/// - `descend(label)` moves down to a child, returning a new zipper
/// - `children()` iterates over all children from current position
/// - Movement is non-destructive; the original zipper remains valid
///
/// # Implementation Notes
///
/// Implementations should be lightweight and prefer Copy semantics where possible.
/// For backends that require locking (e.g., PathMap with RwLock), prefer a
/// lock-per-operation pattern to maximize concurrency.
pub trait DictZipper: Clone {
    /// The character unit type for edge labels
    type Unit: CharUnit;

    /// Check if the current position marks the end of a term.
    ///
    /// A position is "final" if it represents a complete term in the dictionary.
    /// For example, if the dictionary contains "cat" and "catch", the positions
    /// after 't' in "cat" and 'h' in "catch" are both final.
    ///
    /// # Returns
    ///
    /// `true` if this position marks a term boundary, `false` otherwise.
    ///
    /// # Examples
    ///
    /// ```ignore
    /// let zipper = dict.root_zipper();
    /// assert!(!zipper.is_final()); // Root is typically not final
    ///
    /// if let Some(z) = zipper.descend(b'c')
    ///     .and_then(|z| z.descend(b'a'))
    ///     .and_then(|z| z.descend(b't')) {
    ///     assert!(z.is_final()); // "cat" is in dictionary
    /// }
    /// ```
    fn is_final(&self) -> bool;

    /// Navigate to a child node with the given label.
    ///
    /// Attempts to move the zipper focus down one level to the child reached
    /// by the edge labeled with `label`. If no such edge exists, returns `None`.
    ///
    /// # Arguments
    ///
    /// * `label` - The edge label to follow
    ///
    /// # Returns
    ///
    /// `Some(child_zipper)` if the edge exists, `None` otherwise.
    ///
    /// # Examples
    ///
    /// ```ignore
    /// let root = dict.root_zipper();
    ///
    /// // Navigate through "hello"
    /// let h = root.descend(b'h')?;
    /// let e = h.descend(b'e')?;
    /// let l1 = e.descend(b'l')?;
    /// let l2 = l1.descend(b'l')?;
    /// let o = l2.descend(b'o')?;
    ///
    /// if o.is_final() {
    ///     println!("Found 'hello'");
    /// }
    /// ```
    fn descend(&self, label: Self::Unit) -> Option<Self>;

    /// Iterate over all children from the current position.
    ///
    /// Returns an iterator yielding pairs of `(label, child_zipper)` for each
    /// outgoing edge from the current position.
    ///
    /// # Returns
    ///
    /// An iterator over `(Unit, Self)` pairs representing edges and their targets.
    ///
    /// # Performance Note
    ///
    /// The iteration strategy is implementation-dependent. Some backends may
    /// iterate sparsely (only existing edges), while others may check all
    /// possible labels.
    ///
    /// # Examples
    ///
    /// ```ignore
    /// let zipper = dict.root_zipper();
    ///
    /// // Print all first characters in the dictionary
    /// for (label, child) in zipper.children() {
    ///     println!("Edge: {}", label as char);
    ///     if child.is_final() {
    ///         println!("  (single-character term)");
    ///     }
    /// }
    /// ```
    fn children(&self) -> impl Iterator<Item = (Self::Unit, Self)>;

    /// Get the path from root to the current position.
    ///
    /// Returns a sequence of edge labels representing the path from the root
    /// to the current zipper position. This is primarily useful for debugging
    /// and term reconstruction.
    ///
    /// # Returns
    ///
    /// A vector of units representing the path from root.
    ///
    /// # Performance Note
    ///
    /// This may involve reconstruction from a parent chain or similar structure.
    /// For performance-critical code, avoid calling this in tight loops.
    ///
    /// # Examples
    ///
    /// ```ignore
    /// let mut zipper = dict.root_zipper();
    /// zipper = zipper.descend(b'c').unwrap();
    /// zipper = zipper.descend(b'a').unwrap();
    /// zipper = zipper.descend(b't').unwrap();
    ///
    /// let path = zipper.path();
    /// assert_eq!(path, vec![b'c', b'a', b't']);
    /// assert_eq!(String::from_utf8(path).unwrap(), "cat");
    /// ```
    fn path(&self) -> Vec<Self::Unit>;
}

/// Extension trait for dictionaries with associated values.
///
/// A `ValuedDictZipper` extends `DictZipper` with the ability to
/// access values stored at final positions. This is used for dictionaries that
/// map terms to metadata, such as context IDs for hierarchical scoping.
///
/// # Type Parameters
///
/// * `Value` - The type of values stored in the dictionary
///
/// # Examples
///
/// ```ignore
/// use liblevenshtein::dictionary::{ValuedDictZipper, PathMapDictionary};
///
/// // Dictionary mapping terms to context IDs
/// let dict = PathMapDictionary::<Vec<u32>>::new();
/// dict.insert_with_value("print", vec![0]); // global scope
/// dict.insert_with_value("local", vec![1, 2]); // visible in scopes 1 and 2
///
/// let zipper = dict.root_zipper();
/// if let Some(z) = zipper.descend(b'p')
///     .and_then(|z| z.descend(b'r'))
///     .and_then(|z| z.descend(b'i'))
///     .and_then(|z| z.descend(b'n'))
///     .and_then(|z| z.descend(b't')) {
///
///     if let Some(contexts) = z.value() {
///         println!("'print' is visible in contexts: {:?}", contexts);
///     }
/// }
/// ```
pub trait ValuedDictZipper: DictZipper {
    /// The type of values associated with terms
    type Value: DictionaryValue;

    /// Get the value at the current position if it is final.
    ///
    /// Returns the associated value if the current position marks the end of
    /// a term (i.e., `is_final()` returns `true`). Returns `None` if the
    /// position is not final or if no value is associated.
    ///
    /// # Returns
    ///
    /// `Some(value)` if the position is final and has a value, `None` otherwise.
    ///
    /// # Examples
    ///
    /// ```ignore
    /// let dict = PathMapDictionary::<u32>::new();
    /// dict.insert_with_value("answer", 42);
    ///
    /// let zipper = dict.root_zipper();
    /// // Navigate to "answer"
    /// let final_zipper = /* navigation code */;
    ///
    /// match final_zipper.value() {
    ///     Some(42) => println!("Found the answer!"),
    ///     Some(v) => println!("Found value: {}", v),
    ///     None => println!("No value at this position"),
    /// }
    /// ```
    fn value(&self) -> Option<Self::Value>;
}

#[cfg(test)]
mod tests {
    use super::*;

    // These tests verify trait bounds compile correctly
    // Actual functionality tests are in backend-specific test files

    #[test]
    #[allow(dead_code)]
    fn test_dict_zipper_trait_bounds() {
        fn requires_zipper<Z: DictZipper>() {}

        // This test just verifies the trait compiles
        // Concrete implementations will be tested separately
    }

    #[test]
    #[allow(dead_code)]
    fn test_valued_zipper_trait_bounds() {
        fn requires_valued_zipper<Z: ValuedDictZipper>() {}

        // This test just verifies the trait compiles
    }
}
