//! Character-level Double-Array Trie implementation for proper Unicode support.
//!
//! This module provides a character-based variant of Double-Array Trie that operates
//! at the Unicode character level rather than byte level. This ensures correct edit
//! distance semantics for multi-byte UTF-8 sequences.
//!
//! ## Differences from DoubleArrayTrie
//!
//! - Edge labels are `char` (4 bytes) instead of `u8` (1 byte)
//! - Distance calculations count characters, not bytes
//! - Correct semantics: "" → "¡" is distance 1, not 2
//!
//! ## Performance Trade-offs
//!
//! - **Memory**: 4x larger edge labels (char vs u8)
//! - **Speed**: Slightly slower (~10-15%) due to larger data
//! - **Correctness**: Proper Unicode semantics
//!
//! ## Use Cases
//!
//! Use `DoubleArrayTrieChar` when:
//! - Dictionary contains non-ASCII Unicode characters
//! - Edit distance must be measured in characters, not bytes
//! - Correctness is more important than maximum performance

use crate::dictionary::{Dictionary, DictionaryNode};
use std::sync::Arc;

#[cfg(feature = "serialization")]
use serde::{Deserialize, Deserializer, Serialize, Serializer};

/// Custom serialization for Arc<Vec<T>>
#[cfg(feature = "serialization")]
fn serialize_arc_vec<S, T>(arc: &Arc<Vec<T>>, serializer: S) -> Result<S::Ok, S::Error>
where
    S: Serializer,
    T: Serialize,
{
    arc.as_ref().serialize(serializer)
}

/// Custom deserialization for Arc<Vec<T>>
#[cfg(feature = "serialization")]
fn deserialize_arc_vec<'de, D, T>(deserializer: D) -> Result<Arc<Vec<T>>, D::Error>
where
    D: Deserializer<'de>,
    T: Deserialize<'de>,
{
    Vec::<T>::deserialize(deserializer).map(Arc::new)
}

/// Custom serialization for Arc<Vec<Vec<T>>>
#[cfg(feature = "serialization")]
fn serialize_arc_vec_vec<S, T>(arc: &Arc<Vec<Vec<T>>>, serializer: S) -> Result<S::Ok, S::Error>
where
    S: Serializer,
    T: Serialize,
{
    arc.as_ref().serialize(serializer)
}

/// Custom deserialization for Arc<Vec<Vec<T>>>
#[cfg(feature = "serialization")]
fn deserialize_arc_vec_vec<'de, D, T>(deserializer: D) -> Result<Arc<Vec<Vec<T>>>, D::Error>
where
    D: Deserializer<'de>,
    T: Deserialize<'de>,
{
    Vec::<Vec<T>>::deserialize(deserializer).map(Arc::new)
}

/// Shared data for character-level Double-Array Trie.
#[cfg_attr(
    feature = "serialization",
    derive(serde::Serialize, serde::Deserialize)
)]
#[derive(Clone, Debug)]
struct DATSharedChar {
    /// BASE array: offset for computing next state
    #[cfg_attr(
        feature = "serialization",
        serde(
            serialize_with = "serialize_arc_vec",
            deserialize_with = "deserialize_arc_vec"
        )
    )]
    base: Arc<Vec<i32>>,

    /// CHECK array: parent state verification
    #[cfg_attr(
        feature = "serialization",
        serde(
            serialize_with = "serialize_arc_vec",
            deserialize_with = "deserialize_arc_vec"
        )
    )]
    check: Arc<Vec<i32>>,

    /// Final states marking valid term endings
    #[cfg_attr(
        feature = "serialization",
        serde(
            serialize_with = "serialize_arc_vec",
            deserialize_with = "deserialize_arc_vec"
        )
    )]
    is_final: Arc<Vec<bool>>,

    /// Edge lists per state: which chars have valid transitions
    #[cfg_attr(
        feature = "serialization",
        serde(
            serialize_with = "serialize_arc_vec_vec",
            deserialize_with = "deserialize_arc_vec_vec"
        )
    )]
    edges: Arc<Vec<Vec<char>>>,
}

/// Character-level Double-Array Trie for proper Unicode support.
///
/// This variant operates at the Unicode character level, ensuring correct
/// edit distance calculations for multi-byte UTF-8 sequences.
///
/// # Example
///
/// ```
/// use liblevenshtein::dictionary::double_array_trie_char::DoubleArrayTrieChar;
/// use liblevenshtein::dictionary::Dictionary;
///
/// let terms = vec!["café", "中文", "🎉"];
/// let dict = DoubleArrayTrieChar::from_terms(terms);
///
/// assert!(dict.contains("café"));
/// assert!(dict.contains("中文"));
/// assert!(dict.contains("🎉"));
/// ```
#[cfg_attr(
    feature = "serialization",
    derive(serde::Serialize, serde::Deserialize)
)]
#[derive(Clone, Debug)]
pub struct DoubleArrayTrieChar {
    /// Shared data referenced by all nodes
    shared: DATSharedChar,

    /// Free list for deleted/unused states
    #[allow(dead_code)]
    #[cfg_attr(
        feature = "serialization",
        serde(
            serialize_with = "serialize_arc_vec",
            deserialize_with = "deserialize_arc_vec"
        )
    )]
    free_list: Arc<Vec<usize>>,

    /// Number of terms in the dictionary
    num_terms: usize,
}

impl DoubleArrayTrieChar {
    /// Create a new character-level Double-Array Trie from an iterator of terms.
    ///
    /// # Example
    ///
    /// ```
    /// use liblevenshtein::dictionary::double_array_trie_char::DoubleArrayTrieChar;
    ///
    /// let dict = DoubleArrayTrieChar::from_terms(vec!["hello", "world", "café"]);
    /// ```
    pub fn from_terms<I, S>(terms: I) -> Self
    where
        I: IntoIterator<Item = S>,
        S: AsRef<str>,
    {
        let mut terms: Vec<Vec<char>> = terms
            .into_iter()
            .map(|s| s.as_ref().chars().collect())
            .collect();

        terms.sort_unstable();
        terms.dedup();

        let num_terms = terms.len();

        if terms.is_empty() {
            return Self::empty();
        }

        let mut builder = DATBuilderChar::new();
        for term in &terms {
            builder.insert(term);
        }

        let (base, check, is_final, edges) = builder.build();

        Self {
            shared: DATSharedChar {
                base: Arc::new(base),
                check: Arc::new(check),
                is_final: Arc::new(is_final),
                edges: Arc::new(edges),
            },
            free_list: Arc::new(Vec::new()),
            num_terms,
        }
    }

    /// Create an empty character-level Double-Array Trie.
    pub fn empty() -> Self {
        Self {
            shared: DATSharedChar {
                base: Arc::new(vec![0]),
                check: Arc::new(vec![0]),
                is_final: Arc::new(vec![false]),
                edges: Arc::new(vec![vec![]]),
            },
            free_list: Arc::new(Vec::new()),
            num_terms: 0,
        }
    }
}

impl Dictionary for DoubleArrayTrieChar {
    type Node = DoubleArrayTrieCharNode;

    fn root(&self) -> Self::Node {
        DoubleArrayTrieCharNode {
            state: 0,
            shared: self.shared.clone(),
        }
    }

    fn len(&self) -> Option<usize> {
        Some(self.num_terms)
    }
}

/// Node reference for character-level Dictionary trait implementation.
#[derive(Clone)]
pub struct DoubleArrayTrieCharNode {
    /// Current state index
    state: usize,

    /// Shared data
    shared: DATSharedChar,
}

impl DictionaryNode for DoubleArrayTrieCharNode {
    type Unit = char;

    fn is_final(&self) -> bool {
        self.state < self.shared.is_final.len() && self.shared.is_final[self.state]
    }

    fn transition(&self, label: char) -> Option<Self> {
        if self.state >= self.shared.base.len() {
            return None;
        }

        let base = self.shared.base[self.state];
        if base < 0 {
            return None;
        }

        // For char, we need to map to array index
        // Use char as u32 for computation
        let char_code = label as u32;
        let next = (base as u32).wrapping_add(char_code) as usize;

        if next < self.shared.check.len() && self.shared.check[next] == self.state as i32 {
            Some(DoubleArrayTrieCharNode {
                state: next,
                shared: self.shared.clone(),
            })
        } else {
            None
        }
    }

    fn edges(&self) -> Box<dyn Iterator<Item = (char, Self)> + '_> {
        let state = self.state;

        if state >= self.shared.edges.len() {
            return Box::new(std::iter::empty());
        }

        let base = self.shared.base[state];
        if base < 0 {
            return Box::new(std::iter::empty());
        }

        let edges = self.shared.edges[state].clone();
        let shared = self.shared.clone();

        Box::new(edges.into_iter().filter_map(move |c| {
            let char_code = c as u32;
            let next = (base as u32).wrapping_add(char_code) as usize;

            if next < shared.check.len() && shared.check[next] == state as i32 {
                Some((
                    c,
                    DoubleArrayTrieCharNode {
                        state: next,
                        shared: shared.clone(),
                    },
                ))
            } else {
                None
            }
        }))
    }

    fn edge_count(&self) -> Option<usize> {
        if self.state < self.shared.edges.len() {
            Some(self.shared.edges[self.state].len())
        } else {
            Some(0)
        }
    }
}

/// Builder for character-level Double-Array Trie.
struct DATBuilderChar {
    base: Vec<i32>,
    check: Vec<i32>,
    is_final: Vec<bool>,
    edges: Vec<Vec<char>>,
    used: Vec<bool>,
}

impl DATBuilderChar {
    fn new() -> Self {
        Self {
            base: vec![0],
            check: vec![0],
            is_final: vec![false],
            edges: vec![vec![]],
            used: vec![false],
        }
    }

    fn insert(&mut self, term: &[char]) {
        let mut state = 0;

        for &c in term {
            state = self.get_or_create_transition(state, c);
        }

        if state < self.is_final.len() {
            self.is_final[state] = true;
        }
    }

    fn get_or_create_transition(&mut self, from_state: usize, label: char) -> usize {
        // Ensure arrays are large enough
        while from_state >= self.base.len() {
            self.base.push(0);
            self.check.push(0);
            self.is_final.push(false);
            self.edges.push(vec![]);
            self.used.push(false);
        }

        let mut base = self.base[from_state];

        // If base is not set, find a suitable base
        if base == 0 {
            base = self.find_base(&[label]);
            self.base[from_state] = base;
        }

        let char_code = label as u32;
        let next_state = (base as u32).wrapping_add(char_code) as usize;

        // Ensure next_state exists
        while next_state >= self.base.len() {
            self.base.push(0);
            self.check.push(0);
            self.is_final.push(false);
            self.edges.push(vec![]);
            self.used.push(false);
        }

        // Set CHECK and mark as used
        self.check[next_state] = from_state as i32;
        self.used[next_state] = true;

        // Add edge to edge list
        if !self.edges[from_state].contains(&label) {
            self.edges[from_state].push(label);
        }

        next_state
    }

    fn find_base(&mut self, labels: &[char]) -> i32 {
        // Find a base value such that base + label is unused for all labels
        'base_search: for base in 1u32..100000 {
            for &label in labels {
                let char_code = label as u32;
                let next = base.wrapping_add(char_code) as usize;

                // Ensure we have space
                while next >= self.used.len() {
                    self.used.push(false);
                }

                if self.used[next] {
                    continue 'base_search;
                }
            }
            return base as i32;
        }

        // Fallback
        1
    }

    fn build(self) -> (Vec<i32>, Vec<i32>, Vec<bool>, Vec<Vec<char>>) {
        (self.base, self.check, self.is_final, self.edges)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_empty_dict() {
        let dict = DoubleArrayTrieChar::empty();
        assert_eq!(dict.len(), Some(0));
        assert!(!dict.contains("test"));
    }

    #[test]
    fn test_basic_terms() {
        let dict = DoubleArrayTrieChar::from_terms(vec!["hello", "world"]);
        assert!(dict.contains("hello"));
        assert!(dict.contains("world"));
        assert!(!dict.contains("test"));
    }

    #[test]
    fn test_unicode_terms() {
        let dict = DoubleArrayTrieChar::from_terms(vec!["café", "naïve", "résumé"]);
        assert!(dict.contains("café"));
        assert!(dict.contains("naïve"));
        assert!(dict.contains("résumé"));
        assert!(!dict.contains("cafe")); // Different without accent
    }

    #[test]
    fn test_cjk_characters() {
        let dict = DoubleArrayTrieChar::from_terms(vec!["中文", "日本語", "한국어"]);
        assert!(dict.contains("中文"));
        assert!(dict.contains("日本語"));
        assert!(dict.contains("한국어"));
    }

    #[test]
    fn test_emoji() {
        let dict = DoubleArrayTrieChar::from_terms(vec!["hello🎉", "world🌍", "test✨"]);
        assert!(dict.contains("hello🎉"));
        assert!(dict.contains("world🌍"));
        assert!(dict.contains("test✨"));
    }

    #[test]
    fn test_mixed_unicode() {
        let dict = DoubleArrayTrieChar::from_terms(vec!["hello", "café", "中文", "🎉", "test123"]);

        assert!(dict.contains("hello"));
        assert!(dict.contains("café"));
        assert!(dict.contains("中文"));
        assert!(dict.contains("🎉"));
        assert!(dict.contains("test123"));
        assert!(!dict.contains("missing"));
    }

    #[test]
    fn test_node_traversal() {
        let dict = DoubleArrayTrieChar::from_terms(vec!["test"]);
        let root = dict.root();

        let t_node = root.transition('t').expect("Should have 't' edge");
        let e_node = t_node.transition('e').expect("Should have 'e' edge");
        let s_node = e_node.transition('s').expect("Should have 's' edge");
        let t2_node = s_node.transition('t').expect("Should have second 't' edge");

        assert!(t2_node.is_final());
    }

    #[test]
    fn test_edges_iterator() {
        let dict = DoubleArrayTrieChar::from_terms(vec!["cat", "car", "cart"]);
        let root = dict.root();

        let c_node = root.transition('c').unwrap();
        let a_node = c_node.transition('a').unwrap();

        let edges: Vec<char> = a_node.edges().map(|(c, _)| c).collect();
        assert!(edges.contains(&'t'));
        assert!(edges.contains(&'r'));
    }
}
