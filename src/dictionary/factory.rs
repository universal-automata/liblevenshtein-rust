//! Dictionary factory for creating different backend implementations.
//!
//! This module provides a unified interface for creating dictionary instances
//! with different backend implementations (PathMap, DAWG, DynamicDawg).
//!
//! # Example
//!
//! ```rust,ignore
//! use liblevenshtein::dictionary::factory::{DictionaryFactory, DictionaryBackend};
//!
//! // Create a PathMap dictionary
//! let dict = DictionaryFactory::create(
//!     DictionaryBackend::PathMap,
//!     vec!["test", "testing", "tested"]
//! );
//!
//! // Create a DAWG dictionary
//! let dict = DictionaryFactory::create(
//!     DictionaryBackend::Dawg,
//!     vec!["test", "testing", "tested"]
//! );
//! ```

use super::dawg::DawgDictionary;
use super::dynamic_dawg::DynamicDawg;
use super::pathmap::PathMapDictionary;
use super::Dictionary;

/// Dictionary backend types
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DictionaryBackend {
    /// PathMap-based trie dictionary (fastest for queries, highest memory)
    PathMap,
    /// Static DAWG dictionary (space-efficient, fast queries, immutable)
    Dawg,
    /// Dynamic DAWG dictionary (space-efficient, supports modifications)
    DynamicDawg,
}

impl std::fmt::Display for DictionaryBackend {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            DictionaryBackend::PathMap => write!(f, "PathMap"),
            DictionaryBackend::Dawg => write!(f, "DAWG"),
            DictionaryBackend::DynamicDawg => write!(f, "DynamicDAWG"),
        }
    }
}

/// Unified dictionary container that can hold any backend type
#[derive(Debug)]
pub enum DictionaryContainer {
    /// PathMap-based trie dictionary
    PathMap(PathMapDictionary),
    /// Static DAWG dictionary
    Dawg(DawgDictionary),
    /// Dynamic DAWG dictionary
    DynamicDawg(DynamicDawg),
}

impl DictionaryContainer {
    /// Get the backend type of this container
    pub fn backend(&self) -> DictionaryBackend {
        match self {
            DictionaryContainer::PathMap(_) => DictionaryBackend::PathMap,
            DictionaryContainer::Dawg(_) => DictionaryBackend::Dawg,
            DictionaryContainer::DynamicDawg(_) => DictionaryBackend::DynamicDawg,
        }
    }

    /// Get the number of terms in the dictionary
    pub fn len(&self) -> Option<usize> {
        match self {
            DictionaryContainer::PathMap(d) => d.len(),
            DictionaryContainer::Dawg(d) => d.len(),
            DictionaryContainer::DynamicDawg(d) => d.len(),
        }
    }

    /// Check if the dictionary is empty
    pub fn is_empty(&self) -> bool {
        self.len() == Some(0)
    }

    /// Check if a term exists in the dictionary
    pub fn contains(&self, term: &str) -> bool {
        match self {
            DictionaryContainer::PathMap(d) => d.contains(term),
            DictionaryContainer::Dawg(d) => d.contains(term),
            DictionaryContainer::DynamicDawg(d) => d.contains(term),
        }
    }
}

/// Factory for creating dictionaries with different backends
pub struct DictionaryFactory;

impl DictionaryFactory {
    /// Create a dictionary with the specified backend
    ///
    /// # Arguments
    ///
    /// * `backend` - The backend implementation to use
    /// * `terms` - Iterator of terms to insert into the dictionary
    ///
    /// # Returns
    ///
    /// A `DictionaryContainer` holding the created dictionary
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// use liblevenshtein::dictionary::factory::{DictionaryFactory, DictionaryBackend};
    ///
    /// let dict = DictionaryFactory::create(
    ///     DictionaryBackend::Dawg,
    ///     vec!["hello", "world"]
    /// );
    ///
    /// assert!(dict.contains("hello"));
    /// assert_eq!(dict.len(), Some(2));
    /// ```
    pub fn create<I, S>(backend: DictionaryBackend, terms: I) -> DictionaryContainer
    where
        I: IntoIterator<Item = S>,
        S: AsRef<str>,
    {
        match backend {
            DictionaryBackend::PathMap => {
                DictionaryContainer::PathMap(PathMapDictionary::from_iter(terms))
            }
            DictionaryBackend::Dawg => DictionaryContainer::Dawg(DawgDictionary::from_iter(terms)),
            DictionaryBackend::DynamicDawg => {
                DictionaryContainer::DynamicDawg(DynamicDawg::from_iter(terms))
            }
        }
    }

    /// Create an empty dictionary with the specified backend
    ///
    /// # Arguments
    ///
    /// * `backend` - The backend implementation to use
    ///
    /// # Returns
    ///
    /// An empty `DictionaryContainer`
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// use liblevenshtein::dictionary::factory::{DictionaryFactory, DictionaryBackend};
    ///
    /// let dict = DictionaryFactory::empty(DictionaryBackend::PathMap);
    /// assert_eq!(dict.len(), Some(0));
    /// ```
    pub fn empty(backend: DictionaryBackend) -> DictionaryContainer {
        match backend {
            DictionaryBackend::PathMap => DictionaryContainer::PathMap(PathMapDictionary::new()),
            DictionaryBackend::Dawg => DictionaryContainer::Dawg(DawgDictionary::new()),
            DictionaryBackend::DynamicDawg => DictionaryContainer::DynamicDawg(DynamicDawg::new()),
        }
    }

    /// Get a list of all available backends
    pub fn available_backends() -> Vec<DictionaryBackend> {
        vec![
            DictionaryBackend::PathMap,
            DictionaryBackend::Dawg,
            DictionaryBackend::DynamicDawg,
        ]
    }

    /// Get a description of a backend's characteristics
    pub fn backend_description(backend: DictionaryBackend) -> &'static str {
        match backend {
            DictionaryBackend::PathMap => {
                "Fast queries with higher memory usage. Best for in-memory applications."
            }
            DictionaryBackend::Dawg => {
                "Space-efficient immutable dictionary. Best for static dictionaries."
            }
            DictionaryBackend::DynamicDawg => {
                "Space-efficient with modification support. Best for evolving dictionaries."
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_factory_pathmap() {
        let dict = DictionaryFactory::create(
            DictionaryBackend::PathMap,
            vec!["test", "testing", "tested"],
        );

        assert_eq!(dict.backend(), DictionaryBackend::PathMap);
        assert_eq!(dict.len(), Some(3));
        assert!(dict.contains("test"));
        assert!(dict.contains("testing"));
        assert!(dict.contains("tested"));
        assert!(!dict.contains("tester"));
    }

    #[test]
    fn test_factory_dawg() {
        let dict =
            DictionaryFactory::create(DictionaryBackend::Dawg, vec!["hello", "world", "test"]);

        assert_eq!(dict.backend(), DictionaryBackend::Dawg);
        assert_eq!(dict.len(), Some(3));
        assert!(dict.contains("hello"));
        assert!(dict.contains("world"));
        assert!(dict.contains("test"));
        assert!(!dict.contains("testing"));
    }

    #[test]
    fn test_factory_dynamic_dawg() {
        let dict =
            DictionaryFactory::create(DictionaryBackend::DynamicDawg, vec!["foo", "bar", "baz"]);

        assert_eq!(dict.backend(), DictionaryBackend::DynamicDawg);
        assert_eq!(dict.len(), Some(3));
        assert!(dict.contains("foo"));
        assert!(dict.contains("bar"));
        assert!(dict.contains("baz"));
        assert!(!dict.contains("qux"));
    }

    #[test]
    fn test_factory_empty() {
        let pathmap = DictionaryFactory::empty(DictionaryBackend::PathMap);
        assert_eq!(pathmap.len(), Some(0));
        assert!(pathmap.is_empty());

        let dawg = DictionaryFactory::empty(DictionaryBackend::Dawg);
        assert_eq!(dawg.len(), Some(0));
        assert!(dawg.is_empty());

        let dynamic_dawg = DictionaryFactory::empty(DictionaryBackend::DynamicDawg);
        assert_eq!(dynamic_dawg.len(), Some(0));
        assert!(dynamic_dawg.is_empty());
    }

    #[test]
    fn test_backend_display() {
        assert_eq!(DictionaryBackend::PathMap.to_string(), "PathMap");
        assert_eq!(DictionaryBackend::Dawg.to_string(), "DAWG");
        assert_eq!(DictionaryBackend::DynamicDawg.to_string(), "DynamicDAWG");
    }

    #[test]
    fn test_available_backends() {
        let backends = DictionaryFactory::available_backends();
        assert_eq!(backends.len(), 3);
        assert!(backends.contains(&DictionaryBackend::PathMap));
        assert!(backends.contains(&DictionaryBackend::Dawg));
        assert!(backends.contains(&DictionaryBackend::DynamicDawg));
    }

    #[test]
    fn test_backend_descriptions() {
        for backend in DictionaryFactory::available_backends() {
            let desc = DictionaryFactory::backend_description(backend);
            assert!(!desc.is_empty());
            println!("{}: {}", backend, desc);
        }
    }

    #[test]
    fn test_all_backends_work() {
        let terms = vec!["apple", "banana", "cherry"];

        for backend in DictionaryFactory::available_backends() {
            let dict = DictionaryFactory::create(backend, terms.clone());
            assert_eq!(dict.len(), Some(3));
            assert!(dict.contains("apple"));
            assert!(dict.contains("banana"));
            assert!(dict.contains("cherry"));
        }
    }
}
