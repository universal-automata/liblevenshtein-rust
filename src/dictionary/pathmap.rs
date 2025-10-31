//! PathMap-backed dictionary implementation.

use crate::dictionary::value::DictionaryValue;
use crate::dictionary::{
    Dictionary, DictionaryNode, MappedDictionary, MappedDictionaryNode, SyncStrategy,
};
#[cfg(feature = "serialization")]
use crate::serialization::DictionaryFromTerms;
use pathmap::utils::BitMask;
use pathmap::zipper::{Zipper, ZipperMoving, ZipperValues};
use pathmap::PathMap;
use smallvec::SmallVec;
use std::sync::{Arc, RwLock};

/// PathMap-backed dictionary for approximate string matching.
///
/// This implementation uses PathMap as the underlying trie structure,
/// providing efficient memory usage through structural sharing.
///
/// The dictionary uses `RwLock` for interior mutability, allowing:
/// - Multiple concurrent readers (queries)
/// - Exclusive write access for modifications (insert/remove)
///
/// # Generic Values
///
/// The dictionary can map terms to arbitrary values via the `V` type parameter:
/// - `PathMapDictionary<()>`: No values (backward compatible)
/// - `PathMapDictionary<u32>`: Map terms to scope IDs
/// - `PathMapDictionary<Vec<String>>`: Map terms to lists of metadata
///
/// # Examples
///
/// ```
/// use liblevenshtein::dictionary::pathmap::PathMapDictionary;
///
/// // Simple dictionary (no values)
/// let dict: PathMapDictionary<()> = PathMapDictionary::new();
///
/// // Dictionary with scope IDs
/// let dict_with_scopes: PathMapDictionary<u32> = PathMapDictionary::new();
/// ```
#[derive(Clone, Debug)]
pub struct PathMapDictionary<V: DictionaryValue = ()> {
    map: Arc<RwLock<PathMap<V>>>,
    term_count: Arc<RwLock<usize>>,
}

impl<V: DictionaryValue> PathMapDictionary<V> {
    /// Create a new empty dictionary
    pub fn new() -> Self
    where
        V: Default,
    {
        Self {
            map: Arc::new(RwLock::new(PathMap::new())),
            term_count: Arc::new(RwLock::new(0)),
        }
    }

    /// Create a dictionary from an iterator of terms with a default value
    pub fn from_terms<I, S>(terms: I) -> Self
    where
        I: IntoIterator<Item = S>,
        S: AsRef<str>,
        V: Default,
    {
        let mut map = PathMap::new();
        let mut count = 0;

        for term in terms {
            let bytes = term.as_ref().as_bytes();
            if map.insert(bytes, V::default()).is_none() {
                count += 1;
            }
        }

        Self {
            map: Arc::new(RwLock::new(map)),
            term_count: Arc::new(RwLock::new(count)),
        }
    }

    /// Create a dictionary from an iterator of (term, value) pairs
    pub fn from_terms_with_values<I, S>(terms: I) -> Self
    where
        I: IntoIterator<Item = (S, V)>,
        S: AsRef<str>,
    {
        let mut map = PathMap::new();
        let mut count = 0;

        for (term, value) in terms {
            let bytes = term.as_ref().as_bytes();
            if map.insert(bytes, value).is_none() {
                count += 1;
            }
        }

        Self {
            map: Arc::new(RwLock::new(map)),
            term_count: Arc::new(RwLock::new(count)),
        }
    }

    /// Insert a term with a default value into the dictionary
    ///
    /// Returns `true` if the term was newly inserted, `false` if it already existed.
    ///
    /// # Thread Safety
    ///
    /// This method acquires a write lock, blocking concurrent reads and writes.
    ///
    /// # Panics
    ///
    /// Panics if the lock is poisoned (another thread panicked while holding the lock).
    pub fn insert(&self, term: &str) -> bool
    where
        V: Default,
    {
        self.insert_with_value(term, V::default())
    }

    /// Insert a term with a specific value into the dictionary
    ///
    /// Returns `true` if the term was newly inserted, `false` if it already existed.
    /// If the term already existed, its value is updated.
    ///
    /// # Thread Safety
    ///
    /// This method acquires a write lock, blocking concurrent reads and writes.
    ///
    /// # Panics
    ///
    /// Panics if the lock is poisoned (another thread panicked while holding the lock).
    pub fn insert_with_value(&self, term: &str, value: V) -> bool {
        let bytes = term.as_bytes();
        let mut map = self.map.write().unwrap();
        let mut count = self.term_count.write().unwrap();

        if map.insert(bytes, value).is_none() {
            *count += 1;
            true
        } else {
            false
        }
    }

    /// Remove a term from the dictionary
    ///
    /// Returns `true` if the term was present and removed, `false` if it didn't exist.
    ///
    /// # Thread Safety
    ///
    /// This method acquires a write lock, blocking concurrent reads and writes.
    ///
    /// # Panics
    ///
    /// Panics if the lock is poisoned.
    pub fn remove(&self, term: &str) -> bool {
        let bytes = term.as_bytes();
        let mut map = self.map.write().unwrap();
        let mut count = self.term_count.write().unwrap();

        if map.remove_val_at(bytes, true).is_some() {
            *count = count.saturating_sub(1);
            true
        } else {
            false
        }
    }

    /// Clear all terms from the dictionary
    ///
    /// # Thread Safety
    ///
    /// This method acquires a write lock, blocking concurrent reads and writes.
    ///
    /// # Panics
    ///
    /// Panics if the lock is poisoned.
    pub fn clear(&self) {
        let mut map = self.map.write().unwrap();
        let mut count = self.term_count.write().unwrap();

        *map = PathMap::new();
        *count = 0;
    }

    /// Get the current number of terms in the dictionary
    ///
    /// # Thread Safety
    ///
    /// This method acquires a read lock.
    ///
    /// # Panics
    ///
    /// Panics if the lock is poisoned.
    pub fn term_count(&self) -> usize {
        *self.term_count.read().unwrap()
    }

    /// Serialize to PathMap's native .paths format
    ///
    /// # Thread Safety
    ///
    /// This method acquires a read lock.
    ///
    /// # Panics
    ///
    /// Panics if the lock is poisoned.
    pub fn serialize_paths<W: std::io::Write>(&self, writer: &mut W) -> std::io::Result<()> {
        use pathmap::paths_serialization::serialize_paths;
        let map = self.map.read().unwrap();
        serialize_paths(map.read_zipper(), writer)?;
        Ok(())
    }

    /// Deserialize from PathMap's native .paths format
    ///
    /// Creates a new dictionary from the serialized data.
    pub fn deserialize_paths<R: std::io::Read>(reader: R) -> std::io::Result<Self>
    where
        V: Default,
    {
        use pathmap::paths_serialization::deserialize_paths;
        use pathmap::zipper::ZipperIteration;

        let mut map = PathMap::new();
        deserialize_paths(map.write_zipper(), reader, V::default())?;

        // Count terms to populate term_count
        let count = {
            let mut rz = map.read_zipper();
            let mut count = 0;
            while rz.to_next_val() {
                count += 1;
            }
            count
        };

        Ok(Self {
            map: Arc::new(RwLock::new(map)),
            term_count: Arc::new(RwLock::new(count)),
        })
    }

    /// Get the value associated with a term
    ///
    /// Returns `None` if the term doesn't exist in the dictionary.
    ///
    /// # Thread Safety
    ///
    /// This method acquires a read lock.
    ///
    /// # Panics
    ///
    /// Panics if the lock is poisoned.
    pub fn get_value(&self, term: &str) -> Option<V> {
        let bytes = term.as_bytes();
        let map = self.map.read().unwrap();
        map.get_val_at(bytes).cloned()
    }
}

impl<V: DictionaryValue + Default> Default for PathMapDictionary<V> {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(feature = "serialization")]
impl DictionaryFromTerms for PathMapDictionary {
    fn from_terms<I: IntoIterator<Item = String>>(terms: I) -> Self {
        PathMapDictionary::from_terms(terms)
    }
}

impl<V: DictionaryValue> Dictionary for PathMapDictionary<V> {
    type Node = PathMapNode<V>;

    #[inline]
    fn root(&self) -> Self::Node {
        PathMapNode {
            map: Arc::clone(&self.map),
            path: Arc::new(Vec::new()),
        }
    }

    #[inline]
    fn len(&self) -> Option<usize> {
        Some(self.term_count())
    }

    #[inline]
    fn sync_strategy(&self) -> SyncStrategy {
        // PathMap uses Arc for structural sharing and UnsafeCell for mutations.
        // Current analysis: requires external sync for safety.
        //
        // Future: If PathMap's UnsafeCell usage is proven thread-safe,
        // this could return SyncStrategy::InternalSync or ::Persistent
        SyncStrategy::ExternalSync
    }
}

impl<V: DictionaryValue> MappedDictionary for PathMapDictionary<V> {
    type Value = V;

    fn get_value(&self, term: &str) -> Option<Self::Value> {
        PathMapDictionary::get_value(self, term)
    }
}

/// PathMap dictionary node using path-based navigation.
///
/// Instead of storing a zipper (which has lifetime issues), we store
/// the map reference and current path, recreating zippers as needed.
///
/// # Thread Safety
///
/// Nodes hold a read lock on the PathMap only while accessing it,
/// allowing concurrent queries even while the dictionary is being modified
/// (modifications will block until all reads complete).
///
/// # Performance
///
/// Uses `Arc<Vec<u8>>` for paths to enable sharing instead of cloning.
/// Since paths are never mutated after creation, Arc provides efficient
/// reference counting with minimal overhead compared to Vec cloning.
#[derive(Clone)]
pub struct PathMapNode<V: DictionaryValue> {
    map: Arc<RwLock<PathMap<V>>>,
    path: Arc<Vec<u8>>, // Arc for path sharing
}

impl<V: DictionaryValue> PathMapNode<V> {
    /// Create a zipper at the current path
    ///
    /// Acquires a read lock on the underlying PathMap.
    #[inline(always)]
    fn with_zipper<F, R>(&self, f: F) -> R
    where
        F: FnOnce(pathmap::zipper::ReadZipperUntracked<'_, 'static, V>) -> R,
    {
        let map = self.map.read().unwrap();
        let zipper = if self.path.is_empty() {
            map.read_zipper()
        } else {
            map.read_zipper_at_path(&**self.path) // Deref Arc to get &Vec<u8>
        };
        f(zipper)
    }
}

impl<V: DictionaryValue> DictionaryNode for PathMapNode<V> {
    type Unit = u8;

    #[inline]
    fn is_final(&self) -> bool {
        self.with_zipper(|z| z.is_val())
    }

    #[inline]
    fn transition(&self, label: u8) -> Option<Self> {
        // Check if this path exists first
        let exists = self.with_zipper(|mut z| {
            z.descend_to([label]);
            z.path_exists()
        });

        if exists {
            // Only build new path if transition succeeds
            let mut new_path = Vec::with_capacity(self.path.len() + 1);
            new_path.extend_from_slice(&self.path);
            new_path.push(label);

            Some(PathMapNode {
                map: Arc::clone(&self.map),
                path: Arc::new(new_path),
            })
        } else {
            None
        }
    }

    fn edges(&self) -> Box<dyn Iterator<Item = (u8, Self)> + '_> {
        // Lazy iterator approach: Pre-compute valid edge bytes (cheap),
        // then generate PathMapNode on-demand (eliminates Vec collection overhead)

        // Step 1: Get child mask and filter to valid bytes
        // This is cheap - just bit tests, no allocations
        let edge_bytes: SmallVec<[u8; 8]> = self.with_zipper(|zipper| {
            let mask = zipper.child_mask();
            (0..=255u8).filter(|byte| mask.test_bit(*byte)).collect()
        });

        // Step 2: Return lazy iterator that creates nodes on-demand
        // Key optimization: No Vec<(u8, Vec<u8>)> collection!
        // Arc sharing means cheap clones - just atomic ref count increment
        let map = Arc::clone(&self.map);
        let base_path = Arc::clone(&self.path);

        Box::new(edge_bytes.into_iter().filter_map(move |byte| {
            // Verify path exists (acquire lock only when actually iterating)
            let map_guard = map.read().unwrap();
            let mut check_zipper = if base_path.is_empty() {
                map_guard.read_zipper()
            } else {
                map_guard.read_zipper_at_path(&**base_path) // Deref Arc to get &Vec<u8>
            };
            check_zipper.descend_to([byte]);

            if check_zipper.path_exists() {
                drop(map_guard); // Release lock before creating node

                // Build new path with Arc - only allocate Vec once
                let mut new_path = Vec::with_capacity(base_path.len() + 1);
                new_path.extend_from_slice(&base_path);
                new_path.push(byte);

                Some((
                    byte,
                    PathMapNode {
                        map: Arc::clone(&map),
                        path: Arc::new(new_path),
                    },
                ))
            } else {
                None
            }
        }))
    }

    fn edge_count(&self) -> Option<usize> {
        Some(self.with_zipper(|z| z.child_count()))
    }
}

impl<V: DictionaryValue> MappedDictionaryNode for PathMapNode<V> {
    type Value = V;

    #[inline]
    fn value(&self) -> Option<Self::Value> {
        self.with_zipper(|zipper| zipper.val().cloned())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_pathmap_dictionary_creation() {
        let dict: PathMapDictionary<()> =
            PathMapDictionary::from_terms(vec!["hello", "world", "test"]);
        assert_eq!(dict.len(), Some(3));
    }

    #[test]
    fn test_pathmap_dictionary_contains() {
        let dict: PathMapDictionary<()> = PathMapDictionary::from_terms(vec!["hello", "world"]);
        assert!(dict.contains("hello"));
        assert!(dict.contains("world"));
        assert!(!dict.contains("goodbye"));
    }

    #[test]
    fn test_pathmap_node_traversal() {
        let dict: PathMapDictionary<()> = PathMapDictionary::from_terms(vec!["test", "testing"]);
        let root = dict.root();

        // Navigate: t -> e -> s -> t
        let t = root.transition(b't').expect("should have 't'");
        let e = t.transition(b'e').expect("should have 'e'");
        let s = e.transition(b's').expect("should have 's'");
        let t2 = s.transition(b't').expect("should have second 't'");

        assert!(t2.is_final(), "'test' should be final");

        // Continue: i -> n -> g
        let i = t2.transition(b'i').expect("should have 'i'");
        assert!(!i.is_final(), "'testi' should not be final");
    }

    #[test]
    fn test_pathmap_node_edges() {
        let dict: PathMapDictionary<()> = PathMapDictionary::from_terms(vec!["ab", "ac", "ad"]);
        let root = dict.root();
        let a = root.transition(b'a').expect("should have 'a'");

        let edges: Vec<_> = a.edges().map(|(byte, _)| byte).collect();
        assert_eq!(edges.len(), 3);
        assert!(edges.contains(&b'b'));
        assert!(edges.contains(&b'c'));
        assert!(edges.contains(&b'd'));
    }

    #[test]
    fn test_pathmap_dictionary_insert() {
        let dict: PathMapDictionary<()> = PathMapDictionary::from_terms(vec!["test"]);
        assert_eq!(dict.term_count(), 1);

        // Insert new term
        assert!(dict.insert("testing"));
        assert_eq!(dict.term_count(), 2);
        assert!(dict.contains("testing"));

        // Insert duplicate
        assert!(!dict.insert("test"));
        assert_eq!(dict.term_count(), 2);
    }

    #[test]
    fn test_pathmap_dictionary_remove() {
        let dict: PathMapDictionary<()> =
            PathMapDictionary::from_terms(vec!["test", "testing", "tested"]);
        assert_eq!(dict.term_count(), 3);

        // Remove existing term
        assert!(dict.remove("testing"));
        assert_eq!(dict.term_count(), 2);
        assert!(!dict.contains("testing"));
        assert!(dict.contains("test"));
        assert!(dict.contains("tested"));

        // Remove non-existent term
        assert!(!dict.remove("nonexistent"));
        assert_eq!(dict.term_count(), 2);
    }

    #[test]
    fn test_pathmap_dictionary_clear() {
        let dict: PathMapDictionary<()> = PathMapDictionary::from_terms(vec!["test", "testing"]);
        assert_eq!(dict.term_count(), 2);

        dict.clear();
        assert_eq!(dict.term_count(), 0);
        assert!(!dict.contains("test"));
        assert!(!dict.contains("testing"));
    }

    #[test]
    fn test_pathmap_dictionary_concurrent_operations() {
        use std::thread;

        let dict: PathMapDictionary<()> = PathMapDictionary::from_terms(vec!["test"]);
        let dict_clone = dict.clone();

        // Spawn thread that inserts while main thread queries
        let handle = thread::spawn(move || {
            dict_clone.insert("testing");
            dict_clone.insert("tested");
        });

        // Query while other thread modifies
        let _ = dict.contains("test");

        handle.join().unwrap();

        // Verify final state
        assert!(dict.contains("test"));
        assert!(dict.contains("testing"));
        assert!(dict.contains("tested"));
        assert_eq!(dict.term_count(), 3);
    }

    #[test]
    fn test_pathmap_dictionary_with_values() {
        // Test dictionary with u32 values (scope IDs)
        let terms_with_values = vec![("hello", 1u32), ("world", 2u32), ("test", 3u32)];
        let dict: PathMapDictionary<u32> =
            PathMapDictionary::from_terms_with_values(terms_with_values);

        assert_eq!(dict.len(), Some(3));
        assert!(dict.contains("hello"));
        assert_eq!(dict.get_value("hello"), Some(1));
        assert_eq!(dict.get_value("world"), Some(2));
        assert_eq!(dict.get_value("test"), Some(3));
        assert_eq!(dict.get_value("missing"), None);
    }

    #[test]
    fn test_pathmap_dictionary_insert_with_value() {
        let dict: PathMapDictionary<u32> = PathMapDictionary::new();

        // Insert with values
        assert!(dict.insert_with_value("hello", 42));
        assert_eq!(dict.get_value("hello"), Some(42));

        // Update existing value
        assert!(!dict.insert_with_value("hello", 99));
        assert_eq!(dict.get_value("hello"), Some(99));
        assert_eq!(dict.term_count(), 1);
    }

    #[test]
    fn test_pathmap_node_value() {
        let terms_with_values = vec![("hello", 10u32), ("world", 20u32)];
        let dict: PathMapDictionary<u32> =
            PathMapDictionary::from_terms_with_values(terms_with_values);
        let root = dict.root();

        // Navigate to "hello"
        let h = root.transition(b'h').expect("should have 'h'");
        let e = h.transition(b'e').expect("should have 'e'");
        let l1 = e.transition(b'l').expect("should have first 'l'");
        let l2 = l1.transition(b'l').expect("should have second 'l'");
        let o = l2.transition(b'o').expect("should have 'o'");

        assert!(o.is_final());
        assert_eq!(o.value(), Some(10));

        // Non-final node should have no value
        assert!(!h.is_final());
        assert_eq!(h.value(), None);
    }
}
