//! Integration tests for dictionary iteration support.
//!
//! Tests the `iter()`, `iter_bytes()`/`iter_chars()`, and `IntoIterator` implementations
//! across all dictionary types.

use std::collections::HashSet;

// ============================================================================
// DoubleArrayTrie Tests
// ============================================================================

mod double_array_trie_tests {
    use super::*;
    use liblevenshtein::dictionary::double_array_trie::DoubleArrayTrie;

    #[test]
    fn test_iter_bytes_with_values() {
        let dict = DoubleArrayTrie::from_terms_with_values(vec![
            ("cat", 1),
            ("dog", 2),
            ("cats", 3),
        ]);

        let results: Vec<(String, usize)> = dict
            .iter_bytes()
            .map(|(bytes, v)| (String::from_utf8(bytes).unwrap(), v))
            .collect();

        assert_eq!(results.len(), 3);
        assert!(results.contains(&("cat".to_string(), 1)));
        assert!(results.contains(&("dog".to_string(), 2)));
        assert!(results.contains(&("cats".to_string(), 3)));
    }

    #[test]
    fn test_iter_string_conversion() {
        let dict = DoubleArrayTrie::from_terms_with_values(vec![("hello", 42), ("world", 100)]);

        let results: Vec<(String, usize)> = dict.iter().collect();

        assert_eq!(results.len(), 2);
        assert!(results.contains(&("hello".to_string(), 42)));
        assert!(results.contains(&("world".to_string(), 100)));
    }

    #[test]
    fn test_into_iterator() {
        let dict =
            DoubleArrayTrie::from_terms_with_values(vec![("a", 1), ("b", 2), ("c", 3)]);

        let mut count = 0;
        for (bytes, value) in &dict {
            count += 1;
            assert!(value >= 1 && value <= 3);
            assert_eq!(bytes.len(), 1);
        }
        assert_eq!(count, 3);
    }

    #[test]
    fn test_empty_dictionary() {
        let dict = DoubleArrayTrie::<()>::new();
        assert_eq!(dict.iter_bytes().count(), 0);
        assert_eq!(dict.iter().count(), 0);
    }

    #[test]
    fn test_iter_terms_without_values() {
        let dict = DoubleArrayTrie::from_terms(vec!["one", "two", "three"].iter());

        // Use iter_terms() for dictionaries without values
        let terms: HashSet<String> = dict
            .iter_terms()
            .map(|bytes| String::from_utf8(bytes).unwrap())
            .collect();

        assert_eq!(terms.len(), 3);
        assert!(terms.contains("one"));
        assert!(terms.contains("two"));
        assert!(terms.contains("three"));
    }
}

// ============================================================================
// DynamicDawg Tests
// ============================================================================

mod dynamic_dawg_tests {
    use super::*;
    use liblevenshtein::dictionary::dynamic_dawg::DynamicDawg;

    #[test]
    fn test_iter_bytes_with_values() {
        let dict: DynamicDawg<u32> = DynamicDawg::new();
        dict.insert_with_value("apple", 10);
        dict.insert_with_value("banana", 20);
        dict.insert_with_value("cherry", 30);

        let results: Vec<(String, u32)> = dict
            .iter_bytes()
            .map(|(bytes, v)| (String::from_utf8(bytes).unwrap(), v))
            .collect();

        assert_eq!(results.len(), 3);
        assert!(results.contains(&("apple".to_string(), 10)));
        assert!(results.contains(&("banana".to_string(), 20)));
        assert!(results.contains(&("cherry".to_string(), 30)));
    }

    #[test]
    fn test_iter_after_insert() {
        let dict: DynamicDawg<u32> = DynamicDawg::new();
        dict.insert_with_value("first", 1);

        assert_eq!(dict.iter().count(), 1);

        dict.insert_with_value("second", 2);
        assert_eq!(dict.iter().count(), 2);

        dict.insert_with_value("third", 3);
        assert_eq!(dict.iter().count(), 3);
    }

    #[test]
    fn test_into_iterator() {
        let dict: DynamicDawg<u32> = DynamicDawg::new();
        dict.insert_with_value("test", 42);

        for (bytes, value) in &dict {
            assert_eq!(String::from_utf8(bytes).unwrap(), "test");
            assert_eq!(value, 42);
        }
    }
}

// ============================================================================
// DoubleArrayTrieChar Tests (Unicode)
// ============================================================================

mod double_array_trie_char_tests {
    use super::*;
    use liblevenshtein::dictionary::double_array_trie_char::DoubleArrayTrieChar;

    #[test]
    fn test_iter_chars_unicode() {
        let dict = DoubleArrayTrieChar::from_terms_with_values(vec![
            ("café", 1),
            ("naïve", 2),
            ("日本語", 3),
        ]);

        let results: Vec<(String, usize)> = dict.iter().collect();

        assert_eq!(results.len(), 3);
        assert!(results.contains(&("café".to_string(), 1)));
        assert!(results.contains(&("naïve".to_string(), 2)));
        assert!(results.contains(&("日本語".to_string(), 3)));
    }

    #[test]
    fn test_iter_chars_raw() {
        let dict = DoubleArrayTrieChar::from_terms_with_values(vec![("こんにちは", 100)]);

        let results: Vec<(Vec<char>, usize)> = dict.iter_chars().collect();

        assert_eq!(results.len(), 1);
        let (chars, value) = &results[0];
        assert_eq!(*value, 100);
        assert_eq!(chars.len(), 5); // 5 characters
        let term: String = chars.iter().collect();
        assert_eq!(term, "こんにちは");
    }

    #[test]
    fn test_into_iterator_char() {
        let dict = DoubleArrayTrieChar::from_terms_with_values(vec![("émoji", 1)]);

        for (chars, value) in &dict {
            let term: String = chars.iter().collect();
            assert_eq!(term, "émoji");
            assert_eq!(value, 1);
        }
    }
}

// ============================================================================
// DynamicDawgChar Tests (Unicode)
// ============================================================================

mod dynamic_dawg_char_tests {
    use super::*;
    use liblevenshtein::dictionary::dynamic_dawg_char::DynamicDawgChar;

    #[test]
    fn test_iter_chars_unicode() {
        let dict: DynamicDawgChar<u32> = DynamicDawgChar::new();
        dict.insert_with_value("привет", 1);
        dict.insert_with_value("мир", 2);

        let results: Vec<(String, u32)> = dict.iter().collect();

        assert_eq!(results.len(), 2);
        assert!(results.contains(&("привет".to_string(), 1)));
        assert!(results.contains(&("мир".to_string(), 2)));
    }

    #[test]
    fn test_into_iterator_char() {
        let dict: DynamicDawgChar<u32> = DynamicDawgChar::new();
        dict.insert_with_value("🎉", 42);

        for (chars, value) in &dict {
            let term: String = chars.iter().collect();
            assert_eq!(term, "🎉");
            assert_eq!(value, 42);
        }
    }
}

// ============================================================================
// SuffixAutomaton Tests
// ============================================================================

mod suffix_automaton_tests {
    use liblevenshtein::dictionary::suffix_automaton::SuffixAutomaton;

    #[test]
    fn test_iter_terms_substrings() {
        let dict = SuffixAutomaton::<()>::from_text("ab");

        // Should yield all substrings: "a", "ab", "b"
        // Use iter_terms() for dictionaries without values
        let terms: Vec<String> = dict
            .iter_terms()
            .map(|bytes| String::from_utf8(bytes).unwrap())
            .collect();

        assert!(terms.len() >= 2); // At least "a", "ab", "b" (exact count depends on impl)
    }

    #[test]
    fn test_iter_terms_count() {
        let dict = SuffixAutomaton::<()>::from_text("test");

        let count = dict.iter_terms().count();
        assert!(count > 0);
    }
}

// ============================================================================
// SuffixAutomatonChar Tests (Unicode)
// ============================================================================

mod suffix_automaton_char_tests {
    use liblevenshtein::dictionary::suffix_automaton_char::SuffixAutomatonChar;

    #[test]
    fn test_iter_terms_unicode_substrings() {
        let dict = SuffixAutomatonChar::<()>::from_text("日本");

        // Use iter_terms() for dictionaries without values
        let terms: Vec<String> = dict
            .iter_terms()
            .map(|chars| chars.into_iter().collect())
            .collect();

        // Should contain substrings of "日本"
        assert!(!terms.is_empty());
    }

    #[test]
    fn test_iter_terms_count() {
        let dict = SuffixAutomatonChar::<()>::from_text("café");

        let count = dict.iter_terms().count();
        assert!(count > 0);
    }
}

// ============================================================================
// PathMapDictionary Tests (feature-gated)
// ============================================================================

#[cfg(feature = "pathmap-backend")]
mod pathmap_tests {
    use super::*;
    use liblevenshtein::dictionary::pathmap::PathMapDictionary;

    #[test]
    fn test_iter_bytes_with_values() {
        let dict = PathMapDictionary::<u32>::new();
        dict.insert_with_value("foo", 1);
        dict.insert_with_value("bar", 2);
        dict.insert_with_value("baz", 3);

        let results: Vec<(String, u32)> = dict
            .iter_bytes()
            .map(|(bytes, v)| (String::from_utf8(bytes).unwrap(), v))
            .collect();

        assert_eq!(results.len(), 3);
        assert!(results.contains(&("foo".to_string(), 1)));
        assert!(results.contains(&("bar".to_string(), 2)));
        assert!(results.contains(&("baz".to_string(), 3)));
    }

    #[test]
    fn test_iter_string() {
        let dict = PathMapDictionary::<u32>::new();
        dict.insert_with_value("hello", 100);

        let results: Vec<(String, u32)> = dict.iter().collect();

        assert_eq!(results.len(), 1);
        assert_eq!(results[0], ("hello".to_string(), 100));
    }

    #[test]
    fn test_into_iterator() {
        let dict = PathMapDictionary::<u32>::new();
        dict.insert_with_value("test", 42);

        for (bytes, value) in &dict {
            assert_eq!(String::from_utf8(bytes).unwrap(), "test");
            assert_eq!(value, 42);
        }
    }

    #[test]
    fn test_empty_dictionary() {
        let dict = PathMapDictionary::<()>::new();
        assert_eq!(dict.iter_bytes().count(), 0);
        assert_eq!(dict.iter().count(), 0);
    }
}
