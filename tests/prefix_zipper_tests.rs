//! Comprehensive tests for PrefixZipper functionality across all dictionary backends.
//!
//! This test suite validates:
//! - Basic prefix navigation and iteration
//! - Behavior with non-existent prefixes
//! - Empty dictionary handling
//! - Unicode support (character-level variants)
//! - Valued dictionary support
//! - Edge cases (empty prefix, exact matches, long prefixes)
//! - Consistency across backends

use liblevenshtein::dictionary::double_array_trie::DoubleArrayTrie;
use liblevenshtein::dictionary::double_array_trie_char::DoubleArrayTrieChar;
use liblevenshtein::dictionary::double_array_trie_char_zipper::DoubleArrayTrieCharZipper;
use liblevenshtein::dictionary::double_array_trie_zipper::DoubleArrayTrieZipper;
use liblevenshtein::dictionary::dynamic_dawg::DynamicDawg;
use liblevenshtein::dictionary::dynamic_dawg_char::DynamicDawgChar;
use liblevenshtein::dictionary::dynamic_dawg_char_zipper::DynamicDawgCharZipper;
use liblevenshtein::dictionary::dynamic_dawg_zipper::DynamicDawgZipper;
use liblevenshtein::dictionary::prefix_zipper::{PrefixZipper, ValuedPrefixZipper};

// ============================================================================
// Helper Functions
// ============================================================================

/// Sort results for consistent comparison
fn sorted_results<T: Ord>(mut results: Vec<T>) -> Vec<T> {
    results.sort();
    results
}

// ============================================================================
// Basic Functionality Tests - DoubleArrayTrie
// ============================================================================

#[test]
fn test_dat_prefix_exists_single_match() {
    let terms = vec!["hello", "world"];
    let dict = DoubleArrayTrie::from_terms(terms.iter());

    let zipper = DoubleArrayTrieZipper::new_from_dict(&dict);
    let results: Vec<String> = zipper
        .with_prefix(b"wor")
        .unwrap()
        .map(|(path, _)| String::from_utf8(path).unwrap())
        .collect();

    assert_eq!(results, vec!["world"]);
}

#[test]
fn test_dat_prefix_exists_multiple_matches() {
    let terms = vec!["process", "processUser", "produce", "product"];
    let dict = DoubleArrayTrie::from_terms(terms.iter());

    let zipper = DoubleArrayTrieZipper::new_from_dict(&dict);
    let mut results: Vec<String> = zipper
        .with_prefix(b"proc")
        .unwrap()
        .map(|(path, _)| String::from_utf8(path).unwrap())
        .collect();

    results.sort();
    assert_eq!(results, vec!["process", "processUser"]);
}

#[test]
fn test_dat_prefix_not_exists() {
    let terms = vec!["hello", "world"];
    let dict = DoubleArrayTrie::from_terms(terms.iter());

    let zipper = DoubleArrayTrieZipper::new_from_dict(&dict);
    assert!(zipper.with_prefix(b"xyz").is_none());
}

#[test]
fn test_dat_empty_prefix_returns_all() {
    let terms = vec!["cat", "dog", "fish"];
    let dict = DoubleArrayTrie::from_terms(terms.iter());

    let zipper = DoubleArrayTrieZipper::new_from_dict(&dict);
    let mut results: Vec<String> = zipper
        .with_prefix(b"")
        .unwrap()
        .map(|(path, _)| String::from_utf8(path).unwrap())
        .collect();

    results.sort();
    assert_eq!(results, vec!["cat", "dog", "fish"]);
}

#[test]
fn test_dat_prefix_equals_term() {
    let terms = vec!["cat", "cats"];
    let dict = DoubleArrayTrie::from_terms(terms.iter());

    let zipper = DoubleArrayTrieZipper::new_from_dict(&dict);
    let mut results: Vec<String> = zipper
        .with_prefix(b"cat")
        .unwrap()
        .map(|(path, _)| String::from_utf8(path).unwrap())
        .collect();

    results.sort();
    assert_eq!(results, vec!["cat", "cats"]);
}

#[test]
fn test_dat_prefix_longer_than_all_terms() {
    let terms = vec!["cat", "dog"];
    let dict = DoubleArrayTrie::from_terms(terms.iter());

    let zipper = DoubleArrayTrieZipper::new_from_dict(&dict);
    assert!(zipper.with_prefix(b"cathedral").is_none());
}

#[test]
fn test_dat_empty_dictionary() {
    let dict: DoubleArrayTrie = DoubleArrayTrie::from_terms(Vec::<&str>::new().iter());

    let zipper = DoubleArrayTrieZipper::new_from_dict(&dict);
    assert!(zipper.with_prefix(b"any").is_none());
}

// ============================================================================
// Basic Functionality Tests - DynamicDawg
// ============================================================================

#[test]
fn test_dawg_prefix_exists_single_match() {
    let terms = vec!["hello", "world"];
    let dict: DynamicDawg<()> = DynamicDawg::from_terms(terms.iter());

    let zipper = DynamicDawgZipper::new_from_dict(&dict);
    let results: Vec<String> = zipper
        .with_prefix(b"wor")
        .unwrap()
        .map(|(path, _)| String::from_utf8(path).unwrap())
        .collect();

    assert_eq!(results, vec!["world"]);
}

#[test]
fn test_dawg_prefix_exists_multiple_matches() {
    let terms = vec!["process", "processUser", "produce", "product"];
    let dict: DynamicDawg<()> = DynamicDawg::from_terms(terms.iter());

    let zipper = DynamicDawgZipper::new_from_dict(&dict);
    let mut results: Vec<String> = zipper
        .with_prefix(b"proc")
        .unwrap()
        .map(|(path, _)| String::from_utf8(path).unwrap())
        .collect();

    results.sort();
    assert_eq!(results, vec!["process", "processUser"]);
}

#[test]
fn test_dawg_prefix_not_exists() {
    let terms = vec!["hello", "world"];
    let dict: DynamicDawg<()> = DynamicDawg::from_terms(terms.iter());

    let zipper = DynamicDawgZipper::new_from_dict(&dict);
    assert!(zipper.with_prefix(b"xyz").is_none());
}

// ============================================================================
// Character-Level Tests - DoubleArrayTrieChar
// ============================================================================

#[test]
fn test_dat_char_unicode_prefix() {
    let terms = vec!["café", "cafétéria", "naïve"];
    let dict = DoubleArrayTrieChar::from_terms(terms.iter());

    let zipper = DoubleArrayTrieCharZipper::new_from_dict(&dict);
    let café_prefix: Vec<char> = "caf".chars().collect();
    let mut results: Vec<String> = zipper
        .with_prefix(&café_prefix)
        .unwrap()
        .map(|(path, _)| path.iter().collect())
        .collect();

    results.sort();
    assert_eq!(results, vec!["café", "cafétéria"]);
}

#[test]
fn test_dat_char_emoji() {
    let terms = vec!["🎉party", "🎉celebration", "🎂cake"];
    let dict = DoubleArrayTrieChar::from_terms(terms.iter());

    let zipper = DoubleArrayTrieCharZipper::new_from_dict(&dict);
    let emoji_prefix: Vec<char> = "🎉".chars().collect();
    let mut results: Vec<String> = zipper
        .with_prefix(&emoji_prefix)
        .unwrap()
        .map(|(path, _)| path.iter().collect())
        .collect();

    results.sort();
    assert_eq!(results, vec!["🎉celebration", "🎉party"]);
}

#[test]
fn test_dat_char_cjk() {
    let terms = vec!["中文", "中国", "日本"];
    let dict = DoubleArrayTrieChar::from_terms(terms.iter());

    let zipper = DoubleArrayTrieCharZipper::new_from_dict(&dict);
    let zhong_prefix: Vec<char> = "中".chars().collect();
    let mut results: Vec<String> = zipper
        .with_prefix(&zhong_prefix)
        .unwrap()
        .map(|(path, _)| path.iter().collect())
        .collect();

    results.sort();
    assert_eq!(results, vec!["中国", "中文"]);
}

// ============================================================================
// Character-Level Tests - DynamicDawgChar
// ============================================================================

#[test]
fn test_dawg_char_unicode_prefix() {
    let terms = vec!["naïve", "naïveté"];
    let dict: DynamicDawgChar<()> = DynamicDawgChar::from_terms(terms.iter());

    let zipper = DynamicDawgCharZipper::new_from_dict(&dict);
    let naive_prefix: Vec<char> = "naïv".chars().collect();
    let mut results: Vec<String> = zipper
        .with_prefix(&naive_prefix)
        .unwrap()
        .map(|(path, _)| path.iter().collect())
        .collect();

    results.sort();
    assert_eq!(results, vec!["naïve", "naïveté"]);
}

// ============================================================================
// Valued Dictionary Tests
// ============================================================================

#[test]
fn test_valued_dict_prefix_iteration() {
    let terms_with_values = vec![("cat", 1), ("cats", 2), ("dog", 3)];
    let dict = DoubleArrayTrie::from_terms_with_values(
        terms_with_values
            .into_iter()
            .map(|(k, v)| (k, v)),
    );

    let zipper = DoubleArrayTrieZipper::new_from_dict(&dict);
    let mut results: Vec<(String, usize)> = zipper
        .with_prefix_values(b"cat")
        .unwrap()
        .map(|(path, val)| (String::from_utf8(path).unwrap(), val))
        .collect();

    results.sort();
    assert_eq!(results, vec![("cat".to_string(), 1), ("cats".to_string(), 2)]);
}

#[test]
fn test_valued_dict_no_matches() {
    let terms_with_values = vec![("hello", 1), ("world", 2)];
    let dict = DoubleArrayTrie::from_terms_with_values(
        terms_with_values
            .into_iter()
            .map(|(k, v)| (k, v)),
    );

    let zipper = DoubleArrayTrieZipper::new_from_dict(&dict);
    assert!(zipper.with_prefix_values(b"xyz").is_none());
}

// ============================================================================
// Edge Cases
// ============================================================================

#[test]
fn test_single_character_terms() {
    let terms = vec!["a", "b", "c"];
    let dict = DoubleArrayTrie::from_terms(terms.iter());

    let zipper = DoubleArrayTrieZipper::new_from_dict(&dict);
    let results: Vec<String> = zipper
        .with_prefix(b"a")
        .unwrap()
        .map(|(path, _)| String::from_utf8(path).unwrap())
        .collect();

    assert_eq!(results, vec!["a"]);
}

#[test]
fn test_very_long_prefix() {
    let long_term = "a".repeat(100);
    let terms = vec![long_term.as_str()];
    let dict = DoubleArrayTrie::from_terms(terms.iter());

    let zipper = DoubleArrayTrieZipper::new_from_dict(&dict);
    let long_prefix = "a".repeat(50);
    let results: Vec<String> = zipper
        .with_prefix(long_prefix.as_bytes())
        .unwrap()
        .map(|(path, _)| String::from_utf8(path).unwrap())
        .collect();

    assert_eq!(results, vec![long_term]);
}

#[test]
fn test_prefix_substring_but_not_prefix() {
    let terms = vec!["hello", "world"];
    let dict = DoubleArrayTrie::from_terms(terms.iter());

    let zipper = DoubleArrayTrieZipper::new_from_dict(&dict);
    // "ell" is a substring of "hello" but not a prefix
    assert!(zipper.with_prefix(b"ell").is_none());
}

// ============================================================================
// Consistency Tests - Same Results Across Backends
// ============================================================================

#[test]
fn test_consistency_across_backends() {
    let terms = vec!["apple", "application", "apply", "banana", "band"];

    // Build dictionaries with all backends
    let dat = DoubleArrayTrie::from_terms(terms.iter());
    let dawg: DynamicDawg<()> = DynamicDawg::from_terms(terms.iter());

    // Query with same prefix
    let dat_results: Vec<String> = sorted_results(
        DoubleArrayTrieZipper::new_from_dict(&dat)
            .with_prefix(b"app")
            .unwrap()
            .map(|(path, _)| String::from_utf8(path).unwrap())
            .collect(),
    );

    let dawg_results: Vec<String> = sorted_results(
        DynamicDawgZipper::new_from_dict(&dawg)
            .with_prefix(b"app")
            .unwrap()
            .map(|(path, _)| String::from_utf8(path).unwrap())
            .collect(),
    );

    // All backends should return same results
    assert_eq!(dat_results, dawg_results);
    assert_eq!(dat_results, vec!["apple", "application", "apply"]);
}

#[test]
fn test_consistency_char_backends() {
    let terms = vec!["café", "cafétéria", "naïve"];

    let dat_char = DoubleArrayTrieChar::from_terms(terms.iter());
    let dawg_char: DynamicDawgChar<()> = DynamicDawgChar::from_terms(terms.iter());

    let café_prefix: Vec<char> = "caf".chars().collect();

    let dat_results: Vec<String> = sorted_results(
        DoubleArrayTrieCharZipper::new_from_dict(&dat_char)
            .with_prefix(&café_prefix)
            .unwrap()
            .map(|(path, _)| path.iter().collect())
            .collect(),
    );

    let dawg_results: Vec<String> = sorted_results(
        DynamicDawgCharZipper::new_from_dict(&dawg_char)
            .with_prefix(&café_prefix)
            .unwrap()
            .map(|(path, _)| path.iter().collect())
            .collect(),
    );

    assert_eq!(dat_results, dawg_results);
    assert_eq!(dat_results, vec!["café", "cafétéria"]);
}

// ============================================================================
// Performance / Scale Tests
// ============================================================================

#[test]
fn test_large_dictionary_selective_prefix() {
    // Create a larger dictionary
    let mut terms: Vec<String> = Vec::new();
    for i in 0..1000 {
        terms.push(format!("word{}", i));
    }
    // Add specific prefix matches
    terms.push("prefix1".to_string());
    terms.push("prefix2".to_string());
    terms.push("prefix3".to_string());

    let dict = DoubleArrayTrie::from_terms(terms.iter());

    let zipper = DoubleArrayTrieZipper::new_from_dict(&dict);
    let results: Vec<String> = sorted_results(
        zipper
            .with_prefix(b"prefix")
            .unwrap()
            .map(|(path, _)| String::from_utf8(path).unwrap())
            .collect(),
    );

    assert_eq!(results, vec!["prefix1", "prefix2", "prefix3"]);
    assert_eq!(results.len(), 3); // Much smaller than total 1003 terms
}

#[test]
fn test_count_matches() {
    let terms = vec!["test", "testing", "tested", "tester"];
    let dict = DoubleArrayTrie::from_terms(terms.iter());

    let zipper = DoubleArrayTrieZipper::new_from_dict(&dict);
    let count = zipper.with_prefix(b"test").unwrap().count();

    assert_eq!(count, 4);
}
