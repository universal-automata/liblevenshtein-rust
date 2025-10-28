//! Simple spell checker example using liblevenshtein.
//!
//! This example demonstrates how to use liblevenshtein for approximate
//! string matching, useful for spell checking and fuzzy search.

use liblevenshtein::prelude::*;

fn main() {
    // Create a dictionary of valid words
    let dictionary_words = vec![
        "apple",
        "application",
        "apply",
        "banana",
        "band",
        "can",
        "candy",
        "cat",
        "dog",
        "example",
        "test",
        "testing",
        "tested",
        "hello",
        "world",
        "rust",
        "programming",
    ];

    println!(
        "Building dictionary with {} words...",
        dictionary_words.len()
    );
    let dict = DoubleArrayTrie::from_terms(dictionary_words);

    // Create a transducer with Standard algorithm
    let transducer = Transducer::new(dict, Algorithm::Standard);

    println!("\n=== Spell Checker Demo ===\n");

    // Test words with typos
    let test_queries = vec![
        ("aple", 1),       // Missing 'p' in "apple"
        ("applie", 2),     // Extra 'i' in "apple"
        ("tset", 1),       // Transposed letters in "test"
        ("tesing", 1),     // Missing 't' in "testing"
        ("wrld", 2),       // Missing vowels in "world"
        ("programing", 1), // Missing 'm' in "programming"
    ];

    for (query, max_distance) in test_queries {
        println!("Query: '{}' (max distance: {})", query, max_distance);

        let matches: Vec<_> = transducer.query(query, max_distance).collect();

        if matches.is_empty() {
            println!("  No suggestions found\n");
        } else {
            println!("  Suggestions:");
            for term in matches {
                println!("    - {}", term);
            }
            println!();
        }
    }

    // Demonstrate query with distances
    println!("=== Query with Distances ===\n");

    let query = "tast";
    let max_distance = 2;

    println!("Query: '{}' (max distance: {})", query, max_distance);
    println!("Results:");

    for candidate in transducer.query_with_distance(query, max_distance) {
        println!("  - {} (distance: {})", candidate.term, candidate.distance);
    }

    // Compare different algorithms
    println!("\n=== Algorithm Comparison ===\n");

    let test_word = "tset";
    let dict2 = PathMapDictionary::from_terms(vec!["test", "set", "reset"]);

    println!("Query: '{}' with distance 1", test_word);

    // Standard algorithm
    let trans_standard = Transducer::new(dict2.clone(), Algorithm::Standard);
    let matches_standard: Vec<_> = trans_standard.query(test_word, 1).collect();
    println!("\nStandard algorithm:");
    for term in matches_standard {
        println!("  - {}", term);
    }

    // Transposition algorithm
    let trans_transposition = Transducer::new(dict2, Algorithm::Transposition);
    let matches_trans: Vec<_> = trans_transposition.query(test_word, 1).collect();
    println!("\nTransposition algorithm:");
    for term in matches_trans {
        println!("  - {}", term);
    }
}
