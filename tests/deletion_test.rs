//! Test for deletion bug fix

use liblevenshtein::prelude::*;

#[test]
fn test_aple_to_apple() {
    let dict = PathMapDictionary::from_terms(vec!["apple"]);
    let transducer = Transducer::new(dict, Algorithm::Standard);

    let results: Vec<_> = transducer.query("aple", 1).collect();

    println!("Query 'aple' against 'apple' with distance 1:");
    for term in &results {
        println!("  Found: {}", term);
    }

    assert!(
        !results.is_empty(),
        "Should find 'apple' from query 'aple' with distance 1"
    );
    assert!(
        results.contains(&"apple".to_string()),
        "Results should contain 'apple'"
    );
}

#[test]
fn test_apple_to_aple() {
    let dict = PathMapDictionary::from_terms(vec!["aple"]);
    let transducer = Transducer::new(dict, Algorithm::Standard);

    let results: Vec<_> = transducer.query("apple", 1).collect();

    println!("Query 'apple' against 'aple' with distance 1:");
    for term in &results {
        println!("  Found: {}", term);
    }

    assert!(
        !results.is_empty(),
        "Should find 'aple' from query 'apple' with distance 1"
    );
    assert!(
        results.contains(&"aple".to_string()),
        "Results should contain 'aple'"
    );
}

#[test]
fn test_deletion_operations() {
    // Test various deletion scenarios
    let dict = PathMapDictionary::from_terms(vec!["test", "testing", "apple", "world"]);
    let transducer = Transducer::new(dict, Algorithm::Standard);

    // Query has extra character (deletion from query)
    let results: Vec<_> = transducer.query("testt", 1).collect();
    println!("Query 'testt' with distance 1: {:?}", results);
    assert!(
        results.contains(&"test".to_string()),
        "'testt' should match 'test'"
    );

    // Query missing character (insertion from dictionary)
    let results: Vec<_> = transducer.query("aple", 1).collect();
    println!("Query 'aple' with distance 1: {:?}", results);
    assert!(
        results.contains(&"apple".to_string()),
        "'aple' should match 'apple'"
    );
}
