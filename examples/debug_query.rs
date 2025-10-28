//! Debug query processing to understand what's happening

use liblevenshtein::dictionary::suffix_automaton::SuffixAutomaton;
use liblevenshtein::dictionary::Dictionary;
use liblevenshtein::transducer::{Algorithm, Transducer};

fn main() {
    println!("=== Testing with 'a' ===");
    test_query("a", "a");

    println!("\n=== Testing with 'ab' ===");
    test_query("ab", "ab");

    println!("\n=== Testing with 'ab' query on 'a' ===");
    test_query("ab", "a");

    println!("\n=== Testing with 'ab' query on 'b' ===");
    test_query("ab", "b");
}

fn test_query(text: &str, query: &str) {
    let dict = SuffixAutomaton::from_text(text);
    println!("Text: '{}', Query: '{}'", text, query);
    println!("Dict state count: {}", dict.state_count());

    // Test contains
    println!("dict.contains('{}'): {}", query, dict.contains(query));

    // Test transducer
    let transducer = Transducer::new(dict, Algorithm::Standard);
    let results: Vec<_> = transducer.query(query, 0).collect();
    println!("Query results (distance=0): {} matches", results.len());
    for (i, term) in results.iter().enumerate() {
        println!("  [{}] '{}'", i, term);
    }

    // Try with distance=1
    let transducer2 = Transducer::new(SuffixAutomaton::from_text(text), Algorithm::Standard);
    let results2: Vec<_> = transducer2.query(query, 1).collect();
    println!("Query results (distance=1): {} matches", results2.len());
    for (i, term) in results2.iter().enumerate().take(5) {
        println!("  [{}] '{}'", i, term);
    }
}
