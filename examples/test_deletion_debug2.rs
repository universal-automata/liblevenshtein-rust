use liblevenshtein::prelude::*;

fn main() {
    // Same dictionary as the test
    let dict = DoubleArrayTrie::from_terms(vec!["test", "testing", "apple", "world"]);
    let transducer = Transducer::new(dict, Algorithm::Standard);
    
    // Query has extra character - should require 1 deletion to match "test"
    println!("Testing 'testt' with distance 1:");
    let results: Vec<_> = transducer.query("testt", 1).collect();
    println!("Results: {:?}", results);
    println!("Contains 'test': {}", results.contains(&"test".to_string()));
    println!("Contains 'testing': {}", results.contains(&"testing".to_string()));
    
    // Query missing character (insertion from dictionary)
    println!("\nTesting 'aple' with distance 1:");
    let results2: Vec<_> = transducer.query("aple", 1).collect();
    println!("Results: {:?}", results2);
    println!("Contains 'apple': {}", results2.contains(&"apple".to_string()));
}
