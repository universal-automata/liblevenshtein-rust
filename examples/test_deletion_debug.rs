use liblevenshtein::prelude::*;

fn main() {
    let dict = DoubleArrayTrie::from_terms(vec!["test"]);
    let transducer = Transducer::new(dict, Algorithm::Standard);
    
    // Query has extra character - should require 1 deletion to match "test"
    println!("Testing 'testt' against 'test' with distance 1:");
    let results: Vec<_> = transducer.query("testt", 1).collect();
    println!("Results: {:?}", results);
    println!("Expected: [\"test\"]");
    
    // Also test with distance 2
    println!("\nTesting 'testt' against 'test' with distance 2:");
    let results2: Vec<_> = transducer.query("testt", 2).collect();
    println!("Results: {:?}", results2);
    
    // Test the reverse - query missing character
    println!("\nTesting 'tes' against 'test' with distance 1:");
    let results3: Vec<_> = transducer.query("tes", 1).collect();
    println!("Results: {:?}", results3);
    println!("Expected: [\"test\"]");
    
    // Test with distance 0 for sanity check
    println!("\nTesting 'test' against 'test' with distance 0:");
    let results4: Vec<_> = transducer.query("test", 0).collect();
    println!("Results: {:?}", results4);
    println!("Expected: [\"test\"]");
}
