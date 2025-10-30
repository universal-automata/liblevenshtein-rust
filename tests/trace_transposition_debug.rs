use liblevenshtein::prelude::*;
use liblevenshtein::distance::transposition_distance;

#[test]
fn trace_ab_to_ba() {
    println!("\n=== Detailed Transposition Trace ===\n");

    // The failing case: query "ab" should find "ba" at distance 1
    let dict_words = vec!["ba".to_string()];
    let dict = DoubleArrayTrie::from_terms(dict_words.clone());

    println!("Dictionary: {:?}", dict_words);
    println!("Query: \"ab\"");
    println!("Max distance: 1\n");

    // First verify the distance function knows they're close
    let dist = transposition_distance("ab", "ba");
    println!("transposition_distance(\"ab\", \"ba\") = {}", dist);
    assert_eq!(dist, 1, "Distance function should report 1");
    println!("✓ Distance function confirms they differ by 1 transposition\n");

    // Now check the automaton
    let transducer = Transducer::new(dict, Algorithm::Transposition);
    let results: Vec<_> = transducer.query("ab", 1).collect();

    println!("Automaton results: {:?}", results);

    if results.contains(&"ba".to_string()) {
        println!("✓ SUCCESS: Found 'ba'!");
    } else {
        println!("❌ FAILURE: Missing 'ba'!");
        println!("\nThis means the automaton is not exploring the correct paths.");
        println!("The issue is in the state transition logic.");

        println!("\n=== Key Questions ===");
        println!("1. Does the automaton create a special position at (0,1,true)?");
        println!("2. Does that position survive subsumption?");
        println!("3. Does the transition from that position follow 'b' correctly?");
        println!("4. Does it reach the final state?");

        panic!("Transposition test failed: 'ab' should find 'ba' at distance 1");
    }
}
