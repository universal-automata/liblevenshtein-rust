use liblevenshtein::distance::transposition_distance;
use liblevenshtein::prelude::*;

#[test]
fn test_yu_to_uy() {
    println!("\n=== Test 'yu' -> 'uy' ===\n");

    let dict = DoubleArrayTrie::from_terms(vec!["uy".to_string()]);
    let transducer = Transducer::new(dict, Algorithm::Transposition);

    println!("Dictionary: [\"uy\"]");
    println!("Query: \"yu\"");
    println!("Max distance: 1\n");

    // Check distance function
    let dist = transposition_distance("yu", "uy");
    println!("transposition_distance(\"yu\", \"uy\") = {}", dist);
    assert_eq!(dist, 1, "Distance function should return 1");

    // Check automaton
    let results: Vec<_> = transducer.query_with_distance("yu", 1).collect();
    println!("Automaton results: {:?}\n", results);

    if results.is_empty() {
        println!("❌ FAILURE: No results found!");
        panic!("Automaton should find 'uy' at distance 1");
    }

    let candidate = results
        .iter()
        .find(|c| c.term == "uy")
        .expect("Should find 'uy'");
    println!("Found 'uy' at distance: {}", candidate.distance);

    if candidate.distance != 1 {
        println!("❌ FAILURE: Incorrect distance!");
        println!("  Expected: 1");
        println!("  Got: {}", candidate.distance);
        panic!("Distance mismatch");
    }

    println!("✓ SUCCESS!");
}
