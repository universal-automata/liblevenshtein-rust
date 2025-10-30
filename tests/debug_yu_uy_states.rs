use liblevenshtein::prelude::*;

#[test]
fn debug_yu_uy_all_results() {
    println!("\n=== Debug all results for 'yu' -> 'uy' ===\n");

    let dict = DoubleArrayTrie::from_terms(vec!["uy".to_string()]);
    let transducer = Transducer::new(dict, Algorithm::Transposition);

    // Get ALL results within distance 2 to see what we're finding
    let results: Vec<_> = transducer.query_with_distance("yu", 2).collect();

    println!("All results within distance 2:");
    for (i, candidate) in results.iter().enumerate() {
        println!("  {}: term='{}', distance={}", i, candidate.term, candidate.distance);
    }
    println!();

    // Also try distance 1
    let results_d1: Vec<_> = transducer.query_with_distance("yu", 1).collect();
    println!("Results within distance 1:");
    for (i, candidate) in results_d1.iter().enumerate() {
        println!("  {}: term='{}', distance={}", i, candidate.term, candidate.distance);
    }
    println!();

    if results_d1.is_empty() {
        println!("No results at distance 1!");
        println!("This means the transposition path is not completing at distance 1.");
    } else {
        let uy_d1 = results_d1.iter().find(|c| c.term == "uy");
        if let Some(c) = uy_d1 {
            println!("Found 'uy' at distance {}", c.distance);
            if c.distance != 1 {
                panic!("Wrong distance for 'uy': expected 1, got {}", c.distance);
            }
        } else {
            println!("'uy' not found at distance 1, but other terms were");
            panic!("Expected to find 'uy'");
        }
    }
}
