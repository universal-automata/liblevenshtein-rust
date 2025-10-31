use liblevenshtein::distance::merge_and_split_distance;
use liblevenshtein::prelude::*;

#[test]
fn debug_merge_split_b_to_aaa() {
    println!("\n=== Debug MergeAndSplit: 'b' → 'aaa' ===\n");

    // Failing case from proptest
    let dict = DoubleArrayTrie::from_terms(vec!["aaa".to_string()]);
    let transducer = Transducer::new(dict, Algorithm::MergeAndSplit);

    println!("Dictionary: [\"aaa\"]");
    println!("Query: \"b\"");
    println!("Max distance: 3\n");

    // Check what the distance function says
    let cache = liblevenshtein::distance::create_memo_cache();
    let func_dist = merge_and_split_distance("b", "aaa", &cache);
    println!("merge_and_split_distance(\"b\", \"aaa\") = {}", func_dist);

    // Check what the automaton says
    let results: Vec<_> = transducer.query_with_distance("b", 3).collect();
    println!("Automaton results: {:?}\n", results);

    if let Some(candidate) = results.iter().find(|c| c.term == "aaa") {
        println!("Found \"aaa\" at distance: {}", candidate.distance);
        if candidate.distance != func_dist {
            println!("❌ MISMATCH!");
            println!("  Function: {}", func_dist);
            println!("  Automaton: {}", candidate.distance);
        } else {
            println!("✓ Distances match");
        }
    } else {
        println!("❌ \"aaa\" not found in results");
        println!("  Expected distance: {}", func_dist);
    }
}

#[test]
fn debug_merge_split_aaaa() {
    println!("\n=== Debug MergeAndSplit: 'b' → 'aaaa' ===\n");

    // Another failing case
    let dict = DoubleArrayTrie::from_terms(vec!["aaaa".to_string(), "aaaa".to_string()]);
    let transducer = Transducer::new(dict, Algorithm::MergeAndSplit);

    println!("Dictionary: [\"aaaa\", \"aaaa\"] (duplicates)");
    println!("Query: \"b\"");
    println!("Max distance: 3\n");

    let cache = liblevenshtein::distance::create_memo_cache();
    let func_dist = merge_and_split_distance("b", "aaaa", &cache);
    println!("merge_and_split_distance(\"b\", \"aaaa\") = {}", func_dist);

    let results: Vec<_> = transducer.query_with_distance("b", 3).collect();
    println!("Automaton results: {:?}\n", results);

    if results.is_empty() {
        println!("❌ No results found");
        println!("  Expected: [\"aaaa\"] at distance {}", func_dist);
    }
}

#[test]
fn test_merge_split_various_cases() {
    println!("\n=== MergeAndSplit Various Test Cases ===\n");

    let cache = liblevenshtein::distance::create_memo_cache();

    let test_cases = vec![
        ("b", "aaa"),
        ("b", "aaaa"),
        ("a", "aa"),
        ("aa", "a"),
        ("ab", "ba"),
        ("abc", "xyz"),
    ];

    for (query, term) in test_cases {
        let dict = DoubleArrayTrie::from_terms(vec![term.to_string()]);
        let transducer = Transducer::new(dict, Algorithm::MergeAndSplit);

        let func_dist = merge_and_split_distance(query, term, &cache);
        let results: Vec<_> = transducer.query_with_distance(query, 5).collect();

        let auto_dist = results.iter().find(|c| c.term == term).map(|c| c.distance);

        let status = match auto_dist {
            Some(d) if d == func_dist => "✓",
            Some(d) => &format!("❌ (expected {}, got {})", func_dist, d),
            None => &format!("❌ (expected {}, not found)", func_dist),
        };

        println!("  \"{}\" → \"{}\": {}", query, term, status);
    }
}

#[test]
fn test_merge_split_operations() {
    println!("\n=== MergeAndSplit Operation Examples ===\n");

    let cache = liblevenshtein::distance::create_memo_cache();

    println!("Merge operation (two chars → one):");
    println!(
        "  \"ab\" → \"c\": {}",
        merge_and_split_distance("ab", "c", &cache)
    );
    println!(
        "  \"xy\" → \"a\": {}",
        merge_and_split_distance("xy", "a", &cache)
    );

    println!("\nSplit operation (one char → two):");
    println!(
        "  \"a\" → \"bc\": {}",
        merge_and_split_distance("a", "bc", &cache)
    );
    println!(
        "  \"x\" → \"yz\": {}",
        merge_and_split_distance("x", "yz", &cache)
    );

    println!("\nCombined:");
    println!(
        "  \"b\" → \"aaa\": {}",
        merge_and_split_distance("b", "aaa", &cache)
    );
    println!("    Possible: substitute b→a, then split a→aa (2 ops)");
    println!("    Or: delete b, insert a, split a→aa (3 ops)");
}
