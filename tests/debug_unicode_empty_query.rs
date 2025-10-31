use liblevenshtein::prelude::*;

#[test]
fn debug_unicode_vs_ascii_empty_query() {
    println!("\n=== Debug Unicode vs ASCII Empty Query ===\n");

    // ASCII case (works)
    println!("--- ASCII Case ---");
    let dict_ascii = DoubleArrayTrie::from_terms(vec!["a".to_string()]);
    println!("Dictionary: [\"a\"]");
    println!("Character 'a': {:?}", 'a');
    println!("Bytes: {:?}", "a".as_bytes());

    let trans_ascii = Transducer::new(dict_ascii, Algorithm::Standard);
    let results_ascii: Vec<_> = trans_ascii.query("", 1).collect();
    println!("Results: {:?}\n", results_ascii);

    // Unicode case (fails)
    println!("--- Unicode Case ---");
    let dict_unicode = DoubleArrayTrie::from_terms(vec!["¡".to_string()]);
    println!("Dictionary: [\"¡\"]");
    println!("Character '¡': {:?}", '¡');
    println!("Bytes: {:?}", "¡".as_bytes());
    println!("Byte length: {}", "¡".len());
    println!("Char length: {}", "¡".chars().count());

    let trans_unicode = Transducer::new(dict_unicode, Algorithm::Standard);
    let results_unicode: Vec<_> = trans_unicode.query("", 1).collect();
    println!("Results: {:?}\n", results_unicode);

    // Multi-byte ASCII-range characters
    println!("--- Other Multi-Byte Characters ---");
    for term in ["é", "中", "🎉", "aa"] {
        let dict = DoubleArrayTrie::from_terms(vec![term.to_string()]);
        let trans = Transducer::new(dict, Algorithm::Standard);
        let results: Vec<_> = trans.query("", 1).collect();
        println!(
            "  \"{}\": bytes={}, chars={}, results={:?}",
            term,
            term.len(),
            term.chars().count(),
            results
        );
    }

    println!("\n--- Analysis ---");
    println!("ASCII 'a': 1 byte, 1 char → Works ✓");
    println!("Unicode '¡': 2 bytes, 1 char → Fails ❌");
    println!("\nHypothesis: The automaton is working at byte level,");
    println!("so multi-byte characters need multiple insertions.");
    println!("With max_distance=1, '¡' (2 bytes) is out of reach.");

    // Test with higher max_distance for Unicode
    println!("\n--- Testing Unicode with Higher Max Distance ---");
    let dict = DoubleArrayTrie::from_terms(vec!["¡".to_string()]);
    let trans = Transducer::new(dict, Algorithm::Standard);

    for dist in 0..=3 {
        let results: Vec<_> = trans.query("", dist).collect();
        println!("  max_distance={}: {:?}", dist, results);
    }
}

#[test]
fn test_unicode_character_distances() {
    println!("\n=== Unicode Character Distance Analysis ===\n");

    use liblevenshtein::distance::standard_distance;

    // Test distances from empty string
    let test_cases = vec![
        ("a", "1 byte, 1 char"),
        ("¡", "2 bytes, 1 char"),
        ("é", "2 bytes, 1 char"),
        ("中", "3 bytes, 1 char"),
        ("🎉", "4 bytes, 1 char"),
        ("aa", "2 bytes, 2 chars"),
    ];

    for (term, desc) in test_cases {
        let dist = standard_distance("", term);
        println!("\"\" → \"{}\": distance={} ({})", term, dist, desc);
    }

    println!("\n--- Conclusion ---");
    println!("Distance function appears to work at character level (correct).");
    println!("Automaton might be working at byte level (incorrect for Unicode).");
}
