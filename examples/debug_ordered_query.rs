//! Debug ordered query to understand the discrepancy

use liblevenshtein::prelude::*;
use std::fs;

fn main() {
    println!("Loading dictionary...");
    let contents = fs::read_to_string("data/english_words.txt")
        .expect("Failed to read data/english_words.txt");

    let words: Vec<String> = contents
        .lines()
        .map(|s| s.trim().to_lowercase())
        .filter(|s| !s.is_empty() && s.chars().all(|c| c.is_ascii_alphabetic()))
        .collect();

    println!("Loaded {} words\n", words.len());

    let dict = PathMapDictionary::from_terms(words.iter().map(|s| s.as_str()));
    let transducer = Transducer::new(dict, Algorithm::Standard);

    // Test with first query word from benchmark
    let test_word = &words[words.len() / 1000];
    println!("Testing with query: '{}'\n", test_word);

    println!("=== Unordered Query ===");
    let unordered: Vec<_> = transducer.query(test_word, 2).collect();
    println!("Count: {}", unordered.len());
    if unordered.len() < 20 {
        println!("Results: {:?}\n", unordered);
    } else {
        println!("First 10: {:?}...\n", &unordered[..10]);
    }

    println!("=== Ordered Query ===");
    let ordered: Vec<_> = transducer.query_ordered(test_word, 2).collect();
    println!("Count: {}", ordered.len());
    if ordered.len() < 20 {
        for c in &ordered {
            println!("  {} (d={})", c.term, c.distance);
        }
    } else {
        println!("First 10:");
        for c in ordered.iter().take(10) {
            println!("  {} (d={})", c.term, c.distance);
        }
        println!("...");
    }

    println!("\n=== Comparison ===");
    println!("Unordered count: {}", unordered.len());
    println!("Ordered count: {}", ordered.len());

    // Check for duplicates
    let mut seen = std::collections::HashSet::new();
    let mut duplicates = 0;
    for c in &ordered {
        if !seen.insert(&c.term) {
            if duplicates < 10 {
                println!("DUPLICATE: {} (d={})", c.term, c.distance);
            }
            duplicates += 1;
        }
    }
    if duplicates > 0 {
        println!("\n❌ Found {} duplicates in ordered results!", duplicates);
    } else {
        println!("\n✅ No duplicates found");
    }
}
