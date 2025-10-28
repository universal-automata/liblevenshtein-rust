//! Demonstration of CompressedSuffixAutomaton with fuzzy substring matching.
//!
//! This example shows that the compressed version works identically to the
//! original SuffixAutomaton but with reduced memory footprint.

use liblevenshtein::prelude::*;

fn main() {
    println!("=== Compressed Suffix Automaton Demo ===\n");

    // Create compressed suffix automaton from text
    let texts = vec![
        "The quick brown fox jumps over the lazy dog",
        "Pack my box with five dozen liquor jugs",
        "How vexingly quick daft zebras jump",
    ];

    println!("Building compressed suffix automaton from {} texts...", texts.len());
    let compressed_sa = CompressedSuffixAutomaton::from_texts(texts.clone());

    println!("States: {}", compressed_sa.state_count());
    println!("Memory: {} bytes", compressed_sa.memory_bytes());
    println!("Bytes per state: {}\n", compressed_sa.memory_bytes() / compressed_sa.state_count());

    // Test exact substring matching
    println!("--- Exact Substring Matching ---");
    let test_substrings = vec!["quick", "fox", "lazy", "box", "zebras"];

    for substring in &test_substrings {
        if compressed_sa.contains(substring) {
            println!("✓ Found: '{}'", substring);
        } else {
            println!("✗ Not found: '{}'", substring);
        }
    }

    // Test fuzzy substring matching with Transducer
    println!("\n--- Fuzzy Substring Matching (distance = 1) ---");

    let transducer = Transducer::new(compressed_sa.clone(), Algorithm::Standard);

    let queries = vec![
        ("quik", "quick with typo"),
        ("lazzy", "lazy with typo"),
        ("fax", "fox with typo"),
    ];

    for (query, description) in &queries {
        println!("\nQuery: '{}' ({})", query, description);
        let matches: Vec<_> = transducer
            .query_with_distance(query, 1)
            .take(5)
            .collect();

        if matches.is_empty() {
            println!("  No matches found");
        } else {
            for candidate in matches {
                println!("  → '{}' (distance: {})", candidate.term, candidate.distance);
            }
        }
    }

    // Compare memory with estimation
    println!("\n--- Memory Analysis ---");
    let original_sa = SuffixAutomaton::from_texts(texts);

    println!("Original SuffixAutomaton:");
    println!("  States: {}", original_sa.state_count());
    println!("  Estimated memory (HashMap-based): ~{} bytes/state",
             48); // Rough estimate

    println!("\nCompressed SuffixAutomaton:");
    println!("  States: {}", compressed_sa.state_count());
    println!("  Actual memory: ~{} bytes/state",
             compressed_sa.memory_bytes() / compressed_sa.state_count());

    let savings_percent = (1.0 - (compressed_sa.memory_bytes() as f64 /
                                  (original_sa.state_count() * 48) as f64)) * 100.0;
    println!("\nEstimated memory savings: {:.1}%", savings_percent);

    println!("\n=== Demo Complete ===");
}
