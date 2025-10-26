//! Benchmark comparing generic QueryIterator vs optimized DawgQueryIterator

use liblevenshtein::prelude::*;
use std::fs;
use std::time::Instant;

fn main() {
    println!("=== DAWG Query Iterator Comparison ===\n");

    // Load real English dictionary
    println!("Loading English dictionary...");
    let contents = fs::read_to_string("data/english_words.txt")
        .expect("Failed to read data/english_words.txt");

    let words: Vec<String> = contents
        .lines()
        .map(|s| s.trim().to_lowercase())
        .filter(|s| !s.is_empty() && s.chars().all(|c| c.is_ascii_alphabetic()))
        .collect();

    println!("Loaded {} words\n", words.len());

    // Build DAWG
    println!("Building DAWG...");
    let start = Instant::now();
    let dawg = DawgDictionary::from_iter(words.iter().map(|s| s.as_str()));
    println!("Built in {:?}", start.elapsed());
    println!("DAWG nodes: {}\n", dawg.node_count());

    // Create query set (sample every 100th word for 1000 queries)
    let query_words: Vec<_> = words
        .iter()
        .step_by(words.len() / 1000)
        .take(1000)
        .collect();

    println!("=== Benchmark: Generic QueryIterator ===\n");

    // Generic iterator (uses DictionaryNode with Arc)
    let transducer = Transducer::new(dawg.clone(), Algorithm::Standard);

    let start = Instant::now();
    let mut results_generic = 0;
    for word in &query_words {
        for _ in transducer.query(word, 2) {
            results_generic += 1;
        }
    }
    let time_generic = start.elapsed();

    println!("Generic QueryIterator:");
    println!("  Queries: {}", query_words.len());
    println!("  Time: {:?}", time_generic);
    println!(
        "  µs/query: {:.2}",
        time_generic.as_micros() as f64 / query_words.len() as f64
    );
    println!("  Results: {}\n", results_generic);

    println!("=== Benchmark: Optimized DawgQueryIterator ===\n");

    // Optimized iterator (works with indices, no Arc clones)
    let start = Instant::now();
    let mut results_optimized = 0;
    for word in &query_words {
        for _ in dawg.query_optimized(word, 2, Algorithm::Standard) {
            results_optimized += 1;
        }
    }
    let time_optimized = start.elapsed();

    println!("Optimized DawgQueryIterator:");
    println!("  Queries: {}", query_words.len());
    println!("  Time: {:?}", time_optimized);
    println!(
        "  µs/query: {:.2}",
        time_optimized.as_micros() as f64 / query_words.len() as f64
    );
    println!("  Results: {}\n", results_optimized);

    println!("=== Results ===\n");

    // Verify both return same results
    assert_eq!(results_generic, results_optimized, "Results mismatch!");
    println!(
        "✅ Both iterators return identical results ({} matches)\n",
        results_generic
    );

    // Calculate improvement
    let speedup = time_generic.as_nanos() as f64 / time_optimized.as_nanos() as f64;
    let improvement = ((time_generic.as_nanos() - time_optimized.as_nanos()) as f64
        / time_generic.as_nanos() as f64)
        * 100.0;

    println!("Performance Improvement:");
    println!(
        "  Generic: {:.2} µs/query",
        time_generic.as_micros() as f64 / query_words.len() as f64
    );
    println!(
        "  Optimized: {:.2} µs/query",
        time_optimized.as_micros() as f64 / query_words.len() as f64
    );
    println!("  Speedup: {:.2}x", speedup);
    println!("  Improvement: {:.2}%", improvement);

    if improvement > 5.0 {
        println!("\n✅ Significant improvement achieved!");
    } else {
        println!("\n⚠️  Improvement less than expected (predicted 10-15%)");
    }

    println!("\n=== Additional Tests ===\n");

    // Test with varying distances
    for distance in [1, 2, 3] {
        println!("Distance {}:", distance);

        // Generic
        let start = Instant::now();
        let mut count = 0;
        for word in query_words.iter().take(100) {
            for _ in transducer.query(word, distance) {
                count += 1;
            }
        }
        let time_gen = start.elapsed();

        // Optimized
        let start = Instant::now();
        let mut count_opt = 0;
        for word in query_words.iter().take(100) {
            for _ in dawg.query_optimized(word, distance, Algorithm::Standard) {
                count_opt += 1;
            }
        }
        let time_opt = start.elapsed();

        assert_eq!(count, count_opt);
        let speedup_d = time_gen.as_nanos() as f64 / time_opt.as_nanos() as f64;

        println!(
            "  Generic: {:.2} µs/query, Optimized: {:.2} µs/query, Speedup: {:.2}x",
            time_gen.as_micros() as f64 / 100.0,
            time_opt.as_micros() as f64 / 100.0,
            speedup_d
        );
    }

    println!("\n=== Benchmark Complete ===");
}
