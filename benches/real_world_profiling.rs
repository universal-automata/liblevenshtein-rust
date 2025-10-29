//! Real-world profiling benchmark for flame graph analysis.
//!
//! This benchmark simulates realistic dictionary queries to identify
//! performance bottlenecks through profiling and flame graph analysis.

use liblevenshtein::prelude::*;
use std::fs;

fn main() {
    // Load a realistic dictionary
    let dict_path = "/usr/share/dict/words";
    let terms: Vec<String> = if let Ok(contents) = fs::read_to_string(dict_path) {
        contents
            .lines()
            .filter(|line| line.len() >= 3 && line.len() <= 15)
            .take(10000) // Use 10k words for realistic profiling
            .map(|s| s.to_lowercase())
            .collect()
    } else {
        // Fallback if dictionary not available
        vec![
            "test",
            "testing",
            "tester",
            "tested",
            "tests",
            "hello",
            "world",
            "example",
            "benchmark",
            "performance",
            "algorithm",
            "levenshtein",
            "automaton",
            "dictionary",
            "query",
            "optimization",
            "profiling",
            "flamegraph",
            "analysis",
            "bottleneck",
        ]
        .into_iter()
        .map(String::from)
        .collect()
    };

    println!("Building dictionary with {} terms...", terms.len());
    let dict = DoubleArrayTrie::from_terms(terms);

    // Test queries - realistic misspellings and variations
    let queries = vec![
        ("tesing", 1),      // testing with typo
        ("exmaple", 1),     // example with transposition
        ("algorihm", 1),    // algorithm with typo
        ("performnce", 1),  // performance with missing char
        ("optmization", 2), // optimization with missing chars
        ("levenstein", 2),  // levenshtein with typo
        ("dictinary", 2),   // dictionary with typo
        ("automton", 2),    // automaton with missing char
        ("flmaegraph", 2),  // flamegraph with transposition
        ("btleneck", 2),    // bottleneck with missing char
    ];

    println!("Running profiling workload...");
    println!("This will run for ~30 seconds to generate good profiling data");

    // Run for 30 seconds to generate good profiling data
    let start = std::time::Instant::now();
    let mut total_results = 0;
    let mut iterations = 0;

    while start.elapsed().as_secs() < 30 {
        for (query, max_distance) in &queries {
            // Test all three algorithms
            for algorithm in [
                Algorithm::Standard,
                Algorithm::Transposition,
                Algorithm::MergeAndSplit,
            ] {
                let transducer = Transducer::new(dict.clone(), algorithm);

                let results: Vec<_> = transducer.query(query, *max_distance).collect();

                total_results += results.len();
            }
        }
        iterations += 1;

        // Progress indicator
        if iterations % 10 == 0 {
            println!(
                "  {} iterations, {} total results, {:.1}s elapsed",
                iterations,
                total_results,
                start.elapsed().as_secs_f64()
            );
        }
    }

    println!("\nProfiling complete!");
    println!("Total iterations: {}", iterations);
    println!("Total results: {}", total_results);
    println!("Time: {:.2}s", start.elapsed().as_secs_f64());
    println!(
        "Throughput: {:.0} queries/sec",
        (iterations * queries.len() * 3) as f64 / start.elapsed().as_secs_f64()
    );
}
