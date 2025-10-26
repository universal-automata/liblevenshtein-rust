//! Real-world dictionary benchmarks using /usr/share/dict/words
//!
//! This benchmark:
//! 1. Analyzes edge distribution in real vs synthetic dictionaries
//! 2. Compares performance characteristics
//! 3. Validates optimization effectiveness on real data

use liblevenshtein::prelude::*;
use std::collections::HashMap;
use std::fs;

fn main() {
    println!("=== Real-World Dictionary Analysis ===\n");

    // Load real dictionary
    println!("Loading real dictionary...");
    let real_words = load_real_dictionary();
    println!(
        "Loaded {} words from English dictionary\n",
        real_words.len()
    );

    // Load synthetic dictionary for comparison
    println!("Generating synthetic dictionary...");
    let synthetic_words = generate_synthetic_dictionary(10_000);
    println!("Generated {} synthetic words\n", synthetic_words.len());

    // Build DAWGs
    println!("Building DAWG from real dictionary...");
    let start = std::time::Instant::now();
    let real_dawg = DawgDictionary::from_iter(real_words.iter().map(|s| s.as_str()));
    let real_build_time = start.elapsed();
    println!("Real DAWG built in {:?}", real_build_time);
    println!("Real DAWG nodes: {}\n", real_dawg.node_count());

    println!("Building DAWG from synthetic dictionary...");
    let start = std::time::Instant::now();
    let synthetic_dawg = DawgDictionary::from_iter(synthetic_words.iter().map(|s| s.as_str()));
    let synthetic_build_time = start.elapsed();
    println!("Synthetic DAWG built in {:?}", synthetic_build_time);
    println!("Synthetic DAWG nodes: {}\n", synthetic_dawg.node_count());

    // Analyze edge distributions
    println!("=== Edge Distribution Analysis ===\n");

    println!("Real dictionary edge distribution:");
    let real_dist = analyze_edge_distribution(&real_dawg);
    print_distribution(&real_dist);

    println!("\nSynthetic dictionary edge distribution:");
    let synthetic_dist = analyze_edge_distribution(&synthetic_dawg);
    print_distribution(&synthetic_dist);

    // Performance benchmarks
    println!("\n=== Performance Comparison ===\n");

    // Contains benchmark
    println!("Testing contains() performance...");

    // Real dictionary
    let real_test_words: Vec<_> = real_words.iter().take(10_000).collect();
    let start = std::time::Instant::now();
    let mut real_found = 0;
    for _ in 0..100 {
        for word in &real_test_words {
            if real_dawg.contains(word) {
                real_found += 1;
            }
        }
    }
    let real_contains_time = start.elapsed();
    println!(
        "Real dictionary: {} calls in {:?} ({:.2} µs/call)",
        real_test_words.len() * 100,
        real_contains_time,
        real_contains_time.as_micros() as f64 / (real_test_words.len() * 100) as f64
    );
    println!("Found: {}", real_found);

    // Synthetic dictionary
    let synthetic_test_words: Vec<_> = synthetic_words.iter().take(10_000).collect();
    let start = std::time::Instant::now();
    let mut synthetic_found = 0;
    for _ in 0..100 {
        for word in &synthetic_test_words {
            if synthetic_dawg.contains(word) {
                synthetic_found += 1;
            }
        }
    }
    let synthetic_contains_time = start.elapsed();
    println!(
        "Synthetic dictionary: {} calls in {:?} ({:.2} µs/call)",
        synthetic_test_words.len() * 100,
        synthetic_contains_time,
        synthetic_contains_time.as_micros() as f64 / (synthetic_test_words.len() * 100) as f64
    );
    println!("Found: {}", synthetic_found);

    // Query benchmark
    println!("\nTesting fuzzy query performance...");

    // Real dictionary queries
    let real_query_words: Vec<_> = real_words
        .iter()
        .step_by(real_words.len() / 1000)
        .take(1000)
        .collect();

    let real_transducer = Transducer::new(real_dawg.clone(), Algorithm::Standard);
    let start = std::time::Instant::now();
    let mut real_results = 0;
    for word in &real_query_words {
        for _ in real_transducer.query(word, 2) {
            real_results += 1;
        }
    }
    let real_query_time = start.elapsed();
    println!(
        "Real dictionary: {} queries in {:?} ({:.2} µs/query)",
        real_query_words.len(),
        real_query_time,
        real_query_time.as_micros() as f64 / real_query_words.len() as f64
    );
    println!("Total results: {}", real_results);

    // Synthetic dictionary queries
    let synthetic_query_words: Vec<_> = synthetic_words
        .iter()
        .step_by(synthetic_words.len() / 1000)
        .take(1000)
        .collect();

    let synthetic_transducer = Transducer::new(synthetic_dawg.clone(), Algorithm::Standard);
    let start = std::time::Instant::now();
    let mut synthetic_results = 0;
    for word in &synthetic_query_words {
        for _ in synthetic_transducer.query(word, 2) {
            synthetic_results += 1;
        }
    }
    let synthetic_query_time = start.elapsed();
    println!(
        "Synthetic dictionary: {} queries in {:?} ({:.2} µs/query)",
        synthetic_query_words.len(),
        synthetic_query_time,
        synthetic_query_time.as_micros() as f64 / synthetic_query_words.len() as f64
    );
    println!("Total results: {}", synthetic_results);

    println!("\n=== Threshold Analysis ===\n");
    analyze_threshold_effectiveness(&real_dist, &synthetic_dist);

    println!("\n=== Analysis Complete ===");
}

fn load_real_dictionary() -> Vec<String> {
    let contents = fs::read_to_string("data/english_words.txt")
        .expect("Failed to read data/english_words.txt");

    contents
        .lines()
        .map(|s| s.trim().to_lowercase())
        .filter(|s| !s.is_empty() && s.chars().all(|c| c.is_ascii_alphabetic()))
        .collect()
}

fn generate_synthetic_dictionary(count: usize) -> Vec<String> {
    (0..count).map(|i| format!("word{:06}", i)).collect()
}

fn analyze_edge_distribution(dawg: &DawgDictionary) -> HashMap<usize, usize> {
    let mut distribution = HashMap::new();

    // Use internal access to analyze all nodes
    for node_idx in 0..dawg.node_count() {
        let node = dawg.get_node(node_idx);
        let edge_count = node.edges.len();
        *distribution.entry(edge_count).or_insert(0) += 1;
    }

    distribution
}

fn print_distribution(dist: &HashMap<usize, usize>) {
    let total_nodes: usize = dist.values().sum();
    let mut sorted: Vec<_> = dist.iter().collect();
    sorted.sort_by_key(|(k, _)| *k);

    println!("  Edges | Count    | Percent");
    println!("  ------|----------|--------");

    for (edge_count, count) in &sorted {
        let percent = (**count as f64 / total_nodes as f64) * 100.0;
        println!("  {:5} | {:8} | {:6.2}%", edge_count, count, percent);
    }

    // Calculate percentiles
    let mut cumulative = 0;
    println!("\n  Percentiles:");
    for (edge_count, count) in &sorted {
        cumulative += **count;
        let percentile = (cumulative as f64 / total_nodes as f64) * 100.0;
        if percentile >= 50.0 && percentile < 50.0 + (**count as f64 / total_nodes as f64) * 100.0 {
            println!("  50th percentile: {} edges", edge_count);
        }
        if percentile >= 90.0 && percentile < 90.0 + (**count as f64 / total_nodes as f64) * 100.0 {
            println!("  90th percentile: {} edges", edge_count);
        }
        if percentile >= 95.0 && percentile < 95.0 + (**count as f64 / total_nodes as f64) * 100.0 {
            println!("  95th percentile: {} edges", edge_count);
        }
    }

    // Find max edge count
    if let Some((max_edges, count)) = sorted.last() {
        println!("  Maximum: {} edges ({} nodes)", max_edges, count);
    }
}

fn analyze_threshold_effectiveness(
    real_dist: &HashMap<usize, usize>,
    synthetic_dist: &HashMap<usize, usize>,
) {
    println!("Current threshold: 16 (linear search for <16 edges, binary for ≥16)");

    // Calculate what percentage of nodes use each strategy
    let analyze = |dist: &HashMap<usize, usize>, name: &str| {
        let total: usize = dist.values().sum();
        let linear: usize = dist
            .iter()
            .filter(|(edges, _)| **edges < 16)
            .map(|(_, count)| count)
            .sum();
        let binary: usize = total - linear;

        println!("\n{}:", name);
        println!(
            "  Linear search: {} nodes ({:.2}%)",
            linear,
            (linear as f64 / total as f64) * 100.0
        );
        println!(
            "  Binary search: {} nodes ({:.2}%)",
            binary,
            (binary as f64 / total as f64) * 100.0
        );

        // Find nodes near threshold
        let near_threshold: usize = dist
            .iter()
            .filter(|(edges, _)| **edges >= 10 && **edges <= 20)
            .map(|(_, count)| count)
            .sum();
        println!(
            "  Near threshold (10-20 edges): {} nodes ({:.2}%)",
            near_threshold,
            (near_threshold as f64 / total as f64) * 100.0
        );
    };

    analyze(real_dist, "Real dictionary");
    analyze(synthetic_dist, "Synthetic dictionary");
}
