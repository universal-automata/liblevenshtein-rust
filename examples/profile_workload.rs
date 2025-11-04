//! Workload for profiling with flamegraph.
//!
//! This example runs a representative mix of operations for profiling purposes.

use liblevenshtein::prelude::*;
use std::hint::black_box;

fn main() {
    println!("Starting profiling workload...");

    // Create a reasonably sized dictionary
    let words: Vec<String> = (0..5000).map(|i| format!("word{:05}", i)).collect();

    let dict: DynamicDawg<()> = DynamicDawg::from_terms(words);
    let transducer = Transducer::new(dict.clone(), Algorithm::Standard);

    println!("Dictionary created with 5000 words");

    // Workload 1: Many queries with distance 2 (most common use case)
    println!("Running query workload (distance 2)...");
    for i in 0..100 {
        let query = format!("word{:05}", i * 50);
        let results: Vec<_> = transducer.query(black_box(&query), black_box(2)).collect();
        black_box(results);
    }

    // Workload 2: Higher distance queries (more expensive)
    println!("Running high-distance queries...");
    for i in 0..20 {
        let query = format!("wrd{:04}", i * 100);
        let results: Vec<_> = transducer.query(black_box(&query), black_box(3)).collect();
        black_box(results);
    }

    // Workload 3: Queries with insertions/deletions
    println!("Running insertion/deletion workload...");
    for _ in 0..50 {
        // Missing characters (insertions)
        let results: Vec<_> = transducer
            .query(black_box("wrd00500"), black_box(2))
            .collect();
        black_box(results);

        // Extra characters (deletions)
        let results: Vec<_> = transducer
            .query(black_box("woord00500"), black_box(2))
            .collect();
        black_box(results);
    }

    // Workload 4: Dictionary modifications
    println!("Running dictionary modification workload...");
    for i in 0..100 {
        dict.insert(&format!("newword{}", i));
        if i % 2 == 0 {
            dict.remove(&format!("word{:05}", i));
        }
    }

    // Workload 5: Query with distance calculation
    println!("Running query with distance calculation...");
    for i in 0..50 {
        let query = format!("word{:05}", i * 100);
        let results: Vec<_> = transducer
            .query_with_distance(black_box(&query), black_box(2))
            .collect();
        black_box(results);
    }

    // Workload 6: Worst-case queries (similar words)
    println!("Running worst-case workload...");
    for i in 0..20 {
        let query = format!("word{:05}", 2500 + i);
        let results: Vec<_> = transducer.query(black_box(&query), black_box(2)).collect();
        black_box(results);
    }

    println!("Profiling workload complete!");
}
