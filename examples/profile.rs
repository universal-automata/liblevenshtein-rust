//! Profiling example for flame graph generation
//!
//! This example runs representative workloads to identify performance bottlenecks,
//! with focus on areas showing regression in Phase 1:
//! - Distance 3 queries (+10% regression)
//! - Small dictionary queries (+8% regression)
//! - Epsilon closure O(n²) behavior

use levenshtein::prelude::*;

fn create_dictionary(size: usize) -> PathMapDictionary {
    let words: Vec<String> = (0..size)
        .map(|i| {
            let len = 4 + (i % 9);
            format!("word{:0width$}", i, width = len - 4)
        })
        .collect();
    PathMapDictionary::from_iter(words)
}

fn main() {
    println!("Starting profiling workload...");

    // Focus on regression cases

    // 1. Distance 3 queries (10% regression - highest priority)
    println!("Running distance 3 queries...");
    let dict = create_dictionary(1000);
    let transducer = Transducer::new(dict, Algorithm::Standard);

    for _ in 0..1000 {
        let _results: Vec<_> = transducer.query("word500", 3).collect();
    }

    // 2. Small dictionary queries (8% regression)
    println!("Running small dictionary queries...");
    let small_dict = create_dictionary(100);
    let small_transducer = Transducer::new(small_dict, Algorithm::Standard);

    for _ in 0..5000 {
        let _results: Vec<_> = small_transducer.query("word50", 2).collect();
    }

    // 3. Distance 2 queries (to compare with distance 3)
    println!("Running distance 2 queries...");
    let dict2 = create_dictionary(1000);
    let transducer2 = Transducer::new(dict2, Algorithm::Standard);

    for _ in 0..1000 {
        let _results: Vec<_> = transducer2.query("word500", 2).collect();
    }

    // 4. Many results case (stress test epsilon closure)
    println!("Running many results queries...");
    for _ in 0..500 {
        let _results: Vec<_> = transducer.query("word", 3).collect();
    }

    // 5. Worst case similar words (maximum state expansion)
    println!("Running worst case queries...");
    let worst_dict = PathMapDictionary::from_iter(vec![
        "aaaa", "aaab", "aaba", "aabb", "abaa", "abab", "abba", "abbb",
        "baaa", "baab", "baba", "babb", "bbaa", "bbab", "bbba", "bbbb",
    ]);
    let worst_transducer = Transducer::new(worst_dict, Algorithm::Standard);

    for _ in 0..2000 {
        let _results: Vec<_> = worst_transducer.query("aaaa", 2).collect();
    }

    println!("Profiling workload complete!");
}
