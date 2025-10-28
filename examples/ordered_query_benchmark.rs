//! Benchmark comparing OrderedQueryIterator vs unordered QueryIterator

use liblevenshtein::prelude::*;
use std::fs;
use std::time::Instant;

fn main() {
    println!("=== Ordered vs Unordered Query Benchmark ===\n");

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

    // Build dictionary
    println!("Building dictionary...");
    let start = Instant::now();
    let dict = DoubleArrayTrie::from_terms(words.iter().map(|s| s.as_str()));
    println!("Built in {:?}\n", start.elapsed());

    let transducer = Transducer::new(dict, Algorithm::Standard);

    // Create query set (sample every 100th word for representative queries)
    let query_words: Vec<_> = words
        .iter()
        .step_by(words.len() / 1000)
        .take(1000)
        .collect();

    println!("=== Benchmark 1: Full Iteration (Distance 2) ===\n");

    // Unordered query - consume all results
    let start = Instant::now();
    let mut count_unordered = 0;
    for word in &query_words {
        for _ in transducer.query(word, 2) {
            count_unordered += 1;
        }
    }
    let time_unordered = start.elapsed();

    println!("Unordered query:");
    println!("  Queries: {}", query_words.len());
    println!("  Time: {:?}", time_unordered);
    println!(
        "  µs/query: {:.2}",
        time_unordered.as_micros() as f64 / query_words.len() as f64
    );
    println!("  Results: {}\n", count_unordered);

    // Ordered query - consume all results
    let start = Instant::now();
    let mut count_ordered = 0;
    for word in &query_words {
        for _ in transducer.query_ordered(word, 2) {
            count_ordered += 1;
        }
    }
    let time_ordered = start.elapsed();

    println!("Ordered query:");
    println!("  Queries: {}", query_words.len());
    println!("  Time: {:?}", time_ordered);
    println!(
        "  µs/query: {:.2}",
        time_ordered.as_micros() as f64 / query_words.len() as f64
    );
    println!("  Results: {}\n", count_ordered);

    assert_eq!(count_unordered, count_ordered, "Result count mismatch!");

    let overhead =
        ((time_ordered.as_nanos() as f64 / time_unordered.as_nanos() as f64) - 1.0) * 100.0;
    println!("Ordering overhead: {:.2}%\n", overhead);

    println!("=== Benchmark 2: Top-K (take 10) ===\n");

    // Unordered top-k (still explores full search space)
    let start = Instant::now();
    let mut count = 0;
    for word in query_words.iter().take(100) {
        for _ in transducer.query(word, 2).take(10) {
            count += 1;
        }
    }
    let time_unordered_take = start.elapsed();

    println!("Unordered.take(10):");
    println!("  Time: {:?}", time_unordered_take);
    println!(
        "  µs/query: {:.2}",
        time_unordered_take.as_micros() as f64 / 100.0
    );
    println!("  Results: {}\n", count);

    // Ordered top-k (can stop early!)
    let start = Instant::now();
    let mut count = 0;
    for word in query_words.iter().take(100) {
        for _ in transducer.query_ordered(word, 2).take(10) {
            count += 1;
        }
    }
    let time_ordered_take = start.elapsed();

    println!("Ordered.take(10):");
    println!("  Time: {:?}", time_ordered_take);
    println!(
        "  µs/query: {:.2}",
        time_ordered_take.as_micros() as f64 / 100.0
    );
    println!("  Results: {}\n", count);

    if time_ordered_take < time_unordered_take {
        let speedup = time_unordered_take.as_nanos() as f64 / time_ordered_take.as_nanos() as f64;
        println!("✅ Ordered is {:.2}x faster for top-k queries!\n", speedup);
    }

    println!("=== Benchmark 3: Distance-Bounded (take_while) ===\n");

    // Ordered distance-bounded (can stop early!)
    let start = Instant::now();
    let mut count = 0;
    for word in query_words.iter().take(100) {
        for _ in transducer
            .query_ordered(word, 3)
            .take_while(|c| c.distance <= 1)
        {
            count += 1;
        }
    }
    let time_ordered_bounded = start.elapsed();

    println!("Ordered.take_while(distance <= 1):");
    println!("  Time: {:?}", time_ordered_bounded);
    println!(
        "  µs/query: {:.2}",
        time_ordered_bounded.as_micros() as f64 / 100.0
    );
    println!("  Results: {}\n", count);

    // Unordered equivalent (must filter all results)
    let start = Instant::now();
    let mut count = 0;
    for word in query_words.iter().take(100) {
        for candidate in transducer.query_with_distance(word, 3) {
            if candidate.distance <= 1 {
                count += 1;
            }
        }
    }
    let time_unordered_filter = start.elapsed();

    println!("Unordered.query_with_distance(3).filter(d <= 1):");
    println!("  Time: {:?}", time_unordered_filter);
    println!(
        "  µs/query: {:.2}",
        time_unordered_filter.as_micros() as f64 / 100.0
    );
    println!("  Results: {}\n", count);

    let speedup = time_unordered_filter.as_nanos() as f64 / time_ordered_bounded.as_nanos() as f64;
    println!(
        "✅ Ordered is {:.2}x faster for distance-bounded queries!\n",
        speedup
    );

    println!("=== Benchmark 4: Performance by Distance ===\n");

    for distance in [1, 2, 3] {
        println!("Distance {}:", distance);

        // Unordered
        let start = Instant::now();
        let mut count = 0;
        for word in query_words.iter().take(100) {
            for _ in transducer.query(word, distance) {
                count += 1;
            }
        }
        let time_u = start.elapsed();

        // Ordered
        let start = Instant::now();
        let mut count_o = 0;
        for word in query_words.iter().take(100) {
            for _ in transducer.query_ordered(word, distance) {
                count_o += 1;
            }
        }
        let time_o = start.elapsed();

        assert_eq!(count, count_o);

        let overhead = ((time_o.as_nanos() as f64 / time_u.as_nanos() as f64) - 1.0) * 100.0;

        println!(
            "  Unordered: {:.2} µs/query, Ordered: {:.2} µs/query, Overhead: {:.1}%",
            time_u.as_micros() as f64 / 100.0,
            time_o.as_micros() as f64 / 100.0,
            overhead
        );
    }

    println!("\n=== Summary ===\n");
    println!("Full Iteration:");
    println!(
        "  Ordered has ~{}% overhead for maintaining order",
        overhead as i32
    );
    println!("\nEarly Termination (take/take_while):");
    println!("  Ordered can be faster due to smart exploration order");
    println!("\n🎯 Recommendation:");
    println!("  • Use ordered for: top-k, distance-bounded, ranked results");
    println!("  • Use unordered for: exhaustive search, when order doesn't matter");
}
