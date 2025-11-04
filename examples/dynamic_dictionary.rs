//! Example demonstrating runtime dictionary updates.
//!
//! This example shows how to insert and remove terms from the dictionary
//! while it's being used for queries, demonstrating the thread-safe
//! mutation capabilities using DynamicDawg.
//!
//! Run with: cargo run --example dynamic_dictionary

use liblevenshtein::prelude::*;

fn main() {
    println!("=== Dynamic Dictionary Example ===\n");

    // Start with a small dictionary (using DynamicDawg for runtime updates)
    let dict: DynamicDawg<()> = DynamicDawg::from_terms(vec!["cat", "dog", "bird"]);
    let transducer = Transducer::new(dict.clone(), Algorithm::Standard);

    println!("Initial dictionary: cat, dog, bird");
    println!("Term count: {}\n", dict.term_count());

    // Query 1: Before adding new terms
    println!("Query 'cot' (distance 1):");
    let results: Vec<_> = transducer.query("cot", 1).collect();
    for term in &results {
        println!("  - {}", term);
    }
    println!();

    // Add new terms at runtime
    println!("Adding new terms: 'cot', 'coat', 'bat'");
    dict.insert("cot");
    dict.insert("coat");
    dict.insert("bat");
    println!("Term count: {}\n", dict.term_count());

    // Query 2: After adding terms - same transducer sees new terms!
    println!("Query 'cot' (distance 1) - after insertions:");
    let results: Vec<_> = transducer.query("cot", 1).collect();
    for term in &results {
        println!("  - {}", term);
    }
    println!();

    // Query with more distance
    println!("Query 'coat' (distance 2):");
    let results: Vec<_> = transducer.query("coat", 2).collect();
    for term in &results {
        println!("  - {}", term);
    }
    println!();

    // Remove a term
    println!("Removing 'bird'");
    dict.remove("bird");
    println!("Term count: {}\n", dict.term_count());

    // Query 3: After removal
    println!("Query 'brd' (distance 1) - after removing 'bird':");
    let results: Vec<_> = transducer.query("brd", 1).collect();
    if results.is_empty() {
        println!("  (no matches)");
    } else {
        for term in &results {
            println!("  - {}", term);
        }
    }
    println!();

    // Demonstrate concurrent updates
    println!("=== Concurrent Operations ===\n");

    use std::thread;
    use std::time::Duration;

    let dict2: DynamicDawg<()> = DynamicDawg::from_terms(vec!["test"]);
    let transducer2 = Transducer::new(dict2.clone(), Algorithm::Standard);

    // Clone for thread
    let dict_thread = dict2.clone();

    // Spawn thread that adds terms gradually
    let handle = thread::spawn(move || {
        for word in &["testing", "tested", "tester", "tests"] {
            thread::sleep(Duration::from_millis(10));
            dict_thread.insert(word);
            println!("  [Thread] Added: {}", word);
        }
    });

    // Main thread queries while other thread modifies
    thread::sleep(Duration::from_millis(15));
    println!("  [Main] Querying 'test' while thread is adding terms...");

    for _ in 0..3 {
        let results: Vec<_> = transducer2.query("test", 0).collect();
        println!("    Found {} matches", results.len());
        thread::sleep(Duration::from_millis(10));
    }

    handle.join().unwrap();

    println!("\n  Final term count: {}", dict2.term_count());
    let all_results: Vec<_> = transducer2.query("test", 2).collect();
    println!("  All terms within distance 2 of 'test':");
    for term in &all_results {
        println!("    - {}", term);
    }

    println!("\nDynamic dictionary example complete!");
    println!("Final dictionary has {} terms", dict2.term_count());
}
