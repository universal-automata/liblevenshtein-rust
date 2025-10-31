//! Basic cache eviction wrapper example
//!
//! Demonstrates how to use cache eviction wrappers with dictionaries
//! to track access patterns for fuzzy string matching.

#[cfg(feature = "pathmap-backend")]
fn main() {
    use liblevenshtein::prelude::*;
    use liblevenshtein::cache::eviction::Lru;

    println!("=== Cache Eviction Wrapper Example ===\n");

    // Create a dictionary with LRU eviction tracking
    println!("1. Creating PathMap dictionary with LRU wrapper...");
    let dict = PathMapDictionary::from_terms(vec!["test", "testing", "tested", "hello", "world"]);
    let lru_dict = Lru::new(dict);

    println!("   Dictionary created with {} terms\n", lru_dict.len().unwrap_or(0));

    // Create transducer with LRU-wrapped dictionary
    let transducer = Transducer::new(lru_dict, Algorithm::Standard);

    // Perform fuzzy queries
    println!("2. Fuzzy query: 'tset' with distance 2");
    let results: Vec<_> = transducer.query("tset", 2).collect();
    println!("   Results:");
    for result in &results {
        println!("     - {}", result);
    }
    println!();

    println!("3. Fuzzy query: 'helo' with distance 1");
    let results: Vec<_> = transducer.query("helo", 1).collect();
    println!("   Results:");
    for result in &results {
        println!("     - {}", result);
    }
    println!();

    println!("=== Example Complete ===");
    println!("\nNote: The LRU wrapper tracks access patterns.");
    println!("Use lru_dict.recency(term) to check when a term was last accessed.");
}

#[cfg(not(feature = "pathmap-backend"))]
fn main() {
    println!("This example requires the 'pathmap-backend' feature.");
    println!("Run with: cargo run --features pathmap-backend --example fuzzy_cache_basic");
}
