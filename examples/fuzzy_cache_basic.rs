//! Basic fuzzy cache usage example
//!
//! Demonstrates how to use FuzzyCache with different eviction strategies
//! to accelerate fuzzy string matching queries.

use liblevenshtein::prelude::*;
use liblevenshtein::cache::strategy::{LruStrategy, LfuStrategy};

fn main() {
    println!("=== Fuzzy Cache Basic Example ===\n");

    // Create a cache with LRU eviction strategy
    println!("1. Creating cache with LRU strategy (max 100 entries)...");
    let cache = FuzzyCacheBuilder::<String>::new()
        .max_size(100)
        .algorithm(Algorithm::Standard)
        .lru();

    println!("   Cache created: capacity = {}, current size = {}\n",
             cache.capacity(), cache.len());

    // Insert some sample terms
    println!("2. Inserting sample terms...");
    let terms = vec!["hello", "world", "test", "testing", "tested"];
    for term in &terms {
        cache.insert(term, term.to_string());
    }
    println!("   Inserted {} terms, cache size = {}\n", terms.len(), cache.len());

    // Perform fuzzy queries
    println!("3. Fuzzy query: 'helo' with distance 1");
    let results = cache.query("helo", 1);
    println!("   Results:");
    for candidate in &results {
        println!("     - {} (distance: {})", candidate.term, candidate.distance);
    }
    println!();

    println!("4. Fuzzy query: 'tset' with distance 2");
    let results = cache.query("tset", 2);
    println!("   Results:");
    for candidate in &results {
        println!("     - {} (distance: {})", candidate.term, candidate.distance);
    }
    println!();

    // Check metrics
    println!("5. Cache metrics:");
    let metrics = cache.metrics();
    println!("   Total queries: {}", metrics.total_queries());
    println!("   Cache hits: {}", metrics.hits());
    println!("   Cache misses: {}", metrics.misses());
    println!("   Hit rate: {:.2}%", metrics.hit_rate() * 100.0);
    println!("   Evictions: {}\n", metrics.evictions());

    // Demonstrate different strategies
    println!("6. Comparing different eviction strategies:\n");

    // LFU strategy
    println!("   a) LFU (Least Frequently Used):");
    let lfu_cache = FuzzyCacheBuilder::<String>::new()
        .max_size(50)
        .lfu();
    println!("      Created LFU cache with capacity {}", lfu_cache.capacity());

    // TTL strategy
    println!("\n   b) TTL (Time-To-Live):");
    let ttl_cache = FuzzyCacheBuilder::<String>::new()
        .max_size(50)
        .ttl(std::time::Duration::from_secs(300));
    println!("      Created TTL cache with 300s expiration");

    // Cost-aware strategy
    println!("\n   c) Cost-Aware (balances age, size, hits):");
    let cost_cache = FuzzyCacheBuilder::<String>::new()
        .max_size(50)
        .cost_aware();
    println!("      Created cost-aware cache");

    // Composite strategy
    println!("\n   d) Composite Strategy (weighted LRU + LFU):");
    let composite = CompositeStrategyBuilder::<String>::new()
        .add_weighted(LruStrategy::new(), 0.7)
        .add_weighted(LfuStrategy::new(), 0.3)
        .build();
    let composite_cache = FuzzyCacheBuilder::<String>::new()
        .max_size(50)
        .strategy(composite);
    println!("      Created composite cache (70% LRU + 30% LFU)");

    println!("\n=== Example Complete ===");
}
