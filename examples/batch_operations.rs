//! Demonstration of batch operations with DynamicDawg.
//!
//! Run with: cargo run --example batch_operations

use levenshtein::prelude::*;

fn main() {
    println!("Batch Operations with Dynamic DAWG\n");
    println!("===================================\n");

    let dawg = DynamicDawg::from_iter(vec![
        "apple", "application", "apply",
        "banana", "cherry",
    ]);

    println!("1. Initial state:");
    println!("   Terms: {}", dawg.term_count());
    println!("   Nodes: {}", dawg.node_count());

    // Batch updates without compaction
    println!("\n2. Batch updates (no compaction)...\n");
    dawg.insert("apricot");
    dawg.insert("avocado");
    dawg.remove("banana");

    println!("   Before compaction:");
    println!("     Terms: {}", dawg.term_count());
    println!("     Nodes: {} (non-minimal)", dawg.node_count());
    println!("     Needs compaction: {}", dawg.needs_compaction());

    // Compact once
    println!("\n3. Compacting...\n");
    let removed = dawg.compact();
    println!("   Removed {} nodes", removed);
    println!("   Nodes: {} (minimal)", dawg.node_count());

    // Using batch methods
    println!("\n4. Batch methods with auto-compact...\n");
    let added = dawg.extend(vec!["blueberry", "cranberry"]);
    println!("   extend(): Added {} terms", added);

    let removed = dawg.remove_many(vec!["cherry"]);
    println!("   remove_many(): Removed {} terms", removed);

    println!("\n✓ Final dictionary:");
    println!("   Terms: {}", dawg.term_count());
    println!("   Nodes: {} (minimal)", dawg.node_count());
}
