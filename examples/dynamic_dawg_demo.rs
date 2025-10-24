//! Demonstration of DynamicDawg with online modifications.
//!
//! This example shows:
//! - Creating a dynamic DAWG
//! - Online insertions and deletions
//! - Compaction to restore minimality
//! - Trade-offs vs static DAWG
//!
//! Run with: cargo run --example dynamic_dawg_demo

use liblevenshtein::prelude::*;

fn main() {
    println!("Dynamic DAWG Demonstration\n");
    println!("==========================\n");

    // Create an empty dynamic DAWG
    println!("1. Creating dynamic DAWG and adding terms...\n");
    let dawg = DynamicDawg::new();

    dawg.insert("apple");
    dawg.insert("application");
    dawg.insert("apply");
    dawg.insert("apricot");

    println!("   Terms: {}", dawg.term_count());
    println!("   Nodes: {}", dawg.node_count());

    // Use with fuzzy search
    println!("\n2. Fuzzy search with dynamic DAWG...\n");
    let transducer = Transducer::new(dawg.clone(), Algorithm::Standard);

    let query = "aple";
    println!("   Query '{}' with distance 2:", query);
    let results: Vec<_> = transducer.query(query, 2).collect();
    for term in &results {
        println!("     - {}", term);
    }

    // Online insertion
    println!("\n3. Adding new term dynamically...\n");
    dawg.insert("applesauce");
    println!("   Added 'applesauce'");
    println!("   Terms: {} (was 4)", dawg.term_count());
    println!("   Nodes: {}", dawg.node_count());

    // Search again - new term is immediately available
    let query2 = "applesauc";
    println!("\n   Query '{}' with distance 1:", query2);
    let results2: Vec<_> = transducer.query(query2, 1).collect();
    for term in &results2 {
        println!("     - {}", term);
    }

    // Online deletion
    println!("\n4. Removing term dynamically...\n");
    dawg.remove("apricot");
    println!("   Removed 'apricot'");
    println!("   Terms: {} (was 5)", dawg.term_count());
    println!("   Nodes: {} (may have orphaned nodes)", dawg.node_count());
    println!("   Needs compaction: {}", dawg.needs_compaction());

    // Compaction
    println!("\n5. Compacting to restore minimality...\n");
    let removed_nodes = dawg.compact();
    println!("   Removed {} orphaned nodes", removed_nodes);
    println!("   Terms: {} (unchanged)", dawg.term_count());
    println!("   Nodes: {} (minimized)", dawg.node_count());
    println!("   Needs compaction: {}", dawg.needs_compaction());

    // Comparison with static DAWG
    println!("\n6. Comparison: Dynamic vs Static DAWG\n");

    let terms = vec!["apple", "application", "apply", "applesauce"];

    // Static DAWG (built once, immutable)
    let static_dawg = DawgDictionary::from_iter(terms.clone());
    println!("   Static DAWG:");
    println!("     Terms: {}", static_dawg.term_count());
    println!("     Nodes: {} (perfectly minimal)", static_dawg.node_count());

    // Dynamic DAWG (after compaction)
    println!("\n   Dynamic DAWG (after compaction):");
    println!("     Terms: {}", dawg.term_count());
    println!("     Nodes: {}", dawg.node_count());

    // Performance characteristics
    println!("\n7. Performance Characteristics\n");
    println!("   Dynamic DAWG:");
    println!("     ✓ Online insertions: O(m) per term");
    println!("     ✓ Online deletions: O(m) per term");
    println!("     ✓ Compaction: O(n) total size");
    println!("     ✓ Thread-safe: RwLock for concurrent access");
    println!("     ✗ May become non-minimal between compactions");

    println!("\n   Static DAWG:");
    println!("     ✓ Perfectly minimal structure");
    println!("     ✓ No synchronization needed (immutable)");
    println!("     ✗ Cannot modify after construction");
    println!("     ✗ Requires rebuild for updates");

    // Use cases
    println!("\n8. Use Cases\n");
    println!("   Use Dynamic DAWG when:");
    println!("     • Dictionary changes frequently");
    println!("     • Real-time updates required");
    println!("     • Periodic compaction acceptable");
    println!("     • Examples: live spell checker, auto-complete");

    println!("\n   Use Static DAWG when:");
    println!("     • Dictionary is fixed");
    println!("     • Maximum space efficiency needed");
    println!("     • No updates after construction");
    println!("     • Examples: embedded systems, read-only dictionaries");

    println!("\n✓ Dynamic DAWG demonstration completed!");

    println!("\nKey Takeaways:");
    println!("• DynamicDawg supports insert(), remove(), and compact()");
    println!("• Maintains near-minimality with periodic compaction");
    println!("• Thread-safe with RwLock for concurrent access");
    println!("• Perfect for dictionaries that change over time");
    println!("• Compaction restores perfect minimality when needed");
}
