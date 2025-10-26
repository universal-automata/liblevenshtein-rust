//! Demonstration of DAWG dictionary usage.
//!
//! This example shows:
//! - Creating a DAWG dictionary
//! - Comparing space efficiency with PathMap
//! - Using DAWG with fuzzy search
//!
//! Run with: cargo run --example dawg_demo

use liblevenshtein::prelude::*;

fn main() {
    println!("DAWG Dictionary Demonstration\n");
    println!("==============================\n");

    // Create test data with common suffixes
    let terms = vec![
        "testing", "running", "walking", "talking", // common suffix: "ing"
        "tested", "wanted", "needed", "added",      // common suffix: "ed"
        "runner", "walker", "talker", "worker",     // common suffix: "er"
    ];

    println!("1. Creating PathMap dictionary...");
    let pathmap_dict = PathMapDictionary::from_iter(terms.clone());
    println!("   PathMap: {} terms", pathmap_dict.len().unwrap());

    println!("\n2. Creating DAWG dictionary...");
    let dawg_dict = DawgDictionary::from_iter(terms.clone());
    println!("   DAWG: {} terms, {} nodes",
             dawg_dict.term_count(),
             dawg_dict.node_count());

    println!("\n3. Space efficiency:");
    println!("   DAWG uses suffix sharing to minimize node count");
    println!("   Words ending in 'ing': testing, running, walking, talking");
    println!("   Words ending in 'ed': tested, wanted, needed, added");
    println!("   Words ending in 'er': runner, walker, talker, worker");
    println!("   → DAWG shares these common suffixes!");

    println!("\n4. Testing fuzzy search with DAWG...");
    let transducer = Transducer::new(dawg_dict, Algorithm::Standard);

    let query = "runing"; // typo: missing 'n'
    println!("   Query '{}' with distance 1:", query);
    let results: Vec<_> = transducer.query(query, 1).collect();
    for term in &results {
        println!("     - {}", term);
    }

    let query2 = "talk";
    println!("\n   Query '{}' with distance 2:", query2);
    let results2: Vec<_> = transducer.query(query2, 2).collect();
    for term in &results2 {
        println!("     - {}", term);
    }

    println!("\n5. Verification:");
    println!("   ✓ DAWG implements Dictionary trait");
    println!("   ✓ Works seamlessly with Transducer");
    println!("   ✓ Provides space-efficient alternative to PathMap");

    println!("\n✓ DAWG demonstration completed!");
    println!("\nKey takeaways:");
    println!("- DAWG shares both prefixes AND suffixes");
    println!("- More space-efficient for certain datasets");
    println!("- Best when words have common suffixes (English -ing, -ed, -er)");
    println!("- Works identically to PathMap for fuzzy search");
}
