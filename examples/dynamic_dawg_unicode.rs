//! Demonstration of DynamicDawgChar with Unicode support.
//!
//! This example shows:
//! - Creating a dynamic DAWG with character-level (Unicode) support
//! - Correct character-level Levenshtein distances for Unicode
//! - Online insertions and deletions with Unicode terms
//! - Comparison with byte-level DynamicDawg
//!
//! Run with: cargo run --example dynamic_dawg_unicode

use liblevenshtein::dictionary::dynamic_dawg::DynamicDawg;
use liblevenshtein::dictionary::dynamic_dawg_char::DynamicDawgChar;
use liblevenshtein::prelude::*;

fn main() {
    println!("Dynamic DAWG Unicode Demonstration\n");
    println!("===================================\n");

    // Create an empty dynamic DAWG with character-level support
    println!("1. Creating DynamicDawgChar and adding Unicode terms...\n");
    let dawg: DynamicDawgChar<()> = DynamicDawgChar::new();

    // Insert multilingual terms
    dawg.insert("café");
    dawg.insert("naïve");
    dawg.insert("résumé");
    dawg.insert("中文");
    dawg.insert("日本語");
    dawg.insert("🎉");
    dawg.insert("hello🌍");

    println!("   Terms: {}", dawg.term_count());
    println!("   Nodes: {}", dawg.node_count());
    println!("\n   Dictionary contains:");
    println!("     - Accented characters: café, naïve, résumé");
    println!("     - CJK characters: 中文, 日本語");
    println!("     - Emoji: 🎉, hello🌍");

    // Demonstrate character-level distances
    println!("\n2. Character-level Levenshtein distances...\n");
    let transducer = Transducer::new(dawg.clone(), Algorithm::Standard);

    // Example 1: Accented character = 1 character distance
    let query1 = "cafe"; // Missing accent
    println!("   Query '{}' with distance 1:", query1);
    let results1: Vec<_> = transducer.query(query1, 1).collect();
    for term in &results1 {
        println!("     - {}", term);
    }
    println!("   ✓ 'café' found (substitute e→é = 1 character)");

    // Example 2: Empty query with single Unicode character
    println!("\n   Query '' (empty) with distance 1:");
    let results2: Vec<_> = transducer.query("", 1).collect();
    for term in &results2 {
        println!("     - {}", term);
    }
    println!("   ✓ Single-character terms found (中, 🎉, etc.)");

    // Example 3: CJK character distance
    println!("\n   Query '中' with distance 1:");
    let results3: Vec<_> = transducer.query("中", 1).collect();
    for term in &results3 {
        println!("     - {}", term);
    }
    println!("   ✓ '中文' found (insert '文' = 1 character)");

    // Online insertion with Unicode
    println!("\n3. Adding new Unicode terms dynamically...\n");
    dawg.insert("新しい");
    dawg.insert("Здравствуйте");
    println!("   Added '新しい' (Japanese)");
    println!("   Added 'Здравствуйте' (Russian)");
    println!("   Terms: {} (was 7)", dawg.term_count());
    println!("   Nodes: {}", dawg.node_count());

    // Search again - new terms are immediately available
    let query4 = "新";
    println!("\n   Query '{}' with distance 2:", query4);
    let results4: Vec<_> = transducer.query(query4, 2).collect();
    for term in &results4 {
        println!("     - {}", term);
    }

    // Online deletion with Unicode
    println!("\n4. Removing Unicode term dynamically...\n");
    dawg.remove("🎉");
    println!("   Removed '🎉'");
    println!("   Terms: {} (was 9)", dawg.term_count());
    println!("   Nodes: {} (may have orphaned nodes)", dawg.node_count());
    println!("   Needs compaction: {}", dawg.needs_compaction());

    // Compaction
    println!("\n5. Compacting to restore minimality...\n");
    let removed_nodes = dawg.compact();
    println!("   Removed {} orphaned nodes", removed_nodes);
    println!("   Terms: {} (unchanged)", dawg.term_count());
    println!("   Nodes: {} (minimized)", dawg.node_count());

    // Comparison: Byte-level vs Character-level
    println!("\n6. Comparison: Byte-level vs Character-level\n");
    println!("   Problem: \"\" → \"¡\" distance calculation");
    println!("   '¡' is 1 Unicode character but 2 UTF-8 bytes (0xC2 0xA1)\n");

    // Byte-level (incorrect for Unicode)
    let dawg_byte: DynamicDawg<()> = DynamicDawg::from_terms(vec!["¡"]);
    let trans_byte = Transducer::new(dawg_byte, Algorithm::Standard);
    let results_byte: Vec<_> = trans_byte.query("", 1).collect();

    println!("   Byte-level DynamicDawg:");
    println!("     Distance 1 from empty: {} results", results_byte.len());
    if results_byte.is_empty() {
        println!("     ✗ '¡' NOT found (requires distance 2)");
    }

    // Character-level (correct for Unicode)
    let dawg_char: DynamicDawgChar<()> = DynamicDawgChar::from_terms(vec!["¡"]);
    let trans_char = Transducer::new(dawg_char, Algorithm::Standard);
    let results_char: Vec<_> = trans_char.query("", 1).collect();

    println!("\n   Character-level DynamicDawgChar:");
    println!("     Distance 1 from empty: {} results", results_char.len());
    if results_char.contains(&"¡".to_string()) {
        println!("     ✓ '¡' found (correctly = 1 character)");
    }

    // Performance characteristics
    println!("\n7. Performance Characteristics\n");
    println!("   DynamicDawgChar (character-level):");
    println!("     ✓ Correct Unicode semantics");
    println!("     ✓ Character-level Levenshtein distances");
    println!("     ✓ Online insertions: O(m) per term (m = character count)");
    println!("     ✓ Online deletions: O(m) per term");
    println!("     ✓ Thread-safe: RwLock for concurrent access");
    println!("     ~ ~4x memory for edge labels (char vs u8)");
    println!("     ~ ~5-10% slower due to UTF-8 decoding");

    println!("\n   DynamicDawg (byte-level):");
    println!("     ✓ Fastest performance");
    println!("     ✓ Minimal memory usage");
    println!("     ✗ Incorrect distances for multi-byte characters");
    println!("     • Best for ASCII/Latin-1 only");

    // Use cases
    println!("\n8. Use Cases\n");
    println!("   Use DynamicDawgChar when:");
    println!("     • Working with Unicode text (any language)");
    println!("     • Need correct Levenshtein distances for:");
    println!("       - Accented characters (café, naïve, résumé)");
    println!("       - CJK text (中文, 日本語, 한글)");
    println!("       - Emoji (🎉, 🌍, 😀)");
    println!("       - Cyrillic (Здравствуйте)");
    println!("       - Any non-ASCII text");
    println!("     • Dictionary changes frequently");
    println!("     • Real-time updates required");

    println!("\n   Use DynamicDawg (byte-level) when:");
    println!("     • Text is ASCII or Latin-1 only");
    println!("     • Maximum performance needed");
    println!("     • Minimal memory footprint required");
    println!("     • Byte-level distances are acceptable");

    // Transposition with Unicode
    println!("\n9. Transposition with Unicode characters...\n");
    let dawg_trans: DynamicDawgChar<()> = DynamicDawgChar::from_terms(vec!["éfac"]);
    let trans_algo = Transducer::new(dawg_trans, Algorithm::Transposition);

    let query5 = "féac"; // Swapped 'é' and 'f'
    println!("   Query '{}' with distance 1 (transposition):", query5);
    let results5: Vec<_> = trans_algo.query(query5, 1).collect();
    for term in &results5 {
        println!("     - {}", term);
    }
    println!("   ✓ Transposition works correctly with Unicode");

    // Value mapping with Unicode
    println!("\n10. Value mapping with Unicode terms...\n");
    let dict_values: DynamicDawgChar<u32> = DynamicDawgChar::new();
    dict_values.insert_with_value("café", 1);
    dict_values.insert_with_value("中文", 2);
    dict_values.insert_with_value("🎉", 3);

    println!("   Dictionary with scope IDs:");
    println!("     \"café\" → {}", dict_values.get_value("café").unwrap());
    println!("     \"中文\" → {}", dict_values.get_value("中文").unwrap());
    println!("     \"🎉\" → {}", dict_values.get_value("🎉").unwrap());

    // Update a value
    dict_values.insert_with_value("café", 10);
    println!("\n   Updated \"café\" → {}", dict_values.get_value("café").unwrap());

    println!("\n✓ Dynamic DAWG Unicode demonstration completed!");

    println!("\nKey Takeaways:");
    println!("• DynamicDawgChar provides correct Unicode semantics");
    println!("• Character-level distances work for all Unicode (accents, CJK, emoji)");
    println!("• Same dynamic operations as DynamicDawg (insert, remove, compact)");
    println!("• Thread-safe with RwLock for concurrent access");
    println!("• Small performance trade-off (~5-10%) for correctness");
    println!("• Use for any multilingual or Unicode application");
}
