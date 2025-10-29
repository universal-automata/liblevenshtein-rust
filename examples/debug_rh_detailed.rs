use liblevenshtein::prelude::*;

fn main() {
    // The terms will be sorted: ["qpo", "rh", "ry"]
    let terms = vec!["rh", "qpo", "ry"];
    println!("Building DAT with terms (will be sorted): {:?}", terms);

    let dict = DoubleArrayTrie::from_terms(terms);

    println!("\nChecking all combinations:");
    for term in &["qpo", "rh", "ry"] {
        println!("  contains('{}'): {}", term, dict.contains(term));
    }

    println!("\nManual traversal:");
    let root = dict.root();
    for (byte, node) in root.edges() {
        println!("Root -> {} (0x{:02x}), is_final: {}", byte as char, byte, node.is_final());

        for (byte2, node2) in node.edges() {
            println!("  {} -> {} (0x{:02x}), is_final: {}", byte as char, byte2 as char, byte2, node2.is_final());

            for (byte3, node3) in node2.edges() {
                println!("    {} -> {} (0x{:02x}), is_final: {}", byte2 as char, byte3 as char, byte3, node3.is_final());
            }
        }
    }

    // Check byte values
    println!("\nByte values:");
    println!("  'q' = 0x{:02x} ({})", b'q', b'q');
    println!("  'p' = 0x{:02x} ({})", b'p', b'p');
    println!("  'o' = 0x{:02x} ({})", b'o', b'o');
    println!("  'r' = 0x{:02x} ({})", b'r', b'r');
    println!("  'h' = 0x{:02x} ({})", b'h', b'h');
    println!("  'y' = 0x{:02x} ({})", b'y', b'y');
}
