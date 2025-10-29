use liblevenshtein::prelude::*;

fn main() {
    // Manually trace construction of ["n", "a", "ag"]
    let terms = vec!["a", "ag", "n"]; // sorted

    println!("Building DAT with terms: {:?}", terms);
    let dict = DoubleArrayTrie::from_terms(terms);

    println!("\nChecking contains:");
    println!("  contains('a'): {}", dict.contains("a"));
    println!("  contains('ag'): {}", dict.contains("ag"));
    println!("  contains('n'): {}", dict.contains("n"));

    println!("\nManual traversal:");
    let root = dict.root();

    // Try to follow 'a'
    if let Some(a_node) = root.transition(b'a') {
        println!("  Found 'a' transition");
        println!("  'a' is_final: {}", a_node.is_final());

        // Try to follow 'g' from 'a'
        if let Some(g_node) = a_node.transition(b'g') {
            println!("  Found 'g' transition from 'a'");
            println!("  'ag' is_final: {}", g_node.is_final());
        } else {
            println!("  No 'g' transition from 'a'");
        }
    } else {
        println!("  No 'a' transition from root!");
    }

    // Try to follow 'n'
    if let Some(n_node) = root.transition(b'n') {
        println!("  Found 'n' transition");
        println!("  'n' is_final: {}", n_node.is_final());
    } else {
        println!("  No 'n' transition from root!");
    }

    println!("\nAll edges from root:");
    for (byte, node) in root.edges() {
        println!("  {} (0x{:02x}) -> is_final: {}", byte as char, byte, node.is_final());
    }
}
