use liblevenshtein::prelude::*;

fn main() {
    let dict = DoubleArrayTrie::from_terms(vec!["z", "za"]);

    println!("=== Manual State Tracing for query 'za' (distance=0) ===\n");

    // Verify dictionary structure
    println!("Dictionary structure:");
    println!("  contains('z'): {}", dict.contains("z"));
    println!("  contains('za'): {}", dict.contains("za"));

    let root = dict.root();
    println!("\nRoot transitions:");
    for (byte, node) in root.edges() {
        println!(
            "  {} (0x{:02x}) -> is_final: {}",
            byte as char,
            byte,
            node.is_final()
        );

        // Check children
        for (byte2, node2) in node.edges() {
            println!(
                "    {} (0x{:02x}) -> is_final: {}",
                byte2 as char,
                byte2,
                node2.is_final()
            );
        }
    }

    // Now trace with the transducer
    println!("\n=== Transducer Query ===");
    let transducer = Transducer::new(dict, Algorithm::Standard);

    let results_z: Vec<_> = transducer.query("z", 0).collect();
    println!("query('z', 0): {:?}", results_z);

    let results_za: Vec<_> = transducer.query("za", 0).collect();
    println!("query('za', 0): {:?}", results_za);

    // Let's also test with distance=1 to see if it works
    let results_za_1: Vec<_> = transducer.query("za", 1).collect();
    println!("query('za', 1): {:?}", results_za_1);
}
