use liblevenshtein::prelude::*;

fn main() {
    let terms = vec!["z", "za"]; // sorted
    println!("Building DAT with terms: {:?}", terms);

    let dict = DoubleArrayTrie::from_terms(terms);

    println!("\nChecking contains:");
    println!("  contains('z'): {}", dict.contains("z"));
    println!("  contains('za'): {}", dict.contains("za"));

    println!("\nQuerying with distance=0:");
    let transducer = Transducer::new(dict.clone(), Algorithm::Standard);

    let results_z: Vec<_> = transducer.query("z", 0).collect();
    println!("  query('z', 0): {:?}", results_z);

    let results_za: Vec<_> = transducer.query("za", 0).collect();
    println!("  query('za', 0): {:?}", results_za);

    println!("\nManual traversal:");
    let root = dict.root();

    if let Some(z_node) = root.transition(b'z') {
        println!("  Found 'z' transition");
        println!("  'z' is_final: {}", z_node.is_final());

        if let Some(a_node) = z_node.transition(b'a') {
            println!("  Found 'a' transition from 'z'");
            println!("  'za' is_final: {}", a_node.is_final());
        } else {
            println!("  No 'a' transition from 'z'");
        }
    } else {
        println!("  No 'z' transition from root!");
    }
}
