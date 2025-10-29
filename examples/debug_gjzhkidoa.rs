use liblevenshtein::prelude::*;

fn main() {
    let dict = DoubleArrayTrie::from_terms(vec!["gjzhkidoa", "gl"]);

    println!("Dictionary: [\"gjzhkidoa\", \"gl\"]");
    println!("contains('gjzhkidoa'): {}", dict.contains("gjzhkidoa"));
    println!("contains('gl'): {}", dict.contains("gl"));

    let transducer = Transducer::new(dict.clone(), Algorithm::Standard);

    println!("\nQuerying:");
    let results: Vec<_> = transducer.query("gjzhkidoa", 0).collect();
    println!("query('gjzhkidoa', 0): {:?}", results);

    let results: Vec<_> = transducer.query("gl", 0).collect();
    println!("query('gl', 0): {:?}", results);

    println!("\nManual tree walk for 'gjzhkidoa':");
    let mut current = dict.root();
    for &byte in b"gjzhkidoa" {
        if let Some(next) = current.transition(byte) {
            println!("  {} -> is_final: {}", byte as char, next.is_final());
            current = next;
        } else {
            println!("  NO TRANSITION for {} (0x{:02x})", byte as char, byte);
            break;
        }
    }

    println!("\nManual tree walk for 'gl':");
    let mut current = dict.root();
    for &byte in b"gl" {
        if let Some(next) = current.transition(byte) {
            println!("  {} -> is_final: {}", byte as char, next.is_final());
            current = next;
        } else {
            println!("  NO TRANSITION for {} (0x{:02x})", byte as char, byte);
            break;
        }
    }
}
