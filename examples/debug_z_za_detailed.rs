use liblevenshtein::prelude::*;

fn main() {
    println!("=== Testing both DAWG and DAT ===\n");

    let terms = vec!["z", "za"];

    // Test with DawgDictionary
    println!("--- DawgDictionary ---");
    let dawg = DawgDictionary::from_iter(terms.clone());
    println!("contains('z'): {}", dawg.contains("z"));
    println!("contains('za'): {}", dawg.contains("za"));

    let transducer_dawg = Transducer::new(dawg, Algorithm::Standard);
    let results_z: Vec<_> = transducer_dawg.query("z", 0).collect();
    let results_za: Vec<_> = transducer_dawg.query("za", 0).collect();
    println!("query('z', 0): {:?}", results_z);
    println!("query('za', 0): {:?}", results_za);

    // Test with DoubleArrayTrie
    println!("\n--- DoubleArrayTrie ---");
    let dat = DoubleArrayTrie::from_terms(terms);
    println!("contains('z'): {}", dat.contains("z"));
    println!("contains('za'): {}", dat.contains("za"));

    let transducer_dat = Transducer::new(dat, Algorithm::Standard);
    let results_z: Vec<_> = transducer_dat.query("z", 0).collect();
    let results_za: Vec<_> = transducer_dat.query("za", 0).collect();
    println!("query('z', 0): {:?}", results_z);
    println!("query('za', 0): {:?}", results_za);
}
