use liblevenshtein::prelude::*;

fn main() {
    let dict = DoubleArrayTrie::from_terms(vec!["n", "a", "ag"]);
    let transducer = Transducer::new(dict.clone(), Algorithm::Standard);
    
    println!("Dictionary: {:?}", vec!["n", "a", "ag"]);
    println!("Query: 'a', distance: 1");
    
    let results: Vec<_> = transducer.query("a", 1).collect();
    println!("Results: {:?}", results);
    println!("Contains 'a': {}", results.contains(&"a".to_string()));
    
    // Try distance 0
    println!("\nQuery: 'a', distance: 0");
    let results0: Vec<_> = transducer.query("a", 0).collect();
    println!("Results: {:?}", results0);
    
    // Check if "a" is in the dictionary at all
    println!("\nDictionary contains 'a': {}", dict.contains("a"));
}
