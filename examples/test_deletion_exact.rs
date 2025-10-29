use liblevenshtein::prelude::*;

fn main() {
    // EXACT same as the test
    let dict = DoubleArrayTrie::from_terms(vec!["test", "testing", "apple", "world"]);
    let transducer = Transducer::new(dict, Algorithm::Standard);

    // Query has extra character (deletion from query)
    let results: Vec<_> = transducer.query("testt", 1).collect();
    println!("Query 'testt' with distance 1: {:?}", results);
    println!("Contains 'test': {}", results.contains(&"test".to_string()));

    // Query missing character (insertion from dictionary)
    let results: Vec<_> = transducer.query("aple", 1).collect();
    println!("Query 'aple' with distance 1: {:?}", results);
    println!("Contains 'apple': {}", results.contains(&"apple".to_string()));
}
