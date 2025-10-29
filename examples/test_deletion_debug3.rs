use liblevenshtein::prelude::*;

fn main() {
    // Test with single word
    println!("=== Single word dictionary ===");
    let dict1 = DoubleArrayTrie::from_terms(vec!["test"]);
    let trans1 = Transducer::new(dict1, Algorithm::Standard);
    let r1: Vec<_> = trans1.query("testt", 1).collect();
    println!("'testt' in [test]: {:?}", r1);
    
    // Test with multiple words
    println!("\n=== Multiple word dictionary ===");
    let dict2 = DoubleArrayTrie::from_terms(vec!["test", "testing"]);
    let trans2 = Transducer::new(dict2, Algorithm::Standard);
    let r2: Vec<_> = trans2.query("testt", 1).collect();
    println!("'testt' in [test, testing]: {:?}", r2);
    
    let r3: Vec<_> = trans2.query("testt", 2).collect();
    println!("'testt' in [test, testing] (dist=2): {:?}", r3);
    
    // Test without the longer word
    println!("\n=== Without 'testing' ===");
    let dict3 = DoubleArrayTrie::from_terms(vec!["test", "world"]);
    let trans3 = Transducer::new(dict3, Algorithm::Standard);
    let r4: Vec<_> = trans3.query("testt", 1).collect();
    println!("'testt' in [test, world]: {:?}", r4);
}
