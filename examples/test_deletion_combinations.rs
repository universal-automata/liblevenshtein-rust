use liblevenshtein::prelude::*;

fn test_dict(words: Vec<&str>, query: &str, expected: &str) {
    let dict = DoubleArrayTrie::from_terms(words.clone());
    let transducer = Transducer::new(dict, Algorithm::Standard);
    let results: Vec<_> = transducer.query(query, 1).collect();
    let found = results.contains(&expected.to_string());
    println!("Dict {:?}, query '{}': found '{}' = {}", words, query, expected, found);
}

fn main() {
    test_dict(vec!["test"], "testt", "test");
    test_dict(vec!["test", "testing"], "testt", "test");
    test_dict(vec!["test", "apple"], "testt", "test");
    test_dict(vec!["test", "world"], "testt", "test");
    test_dict(vec!["test", "apple", "world"], "testt", "test");
    test_dict(vec!["test", "testing", "apple"], "testt", "test");
    test_dict(vec!["test", "testing", "world"], "testt", "test");
    test_dict(vec!["test", "testing", "apple", "world"], "testt", "test");
    
    println!();
    test_dict(vec!["apple"], "aple", "apple");
    test_dict(vec!["test", "apple"], "aple", "apple");
    test_dict(vec!["testing", "apple"], "aple", "apple");
    test_dict(vec!["test", "testing", "apple"], "aple", "apple");
    test_dict(vec!["test", "testing", "apple", "world"], "aple", "apple");
}
