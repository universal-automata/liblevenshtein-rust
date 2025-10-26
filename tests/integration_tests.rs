use liblevenshtein::dictionary::Dictionary;
use liblevenshtein::prelude::*;

#[test]
fn test_basic_dictionary_ops() {
    let dict = PathMapDictionary::from_iter(vec!["test"]);
    let root = dict.root();

    println!("Root is_final: {}", root.is_final());

    let t = root.transition(b't');
    assert!(t.is_some(), "Should have 't' transition");
    let t_node = t.unwrap();
    println!("After 't', is_final: {}", t_node.is_final());

    let e = t_node.transition(b'e');
    assert!(e.is_some(), "Should have 'e' transition");
    let e_node = e.unwrap();
    println!("After 'te', is_final: {}", e_node.is_final());

    let s = e_node.transition(b's');
    assert!(s.is_some(), "Should have 's' transition");
    let s_node = s.unwrap();
    println!("After 'tes', is_final: {}", s_node.is_final());

    let t2 = s_node.transition(b't');
    assert!(t2.is_some(), "Should have second 't' transition");
    let t2_node = t2.unwrap();
    println!("After 'test', is_final: {}", t2_node.is_final());
    assert!(t2_node.is_final(), "'test' should be final!");
}

#[test]
fn test_simple_query() {
    let dict = PathMapDictionary::from_iter(vec!["test"]);
    let transducer = Transducer::new(dict, Algorithm::Standard);

    let results: Vec<_> = transducer.query("test", 0).collect();
    println!("Results: {:?}", results);
    assert_eq!(results, vec!["test"]);
}
