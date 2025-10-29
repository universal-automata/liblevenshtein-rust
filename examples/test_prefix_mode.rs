use liblevenshtein::prelude::*;

fn main() {
    let dict = DawgDictionary::from_iter(vec!["test", "testing", "tested", "best"]);
    let transducer = Transducer::new(dict, Algorithm::Standard);

    // Test using query_ordered().prefix()
    println!("Using query_ordered().prefix():");
    let results: Vec<_> = transducer
        .query_ordered("tes", 0)
        .prefix()
        .map(|c| c.term)
        .collect();
    println!("Results: {:?}", results);
    
    // Also test the query_builder API
    println!("\nUsing query_builder with prefix_mode:");
    let results2: Vec<_> = transducer
        .query_builder("tes")
        .prefix_mode(true)
        .max_distance(0)
        .execute()
        .collect();
    println!("Results: {:?}", results2);
}
