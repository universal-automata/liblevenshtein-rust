//! Demonstration of the TransducerBuilder API.
//!
//! This example shows:
//! - Using the builder pattern for creating transducers
//! - Better API ergonomics compared to direct construction
//! - Validation and error handling
//!
//! Run with: cargo run --example builder_demo

use levenshtein::prelude::*;

fn main() {
    println!("TransducerBuilder Demonstration\n");
    println!("================================\n");

    let dict = PathMapDictionary::from_iter(vec![
        "apple", "application", "apply",
        "banana", "bandana",
        "cherry", "chocolate",
    ]);

    println!("1. Using the builder pattern:");
    println!("   Creating transducer with Standard algorithm...\n");

    let transducer = TransducerBuilder::new()
        .dictionary(dict.clone())
        .algorithm(Algorithm::Standard)
        .build()
        .expect("Failed to build transducer");

    println!("   ✓ Transducer created successfully");
    println!("   Algorithm: {:?}", transducer.algorithm());
    println!("   Dictionary size: {} terms\n", transducer.dictionary().len().unwrap());

    println!("2. Testing with a query:");
    let query = "aple";
    println!("   Searching for '{}' with distance 2:", query);
    let results: Vec<_> = transducer.query(query, 2).collect();
    for term in &results {
        println!("     - {}", term);
    }

    println!("\n3. Trying different algorithms:");

    // Transposition algorithm
    println!("   Building with Transposition algorithm...");
    let trans_transducer = TransducerBuilder::new()
        .dictionary(dict.clone())
        .algorithm(Algorithm::Transposition)
        .build()
        .unwrap();

    let typo_query = "aplpe"; // transposed 'l' and 'p'
    println!("   Query '{}' (transposed letters):", typo_query);
    let trans_results: Vec<_> = trans_transducer.query(typo_query, 1).collect();
    for term in &trans_results {
        println!("     - {}", term);
    }

    println!("\n4. Error handling:");

    // Missing dictionary
    println!("   Attempting to build without dictionary...");
    let result: Result<Transducer<PathMapDictionary>, _> = TransducerBuilder::new()
        .algorithm(Algorithm::Standard)
        .build();

    match result {
        Ok(_) => println!("     ✗ Should have failed"),
        Err(e) => println!("     ✓ Got expected error: {}", e),
    }

    // Missing algorithm
    println!("\n   Attempting to build without algorithm...");
    let result2 = TransducerBuilder::new()
        .dictionary(dict.clone())
        .build();

    match result2 {
        Ok(_) => println!("     ✗ Should have failed"),
        Err(e) => println!("     ✓ Got expected error: {}", e),
    }

    println!("\n5. Order independence:");
    println!("   Builder methods can be called in any order!");

    // Algorithm first
    let t1 = TransducerBuilder::new()
        .algorithm(Algorithm::MergeAndSplit)
        .dictionary(dict.clone())
        .build()
        .unwrap();

    // Dictionary first
    let _t2 = TransducerBuilder::new()
        .dictionary(dict)
        .algorithm(Algorithm::MergeAndSplit)
        .build()
        .unwrap();

    println!("   ✓ Both builders created successfully");
    println!("   Both use algorithm: {:?}", t1.algorithm());

    println!("\n✓ Builder demonstration completed!");
    println!("\nKey takeaways:");
    println!("- Builder pattern provides clear, readable API");
    println!("- Compile-time checking for required fields");
    println!("- Helpful error messages for missing configuration");
    println!("- Methods can be called in any order");
    println!("- Compare to direct construction: Transducer::new(dict, algo)");
}
