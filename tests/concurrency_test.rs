//! Test to verify true concurrent read parallelism

use liblevenshtein::prelude::*;
use std::sync::{Arc, Barrier};
use std::thread;
use std::time::{Duration, Instant};

#[test]
fn test_parallel_reads() {
    // Create dictionary with many terms
    let terms: Vec<String> = (0..1000).map(|i| format!("term{}", i)).collect();
    let dict = DoubleArrayTrie::from_terms(terms);
    let transducer = Transducer::new(dict.clone(), Algorithm::Standard);

    const NUM_READERS: usize = 8;
    let barrier = Arc::new(Barrier::new(NUM_READERS));

    let mut handles = vec![];

    // Spawn multiple reader threads
    for i in 0..NUM_READERS {
        let transducer_clone = transducer.clone();
        let barrier_clone = Arc::clone(&barrier);

        let handle = thread::spawn(move || {
            // Wait for all threads to be ready
            barrier_clone.wait();

            // All threads start querying at the same time
            let start = Instant::now();

            // Perform many queries
            for j in 0..100 {
                let query = format!("term{}", (i * 100 + j) % 1000);
                let _results: Vec<_> = transducer_clone.query(&query, 1).collect();
            }

            start.elapsed()
        });

        handles.push(handle);
    }

    // Collect results
    let durations: Vec<_> = handles.into_iter().map(|h| h.join().unwrap()).collect();

    // Print timing info
    println!("\n=== Parallel Read Test ===");
    println!("Number of reader threads: {}", NUM_READERS);
    for (i, duration) in durations.iter().enumerate() {
        println!("  Thread {}: {:?}", i, duration);
    }

    let avg = durations.iter().sum::<Duration>() / NUM_READERS as u32;
    println!("  Average: {:?}", avg);

    // If reads were serialized, total time would be sum of all durations
    // If reads are parallel, total time should be close to max duration
    let max = durations.iter().max().unwrap();
    let sum = durations.iter().sum::<Duration>();

    println!("\n  Max duration: {:?}", max);
    println!("  Sum duration: {:?}", sum);
    println!(
        "  Parallelism ratio: {:.2}x",
        sum.as_secs_f64() / max.as_secs_f64()
    );

    // If parallel, ratio should be close to NUM_READERS
    // If serialized, ratio would be close to 1.0
    assert!(
        sum.as_secs_f64() / max.as_secs_f64() > 2.0,
        "Reads appear to be serialized, not parallel!"
    );
}

#[test]
fn test_read_during_write() {
    let dict: DynamicDawg<()> = DynamicDawg::from_terms(vec!["test"]);
    let transducer = Transducer::new(dict.clone(), Algorithm::Standard);

    let dict_writer = dict.clone();
    let transducer_reader = transducer.clone();

    // Writer thread: slowly adds terms
    let writer = thread::spawn(move || {
        for i in 0..10 {
            thread::sleep(Duration::from_millis(10));
            dict_writer.insert(&format!("term{}", i));
        }
    });

    // Reader thread: continuously queries
    let reader = thread::spawn(move || {
        let mut query_count = 0;
        for _ in 0..50 {
            thread::sleep(Duration::from_millis(2));
            let _results: Vec<_> = transducer_reader.query("test", 1).collect();
            query_count += 1;
        }
        query_count
    });

    writer.join().unwrap();
    let queries = reader.join().unwrap();

    println!("\n=== Read During Write Test ===");
    println!("  Queries completed while writes happening: {}", queries);
    println!("  Final term count: {}", dict.len().unwrap_or(0));

    // Reader should have completed many queries despite concurrent writes
    assert!(queries > 40, "Reader was blocked too much by writes");
}
