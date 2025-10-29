//! Profiling benchmark focusing on DAT interaction with Levenshtein automata.
//!
//! This benchmark specifically profiles the hot paths in:
//! 1. DAT edge traversal during Levenshtein matching
//! 2. State transitions in the Levenshtein automaton
//! 3. The composition of DAT × Levenshtein automaton

use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion};
use liblevenshtein::prelude::*;
use std::hint::black_box as bh;

fn load_dictionary() -> Vec<String> {
    // Load a real word list if available, otherwise generate sample data
    if let Ok(contents) = std::fs::read_to_string("/usr/share/dict/words") {
        contents.lines().take(10000).map(String::from).collect()
    } else {
        // Generate sample dictionary
        (0..10000).map(|i| format!("word{:04}", i)).collect()
    }
}

/// Profile DAT edge iteration (called frequently during Levenshtein traversal)
fn bench_dat_edge_iteration(c: &mut Criterion) {
    let terms = load_dictionary();
    let dat = DoubleArrayTrie::from_terms(terms);

    c.bench_function("dat_edge_iteration", |b| {
        b.iter(|| {
            let root = dat.root();
            let mut count = 0;

            // Simulate traversing edges like Levenshtein automaton does
            for edge in root.edges() {
                count += 1;
                bh(&edge);
            }

            bh(count)
        })
    });
}

/// Profile DAT transition performance (critical path in Levenshtein matching)
fn bench_dat_transitions(c: &mut Criterion) {
    let terms = load_dictionary();
    let dat = DoubleArrayTrie::from_terms(terms);

    let test_chars = vec!['a', 'b', 'c', 'd', 'e', 't', 'h', 'i', 's'];

    c.bench_function("dat_transitions", |b| {
        b.iter(|| {
            let mut node = dat.root();

            for &ch in &test_chars {
                if let Some(next) = node.transition(ch as u8) {
                    node = next;
                    bh(&node);
                }
            }
        })
    });
}

/// Profile the complete Levenshtein query pipeline with DAT
fn bench_levenshtein_query_pipeline(c: &mut Criterion) {
    let terms = load_dictionary();
    let dat = DoubleArrayTrie::from_terms(terms);
    let transducer = Transducer::new(dat, Algorithm::Standard);

    let queries = vec![("test", 1), ("hello", 2), ("world", 1), ("programming", 2)];

    let mut group = c.benchmark_group("levenshtein_pipeline");

    for (query, distance) in queries {
        group.bench_with_input(
            BenchmarkId::new("distance", format!("{}_d{}", query, distance)),
            &(query, distance),
            |b, &(q, d)| {
                b.iter(|| {
                    let results: Vec<_> = transducer.query(q, d).collect();
                    bh(results)
                })
            },
        );
    }

    group.finish();
}

/// Profile different Levenshtein algorithm variants with DAT
fn bench_algorithm_variants(c: &mut Criterion) {
    let terms = load_dictionary();
    let dat = DoubleArrayTrie::from_terms(terms.clone());

    let query = "testing";
    let distance = 2;

    let mut group = c.benchmark_group("algorithm_variants");

    // Standard algorithm
    group.bench_function("Standard", |b| {
        let transducer = Transducer::new(dat.clone(), Algorithm::Standard);
        b.iter(|| {
            let results: Vec<_> = transducer.query(query, distance).collect();
            bh(results)
        })
    });

    // Transposition algorithm
    group.bench_function("Transposition", |b| {
        let transducer = Transducer::new(dat.clone(), Algorithm::Transposition);
        b.iter(|| {
            let results: Vec<_> = transducer.query(query, distance).collect();
            bh(results)
        })
    });

    // MergeAndSplit algorithm
    group.bench_function("MergeAndSplit", |b| {
        let transducer = Transducer::new(dat.clone(), Algorithm::MergeAndSplit);
        b.iter(|| {
            let results: Vec<_> = transducer.query(query, distance).collect();
            bh(results)
        })
    });

    group.finish();
}

/// Profile state pool reuse during queries
fn bench_state_pool_efficiency(c: &mut Criterion) {
    let terms = load_dictionary();
    let dat = DoubleArrayTrie::from_terms(terms);
    let transducer = Transducer::new(dat, Algorithm::Standard);

    c.bench_function("state_pool_reuse", |b| {
        b.iter(|| {
            // Multiple queries to test state pool reuse
            for query in &["test", "hello", "world", "rust", "code"] {
                let results: Vec<_> = transducer.query(query, 1).collect();
                bh(results);
            }
        })
    });
}

/// Profile memory allocation patterns during queries
fn bench_allocation_patterns(c: &mut Criterion) {
    let terms = load_dictionary();
    let dat = DoubleArrayTrie::from_terms(terms);
    let transducer = Transducer::new(dat, Algorithm::Standard);

    let mut group = c.benchmark_group("allocation_patterns");

    // Short query (minimal allocations)
    group.bench_function("short_query", |b| {
        b.iter(|| {
            let results: Vec<_> = transducer.query("ab", 1).collect();
            bh(results)
        })
    });

    // Medium query
    group.bench_function("medium_query", |b| {
        b.iter(|| {
            let results: Vec<_> = transducer.query("testing", 2).collect();
            bh(results)
        })
    });

    // Long query (more allocations)
    group.bench_function("long_query", |b| {
        b.iter(|| {
            let results: Vec<_> = transducer.query("constantinople", 3).collect();
            bh(results)
        })
    });

    group.finish();
}

/// Profile the composition operation (DAT × Levenshtein)
fn bench_composition_overhead(c: &mut Criterion) {
    let terms = load_dictionary();
    let dat = DoubleArrayTrie::from_terms(terms);

    c.bench_function("composition_overhead", |b| {
        let transducer = Transducer::new(dat.clone(), Algorithm::Standard);

        b.iter(|| {
            // Profile the main query loop
            let query = "test";
            let distance = 2;

            let mut count = 0;
            for candidate in transducer.query_with_distance(query, distance) {
                count += 1;
                bh(&candidate);
            }
            bh(count)
        })
    });
}

/// Profile characteristic vector operations
fn bench_characteristic_vector(c: &mut Criterion) {
    let terms = load_dictionary();
    let dat = DoubleArrayTrie::from_terms(terms);
    let transducer = Transducer::new(dat, Algorithm::Standard);

    c.bench_function("characteristic_vector_ops", |b| {
        b.iter(|| {
            // Query that exercises characteristic vector computation
            let results: Vec<_> = transducer.query("abcdefghij", 3).collect();
            bh(results)
        })
    });
}

criterion_group!(
    benches,
    bench_dat_edge_iteration,
    bench_dat_transitions,
    bench_levenshtein_query_pipeline,
    bench_algorithm_variants,
    bench_state_pool_efficiency,
    bench_allocation_patterns,
    bench_composition_overhead,
    bench_characteristic_vector,
);
criterion_main!(benches);
