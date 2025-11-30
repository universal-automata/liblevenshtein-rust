use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion, Throughput};
use liblevenshtein::dictionary::{
    dawg::DawgDictionary, dynamic_dawg::DynamicDawg, Dictionary, DictionaryNode,
};
use std::collections::HashSet;

/// Generate a list of dictionary terms for testing
fn generate_terms(size: usize) -> Vec<String> {
    let mut terms = Vec::with_capacity(size);

    // Common English prefixes and suffixes for realistic dictionary
    let prefixes = [
        "pre", "un", "re", "in", "dis", "en", "non", "over", "mis", "sub",
    ];
    let roots = [
        "test", "code", "data", "work", "play", "read", "write", "run", "walk", "talk",
    ];
    let suffixes = [
        "ing", "ed", "er", "est", "ly", "ness", "ment", "tion", "able", "ful",
    ];

    // Generate realistic word combinations
    for i in 0..size {
        let prefix = prefixes[i % prefixes.len()];
        let root = roots[(i / prefixes.len()) % roots.len()];
        let suffix = suffixes[(i / (prefixes.len() * roots.len())) % suffixes.len()];

        terms.push(format!("{}{}{}", prefix, root, suffix));
    }

    terms.sort();
    terms.dedup();
    terms
}

/// Benchmark edge lookup (transition) - will benefit from binary search optimization
fn bench_dawg_edge_lookup(c: &mut Criterion) {
    let mut group = c.benchmark_group("dawg_edge_lookup");

    for size in [100, 500, 1000, 5000].iter() {
        let terms = generate_terms(*size);
        let dawg = DawgDictionary::from_iter(terms.iter().map(|s| s.as_str()));

        // Generate test queries (existing terms)
        let test_queries: Vec<&str> = terms.iter().take(100).map(|s| s.as_str()).collect();

        group.throughput(Throughput::Elements(100));
        group.bench_with_input(BenchmarkId::from_parameter(size), size, |b, _| {
            b.iter(|| {
                for query in &test_queries {
                    let mut node = dawg.root();
                    for &byte in query.as_bytes() {
                        if let Some(next_node) = node.transition(black_box(byte)) {
                            node = next_node;
                        } else {
                            break;
                        }
                    }
                    black_box(node);
                }
            });
        });
    }
    group.finish();
}

/// Benchmark dynamic DAWG edge insertion - will benefit from binary insertion
fn bench_dynamic_dawg_insertion(c: &mut Criterion) {
    let mut group = c.benchmark_group("dynamic_dawg_insertion");

    for size in [100, 500, 1000].iter() {
        let terms = generate_terms(*size);

        group.throughput(Throughput::Elements(*size as u64));
        group.bench_with_input(BenchmarkId::from_parameter(size), size, |b, _| {
            b.iter(|| {
                let dawg: DynamicDawg<()> = DynamicDawg::default();
                for term in &terms {
                    dawg.insert(black_box(term));
                }
                black_box(dawg);
            });
        });
    }
    group.finish();
}

/// Benchmark edge iteration - used heavily in query operations
fn bench_dawg_edge_iteration(c: &mut Criterion) {
    let mut group = c.benchmark_group("dawg_edge_iteration");

    for size in [100, 500, 1000, 5000].iter() {
        let terms = generate_terms(*size);
        let dawg = DawgDictionary::from_iter(terms.iter().map(|s| s.as_str()));

        group.throughput(Throughput::Elements(*size as u64));
        group.bench_with_input(BenchmarkId::from_parameter(size), size, |b, _| {
            b.iter(|| {
                // Traverse all edges in the DAWG
                let mut stack = vec![dawg.root()];
                let mut visited = HashSet::new();
                let mut edge_count = 0;

                while let Some(node) = stack.pop() {
                    // Use a simple hash of the node's final state and edge count as ID
                    let node_id = (node.is_final() as usize, node.edges().count());
                    if visited.insert(node_id) {
                        for (_label, child) in node.edges() {
                            edge_count += 1;
                            stack.push(child);
                        }
                    }
                }
                black_box(edge_count);
            });
        });
    }
    group.finish();
}

/// Benchmark dictionary contains() - uses edge lookup heavily
fn bench_dawg_contains(c: &mut Criterion) {
    let mut group = c.benchmark_group("dawg_contains");

    for size in [100, 500, 1000, 5000].iter() {
        let terms = generate_terms(*size);
        let dawg = DawgDictionary::from_iter(terms.iter().map(|s| s.as_str()));

        // Create test set with 50% hits, 50% misses
        let mut test_queries = Vec::new();
        test_queries.extend(terms.iter().take(50).cloned());
        for i in 0..50 {
            test_queries.push(format!("nonexistent{}", i));
        }

        group.throughput(Throughput::Elements(100));
        group.bench_with_input(BenchmarkId::from_parameter(size), size, |b, _| {
            b.iter(|| {
                let mut count = 0;
                for query in &test_queries {
                    if dawg.contains(black_box(query)) {
                        count += 1;
                    }
                }
                black_box(count);
            });
        });
    }
    group.finish();
}

/// Benchmark dynamic DAWG minimize operation
fn bench_dynamic_dawg_minimize(c: &mut Criterion) {
    let mut group = c.benchmark_group("dynamic_dawg_minimize");

    for size in [100, 500, 1000].iter() {
        let terms = generate_terms(*size);
        let dawg: DynamicDawg<()> = DynamicDawg::default();
        for term in &terms {
            dawg.insert(term);
        }

        group.throughput(Throughput::Elements(*size as u64));
        group.bench_with_input(BenchmarkId::from_parameter(size), size, |b, _| {
            b.iter(|| {
                let dawg_clone = dawg.clone();
                dawg_clone.minimize();
                black_box(dawg_clone);
            });
        });
    }
    group.finish();
}

/// Benchmark DawgDictionary construction (baseline for comparison)
fn bench_dawg_construction(c: &mut Criterion) {
    let mut group = c.benchmark_group("dawg_construction");

    for size in [100, 500, 1000, 5000].iter() {
        let terms = generate_terms(*size);

        group.throughput(Throughput::Elements(*size as u64));
        group.bench_with_input(BenchmarkId::from_parameter(size), size, |b, _| {
            b.iter(|| {
                let dawg = DawgDictionary::from_iter(black_box(terms.iter().map(|s| s.as_str())));
                black_box(dawg);
            });
        });
    }
    group.finish();
}

criterion_group!(
    benches,
    bench_dawg_edge_lookup,
    bench_dynamic_dawg_insertion,
    bench_dawg_edge_iteration,
    bench_dawg_contains,
    bench_dynamic_dawg_minimize,
    bench_dawg_construction,
);
criterion_main!(benches);
