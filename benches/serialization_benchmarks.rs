//! Benchmarks for serialization performance optimization.

use criterion::{black_box, criterion_group, criterion_main, Criterion, BenchmarkId, Throughput};
use liblevenshtein::prelude::*;
use std::io::Cursor;

/// Create a dictionary of the specified size with varied word lengths
fn create_dictionary(size: usize) -> PathMapDictionary {
    let words: Vec<String> = (0..size)
        .map(|i| {
            // Create words of varying lengths (4-12 characters)
            let len = 4 + (i % 9);
            format!("word{:0width$}", i, width = len - 4)
        })
        .collect();
    PathMapDictionary::from_iter(words)
}

/// Benchmark: Bincode serialization performance
fn bench_bincode_serialize(c: &mut Criterion) {
    let mut group = c.benchmark_group("bincode_serialize");

    for size in [100, 500, 1000, 5000].iter() {
        let dict = create_dictionary(*size);
        group.throughput(Throughput::Elements(*size as u64));

        group.bench_with_input(BenchmarkId::from_parameter(size), size, |b, _| {
            b.iter(|| {
                let mut buffer = Vec::new();
                BincodeSerializer::serialize(black_box(&dict), &mut buffer)
                    .expect("Serialization failed");
                black_box(buffer);
            });
        });
    }
    group.finish();
}

/// Benchmark: Bincode deserialization performance
fn bench_bincode_deserialize(c: &mut Criterion) {
    let mut group = c.benchmark_group("bincode_deserialize");

    for size in [100, 500, 1000, 5000].iter() {
        let dict = create_dictionary(*size);
        let mut buffer = Vec::new();
        BincodeSerializer::serialize(&dict, &mut buffer).unwrap();

        group.throughput(Throughput::Elements(*size as u64));
        group.bench_with_input(BenchmarkId::from_parameter(size), size, |b, _| {
            b.iter(|| {
                let cursor = Cursor::new(black_box(&buffer));
                let loaded: PathMapDictionary = BincodeSerializer::deserialize(cursor)
                    .expect("Deserialization failed");
                black_box(loaded);
            });
        });
    }
    group.finish();
}

/// Benchmark: JSON serialization performance
fn bench_json_serialize(c: &mut Criterion) {
    let mut group = c.benchmark_group("json_serialize");

    for size in [100, 500, 1000, 5000].iter() {
        let dict = create_dictionary(*size);
        group.throughput(Throughput::Elements(*size as u64));

        group.bench_with_input(BenchmarkId::from_parameter(size), size, |b, _| {
            b.iter(|| {
                let mut buffer = Vec::new();
                JsonSerializer::serialize(black_box(&dict), &mut buffer)
                    .expect("Serialization failed");
                black_box(buffer);
            });
        });
    }
    group.finish();
}

/// Benchmark: JSON deserialization performance
fn bench_json_deserialize(c: &mut Criterion) {
    let mut group = c.benchmark_group("json_deserialize");

    for size in [100, 500, 1000, 5000].iter() {
        let dict = create_dictionary(*size);
        let mut buffer = Vec::new();
        JsonSerializer::serialize(&dict, &mut buffer).unwrap();

        group.throughput(Throughput::Elements(*size as u64));
        group.bench_with_input(BenchmarkId::from_parameter(size), size, |b, _| {
            b.iter(|| {
                let cursor = Cursor::new(black_box(&buffer));
                let loaded: PathMapDictionary = JsonSerializer::deserialize(cursor)
                    .expect("Deserialization failed");
                black_box(loaded);
            });
        });
    }
    group.finish();
}

#[cfg(feature = "protobuf")]
/// Benchmark: Protobuf V1 serialization performance
fn bench_protobuf_v1_serialize(c: &mut Criterion) {
    let mut group = c.benchmark_group("protobuf_v1_serialize");

    for size in [100, 500, 1000, 5000].iter() {
        let dict = create_dictionary(*size);
        group.throughput(Throughput::Elements(*size as u64));

        group.bench_with_input(BenchmarkId::from_parameter(size), size, |b, _| {
            b.iter(|| {
                let mut buffer = Vec::new();
                ProtobufSerializer::serialize(black_box(&dict), &mut buffer)
                    .expect("Serialization failed");
                black_box(buffer);
            });
        });
    }
    group.finish();
}

#[cfg(feature = "protobuf")]
/// Benchmark: Protobuf V1 deserialization performance
fn bench_protobuf_v1_deserialize(c: &mut Criterion) {
    let mut group = c.benchmark_group("protobuf_v1_deserialize");

    for size in [100, 500, 1000, 5000].iter() {
        let dict = create_dictionary(*size);
        let mut buffer = Vec::new();
        ProtobufSerializer::serialize(&dict, &mut buffer).unwrap();

        group.throughput(Throughput::Elements(*size as u64));
        group.bench_with_input(BenchmarkId::from_parameter(size), size, |b, _| {
            b.iter(|| {
                let cursor = Cursor::new(black_box(&buffer));
                let loaded: PathMapDictionary = ProtobufSerializer::deserialize(cursor)
                    .expect("Deserialization failed");
                black_box(loaded);
            });
        });
    }
    group.finish();
}

#[cfg(feature = "protobuf")]
/// Benchmark: Protobuf V2 (optimized) serialization performance
fn bench_protobuf_v2_serialize(c: &mut Criterion) {
    let mut group = c.benchmark_group("protobuf_v2_serialize");

    for size in [100, 500, 1000, 5000].iter() {
        let dict = create_dictionary(*size);
        group.throughput(Throughput::Elements(*size as u64));

        group.bench_with_input(BenchmarkId::from_parameter(size), size, |b, _| {
            b.iter(|| {
                let mut buffer = Vec::new();
                OptimizedProtobufSerializer::serialize(black_box(&dict), &mut buffer)
                    .expect("Serialization failed");
                black_box(buffer);
            });
        });
    }
    group.finish();
}

#[cfg(feature = "protobuf")]
/// Benchmark: Protobuf V2 (optimized) deserialization performance
fn bench_protobuf_v2_deserialize(c: &mut Criterion) {
    let mut group = c.benchmark_group("protobuf_v2_deserialize");

    for size in [100, 500, 1000, 5000].iter() {
        let dict = create_dictionary(*size);
        let mut buffer = Vec::new();
        OptimizedProtobufSerializer::serialize(&dict, &mut buffer).unwrap();

        group.throughput(Throughput::Elements(*size as u64));
        group.bench_with_input(BenchmarkId::from_parameter(size), size, |b, _| {
            b.iter(|| {
                let cursor = Cursor::new(black_box(&buffer));
                let loaded: PathMapDictionary = OptimizedProtobufSerializer::deserialize(cursor)
                    .expect("Deserialization failed");
                black_box(loaded);
            });
        });
    }
    group.finish();
}

/// Benchmark: Format comparison - serialization speed
fn bench_format_comparison_serialize(c: &mut Criterion) {
    let dict = create_dictionary(1000);
    let mut group = c.benchmark_group("format_comparison_serialize");
    group.throughput(Throughput::Elements(1000));

    group.bench_function("bincode", |b| {
        b.iter(|| {
            let mut buffer = Vec::new();
            BincodeSerializer::serialize(black_box(&dict), &mut buffer).unwrap();
            black_box(buffer);
        });
    });

    group.bench_function("json", |b| {
        b.iter(|| {
            let mut buffer = Vec::new();
            JsonSerializer::serialize(black_box(&dict), &mut buffer).unwrap();
            black_box(buffer);
        });
    });

    #[cfg(feature = "protobuf")]
    group.bench_function("protobuf_v1", |b| {
        b.iter(|| {
            let mut buffer = Vec::new();
            ProtobufSerializer::serialize(black_box(&dict), &mut buffer).unwrap();
            black_box(buffer);
        });
    });

    #[cfg(feature = "protobuf")]
    group.bench_function("protobuf_v2", |b| {
        b.iter(|| {
            let mut buffer = Vec::new();
            OptimizedProtobufSerializer::serialize(black_box(&dict), &mut buffer).unwrap();
            black_box(buffer);
        });
    });

    group.finish();
}

/// Benchmark: Format comparison - deserialization speed
fn bench_format_comparison_deserialize(c: &mut Criterion) {
    let dict = create_dictionary(1000);
    let mut group = c.benchmark_group("format_comparison_deserialize");
    group.throughput(Throughput::Elements(1000));

    let mut bincode_buffer = Vec::new();
    BincodeSerializer::serialize(&dict, &mut bincode_buffer).unwrap();
    group.bench_function("bincode", |b| {
        b.iter(|| {
            let cursor = Cursor::new(black_box(&bincode_buffer));
            let loaded: PathMapDictionary = BincodeSerializer::deserialize(cursor).unwrap();
            black_box(loaded);
        });
    });

    let mut json_buffer = Vec::new();
    JsonSerializer::serialize(&dict, &mut json_buffer).unwrap();
    group.bench_function("json", |b| {
        b.iter(|| {
            let cursor = Cursor::new(black_box(&json_buffer));
            let loaded: PathMapDictionary = JsonSerializer::deserialize(cursor).unwrap();
            black_box(loaded);
        });
    });

    #[cfg(feature = "protobuf")]
    {
        let mut protobuf_v1_buffer = Vec::new();
        ProtobufSerializer::serialize(&dict, &mut protobuf_v1_buffer).unwrap();
        group.bench_function("protobuf_v1", |b| {
            b.iter(|| {
                let cursor = Cursor::new(black_box(&protobuf_v1_buffer));
                let loaded: PathMapDictionary = ProtobufSerializer::deserialize(cursor).unwrap();
                black_box(loaded);
            });
        });

        let mut protobuf_v2_buffer = Vec::new();
        OptimizedProtobufSerializer::serialize(&dict, &mut protobuf_v2_buffer).unwrap();
        group.bench_function("protobuf_v2", |b| {
            b.iter(|| {
                let cursor = Cursor::new(black_box(&protobuf_v2_buffer));
                let loaded: PathMapDictionary = OptimizedProtobufSerializer::deserialize(cursor).unwrap();
                black_box(loaded);
            });
        });
    }

    group.finish();
}

criterion_group!(
    serialization_benches,
    bench_bincode_serialize,
    bench_bincode_deserialize,
    bench_json_serialize,
    bench_json_deserialize,
    bench_format_comparison_serialize,
    bench_format_comparison_deserialize,
);

#[cfg(feature = "protobuf")]
criterion_group!(
    protobuf_benches,
    bench_protobuf_v1_serialize,
    bench_protobuf_v1_deserialize,
    bench_protobuf_v2_serialize,
    bench_protobuf_v2_deserialize,
);

#[cfg(feature = "protobuf")]
criterion_main!(serialization_benches, protobuf_benches);

#[cfg(not(feature = "protobuf"))]
criterion_main!(serialization_benches);
