# Serialization Benchmarks - Baseline (Before Optimizations)

## Benchmark Date
2025-10-24 22:43:11 UTC

## Test Configuration
- Rust: Release build with optimizations
- RUSTFLAGS: `-C target-cpu=native`
- Features: `protobuf`
- Criterion: 100 samples per benchmark

## Baseline Results Summary (1000 terms dictionary)

### Serialization Performance

| Format | Time (µs) | Throughput (Melem/s) |
|--------|-----------|----------------------|
| Bincode | 893.53 | 1.1192 |
| JSON | 909.69 | 1.0993 |
| Protobuf V1 | 815.91 | 1.2256 |
| Protobuf V2 | 803.03 | 1.2453 |

### Deserialization Performance

| Format | Time (µs) | Throughput (Melem/s) |
|--------|-----------|----------------------|
| Bincode | 257.96 | 3.8765 |
| JSON | 281.25 | 3.5555 |
| Protobuf V1 | 485.18 | 2.0611 |
| Protobuf V2 | 448.79 | 2.2282 |

## Detailed Results

### Bincode Serialization

| Size | Time | Throughput |
|------|------|------------|
| 100 | 94.053 µs | 1.0632 Melem/s |
| 500 | 451.39 µs | 1.1077 Melem/s |
| 1000 | 893.53 µs | 1.1192 Melem/s |
| 5000 | 4.2358 ms | 1.1804 Melem/s |

### Bincode Deserialization

| Size | Time | Throughput |
|------|------|------------|
| 100 | 23.980 µs | 4.1701 Melem/s |
| 500 | 128.68 µs | 3.8855 Melem/s |
| 1000 | 257.96 µs | 3.8765 Melem/s |
| 5000 | 1.2818 ms | 3.9007 Melem/s |

### JSON Serialization

| Size | Time | Throughput |
|------|------|------------|
| 100 | 100.76 µs | 992.47 Kelem/s |
| 500 | 450.95 µs | 1.1088 Melem/s |
| 1000 | 909.69 µs | 1.0993 Melem/s |
| 5000 | 4.5181 ms | 1.1067 Melem/s |

### JSON Deserialization

| Size | Time | Throughput |
|------|------|------------|
| 100 | 31.388 µs | 3.1859 Melem/s |
| 500 | 143.81 µs | 3.4767 Melem/s |
| 1000 | 281.25 µs | 3.5555 Melem/s |
| 5000 | 1.5638 ms | 3.1974 Melem/s |

### Protobuf V1 Serialization

| Size | Time | Throughput |
|------|------|------------|
| 100 | 90.777 µs | 1.1016 Melem/s |
| 500 | 414.08 µs | 1.2075 Melem/s |
| 1000 | 815.91 µs | 1.2256 Melem/s |
| 5000 | 4.0106 ms | 1.2467 Melem/s |

### Protobuf V1 Deserialization

| Size | Time | Throughput |
|------|------|------------|
| 100 | 51.156 µs | 1.9548 Melem/s |
| 500 | 243.06 µs | 2.0571 Melem/s |
| 1000 | 485.18 µs | 2.0611 Melem/s |
| 5000 | 2.3385 ms | 2.1382 Melem/s |

### Protobuf V2 Serialization

| Size | Time | Throughput |
|------|------|------------|
| 100 | 88.560 µs | 1.1292 Melem/s |
| 500 | 404.51 µs | 1.2361 Melem/s |
| 1000 | 803.03 µs | 1.2453 Melem/s |
| 5000 | 3.8532 ms | 1.2976 Melem/s |

### Protobuf V2 Deserialization

| Size | Time | Throughput |
|------|------|------------|
| 100 | 46.997 µs | 2.1278 Melem/s |
| 500 | 230.85 µs | 2.1659 Melem/s |
| 1000 | 448.79 µs | 2.2282 Melem/s |
| 5000 | 2.2097 ms | 2.2627 Melem/s |

## Format Comparison (1000 terms)

### Serialization Speed Ranking
1. Protobuf V2: 803.03 µs (fastest)
2. Protobuf V1: 815.91 µs
3. Bincode: 893.53 µs
4. JSON: 909.69 µs (slowest)

### Deserialization Speed Ranking
1. Bincode: 257.96 µs (fastest)
2. JSON: 281.25 µs
3. Protobuf V2: 448.79 µs
4. Protobuf V1: 485.18 µs (slowest)

## Observations

1. **Protobuf V2 is fastest for serialization** but slower for deserialization
   - V2's packed format reduces encoding overhead
   - Delta encoding and flat arrays are efficient to write
   - But reconstruction requires more computation

2. **Bincode is fastest for deserialization**
   - Direct memory representation
   - Minimal transformation needed

3. **Performance scales well** with dictionary size
   - All formats maintain consistent throughput as size increases
   - No significant degradation at 5000 terms

4. **Protobuf V1 vs V2**
   - V2 is ~1.6% faster at serialization
   - V2 is ~7.5% faster at deserialization
   - V2 also achieves 60% smaller file sizes

## Next Steps

Run optimized benchmarks with:
- Vector pre-allocation
- HashMap pre-sizing
- Reduced allocation overhead

Expected improvements: 20-40% faster serialization/deserialization.
