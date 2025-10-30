#!/bin/bash
# Benchmark all optimization profiles for eviction wrappers

set -e

echo "======================================================"
echo "Eviction Wrapper Optimization Benchmark Suite"
echo "======================================================"
echo ""

# Baseline (no optimizations)
echo "[1/6] Running baseline (no optimizations)..."
RUSTFLAGS="-C target-cpu=native" cargo bench \
    --bench eviction_wrapper_benchmarks \
    --features pathmap-backend \
    --no-default-features \
    -- --save-baseline baseline \
    2>&1 | tee bench_results_baseline.txt

# parking_lot only
echo "[2/6] Running with parking_lot..."
RUSTFLAGS="-C target-cpu=native" cargo bench \
    --bench eviction_wrapper_benchmarks \
    --features "pathmap-backend,eviction-parking-lot" \
    --no-default-features \
    -- --save-baseline parking_lot \
    2>&1 | tee bench_results_parking_lot.txt

# Arc<str> only
echo "[3/6] Running with Arc<str> keys..."
RUSTFLAGS="-C target-cpu=native" cargo bench \
    --bench eviction_wrapper_benchmarks \
    --features "pathmap-backend,eviction-arc-str" \
    --no-default-features \
    -- --save-baseline arc_str \
    2>&1 | tee bench_results_arc_str.txt

# DashMap only
echo "[4/6] Running with DashMap..."
RUSTFLAGS="-C target-cpu=native" cargo bench \
    --bench eviction_wrapper_benchmarks \
    --features "pathmap-backend,eviction-dashmap" \
    --no-default-features \
    -- --save-baseline dashmap \
    2>&1 | tee bench_results_dashmap.txt

# Balanced profile
echo "[5/6] Running balanced profile..."
RUSTFLAGS="-C target-cpu=native" cargo bench \
    --bench eviction_wrapper_benchmarks \
    --features "pathmap-backend,eviction-opt-balanced" \
    --no-default-features \
    -- --save-baseline balanced \
    2>&1 | tee bench_results_balanced.txt

# Concurrent profile
echo "[6/6] Running concurrent profile..."
RUSTFLAGS="-C target-cpu=native" cargo bench \
    --bench eviction_wrapper_benchmarks \
    --features "pathmap-backend,eviction-opt-concurrent" \
    --no-default-features \
    -- --save-baseline concurrent \
    2>&1 | tee bench_results_concurrent.txt

echo ""
echo "======================================================"
echo "Benchmark Complete!"
echo "======================================================"
echo ""
echo "Results saved to:"
echo "  - bench_results_baseline.txt"
echo "  - bench_results_parking_lot.txt"
echo "  - bench_results_arc_str.txt"
echo "  - bench_results_dashmap.txt"
echo "  - bench_results_balanced.txt"
echo "  - bench_results_concurrent.txt"
echo ""
echo "To compare results:"
echo "  critic baseline parking_lot"
echo "  critic baseline balanced"
echo "  critic baseline concurrent"
