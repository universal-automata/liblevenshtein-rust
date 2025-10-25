#!/bin/bash
# Profile-Guided Optimization (PGO) build script for liblevenshtein-rust
#
# This script performs a three-step PGO build:
# 1. Build with instrumentation to collect profiling data
# 2. Run profiling benchmark to generate .profraw files
# 3. Build with PGO optimizations using the profiling data

set -e  # Exit on error

echo "=== Profile-Guided Optimization Build ==="
echo

# Clean previous PGO data
echo "Step 0: Cleaning previous PGO data..."
rm -rf /tmp/pgo-data
mkdir -p /tmp/pgo-data
rm -f *.profraw
echo "Clean complete."
echo

# Step 1: Build with instrumentation
echo "Step 1: Building with instrumentation..."
RUSTFLAGS="-C target-cpu=native -C profile-generate=/tmp/pgo-data" \
    cargo build --release --bench profiling_benchmark
echo "Instrumented build complete."
echo

# Step 2: Run profiling workload
echo "Step 2: Running profiling benchmark to collect data..."
PROFILING_BIN=$(find target/release/deps -name "profiling_benchmark-*" -type f -executable | head -1)
if [ -z "$PROFILING_BIN" ]; then
    echo "Error: Could not find profiling benchmark binary"
    exit 1
fi
echo "Running: $PROFILING_BIN"
$PROFILING_BIN
echo "Profiling data collection complete."
echo

# Step 3: Merge profiling data
echo "Step 3: Merging profiling data..."
llvm-profdata merge -o /tmp/pgo-data/merged.profdata /tmp/pgo-data/*.profraw
echo "Profiling data merged."
echo

# Step 4: Build with PGO
echo "Step 4: Building with PGO optimizations..."
RUSTFLAGS="-C target-cpu=native -C profile-use=/tmp/pgo-data/merged.profdata -C llvm-args=-pgo-warn-missing-function" \
    cargo build --release
echo "PGO-optimized build complete."
echo

# Step 5: Verify PGO binary
echo "Step 5: Verifying PGO binary..."
ls -lh target/release/liblevenshtein-cli 2>/dev/null || echo "Note: CLI binary not built (requires 'cli' feature)"
echo
echo "=== PGO Build Complete ==="
echo "The PGO-optimized library is in target/release/"
echo "Run benchmarks with: RUSTFLAGS=\"-C target-cpu=native\" cargo bench"
