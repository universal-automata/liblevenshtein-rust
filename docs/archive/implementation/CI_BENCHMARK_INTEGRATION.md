# CI Benchmark Integration

This document describes the enhancements made to the CI workflows to include benchmark results in the CI reports.

## Overview

The CI workflows have been enhanced to automatically run benchmarks and include formatted results in the GitHub Actions summary reports. This provides visibility into performance characteristics and helps detect performance regressions.

## Changes Made

### 1. CI Workflow (`ci.yml`)

#### Benchmark Execution
- **When**: Runs on pushes to `master` branch only
- **Runner**: Ubuntu Latest with nightly Rust
- **Command**: `cargo bench --all-features --no-fail-fast -- --output-format bencher`

#### Benchmark Result Parsing
A new step parses the bencher output format and generates a formatted markdown table:

```bash
# Parse bencher output format: test name ... bench: <time> ns/iter (+/- <variance>)
grep "bench:" output.txt | while read -r line; do
  # Extract benchmark name (everything before '...') and trim whitespace
  name=$(echo "$line" | sed 's/test \(.*\) \.\.\..*/\1/' | sed 's/^[[:space:]]*//;s/[[:space:]]*$//')

  # Extract time and unit
  time=$(echo "$line" | grep -oP '[\d,]+ ns/iter' | head -1)

  # Calculate throughput (operations per second)
  if [[ "$time" =~ ([0-9,]+) ]]; then
    ns="${BASH_REMATCH[1]//,/}"
    if [ "$ns" -gt 0 ]; then
      ops_per_sec=$(( 1000000000 / ns ))
      throughput=$(printf "%'d ops/s" $ops_per_sec)
    fi
  fi
done
```

#### Test Report Enhancement
The `test-report` job now:
- Depends on `benchmarks` job
- Downloads benchmark artifacts
- Includes benchmark results in the summary
- Shows "skipped" message when benchmarks don't run (non-master branches)

**Example Output:**
```markdown
## Test Results Summary

| Job | Status |
|-----|--------|
| Tests | success |
| Lint | success |
| Benchmarks | success |

✅ All checks passed!

---

## Benchmark Results

| Benchmark | Time | Throughput |
|-----------|------|------------|
| `backend_comparison::bench_construction::DoubleArrayTrie` | 3,234,567 ns/iter | 309 ops/s |
| `backend_comparison::bench_exact_matching::DoubleArrayTrie` | 6,634 ns/iter | 150,738 ops/s |
| `backend_comparison::bench_distance_1::DoubleArrayTrie` | 12,923 ns/iter | 77,384 ops/s |

**Note:** Benchmarks are run on GitHub Actions runners and may vary.

Full results available in artifacts.
```

### 2. Nightly Workflow (`nightly.yml`)

#### Benchmark Execution
- **When**: Nightly at 2 AM UTC, only on Linux x86_64
- **Execution**: Same as CI workflow

#### Benchmark Result Parsing
Same parsing logic as CI workflow, but includes platform name in header:
```markdown
## Benchmark Results - Linux x86_64
```

#### Nightly Summary Enhancement
The `nightly-summary` job now:
- Downloads benchmark artifacts from all platforms
- Includes benchmark results in the summary
- Displays formatted table with performance metrics

## Artifacts

Both workflows upload benchmark results as artifacts:

### CI Workflow
- **Name**: `benchmark-results`
- **Contents**:
  - `output.txt` - Raw bencher output
  - `benchmark-summary.md` - Formatted markdown table
- **Retention**: 30 days

### Nightly Workflow
- **Name**: `nightly-benchmarks-<platform>`
- **Contents**:
  - `benchmark-results.txt` - Raw bencher output
  - `benchmark-summary.md` - Formatted markdown table
- **Retention**: 30 days

## Benefits

1. **Visibility**: Benchmark results are immediately visible in the CI summary
2. **Performance Tracking**: Historical results available via artifacts
3. **Regression Detection**: Easy to spot performance degradations
4. **Comparison**: Tabular format makes it easy to compare different backends
5. **Throughput Calculation**: Automatic ops/sec calculation for better understanding

## Example Benchmarks Reported

The following benchmark suites are automatically reported:

### Backend Comparison (`benches/backend_comparison.rs`)
- Construction time for different backends
- Exact matching performance
- Contains checks
- Distance 1 fuzzy matching
- Distance 2 fuzzy matching

### Suffix Automaton (`benches/suffix_automaton_benchmarks.rs`)
- Suffix automaton construction
- Substring matching
- Fuzzy substring search

### Comprehensive Profiling (`benches/comprehensive_profiling.rs`)
- End-to-end query performance
- Memory allocation patterns
- Edge iteration performance

### Matching Modes (`benches/matching_modes_comparison.rs`)
- Exact matching
- Prefix matching
- Fuzzy matching with different algorithms

## Usage

### Viewing Results in CI

1. Navigate to the GitHub Actions tab
2. Select a workflow run
3. View the "Test Report Summary" or "Nightly Summary" step
4. Benchmark results are displayed in a formatted table

### Downloading Raw Results

1. Navigate to a completed workflow run
2. Scroll to the "Artifacts" section
3. Download `benchmark-results` or `nightly-benchmarks-*`
4. Extract and view the raw bencher output

## Notes

- Benchmarks only run on `master` branch in CI workflow (to save CI time)
- Benchmarks run nightly on all platforms in nightly workflow
- Results may vary between runs due to GitHub Actions runner conditions
- Throughput is calculated as `1,000,000,000 / nanoseconds` = operations per second

## Future Enhancements

Possible improvements:
1. **Historical Tracking**: Store results in a database for trend analysis
2. **Regression Detection**: Automatically flag significant performance drops
3. **Comparison Reports**: Compare results across branches/PRs
4. **Flame Graph Generation**: Include flame graphs in artifacts
5. **Benchmark Selection**: Allow running specific benchmark suites
6. **Performance Badges**: Generate badges showing key metrics

---

**Last Updated**: 2025-01-XX
**Status**: Active
**Workflows Modified**: `ci.yml`, `nightly.yml`
