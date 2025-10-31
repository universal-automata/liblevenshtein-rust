# Eviction Wrapper Optimization Plan

## Current Performance Characteristics

### Identified Bottlenecks

1. **Lock Contention** (`Arc<RwLock<HashMap>>`)
   - Every `get_value()` acquires write lock
   - Single global lock for all metadata
   - High contention in concurrent workloads

2. **String Allocations**
   - `term.to_string()` on every access
   - HashMap uses `String` keys (24 bytes + heap allocation)
   - Unnecessary copies for lookups

3. **Arc Cloning Overhead**
   - `Arc::clone()` on every node transition during traversal
   - Atomic reference count operations

4. **Instant::now() System Calls**
   - Called twice per `get_value()` (once for lookup, once for update)
   - Relatively expensive system call

5. **No Batching or Coalescing**
   - Each access triggers immediate metadata update
   - No temporal locality optimization

## Optimization Strategies

### Phase 1: Low-Hanging Fruit (Immediate Wins)

#### 1.1 Replace `std::sync::RwLock` with `parking_lot::RwLock`

**Benefits:**
- 2-3x faster lock acquisition
- Smaller memory footprint (no poison handling)
- Better performance under contention
- Drop-in replacement

**Implementation:**
```rust
// Add to Cargo.toml
[dependencies]
parking_lot = "0.12"

// In eviction wrapper files:
use parking_lot::RwLock;
```

**Estimated improvement:** 15-25% faster for single-threaded, 2-3x for multi-threaded

**Tradeoffs:** None significant (parking_lot is well-tested)

---

#### 1.2 Use `Arc<str>` instead of `String` for HashMap keys

**Benefits:**
- Reduces allocations (16 bytes vs 24 bytes + heap)
- Better cache locality
- Allows zero-copy lookups with `&str`

**Implementation:**
```rust
use std::collections::HashMap;
use std::sync::Arc;

type MetadataMap = HashMap<Arc<str>, EntryMetadata>;

// Lookup with borrowed str
fn lookup(&self, term: &str) -> Option<...> {
    self.metadata.read().get(term).cloned()
}

// Insert with Arc<str>
fn insert(&self, term: &str) {
    let key: Arc<str> = Arc::from(term);
    self.metadata.write().insert(key, ...);
}
```

**Estimated improvement:** 5-10% fewer allocations

**Tradeoffs:** Slightly more complex key management

---

### Phase 2: Concurrency Optimization (High Contention)

#### 2.1 Replace `HashMap` with `DashMap`

**Benefits:**
- Lock-free concurrent access
- Sharded internal locks (16-256 shards)
- No global lock contention
- Better scalability

**Implementation:**
```rust
// Add to Cargo.toml
[dependencies]
dashmap = "6.1"

// In wrapper:
use dashmap::DashMap;
use std::sync::Arc;

pub struct Lru<D> {
    inner: D,
    metadata: Arc<DashMap<Arc<str>, EntryMetadata>>,
}

impl<D> Lru<D> {
    fn record_access(&self, term: &str) {
        self.metadata
            .entry(Arc::from(term))
            .and_modify(|m| m.update_access())
            .or_insert_with(EntryMetadata::new);
    }
}
```

**Estimated improvement:** 3-10x faster for 4+ concurrent threads

**Tradeoffs:**
- Larger memory footprint (~200 bytes overhead)
- No global iteration without lock
- Different API for iteration

---

#### 2.2 Add `batch_record_access()` for bulk operations

**Benefits:**
- Amortizes lock overhead
- Better for fuzzy query results
- Reduces contention

**Implementation:**
```rust
pub fn batch_record_access(&self, terms: &[&str]) {
    let mut metadata = self.metadata.write();
    for &term in terms {
        metadata.entry(Arc::from(term))
            .and_modify(|m| m.update_access())
            .or_insert_with(EntryMetadata::new);
    }
}
```

**Estimated improvement:** 50-80% faster for batch updates

---

### Phase 3: Memory and Cache Efficiency

#### 3.1 Reduce Instant::now() calls

**Option A: Coarse-grained timestamps**
```rust
use std::sync::atomic::{AtomicU64, Ordering};

static CURRENT_TIMESTAMP: AtomicU64 = AtomicU64::new(0);

// Background thread updates every 100ms
fn timestamp_updater() {
    loop {
        let now = Instant::now().elapsed().as_millis() as u64;
        CURRENT_TIMESTAMP.store(now, Ordering::Relaxed);
        thread::sleep(Duration::from_millis(100));
    }
}

// In metadata:
struct EntryMetadata {
    last_accessed: u64, // milliseconds since epoch
}

fn update_access(&mut self) {
    self.last_accessed = CURRENT_TIMESTAMP.load(Ordering::Relaxed);
}
```

**Option B: Lazy timestamp updates**
```rust
// Only update timestamp if > 1 second old
fn update_access(&mut self) {
    let now = Instant::now();
    if now.duration_since(self.last_accessed) > Duration::from_secs(1) {
        self.last_accessed = now;
    }
}
```

**Estimated improvement:** 10-20% fewer system calls

**Tradeoffs:** Slightly less precise timestamps (usually acceptable for caching)

---

#### 3.2 Compact metadata representation

**Current size per entry:**
- `String` key: 24 bytes + heap allocation
- `Instant`: 16 bytes (two u64s)
- HashMap overhead: ~8 bytes
- **Total: ~48 bytes + heap**

**Optimized size:**
- `Arc<str>` key: 16 bytes (shared)
- `u64` timestamp: 8 bytes
- `u32` hit_count: 4 bytes (for LFU)
- `u32` size: 4 bytes (for memory pressure)
- **Total: ~32 bytes (33% reduction)**

**Implementation:**
```rust
#[repr(C)]
struct CompactMetadata {
    last_accessed_ms: u64,
    hit_count: u32,
    size_bytes: u32,
}
```

---

### Phase 4: Feature Flags for Optimization Levels

Add Cargo feature flags for different optimization profiles:

```toml
[features]
default = ["eviction-opt-balanced"]

# Optimization profiles
eviction-opt-none = []           # No optimizations, std lib only
eviction-opt-balanced = [        # Good balance (default)
    "eviction-parking-lot",
    "eviction-compact-metadata"
]
eviction-opt-concurrent = [      # Max concurrent performance
    "eviction-dashmap",
    "eviction-parking-lot",
    "eviction-compact-metadata",
    "eviction-coarse-timestamps"
]
eviction-opt-memory = [          # Min memory usage
    "eviction-compact-metadata"
]

# Individual optimizations
eviction-parking-lot = ["parking_lot"]
eviction-dashmap = ["dashmap"]
eviction-compact-metadata = []
eviction-coarse-timestamps = []
```

---

### Phase 5: Advanced Optimizations (Future)

#### 5.1 Lock-free metadata with atomics

For simple counters (LFU), use `AtomicU32`:

```rust
use std::sync::atomic::{AtomicU32, Ordering};

struct LfuMetadata {
    access_count: AtomicU32,
}

impl LfuMetadata {
    fn increment(&self) {
        self.access_count.fetch_add(1, Ordering::Relaxed);
    }
}
```

**Estimated improvement:** Near-zero contention for LFU

---

#### 5.2 SIMD-accelerated eviction scoring

For finding min/max scores across candidates:

```rust
#[cfg(target_arch = "x86_64")]
use std::arch::x86_64::*;

unsafe fn find_max_score_simd(scores: &[f64]) -> usize {
    // Use AVX2 for parallel max reduction
    // Process 4 f64s at a time
}
```

---

#### 5.3 Probabilistic eviction (skip updates randomly)

```rust
use rand::random;

fn maybe_record_access(&self, term: &str) {
    // Only record 50% of accesses
    if random::<u8>() < 128 {
        self.record_access(term);
    }
}
```

**Estimated improvement:** 50% fewer metadata updates

**Tradeoffs:** Less precise LRU/LFU tracking

---

## Implementation Roadmap

### Milestone 1: Baseline Benchmarks (Complete)
- ✅ Create benchmark suite
- ✅ Establish baseline performance metrics
- Document current overhead

### Milestone 2: parking_lot Migration (1-2 hours)
- Replace `std::sync::RwLock` with `parking_lot::RwLock`
- Run benchmarks
- Document improvements

### Milestone 3: Arc<str> Keys (2-3 hours)
- Migrate HashMap keys from `String` to `Arc<str>`
- Update all wrapper implementations
- Run benchmarks

### Milestone 4: DashMap Integration (3-4 hours)
- Add DashMap support behind feature flag
- Implement for LRU, LFU, Age wrappers
- Concurrent benchmarks

### Milestone 5: Compact Metadata (4-5 hours)
- Design unified metadata struct
- Migrate all wrappers
- Memory usage benchmarks

### Milestone 6: Feature Flags (2-3 hours)
- Set up feature flag system
- Document optimization profiles
- CI testing for each profile

---

## Expected Performance Improvements

| Optimization | Single-thread | Multi-thread (4) | Memory |
|--------------|---------------|------------------|---------|
| Baseline | 1.0x | 1.0x | 100% |
| + parking_lot | 1.2x | 2.5x | 95% |
| + Arc<str> | 1.3x | 2.5x | 85% |
| + DashMap | 1.3x | 8.0x | 90% |
| + Compact | 1.4x | 8.0x | 70% |
| **All** | **1.5x** | **10x** | **65%** |

---

## Compatibility Matrix

| Optimization | Breaking Change | MSRV Impact | Dependencies |
|--------------|-----------------|-------------|--------------|
| parking_lot | No | None | +1 (parking_lot) |
| Arc<str> | No (internal) | None | 0 |
| DashMap | No (behind flag) | None | +1 (dashmap) |
| Compact metadata | No (internal) | None | 0 |

---

## Testing Strategy

1. **Correctness tests** - All existing tests must pass
2. **Benchmark regression** - No > 5% regression in any scenario
3. **Concurrent stress tests** - 1000+ threads accessing same cache
4. **Memory leak tests** - Valgrind/Miri validation
5. **Feature flag combinations** - Test all valid combinations

---

## References

- [parking_lot documentation](https://docs.rs/parking_lot)
- [DashMap documentation](https://docs.rs/dashmap)
- [Arc::from str coercion](https://doc.rust-lang.org/std/sync/struct.Arc.html#impl-From%3C%26str%3E-for-Arc%3Cstr%3E)
- [Rust Performance Book - Lock Contention](https://nnethercote.github.io/perf-book/parallelism.html)
