//! Cache eviction wrappers for liblevenshtein-rust.
//!
//! This module provides composable dictionary wrappers that add eviction-related
//! metadata tracking without requiring intrusive changes to dictionary implementations.
//!
//! # Overview
//!
//! The eviction wrappers use a decorator pattern to add caching behavior to any
//! dictionary implementation. Each wrapper maintains separate metadata (access times,
//! hit counts, sizes, etc.) in thread-safe storage.
//!
//! # Architecture
//!
//! ```text
//! ┌─────────────────────────────────────────────────────────────────┐
//! │                    Eviction Wrapper Pattern                      │
//! │  ┌──────────────────────────────────────────────────────────┐  │
//! │  │                  Wrapper<D> (e.g., Lru<D>)                │  │
//! │  │  ┌────────────┬──────────────────────────────────────┐   │  │
//! │  │  │   inner    │  Arc<RwLock<HashMap<String, Meta>>>  │   │  │
//! │  │  └────────────┴──────────────────────────────────────┘   │  │
//! │  └──────────────────────────────────────────────────────────┘  │
//! │                              │                                   │
//! │                              ▼                                   │
//! │  ┌──────────────────────────────────────────────────────────┐  │
//! │  │              Inner Dictionary (any D)                     │  │
//! │  │     (PathMapDictionary, DawgDictionary, etc.)             │  │
//! │  └──────────────────────────────────────────────────────────┘  │
//! └─────────────────────────────────────────────────────────────────┘
//! ```
//!
//! # Available Wrappers
//!
//! - **Noop**: Zero-cost passthrough (identity wrapper)
//! - **LazyInit**: Deferred dictionary initialization (3 variants)
//! - **TTL**: Time-to-live filtering (filters expired entries)
//! - **LRU**: Least Recently Used tracking
//! - **Age**: FIFO/age-based tracking
//! - **LFU**: Least Frequently Used tracking
//! - **CostAware**: Cost-to-value ratio balancing
//! - **MemoryPressure**: Memory pressure-aware eviction
//!
//! # Examples
//!
//! ## Basic LRU Wrapper
//!
//! ```rust
//! use liblevenshtein::prelude::*;
//! use liblevenshtein::cache::eviction::Lru;
//!
//! let dict = PathMapDictionary::from_terms_with_values([
//!     ("hello", 1),
//!     ("world", 2),
//! ]);
//!
//! let lru = Lru::new(dict);
//! assert_eq!(lru.get_value("hello"), Some(1));
//!
//! // Find least recently used
//! let lru_term = lru.find_lru(&["hello", "world"]);
//! ```
//!
//! ## Composing Wrappers
//!
//! ```rust
//! use liblevenshtein::prelude::*;
//! use liblevenshtein::cache::eviction::{Lru, Ttl};
//! use std::time::Duration;
//!
//! let dict = PathMapDictionary::from_terms_with_values([
//!     ("foo", 42),
//!     ("bar", 99),
//! ]);
//!
//! // Compose TTL + LRU
//! let ttl = Ttl::new(dict, Duration::from_secs(300));
//! let lru = Lru::new(ttl);
//!
//! assert_eq!(lru.get_value("foo"), Some(42));
//! ```
//!
//! ## Memory Pressure Tracking
//!
//! ```rust
//! use liblevenshtein::prelude::*;
//! use liblevenshtein::cache::eviction::MemoryPressure;
//!
//! let dict = PathMapDictionary::from_terms_with_values([
//!     ("large", vec![1, 2, 3, 4, 5]),
//!     ("small", vec![1]),
//! ]);
//!
//! let memory = MemoryPressure::new(dict);
//! memory.get_value("large");
//! memory.get_value("small");
//!
//! // Find highest pressure (large size / low hit rate)
//! let high_pressure = memory.find_highest_pressure(&["large", "small"]);
//! ```

pub mod eviction;
pub mod multimap;
