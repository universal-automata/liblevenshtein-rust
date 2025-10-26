//! Advanced contextual filtering using bitmap-based node masking
//!
//! Instead of rebuilding sub-tries, we use a bitmap to mark which
//! dictionary entries are "active" for the current context. This allows
//! instant context switching with zero overhead.

use liblevenshtein::prelude::*;
use std::collections::HashMap;
use std::time::Instant;

/// Context-aware dictionary wrapper with bitmap masking
pub struct ContextualDictionary<D: Dictionary> {
    /// The full dictionary
    dict: D,
    /// Mapping from term to index
    term_to_index: HashMap<String, usize>,
    /// All terms in order
    all_terms: Vec<String>,
    /// Current active set (bitmap)
    active_mask: Vec<bool>,
}

impl<D: Dictionary> ContextualDictionary<D> {
    pub fn new(dict: D, terms: Vec<String>) -> Self {
        let term_to_index: HashMap<String, usize> = terms
            .iter()
            .enumerate()
            .map(|(i, t)| (t.clone(), i))
            .collect();

        let active_mask = vec![true; terms.len()];

        Self {
            dict,
            term_to_index,
            all_terms: terms,
            active_mask,
        }
    }

    /// Set active context by providing a predicate
    pub fn set_context<F>(&mut self, predicate: F)
    where
        F: Fn(&str) -> bool,
    {
        for (i, term) in self.all_terms.iter().enumerate() {
            self.active_mask[i] = predicate(term);
        }
    }

    /// Get dictionary reference for querying
    pub fn dict(&self) -> &D {
        &self.dict
    }

    /// Check if a term is active in current context
    pub fn is_active(&self, term: &str) -> bool {
        self.term_to_index
            .get(term)
            .map(|&idx| self.active_mask[idx])
            .unwrap_or(false)
    }

    /// Get count of active terms
    pub fn active_count(&self) -> usize {
        self.active_mask.iter().filter(|&&active| active).count()
    }

    /// Reset to all active
    pub fn reset(&mut self) {
        self.active_mask.fill(true);
    }
}

#[derive(Debug, Clone)]
struct CodeSymbol {
    name: String,
    scope: String,
    visibility: String,
    kind: String,
}

fn main() {
    println!("=== Advanced Contextual Filtering with Bitmap Masking ===\n");

    // Create a realistic code symbol database
    let mut symbols = vec![];

    // Simulate different scopes and contexts
    let scopes = vec!["global", "ClassA", "ClassB", "FunctionX"];
    let visibilities = vec!["public", "private", "protected"];
    let kinds = vec!["variable", "function", "class", "constant"];

    for scope in &scopes {
        for vis in &visibilities {
            for kind in &kinds {
                for i in 0..50 {
                    symbols.push(CodeSymbol {
                        name: format!("{}_{}_{}_{}", scope, kind, vis, i),
                        scope: scope.to_string(),
                        visibility: vis.to_string(),
                        kind: kind.to_string(),
                    });
                }
            }
        }
    }

    // Add some specific symbols
    symbols.extend(vec![
        CodeSymbol {
            name: "getValue".to_string(),
            scope: "global".to_string(),
            visibility: "public".to_string(),
            kind: "function".to_string(),
        },
        CodeSymbol {
            name: "getVariable".to_string(),
            scope: "ClassA".to_string(),
            visibility: "public".to_string(),
            kind: "function".to_string(),
        },
        CodeSymbol {
            name: "getResult".to_string(),
            scope: "ClassA".to_string(),
            visibility: "private".to_string(),
            kind: "function".to_string(),
        },
    ]);

    println!("Total symbols: {}\n", symbols.len());

    // Build dictionary
    let all_names: Vec<String> = symbols.iter().map(|s| s.name.clone()).collect();
    let dict = PathMapDictionary::from_iter(all_names.iter().map(|s| s.as_str()));

    // Create contextual dictionary wrapper
    let mut ctx_dict = ContextualDictionary::new(dict, all_names.clone());

    println!("--- Scenario 1: Global Scope Context ---");
    let start = Instant::now();

    // Set context to global scope only
    ctx_dict.set_context(|term| {
        symbols
            .iter()
            .any(|s| s.name == term && s.scope == "global")
    });
    let context_switch_time = start.elapsed();

    println!("Context switch time: {:?}", context_switch_time);
    println!(
        "Active symbols: {} ({}% of total)\n",
        ctx_dict.active_count(),
        ctx_dict.active_count() * 100 / symbols.len()
    );

    // Query with context filtering
    print!("Searching for 'getv' in global scope: ");
    let results: Vec<_> = Transducer::new(ctx_dict.dict().clone(), Algorithm::Standard)
        .query_ordered("getv", 1)
        .prefix()
        .filter(|c| ctx_dict.is_active(&c.term))
        .take(3)
        .collect();

    for r in &results {
        print!("{}, ", r.term);
    }
    println!("\n");

    println!("--- Scenario 2: ClassA Scope Context ---");
    let start = Instant::now();

    // Switch context to ClassA scope
    ctx_dict.set_context(|term| {
        symbols
            .iter()
            .any(|s| s.name == term && s.scope == "ClassA")
    });
    let context_switch_time = start.elapsed();

    println!("Context switch time: {:?}", context_switch_time);
    println!(
        "Active symbols: {} ({}% of total)\n",
        ctx_dict.active_count(),
        ctx_dict.active_count() * 100 / symbols.len()
    );

    print!("Searching for 'getv' in ClassA scope: ");
    let results: Vec<_> = Transducer::new(ctx_dict.dict().clone(), Algorithm::Standard)
        .query_ordered("getv", 1)
        .prefix()
        .filter(|c| ctx_dict.is_active(&c.term))
        .take(3)
        .collect();

    for r in &results {
        print!("{}, ", r.term);
    }
    println!("\n");

    println!("--- Scenario 3: Public Symbols Only ---");
    let start = Instant::now();

    // Switch context to public symbols
    ctx_dict.set_context(|term| {
        symbols
            .iter()
            .any(|s| s.name == term && s.visibility == "public")
    });
    let context_switch_time = start.elapsed();

    println!("Context switch time: {:?}", context_switch_time);
    println!(
        "Active symbols: {} ({}% of total)\n",
        ctx_dict.active_count(),
        ctx_dict.active_count() * 100 / symbols.len()
    );

    print!("Searching for 'getv' (public only): ");
    let results: Vec<_> = Transducer::new(ctx_dict.dict().clone(), Algorithm::Standard)
        .query_ordered("getv", 1)
        .prefix()
        .filter(|c| ctx_dict.is_active(&c.term))
        .take(3)
        .collect();

    for r in &results {
        print!("{}, ", r.term);
    }
    println!("\n");

    println!("--- Scenario 4: Composite Context (ClassA + Public + Function) ---");
    let start = Instant::now();

    // Complex multi-criteria context
    ctx_dict.set_context(|term| {
        symbols.iter().any(|s| {
            s.name == term
                && s.scope == "ClassA"
                && s.visibility == "public"
                && s.kind == "function"
        })
    });
    let context_switch_time = start.elapsed();

    println!("Context switch time: {:?}", context_switch_time);
    println!(
        "Active symbols: {} ({}% of total)\n",
        ctx_dict.active_count(),
        ctx_dict.active_count() * 100 / symbols.len()
    );

    print!("Searching for 'get' (ClassA public functions): ");
    let results: Vec<_> = Transducer::new(ctx_dict.dict().clone(), Algorithm::Standard)
        .query_ordered("get", 0)
        .prefix()
        .filter(|c| ctx_dict.is_active(&c.term))
        .take(5)
        .collect();

    for r in &results {
        print!("{}, ", r.term);
    }
    println!("\n");

    println!("\n=== Performance Analysis ===\n");

    // Benchmark: Post-filtering vs Bitmap masking
    println!("Comparing approaches for 1000 queries:\n");

    // Approach 1: Post-filtering without any optimization
    ctx_dict.reset();
    let start = Instant::now();
    for _ in 0..1000 {
        let _: Vec<_> = Transducer::new(ctx_dict.dict().clone(), Algorithm::Standard)
            .query_ordered("get", 1)
            .prefix()
            .filter(|c| {
                // Simulate complex filter logic
                symbols
                    .iter()
                    .any(|s| s.name == c.term && s.scope == "ClassA" && s.visibility == "public")
            })
            .take(5)
            .collect();
    }
    let post_filter_time = start.elapsed();
    println!("Post-filtering (no optimization): {:?}", post_filter_time);

    // Approach 2: Bitmap masking (set once, query many times)
    let start = Instant::now();
    ctx_dict.set_context(|term| {
        symbols
            .iter()
            .any(|s| s.name == term && s.scope == "ClassA" && s.visibility == "public")
    });
    let context_setup = start.elapsed();

    let start = Instant::now();
    for _ in 0..1000 {
        let _: Vec<_> = Transducer::new(ctx_dict.dict().clone(), Algorithm::Standard)
            .query_ordered("get", 1)
            .prefix()
            .filter(|c| ctx_dict.is_active(&c.term)) // O(1) bitmap lookup
            .take(5)
            .collect();
    }
    let bitmap_query_time = start.elapsed();
    let bitmap_total = context_setup + bitmap_query_time;

    println!("Bitmap masking:");
    println!("  Context setup: {:?}", context_setup);
    println!("  1000 queries: {:?}", bitmap_query_time);
    println!("  Total: {:?}", bitmap_total);

    if post_filter_time > bitmap_total {
        let speedup = post_filter_time.as_nanos() as f64 / bitmap_total.as_nanos() as f64;
        println!("\n🚀 Speedup: {:.2}x faster with bitmap masking!", speedup);
    }

    println!("\n=== Recommendations ===\n");
    println!("Use bitmap masking when:");
    println!("  ✅ Context changes less frequently than queries");
    println!("  ✅ Multiple queries within same context");
    println!("  ✅ Filter logic is complex or expensive");
    println!();
    println!("Use sub-trie construction when:");
    println!("  ✅ Context is very restrictive (>90% filtered out)");
    println!("  ✅ Many queries within same context");
    println!("  ✅ Memory is not a constraint");
    println!();
    println!("Use post-filtering when:");
    println!("  ✅ Context changes every query");
    println!("  ✅ Dictionary is small (<1000 terms)");
    println!("  ✅ Filter is very simple (one condition)");
}
