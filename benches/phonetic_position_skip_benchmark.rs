//! Benchmarks for phonetic rule application with/without position skipping optimization.
//!
//! **Scientific Experiment**: Evaluate whether position skipping improves performance.
//!
//! **Hypothesis**:
//! - H₀ (Null): Position skipping provides no measurable performance improvement.
//! - H₁ (Alternative): Position skipping reduces rule application time by skipping
//!   redundant position checks in the range [0, last_pos).
//!
//! **Formal Specification**: `docs/verification/phonetic/position_skipping_proof.v`
//!
//! The Coq proof establishes that position skipping is SAFE when no rules use
//! `Context::Final`. This benchmark measures the performance impact.

use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion, Throughput};
use liblevenshtein::phonetic::{
    apply_rules_seq, apply_rules_seq_opt, apply_rules_seq_optimized, orthography_rules,
    phonetic_rules, test_rules, zompist_rules, Context, Phone, RewriteRule,
};

// ============================================================================
// Test Data Generation
// ============================================================================

/// Generate a phonetic string with realistic patterns for benchmarking.
///
/// Creates strings that exercise the rule engine with various patterns:
/// - Digraph candidates (ch, sh, ph, gh, th, qu)
/// - Context-sensitive patterns (c before e/i, g before e/i)
/// - Word boundaries (for Final context testing)
fn generate_phonetic_string(len: usize) -> Vec<Phone> {
    // Pattern that exercises many rules: contains digraphs, context-sensitive letters
    let pattern = [
        // "church" pattern - exercises ch digraph
        Phone::Consonant(b'c'),
        Phone::Consonant(b'h'),
        Phone::Vowel(b'u'),
        Phone::Consonant(b'r'),
        Phone::Consonant(b'c'),
        Phone::Consonant(b'h'),
        // "phone" pattern - exercises ph digraph
        Phone::Consonant(b'p'),
        Phone::Consonant(b'h'),
        Phone::Vowel(b'o'),
        Phone::Consonant(b'n'),
        Phone::Vowel(b'e'),
        // "edge" pattern - exercises g before e
        Phone::Vowel(b'e'),
        Phone::Consonant(b'd'),
        Phone::Consonant(b'g'),
        Phone::Vowel(b'e'),
        // "think" pattern - exercises th
        Phone::Consonant(b't'),
        Phone::Consonant(b'h'),
        Phone::Vowel(b'i'),
        Phone::Consonant(b'n'),
        Phone::Consonant(b'k'),
        // "quick" pattern - exercises qu
        Phone::Consonant(b'q'),
        Phone::Consonant(b'u'),
        Phone::Vowel(b'i'),
        Phone::Consonant(b'c'),
        Phone::Consonant(b'k'),
        // "face" pattern - exercises c before e
        Phone::Consonant(b'f'),
        Phone::Vowel(b'a'),
        Phone::Consonant(b'c'),
        Phone::Vowel(b'e'),
        // "might" pattern - exercises gh
        Phone::Consonant(b'm'),
        Phone::Vowel(b'i'),
        Phone::Consonant(b'g'),
        Phone::Consonant(b'h'),
        Phone::Consonant(b't'),
    ];

    pattern.iter().cycle().take(len).cloned().collect()
}

/// Generate a simple repetitive pattern for worst-case analysis.
fn generate_simple_string(len: usize) -> Vec<Phone> {
    // Simple alternating consonant-vowel pattern
    let pattern = [Phone::Consonant(b't'), Phone::Vowel(b'e')];
    pattern.iter().cycle().take(len).cloned().collect()
}

/// Generate a string with many consecutive rule applications at same position.
///
/// This is the best case for position skipping: rules repeatedly apply
/// near the same position, so skipping [0, last_pos) saves iterations.
fn generate_localized_transformations(len: usize) -> Vec<Phone> {
    // Create a string where transformations cluster near the beginning
    let mut result = Vec::with_capacity(len);

    // Start with many transformable patterns at position 0
    result.extend_from_slice(&[
        Phone::Consonant(b'c'),
        Phone::Consonant(b'h'), // ch → digraph
        Phone::Consonant(b'c'),
        Phone::Consonant(b'h'), // ch → digraph
        Phone::Consonant(b'p'),
        Phone::Consonant(b'h'), // ph → f
    ]);

    // Fill rest with simple pattern
    while result.len() < len {
        result.push(Phone::Consonant(b't'));
        result.push(Phone::Vowel(b'a'));
    }

    result.truncate(len);
    result
}

// ============================================================================
// Rule Set Helpers
// ============================================================================

/// Check if a rule set contains any position-dependent contexts.
///
/// **Formal Specification**: `position_skipping_proof.v:1202-1211`
///
/// Only `Context::Final` is position-dependent because it matches when
/// `pos == s.len()`, which changes when strings are shortened.
fn has_final_context(rules: &[RewriteRule]) -> bool {
    rules.iter().any(|r| matches!(r.context, Context::Final))
}

/// Create a safe rule set (no Context::Final).
///
/// Uses phonetic rules only, which have no position-dependent contexts.
fn safe_rules() -> Vec<RewriteRule> {
    phonetic_rules()
}

/// Create an unsafe rule set (contains Context::Final).
///
/// Uses orthography rules, which include `rule_silent_e_final` with `Context::Final`.
fn unsafe_rules() -> Vec<RewriteRule> {
    orthography_rules()
}

// ============================================================================
// Baseline Benchmarks (Before Optimization)
// ============================================================================

/// Benchmark: Standard rule application baseline with varying string lengths.
fn bench_apply_rules_baseline(c: &mut Criterion) {
    let mut group = c.benchmark_group("phonetic_apply_rules_baseline");

    // Test with orthography rules (contains Context::Final - optimization unsafe)
    let ortho_rules = orthography_rules();
    assert!(
        has_final_context(&ortho_rules),
        "orthography_rules should contain Context::Final"
    );

    // Test with phonetic rules (no Context::Final - optimization safe)
    let phon_rules = phonetic_rules();
    assert!(
        !has_final_context(&phon_rules),
        "phonetic_rules should not contain Context::Final"
    );

    for len in [10, 25, 50, 100, 200, 500] {
        let input = generate_phonetic_string(len);
        let fuel = input.len() * 100;

        group.throughput(Throughput::Elements(len as u64));

        // Orthography rules (has Final context)
        group.bench_with_input(
            BenchmarkId::new("orthography", len),
            &(&ortho_rules, &input, fuel),
            |b, (rules, input, fuel)| {
                b.iter(|| apply_rules_seq(black_box(*rules), black_box(*input), black_box(*fuel)))
            },
        );

        // Phonetic rules (no Final context - candidate for optimization)
        group.bench_with_input(
            BenchmarkId::new("phonetic", len),
            &(&phon_rules, &input, fuel),
            |b, (rules, input, fuel)| {
                b.iter(|| apply_rules_seq(black_box(*rules), black_box(*input), black_box(*fuel)))
            },
        );
    }
    group.finish();
}

/// Benchmark: Rule application with different input patterns.
fn bench_apply_rules_patterns(c: &mut Criterion) {
    let mut group = c.benchmark_group("phonetic_apply_rules_patterns");

    let phon_rules = phonetic_rules();
    let len = 100;
    let fuel = len * 100;

    // Pattern 1: Realistic phonetic patterns (mixed transformations)
    let realistic_input = generate_phonetic_string(len);
    group.bench_with_input(
        BenchmarkId::new("realistic", len),
        &(&phon_rules, &realistic_input, fuel),
        |b, (rules, input, fuel)| {
            b.iter(|| apply_rules_seq(black_box(*rules), black_box(*input), black_box(*fuel)))
        },
    );

    // Pattern 2: Simple repetitive (few transformations)
    let simple_input = generate_simple_string(len);
    group.bench_with_input(
        BenchmarkId::new("simple", len),
        &(&phon_rules, &simple_input, fuel),
        |b, (rules, input, fuel)| {
            b.iter(|| apply_rules_seq(black_box(*rules), black_box(*input), black_box(*fuel)))
        },
    );

    // Pattern 3: Localized transformations (best case for position skipping)
    let localized_input = generate_localized_transformations(len);
    group.bench_with_input(
        BenchmarkId::new("localized", len),
        &(&phon_rules, &localized_input, fuel),
        |b, (rules, input, fuel)| {
            b.iter(|| apply_rules_seq(black_box(*rules), black_box(*input), black_box(*fuel)))
        },
    );

    group.finish();
}

/// Benchmark: Combined rule sets (orthography + phonetic).
fn bench_apply_rules_combined(c: &mut Criterion) {
    let mut group = c.benchmark_group("phonetic_apply_rules_combined");

    // Zompist rules = orthography + phonetic + test
    let zompist = zompist_rules();
    assert!(
        has_final_context(&zompist),
        "zompist_rules should contain Context::Final"
    );

    // Safe subset: only phonetic + test (no Final context)
    let mut safe_combined: Vec<RewriteRule> = phonetic_rules();
    safe_combined.extend(test_rules());
    assert!(
        !has_final_context(&safe_combined),
        "safe_combined should not contain Context::Final"
    );

    for len in [25, 50, 100, 200] {
        let input = generate_phonetic_string(len);
        let fuel = input.len() * 100;

        group.throughput(Throughput::Elements(len as u64));

        // Full zompist rules (contains Final - optimization unsafe)
        group.bench_with_input(
            BenchmarkId::new("zompist_full", len),
            &(&zompist, &input, fuel),
            |b, (rules, input, fuel)| {
                b.iter(|| apply_rules_seq(black_box(*rules), black_box(*input), black_box(*fuel)))
            },
        );

        // Safe combined (no Final - optimization safe)
        group.bench_with_input(
            BenchmarkId::new("safe_combined", len),
            &(&safe_combined, &input, fuel),
            |b, (rules, input, fuel)| {
                b.iter(|| apply_rules_seq(black_box(*rules), black_box(*input), black_box(*fuel)))
            },
        );
    }
    group.finish();
}

/// Benchmark: Effect of fuel limit on performance.
fn bench_apply_rules_fuel(c: &mut Criterion) {
    let mut group = c.benchmark_group("phonetic_apply_rules_fuel");

    let phon_rules = phonetic_rules();
    let input = generate_phonetic_string(100);

    for fuel_multiplier in [10, 50, 100, 200] {
        let fuel = input.len() * fuel_multiplier;

        group.bench_with_input(
            BenchmarkId::new("phonetic_fuel", fuel_multiplier),
            &(&phon_rules, &input, fuel),
            |b, (rules, input, fuel)| {
                b.iter(|| apply_rules_seq(black_box(*rules), black_box(*input), black_box(*fuel)))
            },
        );
    }
    group.finish();
}

/// Benchmark: Rule count scaling.
fn bench_apply_rules_rule_count(c: &mut Criterion) {
    let mut group = c.benchmark_group("phonetic_apply_rules_rule_count");

    let input = generate_phonetic_string(50);
    let fuel = input.len() * 100;

    // Test with varying numbers of rules
    let phon_rules = phonetic_rules(); // 3 rules
    let ortho_rules = orthography_rules(); // 8 rules
    let zompist = zompist_rules(); // 13 rules

    group.bench_with_input(
        BenchmarkId::new("3_rules_phonetic", 3),
        &(&phon_rules, &input, fuel),
        |b, (rules, input, fuel)| {
            b.iter(|| apply_rules_seq(black_box(*rules), black_box(*input), black_box(*fuel)))
        },
    );

    group.bench_with_input(
        BenchmarkId::new("8_rules_orthography", 8),
        &(&ortho_rules, &input, fuel),
        |b, (rules, input, fuel)| {
            b.iter(|| apply_rules_seq(black_box(*rules), black_box(*input), black_box(*fuel)))
        },
    );

    group.bench_with_input(
        BenchmarkId::new("13_rules_zompist", 13),
        &(&zompist, &input, fuel),
        |b, (rules, input, fuel)| {
            b.iter(|| apply_rules_seq(black_box(*rules), black_box(*input), black_box(*fuel)))
        },
    );

    group.finish();
}

// ============================================================================
// Position Skipping Optimization Comparison (Post-Implementation)
// ============================================================================

/// Benchmark: Direct comparison of standard vs optimized rule application.
///
/// **Scientific Experiment**: Tests H₁ (position skipping improves performance).
///
/// Compares:
/// - `apply_rules_seq` - Standard implementation (always scans from position 0)
/// - `apply_rules_seq_optimized` - Optimized implementation (position skipping)
/// - `apply_rules_seq_opt` - Auto-detecting wrapper
///
/// Uses phonetic rules (no Context::Final) where optimization is safe.
fn bench_position_skipping_comparison(c: &mut Criterion) {
    let mut group = c.benchmark_group("phonetic_position_skipping_comparison");

    // Use phonetic rules (no Final context - optimization is safe)
    let phon_rules = phonetic_rules();
    assert!(
        !has_final_context(&phon_rules),
        "phonetic_rules should not contain Context::Final for optimization safety"
    );

    for len in [10, 25, 50, 100, 200, 500] {
        let input = generate_phonetic_string(len);
        let fuel = input.len() * 100;

        group.throughput(Throughput::Elements(len as u64));

        // Standard implementation (baseline)
        group.bench_with_input(
            BenchmarkId::new("standard", len),
            &(&phon_rules, &input, fuel),
            |b, (rules, input, fuel)| {
                b.iter(|| apply_rules_seq(black_box(*rules), black_box(*input), black_box(*fuel)))
            },
        );

        // Optimized implementation (position skipping)
        group.bench_with_input(
            BenchmarkId::new("optimized", len),
            &(&phon_rules, &input, fuel),
            |b, (rules, input, fuel)| {
                b.iter(|| {
                    apply_rules_seq_optimized(black_box(*rules), black_box(*input), black_box(*fuel))
                })
            },
        );

        // Auto-detecting wrapper
        group.bench_with_input(
            BenchmarkId::new("auto_opt", len),
            &(&phon_rules, &input, fuel),
            |b, (rules, input, fuel)| {
                b.iter(|| {
                    apply_rules_seq_opt(black_box(*rules), black_box(*input), black_box(*fuel))
                })
            },
        );
    }
    group.finish();
}

/// Benchmark: Position skipping with localized transformations (best case).
///
/// When transformations cluster near the same position, position skipping
/// should show maximum benefit by avoiding redundant scans of [0, last_pos).
fn bench_position_skipping_localized(c: &mut Criterion) {
    let mut group = c.benchmark_group("phonetic_position_skipping_localized");

    let phon_rules = phonetic_rules();

    for len in [25, 50, 100, 200] {
        // Localized input: transformations cluster at the beginning
        let input = generate_localized_transformations(len);
        let fuel = input.len() * 100;

        group.throughput(Throughput::Elements(len as u64));

        // Standard implementation
        group.bench_with_input(
            BenchmarkId::new("standard", len),
            &(&phon_rules, &input, fuel),
            |b, (rules, input, fuel)| {
                b.iter(|| apply_rules_seq(black_box(*rules), black_box(*input), black_box(*fuel)))
            },
        );

        // Optimized implementation
        group.bench_with_input(
            BenchmarkId::new("optimized", len),
            &(&phon_rules, &input, fuel),
            |b, (rules, input, fuel)| {
                b.iter(|| {
                    apply_rules_seq_optimized(black_box(*rules), black_box(*input), black_box(*fuel))
                })
            },
        );
    }
    group.finish();
}

/// Benchmark: Position skipping with simple (low transformation) input.
///
/// Simple inputs with few transformations should show minimal difference,
/// as position skipping has less opportunity to skip redundant scans.
fn bench_position_skipping_simple(c: &mut Criterion) {
    let mut group = c.benchmark_group("phonetic_position_skipping_simple");

    let phon_rules = phonetic_rules();

    for len in [25, 50, 100, 200] {
        // Simple input: few transformations
        let input = generate_simple_string(len);
        let fuel = input.len() * 100;

        group.throughput(Throughput::Elements(len as u64));

        // Standard implementation
        group.bench_with_input(
            BenchmarkId::new("standard", len),
            &(&phon_rules, &input, fuel),
            |b, (rules, input, fuel)| {
                b.iter(|| apply_rules_seq(black_box(*rules), black_box(*input), black_box(*fuel)))
            },
        );

        // Optimized implementation
        group.bench_with_input(
            BenchmarkId::new("optimized", len),
            &(&phon_rules, &input, fuel),
            |b, (rules, input, fuel)| {
                b.iter(|| {
                    apply_rules_seq_optimized(black_box(*rules), black_box(*input), black_box(*fuel))
                })
            },
        );
    }
    group.finish();
}

// ============================================================================
// Criterion Configuration
// ============================================================================

criterion_group!(
    benches,
    bench_apply_rules_baseline,
    bench_apply_rules_patterns,
    bench_apply_rules_combined,
    bench_apply_rules_fuel,
    bench_apply_rules_rule_count,
    bench_position_skipping_comparison,
    bench_position_skipping_localized,
    bench_position_skipping_simple,
);
criterion_main!(benches);
