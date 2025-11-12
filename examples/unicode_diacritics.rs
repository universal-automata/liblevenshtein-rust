//! Unicode Diacritics Example
//!
//! Demonstrates SubstitutionSetChar for Unicode character substitutions.
//! Shows how to use preset builders for common international text patterns.
//!
//! Run this example with:
//! ```bash
//! cargo run --example unicode_diacritics
//! ```

use liblevenshtein::transducer::SubstitutionSetChar;

fn main() {
    println!("=== Unicode Substitutions with SubstitutionSetChar ===\n");

    // Example 1: Latin diacritics
    println!("--- Example 1: Latin Diacritics ---\n");

    let diacritics = SubstitutionSetChar::diacritics_latin();
    println!("Created diacritics_latin() preset with {} pairs\n", diacritics.len());

    println!("Diacritic equivalences included:");
    println!("  - é, è, ê, ë ↔ e");
    println!("  - á, à, â, ä, ã, å ↔ a");
    println!("  - ñ ↔ n");
    println!("  - ç ↔ c");
    println!("  - ü, ù, û, ú ↔ u");
    println!("  - (and many more...)\n");

    // Test some equivalences
    let latin_tests = vec![
        ('é', 'e', true),
        ('e', 'é', true),
        ('ñ', 'n', true),
        ('ü', 'u', true),
        ('ç', 'c', true),
        ('x', 'y', false), // Not in set
    ];

    println!("Testing substitution equivalences:\n");
    for (a, b, should_match) in latin_tests {
        let matches = diacritics.contains(a, b);
        let status = if matches == should_match { "✓" } else { "✗" };
        println!("  {} {} ↔ {} : {}", status, a, b, if matches { "allowed" } else { "not allowed" });
    }

    // Example 2: Greek case-insensitive
    println!("\n--- Example 2: Greek Case-Insensitive ---\n");

    let greek = SubstitutionSetChar::greek_case_insensitive();
    println!("Created greek_case_insensitive() preset with {} pairs\n", greek.len());

    println!("Greek case equivalences:");
    println!("  - Α ↔ α (Alpha)");
    println!("  - Β ↔ β (Beta)");
    println!("  - Γ ↔ γ (Gamma)");
    println!("  - Δ ↔ δ (Delta)");
    println!("  - (... all 24 letters)\n");

    let greek_tests = vec![
        ('Α', 'α', true),  // Alpha
        ('α', 'Α', true),  // Alpha (reverse)
        ('Ω', 'ω', true),  // Omega
        ('Σ', 'σ', true),  // Sigma
        ('Σ', 'ς', true),  // Sigma final form
        ('Α', 'Β', false), // Different letters
    ];

    println!("Testing Greek case equivalences:\n");
    for (a, b, should_match) in greek_tests {
        let matches = greek.contains(a, b);
        let status = if matches == should_match { "✓" } else { "✗" };
        println!("  {} {} ↔ {} : {}", status, a, b, if matches { "allowed" } else { "not allowed" });
    }

    // Example 3: Cyrillic case-insensitive
    println!("\n--- Example 3: Cyrillic Case-Insensitive ---\n");

    let cyrillic = SubstitutionSetChar::cyrillic_case_insensitive();
    println!("Created cyrillic_case_insensitive() preset with {} pairs\n", cyrillic.len());

    println!("Cyrillic case equivalences:");
    println!("  - А ↔ а");
    println!("  - Б ↔ б");
    println!("  - В ↔ в");
    println!("  - (... all 33 Russian letters)\n");

    let cyrillic_tests = vec![
        ('А', 'а', true),  // A
        ('а', 'А', true),  // A (reverse)
        ('Я', 'я', true),  // Ya
        ('Ж', 'ж', true),  // Zhe
        ('А', 'Б', false), // Different letters
    ];

    println!("Testing Cyrillic case equivalences:\n");
    for (a, b, should_match) in cyrillic_tests {
        let matches = cyrillic.contains(a, b);
        let status = if matches == should_match { "✓" } else { "✗" };
        println!("  {} {} ↔ {} : {}", status, a, b, if matches { "allowed" } else { "not allowed" });
    }

    // Example 4: Japanese Hiragana/Katakana
    println!("\n--- Example 4: Japanese Hiragana ↔ Katakana ---\n");

    let japanese = SubstitutionSetChar::japanese_hiragana_katakana();
    println!("Created japanese_hiragana_katakana() preset with {} pairs\n", japanese.len());

    println!("Hiragana/Katakana equivalences (sample):");
    println!("  - あ ↔ ア (a)");
    println!("  - か ↔ カ (ka)");
    println!("  - さ ↔ サ (sa)");
    println!("  - (... and more)\n");

    let japanese_tests = vec![
        ('あ', 'ア', true), // a
        ('ア', 'あ', true), // a (reverse)
        ('か', 'カ', true), // ka
        ('さ', 'サ', true), // sa
        ('あ', 'か', false), // Different syllables
    ];

    println!("Testing Hiragana↔Katakana equivalences:\n");
    for (a, b, should_match) in japanese_tests {
        let matches = japanese.contains(a, b);
        let status = if matches == should_match { "✓" } else { "✗" };
        println!("  {} {} ↔ {} : {}", status, a, b, if matches { "allowed" } else { "not allowed" });
    }

    // Example 5: Custom Unicode set
    println!("\n--- Example 5: Custom Unicode Substitutions ---\n");

    let mut custom = SubstitutionSetChar::new();

    // Add custom equivalences
    custom.allow('α', 'a'); // Greek alpha to Latin 'a'
    custom.allow('a', 'α');

    custom.allow('β', 'b'); // Greek beta to Latin 'b'
    custom.allow('b', 'β');

    custom.allow('π', 'p'); // Greek pi to Latin 'p'
    custom.allow('p', 'π');

    println!("Created custom substitution set:");
    println!("  - α ↔ a (Greek alpha to Latin a)");
    println!("  - β ↔ b (Greek beta to Latin b)");
    println!("  - π ↔ p (Greek pi to Latin p)\n");

    assert!(custom.contains('α', 'a'));
    assert!(custom.contains('β', 'b'));
    assert!(custom.contains('π', 'p'));
    println!("✓ Custom substitutions verified!\n");

    // Summary
    println!("=== Summary ===\n");
    println!("✓ SubstitutionSetChar supports full Unicode range");
    println!("✓ Preset builders for common patterns:");
    println!("  - diacritics_latin() - Accented ↔ unaccented");
    println!("  - greek_case_insensitive() - Α ↔ α");
    println!("  - cyrillic_case_insensitive() - А ↔ а");
    println!("  - japanese_hiragana_katakana() - あ ↔ ア");
    println!("✓ Custom sets for domain-specific needs");
    println!("\n📌 Use SubstitutionSetChar for international text matching!");
}
