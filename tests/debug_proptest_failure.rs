//! Debug test for proptest failure

use liblevenshtein::prelude::*;

#[test]
fn test_minimal_failing_case() {
    // Test step by step
    println!("=== Step 1: Create from ['kb', 'jb'] ===");
    let dict: DynamicDawg<()> = DynamicDawg::from_terms(vec!["kb", "jb"]);

    println!("After initial creation:");
    println!("  contains('kb'): {}", dict.contains("kb"));
    println!("  contains('jb'): {}", dict.contains("jb"));
    println!("  contains('k'): {}", dict.contains("k"));
    println!("  contains('j'): {}", dict.contains("j"));
    println!("  contains('b'): {}", dict.contains("b"));

    println!("\n=== Step 2: Insert 'j' ===");
    let inserted = dict.insert("j");
    println!("insert('j') returned: {}", inserted);

    println!("\nAfter inserting 'j':");
    println!("  contains('kb'): {}", dict.contains("kb"));
    println!("  contains('jb'): {}", dict.contains("jb"));
    println!("  contains('j'): {}", dict.contains("j"));
    println!(
        "  contains('k'): {} <-- SHOULD BE FALSE!",
        dict.contains("k")
    );
    println!("  contains('b'): {}", dict.contains("b"));

    // The bug: 'k' should NOT be in the dictionary!
    assert!(
        !dict.contains("k"),
        "Dictionary should not contain 'k' but contains() returned true!"
    );
}
