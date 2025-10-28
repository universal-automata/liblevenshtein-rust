//! Comprehensive example demonstrating substring search with suffix automata.
//!
//! This example shows how to use suffix automata for approximate substring matching,
//! which is useful for:
//! - Code search with typos
//! - Document search
//! - Finding misspelled words in text
//! - Fuzzy text matching

use liblevenshtein::dictionary::suffix_automaton::SuffixAutomaton;
use liblevenshtein::transducer::{Algorithm, Transducer};

fn main() {
    println!("╔═══════════════════════════════════════════════════════════════╗");
    println!("║         Substring Search with Suffix Automata Demo           ║");
    println!("╚═══════════════════════════════════════════════════════════════╝\n");

    // Example 1: Code Search
    code_search_example();

    // Example 2: Document Search
    document_search_example();

    // Example 3: Multi-Document Search
    multi_document_search_example();

    // Example 4: Ordered Results
    ordered_results_example();
}

fn code_search_example() {
    println!("┌─────────────────────────────────────────────────────────────┐");
    println!("│ Example 1: Code Search with Typos                          │");
    println!("└─────────────────────────────────────────────────────────────┘\n");

    let code = r#"
fn calculate_total(items: &[Item]) -> f64 {
    items.iter()
        .map(|item| item.price * item.quantity)
        .sum()
}

async fn fetch_user_data(user_id: u64) -> Result<User, Error> {
    let response = http_client.get(&format!("/users/{}", user_id)).await?;
    response.json().await
}
"#;

    // Build suffix automaton from code
    let dict = SuffixAutomaton::from_text(code);
    let transducer = Transducer::new(dict, Algorithm::Standard);

    println!("Indexed code snippet ({} characters)\n", code.len());

    // Search 1: Exact match
    println!("Search: \"calculate\" (exact match, distance=0)");
    let results: Vec<_> = transducer.query("calculate", 0).take(5).collect();
    print_results(&results);

    // Search 2: With typo
    println!("\nSearch: \"calculte\" (1 typo, distance=1)");
    let results: Vec<_> = transducer.query("calculte", 1).take(5).collect();
    print_results(&results);

    // Search 3: Function name with typos
    println!("\nSearch: \"fetch_usr\" (typo in 'user', distance=1)");
    let results: Vec<_> = transducer.query("fetch_usr", 1).take(5).collect();
    print_results(&results);

    // Search 4: Multi-word phrase
    println!("\nSearch: \"async fn fetch\" (exact match)");
    let results: Vec<_> = transducer.query("async fn fetch", 0).take(5).collect();
    print_results(&results);

    println!();
}

fn document_search_example() {
    println!("┌─────────────────────────────────────────────────────────────┐");
    println!("│ Example 2: Document Search with Misspellings               │");
    println!("└─────────────────────────────────────────────────────────────┘\n");

    let document = "The Levenshtein distance is a string metric for measuring the \
                    difference between two sequences. It is named after Vladimir \
                    Levenshtein, who considered this distance in 1965. The metric \
                    is also known as edit distance.";

    let dict = SuffixAutomaton::from_text(document);
    let transducer = Transducer::new(dict, Algorithm::Standard);

    println!("Indexed document ({} characters)\n", document.len());

    // Search with misspellings
    println!("Search: \"Levenstein\" (misspelled, distance=1)");
    let results: Vec<_> = transducer.query("Levenstein", 1).take(5).collect();
    print_results(&results);

    println!("\nSearch: \"metrik\" (misspelled 'metric', distance=1)");
    let results: Vec<_> = transducer.query("metrik", 1).take(5).collect();
    print_results(&results);

    println!("\nSearch: \"edt distance\" (typo in 'edit', distance=1)");
    let results: Vec<_> = transducer.query("edt distance", 1).take(5).collect();
    print_results(&results);

    println!();
}

fn multi_document_search_example() {
    println!("┌─────────────────────────────────────────────────────────────┐");
    println!("│ Example 3: Multi-Document Search                           │");
    println!("└─────────────────────────────────────────────────────────────┘\n");

    let documents = vec![
        "Rust is a systems programming language focused on safety and performance.",
        "The Python programming language emphasizes code readability.",
        "JavaScript is widely used for web development and Node.js servers.",
    ];

    // Index all documents
    let dict = SuffixAutomaton::from_texts(documents.clone());
    let transducer = Transducer::new(dict.clone(), Algorithm::Standard);

    println!("Indexed {} documents\n", documents.len());

    // Search across all documents
    println!("Search: \"programming\" (exact match)");
    let results: Vec<_> = transducer.query("programming", 0).take(10).collect();
    print_results(&results);

    println!("\nSearch: \"program\" (substring, distance=0)");
    let results: Vec<_> = transducer.query("program", 0).take(10).collect();
    print_results(&results);

    println!("\nSearch: \"developmnt\" (typo, distance=1)");
    let results: Vec<_> = transducer.query("developmnt", 1).take(10).collect();
    print_results(&results);

    // Show which documents were indexed
    println!("\nOriginal documents:");
    for text in dict.source_texts() {
        println!("  - {}", text);
    }

    println!();
}

fn ordered_results_example() {
    println!("┌─────────────────────────────────────────────────────────────┐");
    println!("│ Example 4: Ordered Results (by distance, then alphabetical)│");
    println!("└─────────────────────────────────────────────────────────────┘\n");

    let text = "The quick brown fox jumps over the lazy dog. The five boxing \
                wizards jump quickly. Pack my box with five dozen liquor jugs.";

    let dict = SuffixAutomaton::from_text(text);
    let transducer = Transducer::new(dict, Algorithm::Standard);

    println!("Indexed text ({} characters)\n", text.len());

    // Use ordered query for top-k results
    println!("Search: \"qick\" (typo in 'quick', distance=2, top 10 results)");
    println!("Results ordered by: 1) edit distance, 2) alphabetical\n");

    for (i, candidate) in transducer
        .query_ordered("qick", 2)
        .take(10)
        .enumerate()
    {
        println!(
            "  {}. {} (distance={})",
            i + 1,
            candidate.term,
            candidate.distance
        );
    }

    println!("\nSearch: \"box\" (exact match, show all variations)");
    for (i, candidate) in transducer
        .query_ordered("box", 0)
        .take(10)
        .enumerate()
    {
        println!("  {}. {}", i + 1, candidate.term);
    }

    println!();
}

fn print_results(results: &[String]) {
    if results.is_empty() {
        println!("  No matches found");
    } else {
        println!("  Found {} match(es):", results.len());
        for (i, term) in results.iter().enumerate() {
            // Truncate long results for display
            let display = if term.len() > 50 {
                format!("{}...", &term[..47])
            } else {
                term.clone()
            };
            println!("    {}. \"{}\"", i + 1, display);
        }
    }
}
