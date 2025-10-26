//! Code completion demonstration using filtering and prefix matching
//!
//! This example shows how to build a powerful code completion system using:
//! - Prefix matching for autocomplete (dictionary terms can be longer than query)
//! - Filtering for context-aware suggestions (by type, scope, visibility)
//! - Typo tolerance with low edit distances (1-2)

use liblevenshtein::prelude::*;

/// Represents different types of code identifiers
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum IdentifierType {
    Variable,
    Function,
    Class,
    Constant,
}

/// A code identifier with metadata
#[derive(Debug, Clone)]
struct Identifier {
    name: String,
    id_type: IdentifierType,
    is_public: bool,
}

impl Identifier {
    fn new(name: &str, id_type: IdentifierType, is_public: bool) -> Self {
        Self {
            name: name.to_string(),
            id_type,
            is_public,
        }
    }
}

fn main() {
    // Simulate a codebase with various identifiers
    let identifiers = vec![
        // Variables
        Identifier::new("getValue", IdentifierType::Variable, false),
        Identifier::new("getVariable", IdentifierType::Variable, false),
        Identifier::new("getResult", IdentifierType::Variable, false),
        Identifier::new("userId", IdentifierType::Variable, false),
        Identifier::new("userName", IdentifierType::Variable, false),
        Identifier::new("userEmail", IdentifierType::Variable, false),
        // Functions
        Identifier::new("getUserById", IdentifierType::Function, true),
        Identifier::new("getUserName", IdentifierType::Function, true),
        Identifier::new("getValueFromCache", IdentifierType::Function, false),
        Identifier::new("getValue", IdentifierType::Function, true),
        Identifier::new("setValue", IdentifierType::Function, true),
        Identifier::new("calculate", IdentifierType::Function, true),
        Identifier::new("validateInput", IdentifierType::Function, true),
        // Classes
        Identifier::new("User", IdentifierType::Class, true),
        Identifier::new("UserService", IdentifierType::Class, true),
        Identifier::new("ValueObject", IdentifierType::Class, true),
        Identifier::new("Calculator", IdentifierType::Class, true),
        // Constants
        Identifier::new("MAX_VALUE", IdentifierType::Constant, true),
        Identifier::new("MIN_VALUE", IdentifierType::Constant, true),
        Identifier::new("DEFAULT_USER", IdentifierType::Constant, true),
    ];

    // Build dictionary from identifier names
    let names: Vec<&str> = identifiers.iter().map(|id| id.name.as_str()).collect();
    let dict = PathMapDictionary::from_iter(names);

    println!("=== Code Completion Demo ===\n");
    println!("Dictionary contains {} identifiers\n", identifiers.len());

    // Scenario 1: Basic prefix matching (autocomplete)
    println!("--- Scenario 1: Autocomplete for 'getVal' ---");
    println!("User types: 'getVal'");
    println!("Suggestions (distance 0, prefix match):\n");

    for candidate in Transducer::new(dict.clone(), Algorithm::Standard)
        .query_ordered("getVal", 0)
        .prefix()
        .take(5)
    {
        println!("  {} (distance: {})", candidate.term, candidate.distance);
    }

    // Scenario 2: Prefix matching with typo tolerance
    println!("\n--- Scenario 2: Autocomplete with typo tolerance ---");
    println!("User types: 'getUserNme' (typo: missing 'a')");
    println!("Suggestions (distance 1, prefix match):\n");

    for candidate in Transducer::new(dict.clone(), Algorithm::Standard)
        .query_ordered("getUserNme", 1)
        .prefix()
        .take(5)
    {
        println!("  {} (distance: {})", candidate.term, candidate.distance);
    }

    // Scenario 3: Filter by identifier type (functions only)
    println!("\n--- Scenario 3: Filter to show only functions ---");
    println!("User types: 'getVal', wants only functions");
    println!("Filtered suggestions:\n");

    for candidate in Transducer::new(dict.clone(), Algorithm::Standard)
        .query_ordered("getVal", 1)
        .prefix()
        .filter(|c| {
            // Check if this identifier is a function
            identifiers
                .iter()
                .any(|id| id.name == c.term && id.id_type == IdentifierType::Function)
        })
        .take(5)
    {
        let id = identifiers
            .iter()
            .find(|id| id.name == candidate.term)
            .unwrap();
        println!(
            "  {} (distance: {}, type: {:?})",
            candidate.term, candidate.distance, id.id_type
        );
    }

    // Scenario 4: Filter by visibility (public only)
    println!("\n--- Scenario 4: Filter to show only public identifiers ---");
    println!("User types: 'user', wants only public APIs");
    println!("Filtered suggestions:\n");

    for candidate in Transducer::new(dict.clone(), Algorithm::Standard)
        .query_ordered("user", 0)
        .prefix()
        .filter(|c| {
            // Check if this identifier is public
            identifiers
                .iter()
                .any(|id| id.name == c.term && id.is_public)
        })
        .take(5)
    {
        let id = identifiers
            .iter()
            .find(|id| id.name == candidate.term)
            .unwrap();
        println!(
            "  {} (type: {:?}, public: {})",
            candidate.term, id.id_type, id.is_public
        );
    }

    // Scenario 5: Complex filtering - camelCase prefix matching
    println!("\n--- Scenario 5: Filter by naming convention (camelCase) ---");
    println!("User types: 'getv', wants camelCase identifiers only");
    println!("Filtered suggestions:\n");

    for candidate in Transducer::new(dict.clone(), Algorithm::Standard)
        .query_ordered("getv", 1)
        .prefix()
        .filter(|c| {
            // Check if identifier follows camelCase (starts with lowercase)
            c.term
                .chars()
                .next()
                .map(|ch| ch.is_lowercase())
                .unwrap_or(false)
        })
        .take(5)
    {
        println!("  {} (distance: {})", candidate.term, candidate.distance);
    }

    // Scenario 6: Top-K results with combined filtering
    println!("\n--- Scenario 6: Top 3 public functions starting with 'get' ---");
    println!("User wants top 3 public functions");
    println!("Results:\n");

    for candidate in Transducer::new(dict.clone(), Algorithm::Standard)
        .query_ordered("get", 0)
        .prefix()
        .filter(|c| {
            identifiers.iter().any(|id| {
                id.name == c.term && id.id_type == IdentifierType::Function && id.is_public
            })
        })
        .take(3)
    // Only top 3
    {
        let id = identifiers
            .iter()
            .find(|id| id.name == candidate.term)
            .unwrap();
        println!(
            "  {} (type: {:?}, public: {})",
            candidate.term, id.id_type, id.is_public
        );
    }

    // Scenario 7: Distance-bounded search
    println!("\n--- Scenario 7: All matches within distance 1 of 'calcul' ---");
    println!("User types: 'calcul' (incomplete)");
    println!("Results:\n");

    for candidate in Transducer::new(dict.clone(), Algorithm::Standard)
        .query_ordered("calcul", 2)
        .prefix()
        .take_while(|c| c.distance <= 1)
    // Stop after distance 1
    {
        println!("  {} (distance: {})", candidate.term, candidate.distance);
    }

    // Scenario 8: Demonstrate ordering guarantees
    println!("\n--- Scenario 8: Ordering demonstration (distance first, then lexicographic) ---");
    println!("User types: 'user'");
    println!("All results shown in order:\n");

    let mut last_distance = 0;
    for candidate in Transducer::new(dict.clone(), Algorithm::Standard)
        .query_ordered("user", 2)
        .prefix()
        .take(10)
    {
        if candidate.distance > last_distance {
            println!("\n  --- Distance {} ---", candidate.distance);
            last_distance = candidate.distance;
        }
        println!("    {}", candidate.term);
    }

    println!("\n=== Demo Complete ===");
    println!("\nKey Features Demonstrated:");
    println!("  ✓ Prefix matching for autocomplete");
    println!("  ✓ Typo tolerance with edit distance");
    println!("  ✓ Context-aware filtering (by type, visibility, naming)");
    println!("  ✓ Lazy evaluation with take() and take_while()");
    println!("  ✓ Distance-first + lexicographic ordering");
}
