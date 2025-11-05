//! LSP Completion Server Example
//!
//! This example demonstrates how to integrate `DynamicContextualCompletionEngine`
//! into a Language Server Protocol (LSP) completion provider.
//!
//! ## Overview
//!
//! The server tracks:
//! - Open documents and their file-level contexts
//! - Scope boundaries (functions, blocks) within documents
//! - Variable declarations and their visibility
//!
//! ## Usage
//!
//! ```bash
//! cargo run --example lsp_completion
//! ```
//!
//! ## LSP Protocol Flow
//!
//! 1. Client: textDocument/didOpen → Server creates file context
//! 2. Client: textDocument/didChange → Server updates scopes and drafts
//! 3. Client: textDocument/completion → Server queries engine, returns results
//! 4. Client: textDocument/didClose → Server removes context

use liblevenshtein::contextual::{DynamicContextualCompletionEngine, ContextId};
use liblevenshtein::dictionary::PathMapDictionary;
use std::collections::HashMap;
use std::error::Error;

// ============================================================================
// LSP Data Structures (simplified)
// ============================================================================

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
struct Position {
    line: usize,
    character: usize,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct Range {
    start: Position,
    end: Position,
}

impl Range {
    fn contains(&self, pos: Position) -> bool {
        (self.start.line < pos.line ||
         (self.start.line == pos.line && self.start.character <= pos.character))
        &&
        (self.end.line > pos.line ||
         (self.end.line == pos.line && self.end.character >= pos.character))
    }
}

#[derive(Debug, Clone)]
struct CompletionItem {
    label: String,
    detail: Option<String>,
    sort_text: Option<String>,
}

// ============================================================================
// LSP Completion Server
// ============================================================================

struct LspCompletionServer {
    /// The contextual completion engine
    engine: DynamicContextualCompletionEngine<PathMapDictionary<()>>,

    /// Map from file URI to root context for that file
    file_contexts: HashMap<String, ContextId>,

    /// Map from (URI, scope range) to ContextId
    scope_map: HashMap<(String, Range), ContextId>,
}

impl LspCompletionServer {
    /// Create a new LSP completion server
    fn new() -> Result<Self, Box<dyn Error>> {
        let dict = PathMapDictionary::new();
        let mut engine = DynamicContextualCompletionEngine::from_pathmap_dictionary(dict);

        // Pre-populate root context with standard library / language keywords
        let root = engine.root_context();
        for keyword in &["String", "Vec", "HashMap", "println", "format", "Result", "Option"] {
            engine.finalize(root, keyword)?;
        }

        Ok(Self {
            engine,
            file_contexts: HashMap::new(),
            scope_map: HashMap::new(),
        })
    }

    // ------------------------------------------------------------------------
    // LSP Lifecycle Events
    // ------------------------------------------------------------------------

    /// Handle textDocument/didOpen notification
    fn did_open(&mut self, uri: String, text: String) -> Result<(), Box<dyn Error>> {
        println!("[didOpen] {}", uri);

        // Create file-level context
        let root = self.engine.root_context();
        let file_ctx = self.engine.create_context(root)?;
        self.file_contexts.insert(uri.clone(), file_ctx);

        // Parse document to extract scopes and variables
        self.update_scopes(&uri, &text)?;

        println!("  → File context created: {:?}", file_ctx);

        Ok(())
    }

    /// Handle textDocument/didChange notification
    fn did_change(&mut self, uri: String, text: String) -> Result<(), Box<dyn Error>> {
        println!("[didChange] {}", uri);

        // Remove old scopes for this file
        self.scope_map.retain(|(file, _), ctx_id| {
            if file == &uri {
                self.engine.remove_context(*ctx_id);
                false
            } else {
                true
            }
        });

        // Re-parse document
        self.update_scopes(&uri, &text)?;

        Ok(())
    }

    /// Handle textDocument/didClose notification
    fn did_close(&mut self, uri: String) {
        println!("[didClose] {}", uri);

        // Remove file context
        if let Some(ctx) = self.file_contexts.remove(&uri) {
            self.engine.remove_context(ctx);
        }

        // Remove all scopes for this file
        self.scope_map.retain(|(file, _), ctx_id| {
            if file == &uri {
                self.engine.remove_context(*ctx_id);
                false
            } else {
                true
            }
        });
    }

    /// Handle textDocument/completion request
    fn completion(
        &self,
        uri: &str,
        position: Position,
        query: &str,
    ) -> Result<Vec<CompletionItem>, Box<dyn Error>> {
        println!("[completion] {} @ {:?} query=\"{}\"", uri, position, query);

        // Find context at cursor position
        let ctx = self.find_context_at_position(uri, position)?;

        // Query engine with distance=1 for typo tolerance
        let completions = self.engine.complete(ctx, query, 1)?;

        // Convert to LSP CompletionItems
        let items: Vec<_> = completions
            .into_iter()
            .map(|c| CompletionItem {
                label: c.term,
                detail: Some(format!("distance: {}", c.distance)),
                sort_text: Some(format!("{:02}_{}", c.distance, c.term)),
            })
            .collect();

        println!("  → {} completions", items.len());

        Ok(items)
    }

    // ------------------------------------------------------------------------
    // Scope Parsing (Simplified)
    // ------------------------------------------------------------------------

    /// Update scopes for a document (simplified parser)
    fn update_scopes(&mut self, uri: &str, text: &str) -> Result<(), Box<dyn Error>> {
        let file_ctx = self.file_contexts[uri];
        let lines: Vec<&str> = text.lines().collect();

        let mut scope_stack = vec![file_ctx];
        let mut indent_stack = vec![0];

        for (line_num, line) in lines.iter().enumerate() {
            let indent = line.chars().take_while(|&c| c == ' ').count();

            // Pop scopes when indent decreases
            while indent < *indent_stack.last().unwrap_or(&0) && indent_stack.len() > 1 {
                scope_stack.pop();
                indent_stack.pop();
            }

            let parent = *scope_stack.last().unwrap();

            // Detect function declarations: "fn name(...) {"
            if line.trim_start().starts_with("fn ") {
                let fn_ctx = self.engine.create_context(parent)?;
                scope_stack.push(fn_ctx);
                indent_stack.push(indent + 4);  // Assume 4-space indent

                let range = Range {
                    start: Position { line: line_num, character: indent },
                    end: Position { line: lines.len(), character: 0 },  // Until end (refined later)
                };
                self.scope_map.insert((uri.to_string(), range), fn_ctx);

                // Extract function parameters
                if let Some(params) = extract_parameters(line) {
                    for param in params {
                        self.engine.finalize(fn_ctx, &param)?;
                    }
                }
            }

            // Detect variable declarations: "let x = ..."
            if let Some(var_name) = extract_variable(line) {
                self.engine.finalize(parent, var_name)?;
            }
        }

        Ok(())
    }

    /// Find the most specific context containing the given position
    fn find_context_at_position(
        &self,
        uri: &str,
        pos: Position,
    ) -> Result<ContextId, Box<dyn Error>> {
        // Start with file context
        let mut best_ctx = *self.file_contexts
            .get(uri)
            .ok_or("File not open")?;

        // Find innermost scope containing position
        for ((file, range), ctx_id) in &self.scope_map {
            if file == uri && range.contains(pos) {
                best_ctx = *ctx_id;
            }
        }

        Ok(best_ctx)
    }
}

// ============================================================================
// Helper Functions (Simplified Parsing)
// ============================================================================

/// Extract function parameter names from a function declaration
///
/// Example: "fn process(x: i32, name: String) {" → ["x", "name"]
fn extract_parameters(line: &str) -> Option<Vec<String>> {
    let start = line.find('(')?;
    let end = line.find(')')?;
    let params_str = &line[start + 1..end];

    let params: Vec<String> = params_str
        .split(',')
        .filter_map(|param| {
            // Extract "name: Type" → "name"
            param.trim().split(':').next().map(|s| s.trim().to_string())
        })
        .filter(|s| !s.is_empty())
        .collect();

    Some(params)
}

/// Extract variable name from a let binding
///
/// Example: "let count = 10;" → "count"
fn extract_variable(line: &str) -> Option<&str> {
    let trimmed = line.trim();

    if let Some(rest) = trimmed.strip_prefix("let ") {
        if let Some(eq_pos) = rest.find('=') {
            let var_part = rest[..eq_pos].trim();
            // Handle "let mut x = ..." → "x"
            let var_name = var_part.strip_prefix("mut ").unwrap_or(var_part).trim();
            // Handle type annotations: "let x: i32 = ..." → "x"
            if let Some(colon_pos) = var_name.find(':') {
                return Some(var_name[..colon_pos].trim());
            }
            return Some(var_name);
        }
    }

    None
}

// ============================================================================
// Example Usage
// ============================================================================

fn main() -> Result<(), Box<dyn Error>> {
    println!("=== LSP Completion Server Example ===\n");

    let mut server = LspCompletionServer::new()?;

    // ========================================================================
    // Scenario 1: Open a Rust file
    // ========================================================================

    println!("--- Scenario 1: Open main.rs ---\n");

    let main_rs = r#"
fn main() {
    let count = 0;
    let counter = 1;

    println!("count: {}", count);
}

fn process(input: String, max: i32) {
    let result = input.len();
    println!("{}", result);
}
"#;

    server.did_open("file:///main.rs".to_string(), main_rs.to_string())?;

    // ========================================================================
    // Scenario 2: Completion in main() function
    // ========================================================================

    println!("\n--- Scenario 2: Complete 'cou' in main() ---\n");

    let position = Position { line: 4, character: 10 };  // Inside main()
    let items = server.completion("file:///main.rs", position, "cou")?;

    for item in &items {
        println!("  • {} {}", item.label, item.detail.as_ref().unwrap());
    }

    // ========================================================================
    // Scenario 3: Completion in process() function
    // ========================================================================

    println!("\n--- Scenario 3: Complete 'inp' in process() ---\n");

    let position = Position { line: 9, character: 20 };  // Inside process()
    let items = server.completion("file:///main.rs", position, "inp")?;

    for item in &items {
        println!("  • {} {}", item.label, item.detail.as_ref().unwrap());
    }

    // Expected: "input" (parameter), not "count"/"counter" from main()

    // ========================================================================
    // Scenario 4: Typo tolerance
    // ========================================================================

    println!("\n--- Scenario 4: Complete 'prntln' (typo) ---\n");

    let position = Position { line: 4, character: 5 };  // Inside main()
    let items = server.completion("file:///main.rs", position, "prntln")?;

    for item in &items {
        println!("  • {} {}", item.label, item.detail.as_ref().unwrap());
    }

    // Expected: "println" with distance=1 (insert 'i')

    // ========================================================================
    // Scenario 5: Document change
    // ========================================================================

    println!("\n--- Scenario 5: Edit main.rs (add variable) ---\n");

    let updated_main_rs = r#"
fn main() {
    let count = 0;
    let counter = 1;
    let country = "USA";

    println!("count: {}", count);
}

fn process(input: String, max: i32) {
    let result = input.len();
    println!("{}", result);
}
"#;

    server.did_change("file:///main.rs".to_string(), updated_main_rs.to_string())?;

    println!("--- Complete 'cou' again (should now include 'country') ---\n");

    let position = Position { line: 5, character: 10 };
    let items = server.completion("file:///main.rs", position, "cou")?;

    for item in &items {
        println!("  • {} {}", item.label, item.detail.as_ref().unwrap());
    }

    // Expected: "count", "counter", "country"

    // ========================================================================
    // Scenario 6: Close document
    // ========================================================================

    println!("\n--- Scenario 6: Close main.rs ---\n");

    server.did_close("file:///main.rs".to_string());

    println!("  → File context removed");

    // ========================================================================
    // Summary
    // ========================================================================

    println!("\n=== Summary ===");
    println!("This example demonstrates:");
    println!("  1. Document lifecycle (open/change/close)");
    println!("  2. Scope-aware completion (function parameters, local vars)");
    println!("  3. Typo tolerance (distance=1 fuzzy matching)");
    println!("  4. Incremental updates (re-parsing on change)");
    println!("\nFor production LSP servers, consider:");
    println!("  • Tree-sitter or full AST parsing for accurate scopes");
    println!("  • Incremental parsing (only re-parse changed regions)");
    println!("  • Caching completion results");
    println!("  • Asynchronous query execution");
    println!("  • Comprehensive language support (imports, types, etc.)");

    Ok(())
}
