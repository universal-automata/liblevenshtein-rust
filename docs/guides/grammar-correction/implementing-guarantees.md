# Implementing Theoretical Guarantees

**Implementation Guide**
**Date**: 2025-11-04
**Project**: liblevenshtein-rust
**Based on**: `../../design/grammar-correction/theoretical-analysis/complete-analysis.md`

This guide provides concrete implementation strategies to achieve the theoretical properties analyzed in `../../design/grammar-correction/theoretical-analysis/complete-analysis.md`.

---

## Table of Contents

1. [Determinism Implementation](#1-determinism-implementation)
2. [Correctness Verification](#2-correctness-verification)
3. [Optimality Approximation](#3-optimality-approximation)
4. [Performance Optimization](#4-performance-optimization)
5. [Testing Strategies](#5-testing-strategies)
6. [Configuration Management](#6-configuration-management)
7. [Code Examples](#7-code-examples)

---

## 1. Determinism Implementation

### 1.1 Layer 1: Lexical Correction

**Requirement**: Same input → same candidates in same order

**Implementation**:

```rust
pub struct LexicalCorrector {
    dictionary: Dictionary,
    max_distance: usize,
    deterministic: bool,
}

impl LexicalCorrector {
    pub fn correct(&self, token: &str, k: usize) -> Vec<(String, usize)> {
        // 1. Build Levenshtein automaton (deterministic)
        let automaton = LevenshteinAutomaton::new(token, self.max_distance);

        // 2. Query dictionary (deterministic)
        let mut candidates: Vec<(String, usize)> = self.dictionary
            .iter()
            .filter_map(|word| {
                if automaton.accepts(word) {
                    let distance = levenshtein_distance(token, word);
                    Some((word.to_string(), distance))
                } else {
                    None
                }
            })
            .collect();

        // 3. Sort by (distance, lexicographic) for determinism
        if self.deterministic {
            candidates.sort_by(|a, b| {
                a.1.cmp(&b.1)  // Primary: distance
                    .then_with(|| a.0.cmp(&b.0))  // Secondary: lexicographic
            });
        } else {
            // Non-deterministic: sort by distance only (faster)
            candidates.sort_by_key(|x| x.1);
        }

        // 4. Return top-k
        candidates.truncate(k);
        candidates
    }
}
```

**Key Points**:
- Deterministic flag controls tie-breaking behavior
- Sorting ensures reproducibility
- Lexicographic ordering is arbitrary but consistent

**Test**:

```rust
#[test]
fn test_lexical_determinism() {
    let corrector = LexicalCorrector::new(dictionary, 2, true);

    let result1 = corrector.correct("teh", 5);
    let result2 = corrector.correct("teh", 5);

    assert_eq!(result1, result2, "Lexical correction must be deterministic");
}
```

### 1.2 Layer 2: Grammar Correction

**Requirement**: BFS with deterministic queue and tie-breaking

**Implementation**:

```rust
pub struct GrammarCorrector {
    parser: TreeSitterParser,
    max_distance: usize,
    beam_width: usize,
    deterministic: bool,
}

impl GrammarCorrector {
    pub fn correct(&self, tokens: &[Token]) -> Vec<ParseTree> {
        // Use VecDeque for deterministic FIFO queue
        let mut queue: VecDeque<SearchState> = VecDeque::new();
        let mut results: Vec<ParseTree> = Vec::new();

        // Initial state
        queue.push_back(SearchState {
            parse_state: self.parser.initial_state(),
            edits: vec![],
            cost: 0,
            state_id: 0,  // For deterministic ordering
        });

        let mut next_state_id = 1;

        while let Some(state) = queue.pop_front() {
            // Prune if cost exceeds max
            if state.cost > self.max_distance {
                continue;
            }

            // Check if complete parse
            if state.parse_state.is_complete() {
                results.push(state.to_parse_tree());
                continue;
            }

            // Generate next states
            let mut next_states: Vec<SearchState> = self.parser
                .lookahead_iterator(&state.parse_state)
                .flat_map(|symbol| {
                    self.apply_edits(&state, symbol, &mut next_state_id)
                })
                .collect();

            // Deterministic ordering
            if self.deterministic {
                // Sort by (cost, state_id) for deterministic exploration
                next_states.sort_by_key(|s| (s.cost, s.state_id));
            }

            // Beam search pruning
            next_states.truncate(self.beam_width);

            // Add to queue
            queue.extend(next_states);
        }

        // Sort results for deterministic output
        if self.deterministic {
            results.sort_by_key(|tree| tree.cost);
        }

        results
    }

    fn apply_edits(
        &self,
        state: &SearchState,
        symbol: Symbol,
        next_state_id: &mut usize,
    ) -> Vec<SearchState> {
        let mut new_states = Vec::new();

        // Match (cost 0)
        if state.next_token() == Some(symbol) {
            new_states.push(SearchState {
                parse_state: state.parse_state.advance(symbol),
                edits: state.edits.clone(),
                cost: state.cost,
                state_id: *next_state_id,
            });
            *next_state_id += 1;
        }

        // Insert (cost 1)
        new_states.push(SearchState {
            parse_state: state.parse_state.advance(symbol),
            edits: {
                let mut e = state.edits.clone();
                e.push(Edit::Insert(symbol));
                e
            },
            cost: state.cost + 1,
            state_id: *next_state_id,
        });
        *next_state_id += 1;

        // Delete (cost 1) - skip current token
        if let Some(token) = state.next_token() {
            new_states.push(SearchState {
                parse_state: state.parse_state.clone(),
                edits: {
                    let mut e = state.edits.clone();
                    e.push(Edit::Delete(token));
                    e
                },
                cost: state.cost + 1,
                state_id: *next_state_id,
            });
            *next_state_id += 1;
        }

        // Substitute (cost 1)
        if let Some(token) = state.next_token() {
            new_states.push(SearchState {
                parse_state: state.parse_state.advance(symbol),
                edits: {
                    let mut e = state.edits.clone();
                    e.push(Edit::Substitute(token, symbol));
                    e
                },
                cost: state.cost + 1,
                state_id: *next_state_id,
            });
            *next_state_id += 1;
        }

        new_states
    }
}
```

**Key Points**:
- `state_id` ensures deterministic ordering when costs are equal
- VecDeque (FIFO) for BFS, not HashMap
- Sort results for reproducibility

**Test**:

```rust
#[test]
fn test_grammar_determinism() {
    let corrector = GrammarCorrector::new(parser, 2, 20, true);

    let tokens = tokenize("1 + 2 3");
    let result1 = corrector.correct(&tokens);
    let result2 = corrector.correct(&tokens);

    assert_eq!(result1, result2, "Grammar correction must be deterministic");
}
```

### 1.3 Layer 3: Semantic Validation

**Requirement**: Deterministic type inference

**Implementation**:

```rust
pub struct SemanticValidator {
    fresh_counter: Cell<usize>,  // Deterministic fresh variable generation
}

impl SemanticValidator {
    pub fn validate(&self, parse_tree: &ParseTree) -> Result<Type, TypeError> {
        // Reset fresh counter for determinism
        self.fresh_counter.set(0);

        let ast = parse_tree_to_ast(parse_tree);
        self.type_infer(&ast, &Context::empty())
    }

    fn type_infer(&self, ast: &AST, ctx: &Context) -> Result<Type, TypeError> {
        // Algorithm W implementation with deterministic fresh variables
        match ast {
            AST::Var(name) => {
                ctx.lookup(name).ok_or_else(|| TypeError::Unbound(name.clone()))
            }
            AST::Lambda(param, body) => {
                let param_type = self.fresh_type_var();
                let ctx_extended = ctx.extend(param.clone(), param_type.clone());
                let body_type = self.type_infer(body, &ctx_extended)?;
                Ok(Type::Arrow(Box::new(param_type), Box::new(body_type)))
            }
            AST::App(func, arg) => {
                let func_type = self.type_infer(func, ctx)?;
                let arg_type = self.type_infer(arg, ctx)?;
                let result_type = self.fresh_type_var();
                let expected = Type::Arrow(Box::new(arg_type.clone()), Box::new(result_type.clone()));
                self.unify(&func_type, &expected)?;
                Ok(result_type)
            }
            // ... more cases
        }
    }

    fn fresh_type_var(&self) -> Type {
        let id = self.fresh_counter.get();
        self.fresh_counter.set(id + 1);
        Type::Var(format!("t{}", id))  // Deterministic: t0, t1, t2, ...
    }
}
```

**Key Points**:
- Counter-based fresh variable generation (not random or timestamp-based)
- Reset counter for each validation (reproducibility)
- Deterministic naming scheme

**Test**:

```rust
#[test]
fn test_semantic_determinism() {
    let validator = SemanticValidator::new();

    let tree = parse("(λx. x) 5");
    let result1 = validator.validate(&tree);
    let result2 = validator.validate(&tree);

    assert_eq!(result1, result2, "Type inference must be deterministic");
}
```

### 1.4 Layer 4: Semantic Repair

**Requirement**: Deterministic SMT solver

**Implementation**:

```rust
pub struct SemanticRepairer {
    solver: Z3Solver,
    deterministic: bool,
}

impl SemanticRepairer {
    pub fn new(deterministic: bool) -> Self {
        let mut config = Z3Config::new();
        if deterministic {
            config.set("smt.random_seed", "42");  // Fixed seed for reproducibility
            config.set("sat.random_seed", "42");
        }

        Self {
            solver: Z3Solver::new(config),
            deterministic,
        }
    }

    pub fn repair(&self, ast: &AST, type_error: &TypeError) -> Vec<AST> {
        // 1. Localize error (deterministic)
        let error_location = self.localize_error(ast, type_error);

        // 2. Generate repair constraints
        let constraints = self.generate_constraints(ast, error_location);

        // 3. Solve MaxSMT
        let models = self.solver.max_smt(&constraints);

        // 4. Extract repairs
        let mut repairs: Vec<AST> = models
            .iter()
            .map(|model| self.apply_model(ast, model))
            .collect();

        // 5. Verify repairs
        repairs.retain(|repair| self.is_well_typed(repair));

        // 6. Sort for determinism
        if self.deterministic {
            repairs.sort_by_key(|repair| self.repair_cost(ast, repair));
        }

        repairs
    }
}
```

**Key Points**:
- Set Z3 random seed for reproducibility
- Sort repairs by cost for deterministic ordering
- Verification step ensures correctness

**Test**:

```rust
#[test]
fn test_repair_determinism() {
    let repairer = SemanticRepairer::new(true);

    let ast = parse("x + \"hello\"");  // Type error
    let result1 = repairer.repair(&ast, &type_error);
    let result2 = repairer.repair(&ast, &type_error);

    assert_eq!(result1, result2, "Semantic repair must be deterministic");
}
```

---

## 2. Correctness Verification

### 2.1 Property-Based Testing

**Strategy**: Generate random inputs, verify properties hold

**Implementation** (using proptest):

```rust
use proptest::prelude::*;

proptest! {
    #[test]
    fn prop_lexical_correctness(s in "[a-z]{1,10}", d in 1..=3usize) {
        let corrector = LexicalCorrector::new(dictionary(), d, true);
        let results = corrector.correct(&s, 10);

        // Property: All results are within distance d
        for (candidate, distance) in results {
            prop_assert!(distance <= d);
            prop_assert!(levenshtein_distance(&s, &candidate) <= d);
        }
    }

    #[test]
    fn prop_grammar_correctness(tokens in prop::collection::vec(any::<Token>(), 1..20)) {
        let corrector = GrammarCorrector::new(parser(), 2, 20, true);
        let results = corrector.correct(&tokens);

        // Property: All results are syntactically valid
        for tree in results {
            prop_assert!(tree.is_syntactically_valid());
            prop_assert!(!tree.has_error_nodes());
        }
    }

    #[test]
    fn prop_semantic_correctness(ast in arb_ast()) {
        let validator = SemanticValidator::new();

        // Property: If validation succeeds, program is well-typed
        if let Ok(ty) = validator.validate(&ast) {
            prop_assert!(is_well_typed(&ast, &ty));
        }
    }

    #[test]
    fn prop_repair_correctness(ast in arb_ast_with_type_error()) {
        let repairer = SemanticRepairer::new(true);
        let validator = SemanticValidator::new();

        if let Some(error) = find_type_error(&ast) {
            let repairs = repairer.repair(&ast, &error);

            // Property: All repairs are well-typed
            for repair in repairs {
                prop_assert!(validator.validate(&repair).is_ok());
            }
        }
    }
}
```

### 2.2 Invariant Checking

**Strategy**: Assert invariants at key points

**Implementation**:

```rust
impl GrammarCorrector {
    fn correct(&self, tokens: &[Token]) -> Vec<ParseTree> {
        let results = self.bfs_search(tokens);

        // Invariant: All results are valid parse trees
        debug_assert!(results.iter().all(|tree| tree.is_valid()));

        // Invariant: All results are within max distance
        debug_assert!(results.iter().all(|tree| tree.cost <= self.max_distance));

        results
    }
}
```

### 2.3 Double-Checking

**Strategy**: Verify repairs with independent validator

**Implementation**:

```rust
impl SemanticRepairer {
    pub fn repair(&self, ast: &AST, type_error: &TypeError) -> Vec<AST> {
        let repairs = self.smt_repair(ast, type_error);

        // Double-check: Verify all repairs are well-typed
        let validator = SemanticValidator::new();
        let verified_repairs: Vec<AST> = repairs
            .into_iter()
            .filter(|repair| validator.validate(repair).is_ok())
            .collect();

        if verified_repairs.is_empty() {
            warn!("SMT repair failed verification");
        }

        verified_repairs
    }
}
```

---

## 3. Optimality Approximation

### 3.1 Beam Search with Adaptive Width

**Strategy**: Expand beam when quality drops

**Implementation**:

```rust
pub struct AdaptiveBeamSearch {
    initial_width: usize,
    max_width: usize,
    expansion_threshold: f64,
}

impl AdaptiveBeamSearch {
    pub fn search(&self, initial_state: State) -> Vec<Solution> {
        let mut beam_width = self.initial_width;
        let mut prev_best_score = f64::INFINITY;

        loop {
            let results = self.beam_search(initial_state.clone(), beam_width);
            let best_score = results.first().map(|s| s.score).unwrap_or(f64::INFINITY);

            // Check if expanding beam improves quality
            let improvement = (prev_best_score - best_score) / prev_best_score;

            if improvement < self.expansion_threshold || beam_width >= self.max_width {
                return results;
            }

            // Expand beam
            beam_width = (beam_width * 2).min(self.max_width);
            prev_best_score = best_score;
        }
    }
}
```

### 3.2 A* Heuristic

**Strategy**: Use admissible heuristic to guide search

**Implementation**:

```rust
impl GrammarCorrector {
    fn heuristic(&self, state: &SearchState, target: &[Token]) -> usize {
        // Admissible heuristic: underestimate remaining cost
        let remaining_tokens = target.len() - state.position;

        // Lower bound: at least need to process remaining tokens
        // (could all match perfectly, so cost 0 per token)
        0.max(remaining_tokens.saturating_sub(state.remaining_budget()))
    }

    fn a_star_search(&self, tokens: &[Token]) -> Vec<ParseTree> {
        // Priority queue by f(n) = g(n) + h(n)
        let mut queue: BinaryHeap<Reverse<(usize, SearchState)>> = BinaryHeap::new();

        queue.push(Reverse((0, initial_state())));

        while let Some(Reverse((f_score, state))) = queue.pop() {
            if state.is_complete() {
                return vec![state.to_parse_tree()];
            }

            for next_state in self.expand(&state) {
                let g_score = next_state.cost;  // Cost so far
                let h_score = self.heuristic(&next_state, tokens);  // Estimated remaining
                let f_score = g_score + h_score;

                queue.push(Reverse((f_score, next_state)));
            }
        }

        vec![]
    }
}
```

### 3.3 Pareto Frontier Computation

**Strategy**: Keep all non-dominated solutions

**Implementation**:

```rust
pub struct ParetoOptimizer {
    objectives: Vec<Box<dyn Fn(&Solution) -> f64>>,
}

impl ParetoOptimizer {
    pub fn compute_frontier(&self, candidates: Vec<Solution>) -> Vec<Solution> {
        let mut frontier: Vec<Solution> = Vec::new();

        'candidate: for candidate in candidates {
            // Check if candidate is dominated by any solution in frontier
            for existing in &frontier {
                if self.dominates(existing, &candidate) {
                    continue 'candidate;  // Skip dominated candidate
                }
            }

            // Remove solutions dominated by candidate
            frontier.retain(|existing| !self.dominates(&candidate, existing));

            // Add candidate to frontier
            frontier.push(candidate);
        }

        frontier
    }

    fn dominates(&self, a: &Solution, b: &Solution) -> bool {
        let mut strictly_better = false;

        for objective in &self.objectives {
            let score_a = objective(a);
            let score_b = objective(b);

            if score_a > score_b {
                return false;  // a worse in some objective
            } else if score_a < score_b {
                strictly_better = true;  // a better in this objective
            }
        }

        strictly_better  // a at least as good in all, better in at least one
    }
}

// Usage
let optimizer = ParetoOptimizer {
    objectives: vec![
        Box::new(|s| s.lexical_cost as f64),
        Box::new(|s| s.grammar_cost as f64),
        Box::new(|s| s.semantic_cost as f64),
    ],
};

let candidates = pipeline.generate_candidates(input);
let pareto_frontier = optimizer.compute_frontier(candidates);

// Present to user
for (i, solution) in pareto_frontier.iter().enumerate() {
    println!("{}. {} (lex: {}, gram: {}, sem: {})",
        i + 1,
        solution.text,
        solution.lexical_cost,
        solution.grammar_cost,
        solution.semantic_cost
    );
}
```

---

## 4. Performance Optimization

### 4.1 Incremental Parsing (Tree-sitter)

**Strategy**: Reuse previous parse when input changes

**Implementation**:

```rust
pub struct IncrementalParser {
    parser: TreeSitterParser,
    prev_tree: Option<Tree>,
    prev_input: String,
}

impl IncrementalParser {
    pub fn parse(&mut self, input: &str) -> Tree {
        let tree = if let Some(prev) = &self.prev_tree {
            // Incremental parse (O(log n) typically)
            self.parser.parse_incremental(input, prev)
        } else {
            // Full parse (O(n))
            self.parser.parse(input, None)
        };

        self.prev_tree = Some(tree.clone());
        self.prev_input = input.to_string();
        tree
    }
}
```

### 4.2 Caching

**Strategy**: Cache expensive computations

**Implementation**:

```rust
use lru::LruCache;

pub struct CachedLexicalCorrector {
    corrector: LexicalCorrector,
    cache: Mutex<LruCache<String, Vec<(String, usize)>>>,
}

impl CachedLexicalCorrector {
    pub fn correct(&self, token: &str, k: usize) -> Vec<(String, usize)> {
        let cache_key = format!("{}:{}", token, k);

        // Check cache
        {
            let mut cache = self.cache.lock().unwrap();
            if let Some(result) = cache.get(&cache_key) {
                return result.clone();
            }
        }

        // Compute
        let result = self.corrector.correct(token, k);

        // Store in cache
        {
            let mut cache = self.cache.lock().unwrap();
            cache.put(cache_key, result.clone());
        }

        result
    }
}
```

### 4.3 Parallelization

**Strategy**: Process independent candidates in parallel

**Implementation**:

```rust
use rayon::prelude::*;

impl SemanticValidator {
    pub fn validate_batch(&self, parse_trees: Vec<ParseTree>) -> Vec<Result<Type, TypeError>> {
        // Parallel validation (candidates are independent)
        parse_trees
            .par_iter()
            .map(|tree| self.validate(tree))
            .collect()
    }
}

impl Pipeline {
    pub fn correct(&self, input: &str) -> Vec<Correction> {
        // Layer 1: Lexical (sequential)
        let token_candidates = self.lexical.correct_all_tokens(input);

        // Layer 2: Grammar (parallel for each token combination)
        let parse_trees: Vec<ParseTree> = token_candidates
            .par_iter()
            .flat_map(|tokens| self.grammar.correct(tokens))
            .collect();

        // Layer 3: Semantic (parallel)
        let validated: Vec<(ParseTree, Type)> = parse_trees
            .into_par_iter()
            .filter_map(|tree| {
                self.semantic.validate(&tree).ok().map(|ty| (tree, ty))
            })
            .collect();

        // ... continue pipeline

        validated.into_iter().map(|(tree, ty)| Correction { tree, ty }).collect()
    }
}
```

### 4.4 Timeouts

**Strategy**: Bound expensive operations

**Implementation**:

```rust
use std::time::{Duration, Instant};

impl SemanticRepairer {
    pub fn repair_with_timeout(
        &self,
        ast: &AST,
        type_error: &TypeError,
        timeout: Duration,
    ) -> Vec<AST> {
        let start = Instant::now();
        let mut repairs = Vec::new();

        // Set solver timeout
        self.solver.set_timeout(timeout.as_millis() as u32);

        // Attempt repair
        match self.smt_repair(ast, type_error) {
            Ok(result) if start.elapsed() < timeout => {
                repairs = result;
            }
            Ok(_) => {
                warn!("SMT repair timed out");
            }
            Err(e) => {
                error!("SMT repair failed: {}", e);
            }
        }

        repairs
    }
}
```

---

## 5. Testing Strategies

### 5.1 Unit Tests

```rust
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_lexical_empty() {
        let corrector = LexicalCorrector::new(dictionary(), 2, true);
        let result = corrector.correct("", 5);
        assert!(result.is_empty());
    }

    #[test]
    fn test_grammar_balanced_parens() {
        let corrector = GrammarCorrector::new(parser(), 1, 20, true);
        let tokens = tokenize("(x + y");  // Missing ')'
        let result = corrector.correct(&tokens);
        assert!(result.iter().any(|tree| tree.is_balanced()));
    }

    #[test]
    fn test_semantic_simple_types() {
        let validator = SemanticValidator::new();
        let ast = parse("λx. x");  // Identity function
        let result = validator.validate(&ast);
        assert!(result.is_ok());
    }
}
```

### 5.2 Integration Tests

```rust
#[test]
fn test_full_pipeline() {
    let pipeline = Pipeline::new(config());

    let input = "prnt(x + y";  // Typo + missing ')'
    let results = pipeline.correct(input);

    // Check at least one valid correction exists
    assert!(!results.is_empty());

    // Check all corrections are valid
    for correction in results {
        assert!(correction.is_syntactically_valid());
        assert!(correction.is_well_typed());
    }
}

#[test]
fn test_error_cascade() {
    let pipeline = Pipeline::new(config());

    let input = "for i in rang(10):";  // Typo causes cascade
    let results = pipeline.correct(input);

    // Should fix both typo and missing block
    let best = results.first().unwrap();
    assert!(best.text.contains("range"));  // Typo fixed
    assert!(best.text.contains("pass") || best.text.contains("break"));  // Block added
}
```

### 5.3 Performance Tests

```rust
#[test]
fn test_performance_budget() {
    use std::time::Instant;

    let pipeline = Pipeline::new(config());
    let input = generate_input_with_errors(100);  // 100 tokens

    let start = Instant::now();
    let results = pipeline.correct(&input);
    let duration = start.elapsed();

    assert!(!results.is_empty());
    assert!(duration < Duration::from_millis(500), "Exceeds 500ms budget");
}

#[bench]
fn bench_lexical_correction(b: &mut Bencher) {
    let corrector = LexicalCorrector::new(dictionary(), 2, false);
    b.iter(|| {
        corrector.correct("prnt", 5)
    });
}
```

---

## 6. Configuration Management

### 6.1 Configuration Struct

```rust
#[derive(Debug, Clone)]
pub struct PipelineConfig {
    // Determinism
    pub deterministic_mode: bool,

    // Lexical
    pub lexical_max_distance: usize,
    pub lexical_top_k: usize,

    // Grammar
    pub grammar_max_distance: usize,
    pub grammar_beam_width: usize,
    pub grammar_use_astar: bool,

    // Semantic
    pub type_inference_timeout: Duration,
    pub smt_repair_timeout: Duration,
    pub smt_random_seed: Option<u32>,

    // Session Types
    pub session_type_depth: usize,

    // Feedback
    pub enable_feedback: bool,
    pub feedback_model_path: Option<PathBuf>,

    // Performance
    pub enable_caching: bool,
    pub enable_parallelization: bool,
    pub cache_size: usize,
}

impl Default for PipelineConfig {
    fn default() -> Self {
        Self {
            deterministic_mode: false,
            lexical_max_distance: 2,
            lexical_top_k: 5,
            grammar_max_distance: 2,
            grammar_beam_width: 20,
            grammar_use_astar: true,
            type_inference_timeout: Duration::from_secs(1),
            smt_repair_timeout: Duration::from_secs(2),
            smt_random_seed: None,  // Non-deterministic by default
            session_type_depth: 10,
            enable_feedback: true,
            feedback_model_path: None,
            enable_caching: true,
            enable_parallelization: true,
            cache_size: 1000,
        }
    }
}

impl PipelineConfig {
    pub fn for_testing() -> Self {
        Self {
            deterministic_mode: true,
            smt_random_seed: Some(42),
            enable_feedback: false,
            ..Default::default()
        }
    }

    pub fn for_production() -> Self {
        Self {
            deterministic_mode: false,
            grammar_beam_width: 50,  // Higher quality
            smt_repair_timeout: Duration::from_secs(5),  // More time
            ..Default::default()
        }
    }

    pub fn for_interactive() -> Self {
        Self {
            grammar_beam_width: 10,  // Faster
            smt_repair_timeout: Duration::from_millis(500),  // Lower latency
            ..Default::default()
        }
    }
}
```

### 6.2 Environment-Based Configuration

```rust
impl PipelineConfig {
    pub fn from_env() -> Self {
        use std::env;

        let mut config = Self::default();

        if let Ok(val) = env::var("DETERMINISTIC") {
            config.deterministic_mode = val.parse().unwrap_or(false);
        }

        if let Ok(val) = env::var("BEAM_WIDTH") {
            config.grammar_beam_width = val.parse().unwrap_or(20);
        }

        // ... more env vars

        config
    }
}
```

---

## 7. Code Examples

### 7.1 Complete Pipeline

```rust
pub struct MultiLayerPipeline {
    config: PipelineConfig,
    lexical: LexicalCorrector,
    grammar: GrammarCorrector,
    semantic: SemanticValidator,
    repair: SemanticRepairer,
    process: ProcessVerifier,
}

impl MultiLayerPipeline {
    pub fn new(config: PipelineConfig) -> Self {
        Self {
            lexical: LexicalCorrector::new(
                load_dictionary(),
                config.lexical_max_distance,
                config.deterministic_mode,
            ),
            grammar: GrammarCorrector::new(
                load_parser(),
                config.grammar_max_distance,
                config.grammar_beam_width,
                config.deterministic_mode,
            ),
            semantic: SemanticValidator::new(),
            repair: SemanticRepairer::new(config.deterministic_mode),
            process: ProcessVerifier::new(config.session_type_depth),
            config,
        }
    }

    pub fn correct(&self, input: &str) -> Vec<Correction> {
        // Layer 1: Lexical
        let lexical_start = Instant::now();
        let token_candidates = self.lexical.correct_all_tokens(input, self.config.lexical_top_k);
        debug!("Lexical: {:?}", lexical_start.elapsed());

        // Layer 2: Grammar
        let grammar_start = Instant::now();
        let parse_trees: Vec<ParseTree> = token_candidates
            .into_iter()
            .flat_map(|tokens| self.grammar.correct(&tokens))
            .collect();
        debug!("Grammar: {:?}", grammar_start.elapsed());

        // Layer 3: Semantic Validation
        let semantic_start = Instant::now();
        let mut validated: Vec<(ParseTree, Type)> = parse_trees
            .into_iter()
            .filter_map(|tree| {
                self.semantic.validate(&tree).ok().map(|ty| (tree, ty))
            })
            .collect();
        debug!("Semantic Validation: {:?}", semantic_start.elapsed());

        // Layer 4: Semantic Repair (if no valid programs)
        if validated.is_empty() {
            let repair_start = Instant::now();
            let repaired = self.repair.repair_batch(&parse_trees, self.config.smt_repair_timeout);
            validated.extend(repaired.into_iter().filter_map(|tree| {
                self.semantic.validate(&tree).ok().map(|ty| (tree, ty))
            }));
            debug!("Semantic Repair: {:?}", repair_start.elapsed());
        }

        // Layer 5: Process Verification (if applicable)
        if self.config.session_type_depth > 0 {
            let process_start = Instant::now();
            validated.retain(|(tree, _)| {
                self.process.verify(tree).is_ok()
            });
            debug!("Process Verification: {:?}", process_start.elapsed());
        }

        // Convert to corrections
        validated
            .into_iter()
            .map(|(tree, ty)| Correction {
                text: tree.to_string(),
                tree,
                ty,
                cost: self.total_cost(input, &tree),
            })
            .collect()
    }

    pub fn correct_with_pareto(&self, input: &str) -> Vec<Correction> {
        let candidates = self.correct(input);

        // Compute Pareto frontier
        let optimizer = ParetoOptimizer {
            objectives: vec![
                Box::new(|c: &Correction| c.lexical_cost() as f64),
                Box::new(|c: &Correction| c.grammar_cost() as f64),
                Box::new(|c: &Correction| c.semantic_cost() as f64),
            ],
        };

        optimizer.compute_frontier(candidates)
    }
}
```

### 7.2 Usage Examples

```rust
fn main() {
    // Example 1: Testing mode (deterministic)
    let config = PipelineConfig::for_testing();
    let pipeline = MultiLayerPipeline::new(config);

    let input = "prnt(x + y";
    let corrections = pipeline.correct(input);
    for correction in corrections {
        println!("{}: cost {}", correction.text, correction.cost);
    }

    // Example 2: Production mode (quality)
    let config = PipelineConfig::for_production();
    let pipeline = MultiLayerPipeline::new(config);

    let input = "for i in rang(10):";
    let corrections = pipeline.correct_with_pareto(input);
    for (i, correction) in corrections.iter().enumerate() {
        println!("{}. {} (lex: {}, gram: {}, sem: {})",
            i + 1,
            correction.text,
            correction.lexical_cost(),
            correction.grammar_cost(),
            correction.semantic_cost()
        );
    }

    // Example 3: Interactive mode (low latency)
    let config = PipelineConfig::for_interactive();
    let pipeline = MultiLayerPipeline::new(config);

    loop {
        let input = read_user_input();
        let start = Instant::now();
        let corrections = pipeline.correct(&input);
        let latency = start.elapsed();

        println!("Found {} corrections in {:?}", corrections.len(), latency);
        // ... show to user
    }
}
```

---

## Conclusion

This implementation guide provides concrete strategies to achieve the theoretical properties analyzed in `../../design/grammar-correction/theoretical-analysis/complete-analysis.md`:

1. **Determinism**: Tie-breaking, fixed seeds, counter-based fresh variables
2. **Correctness**: Verification, double-checking, property-based testing
3. **Optimality**: Beam search, A*, Pareto optimization
4. **Performance**: Incremental parsing, caching, parallelization, timeouts

For complete theoretical analysis, see `../../design/grammar-correction/theoretical-analysis/complete-analysis.md`.

For quick reference, see `../../design/grammar-correction/theoretical-analysis/quick-reference.md`.

For visual representations, see `../../design/grammar-correction/theoretical-analysis/visual-guide.md`.

---

**Document Version**: 1.0
**Last Updated**: 2025-11-04
**Status**: Implementation Guide
