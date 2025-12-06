# Implementation Roadmap

This document outlines the recommended path for implementing full semantic type
checking in MeTTaIL, progressing from the current foundation to complete OSLF
support.

---

## Table of Contents

1. [Overview](#overview)
2. [Phase 1: Gph-enriched Lawvere Foundation](#phase-1-gph-enriched-lawvere-foundation)
3. [Phase 2: Predicate Infrastructure](#phase-2-predicate-infrastructure)
4. [Phase 3: Behavioral Types](#phase-3-behavioral-types)
5. [Phase 4: Full OSLF](#phase-4-full-oslf)
6. [Phase 5: WFST Integration](#phase-5-wfst-integration)
7. [Phase 6: Rholang Integration](#phase-6-rholang-integration)
8. [Dependencies](#dependencies)
9. [Validation Criteria](#validation-criteria)

---

## Overview

### The Layered Approach

We recommend a **layered implementation** that builds incrementally:

```
┌─────────────────────────────────────────────────────────────────┐
│  Phase 6: Rholang Integration                                   │
│  - Type checker in compiler pipeline                            │
│  - Behavioral type enforcement                                  │
│  - Gradual typing migration                                     │
├─────────────────────────────────────────────────────────────────┤
│  Phase 5: WFST Integration                                      │
│  - Three-tier correction pipeline                               │
│  - FuzzySource trait for PathMap/MORK                           │
│  - Semantic type filtering for corrections                      │
├─────────────────────────────────────────────────────────────────┤
│  Phase 4: Full OSLF                                             │
│  - Presheaf construction                                        │
│  - Internal language extraction                                 │
│  - Refined binding types                                        │
├─────────────────────────────────────────────────────────────────┤
│  Phase 3: Behavioral Types                                      │
│  - Internal graph representation                                │
│  - Step modalities (F!, F*)                                     │
│  - Reachability (◇, □)                                          │
├─────────────────────────────────────────────────────────────────┤
│  Phase 2: Predicate Infrastructure                              │
│  - Predicate language                                           │
│  - Substitution and quantification                              │
│  - Datalog encoding                                             │
├─────────────────────────────────────────────────────────────────┤
│  Phase 1: Gph-enriched Lawvere Foundation                       │
│  - Graph-enriched hom-sets                                      │
│  - Reduction rules as edges                                     │
│  - Strategy control                                             │
├─────────────────────────────────────────────────────────────────┤
│  Current: Basic Type Checking                                   │
│  - Sort validation                                              │
│  - Constructor checking                                         │
│  - Rewrite engine                                               │
└─────────────────────────────────────────────────────────────────┘
```

### Why This Order?

1. **Incremental validation**: Each phase is testable independently
2. **Practical value early**: Gph-theories provide useful semantics quickly
3. **Complexity management**: Add features as foundations solidify
4. **Fallback positions**: Can stop at any phase with working system

---

## Phase 1: Gph-enriched Lawvere Foundation

### Goal

Represent operational semantics directly using graph-enriched hom-sets.

### Deliverables

1. **Gph-theory representation**
   ```rust
   pub struct GphTheory {
       pub sorts: Vec<Sort>,
       pub constructors: Vec<Constructor>,
       pub reductions: Vec<Reduction>,  // Edges in hom-graphs
   }

   pub struct Reduction {
       pub name: String,
       pub source: Term,   // LHS pattern
       pub target: Term,   // RHS term
       pub context: ReductionContext,
   }
   ```

2. **Reduction context markers**
   ```rust
   pub struct ReductionContext {
       pub position: Position,      // Where reduction can occur
       pub strategy: Strategy,      // Evaluation strategy
       pub resource: Option<Gas>,   // Optional gas consumption
   }
   ```

3. **Graph operations**
   ```rust
   impl GphTheory {
       /// Get all possible reductions from a term
       pub fn successors(&self, term: &Term) -> Vec<(Reduction, Term)>;

       /// Check if a reduction sequence exists
       pub fn reachable(&self, from: &Term, to: &Term) -> bool;

       /// Normalize using strategy
       pub fn normalize(&self, term: Term, strategy: Strategy) -> Term;
   }
   ```

### Validation

- [ ] SKI combinator calculus example works
- [ ] MeTTa multiset rewriting works
- [ ] Gas consumption tracks correctly
- [ ] Strategies (innermost, outermost) produce correct results

---

## Phase 2: Predicate Infrastructure

### Goal

Add a predicate language for expressing properties of terms.

### Deliverables

1. **Predicate types**
   ```rust
   pub enum Predicate {
       // Atomic predicates
       Atom(String),              // Named predicate
       Constructor(String),       // Term uses constructor
       Equals(Term, Term),        // Term equality

       // Logical connectives
       And(Box<Predicate>, Box<Predicate>),
       Or(Box<Predicate>, Box<Predicate>),
       Not(Box<Predicate>),
       Implies(Box<Predicate>, Box<Predicate>),

       // Quantification
       Forall(Var, Sort, Box<Predicate>),
       Exists(Var, Sort, Box<Predicate>),

       // Substitution
       Subst(Box<Predicate>, Substitution),
   }
   ```

2. **Predicate evaluation**
   ```rust
   impl Predicate {
       /// Evaluate predicate on a term
       pub fn eval(&self, term: &Term, env: &Env) -> bool;

       /// Check satisfiability
       pub fn satisfiable(&self, theory: &Theory) -> Option<Substitution>;
   }
   ```

3. **Datalog encoding**
   ```rust
   ascent! {
       // Encode predicates as Datalog relations
       relation holds(Predicate, Term);
       relation constructor_of(Term, String);
       relation subterm(Term, Term);

       // Derived rules
       holds(And(p, q), t) <-- holds(p, t), holds(q, t);
       holds(Or(p, q), t) <-- holds(p, t);
       holds(Or(p, q), t) <-- holds(q, t);
       holds(Exists(x, s, p), t) <--
           of_sort(witness, s),
           holds(p.subst(x, witness), t);
   }
   ```

### Validation

- [ ] Predicate evaluation is correct
- [ ] Quantifier handling works
- [ ] Datalog encoding matches direct evaluation
- [ ] Performance acceptable for realistic predicates

---

## Phase 3: Behavioral Types

### Goal

Express and check properties about computation steps.

### Deliverables

1. **Internal graph representation**
   ```rust
   pub struct InternalGraph<S> {
       pub states: Set<S>,
       pub edges: Vec<Edge<S>>,
   }

   pub struct Edge<S> {
       pub source: S,
       pub target: S,
       pub label: ReductionLabel,
   }
   ```

2. **Step modalities**
   ```rust
   impl InternalGraph<Term> {
       /// F!(φ): Exists a successor satisfying φ
       pub fn possible(&self, phi: &Predicate) -> Predicate {
           Predicate::Exists(
               Var::fresh("succ"),
               Sort::term(),
               Box::new(Predicate::And(
                   Box::new(Predicate::Successor(Var::current(), Var::fresh("succ"))),
                   Box::new(phi.subst(Var::current(), Var::fresh("succ"))),
               ))
           )
       }

       /// F*(φ): All successors satisfy φ
       pub fn necessary(&self, phi: &Predicate) -> Predicate {
           Predicate::Forall(
               Var::fresh("succ"),
               Sort::term(),
               Box::new(Predicate::Implies(
                   Box::new(Predicate::Successor(Var::current(), Var::fresh("succ"))),
                   Box::new(phi.subst(Var::current(), Var::fresh("succ"))),
               ))
           )
       }
   }
   ```

3. **Reachability modalities**
   ```rust
   impl InternalGraph<Term> {
       /// ◇φ: Eventually φ (least fixed point)
       pub fn eventually(&self, phi: &Predicate) -> Predicate {
           // μX. φ ∨ F!(X)
           self.lfp(|x| Predicate::Or(
               Box::new(phi.clone()),
               Box::new(self.possible(&x)),
           ))
       }

       /// □φ: Always φ (greatest fixed point)
       pub fn always(&self, phi: &Predicate) -> Predicate {
           // νX. φ ∧ F*(X)
           self.gfp(|x| Predicate::And(
               Box::new(phi.clone()),
               Box::new(self.necessary(&x)),
           ))
       }
   }
   ```

4. **Behavioral type examples**
   ```rust
   // Termination: eventually reach normal form
   let terminates = graph.eventually(&Predicate::NormalForm);

   // Progress: always can make progress or is done
   let progress = graph.always(&Predicate::Or(
       Box::new(Predicate::NormalForm),
       Box::new(graph.possible(&Predicate::True)),
   ));

   // Safety: never enter bad state
   let safe = graph.always(&Predicate::Not(Box::new(bad_state)));
   ```

### Validation

- [ ] Step modalities compute correctly
- [ ] Fixed points terminate (with bounded depth)
- [ ] Behavioral properties match expected semantics
- [ ] Integration with Gph-theories works

---

## Phase 4: Full OSLF

### Goal

Implement the complete presheaf construction for maximum expressiveness.

### Deliverables

1. **Presheaf representation**
   ```rust
   pub struct Presheaf<T: Theory> {
       pub base: T,
       pub object: Box<dyn Fn(&Object<T>) -> Set>,
       pub morphism: Box<dyn Fn(&Morphism<T>) -> Function>,
   }

   impl<T: Theory> Presheaf<T> {
       /// Yoneda embedding
       pub fn yoneda(obj: &Object<T>) -> Self {
           Presheaf {
               base: obj.theory(),
               object: Box::new(|c| T::hom(c, obj)),
               morphism: Box::new(|f| /* precomposition with f */),
           }
       }
   }
   ```

2. **Internal hom**
   ```rust
   impl<T: Theory> Presheaf<T> {
       /// Internal hom [P, Q]
       pub fn hom(p: &Self, q: &Self) -> Self {
           Presheaf {
               base: p.base.clone(),
               object: Box::new(|c| {
                   // Natural transformations y(c) × P → Q
                   NatTrans::all(&Presheaf::product(&Presheaf::yoneda(c), p), q)
               }),
               morphism: /* ... */,
           }
       }
   }
   ```

3. **Subobject classifier**
   ```rust
   pub struct Omega<T: Theory>(Presheaf<T>);

   impl<T: Theory> Omega<T> {
       /// The subobject classifier
       pub fn new(theory: &T) -> Self {
           Omega(Presheaf {
               base: theory.clone(),
               object: Box::new(|c| {
                   // Sieves on c
                   theory.sieves(c)
               }),
               morphism: /* pullback of sieves */,
           })
       }

       /// Predicate as subobject
       pub fn classify<P: Predicate>(&self, pred: &P) -> Morphism<Presheaf<T>, Omega<T>> {
           // Characteristic morphism of predicate
       }
   }
   ```

4. **Internal language extraction**
   ```rust
   pub struct TypeTheory<T: Theory> {
       pub types: Vec<Type>,
       pub terms: Vec<TypedTerm>,
       pub judgments: Vec<Judgment>,
   }

   impl<T: Theory> TypeTheory<T> {
       /// Extract type theory from presheaf topos
       pub fn from_presheaf(p: &Presheaf<T>) -> Self {
           // L functor application
       }
   }
   ```

### Validation

- [ ] Yoneda embedding preserves structure
- [ ] Internal hom computes correctly
- [ ] Predicates correspond to subobjects
- [ ] Type theory extraction produces valid rules

---

## Phase 5: WFST Integration

### Goal

Integrate MeTTaIL semantic type checking with liblevenshtein's correction WFST
to create a three-tier correction pipeline.

### Deliverables

1. **FuzzySource trait for PathMap/MORK**
   ```rust
   /// Trait for fuzzy dictionary lookups
   pub trait FuzzySource {
       /// Query with fuzzy matching, returns (candidate, distance) pairs
       fn fuzzy_lookup(&self, query: &[u8], max_distance: u8)
           -> impl Iterator<Item = (Vec<u8>, u8)>;

       /// Prefix search for completion
       fn prefix_search(&self, prefix: &[u8])
           -> impl Iterator<Item = Vec<u8>>;
   }

   impl FuzzySource for PathMap {
       fn fuzzy_lookup(&self, query: &[u8], max_distance: u8)
           -> impl Iterator<Item = (Vec<u8>, u8)>
       {
           // Use liblevenshtein automaton with PathMap traversal
           let automaton = LevenshteinAutomaton::new(query, max_distance);
           self.traverse_with_automaton(&automaton)
       }
   }

   impl FuzzySource for MorkSpace {
       fn fuzzy_lookup(&self, query: &[u8], max_distance: u8)
           -> impl Iterator<Item = (Vec<u8>, u8)>
       {
           // Bloom filter check + PathMap lookup
           if self.bloom.may_contain_within(query, max_distance) {
               self.pathmap.fuzzy_lookup(query, max_distance)
           } else {
               std::iter::empty()
           }
       }
   }
   ```

2. **Candidate lattice generation**
   ```rust
   /// Weighted finite-state transducer for correction lattice
   pub struct CandidateLattice<W: Semiring> {
       states: Vec<LatticeState>,
       arcs: Vec<Arc<W>>,
   }

   pub struct Arc<W: Semiring> {
       source: StateId,
       target: StateId,
       input: Option<Symbol>,   // Input symbol (or epsilon)
       output: Option<Symbol>,  // Output symbol (or epsilon)
       weight: W,               // Semiring weight
   }

   impl<W: Semiring> CandidateLattice<W> {
       /// Build lattice from fuzzy candidates
       pub fn from_candidates<S: FuzzySource>(
           source: &S,
           query: &[u8],
           max_distance: u8,
       ) -> Self {
           let candidates = source.fuzzy_lookup(query, max_distance);
           Self::build_lattice(candidates)
       }

       /// Compose with grammar transducer
       pub fn compose_with_grammar(&self, grammar: &GrammarFst<W>) -> Self {
           // WFST composition
       }

       /// Filter by semantic type predicates
       pub fn filter_by_type<C: TypeChecker>(
           &self,
           checker: &C,
           predicates: &[Predicate],
       ) -> Self {
           // Keep only candidates satisfying type predicates
       }
   }
   ```

3. **Three-tier pipeline**
   ```rust
   /// Unified correction pipeline
   pub struct CorrectionPipeline<W: Semiring> {
       tier1: Tier1LexicalCorrector<W>,
       tier2: Tier2SyntacticValidator<W>,
       tier3: Tier3SemanticChecker<W>,
   }

   impl<W: Semiring> CorrectionPipeline<W> {
       /// Run full correction pipeline
       pub fn correct(&self, input: &str, context: &Context) -> Vec<Correction<W>> {
           // Tier 1: Generate lexical candidates
           let lattice = self.tier1.generate_lattice(input);

           // Tier 2: Filter by grammar
           let syntactic = self.tier2.filter(&lattice, &context.grammar);

           // Tier 3: Filter by semantic types
           let semantic = self.tier3.filter(&syntactic, &context.type_env);

           // Return ranked corrections
           semantic.best_paths(context.top_k)
       }
   }

   /// Tier 1: Lexical correction (liblevenshtein)
   pub struct Tier1LexicalCorrector<W: Semiring> {
       dictionary: Box<dyn FuzzySource>,
       phonetic_rules: Vec<PhoneticRule>,
       semiring: PhantomData<W>,
   }

   /// Tier 2: Syntactic validation (MORK/CFG)
   pub struct Tier2SyntacticValidator<W: Semiring> {
       mork_space: MorkSpace,
       grammar: GrammarFst<W>,
   }

   /// Tier 3: Semantic type checking (MeTTaIL)
   pub struct Tier3SemanticChecker<W: Semiring> {
       theory: GphTheory,
       predicates: PredicateEnv,
       checker: MettailTypeChecker,
   }
   ```

4. **Grammar storage in MORK**
   ```rust
   /// Store grammar rules in MORK Space for efficient validation
   pub struct GrammarMorkSpace {
       mork: MorkSpace,
       productions: Vec<ProductionRule>,
   }

   impl GrammarMorkSpace {
       /// Load grammar from file
       pub fn load(path: &Path) -> Result<Self, Error> {
           let grammar = Grammar::parse(std::fs::read_to_string(path)?)?;
           let mork = MorkSpace::new();

           for rule in grammar.productions() {
               mork.insert_pattern(rule.lhs(), rule.rhs())?;
           }

           Ok(Self { mork, productions: grammar.productions() })
       }

       /// Check if symbol sequence is valid
       pub fn is_valid(&self, symbols: &[Symbol]) -> bool {
           self.mork.matches_any_pattern(symbols)
       }
   }
   ```

5. **Type predicate storage integration**
   ```rust
   /// Store type predicates in MORK for efficient lookup
   pub struct TypePredicateMork {
       mork: MorkSpace,
       predicates: HashMap<PredicateId, Predicate>,
   }

   impl TypePredicateMork {
       /// Store predicate indexed by applicable sorts
       pub fn insert(&mut self, pred: Predicate) -> PredicateId {
           let id = PredicateId::new();
           let key = self.predicate_key(&pred);
           self.mork.insert(&key, &pred.encode())?;
           self.predicates.insert(id, pred);
           id
       }

       /// Find predicates applicable to a term
       pub fn find_applicable(&self, term: &Term) -> Vec<&Predicate> {
           let sort = term.sort();
           let pattern = self.sort_pattern(&sort);
           self.mork.match_pattern(&pattern)
               .filter_map(|id| self.predicates.get(&id))
               .collect()
       }
   }
   ```

### Validation

- [ ] FuzzySource trait works with PathMap and MORK
- [ ] Candidate lattice correctly represents alternatives
- [ ] Grammar validation filters invalid candidates
- [ ] Type predicates correctly reject ill-typed corrections
- [ ] Three-tier pipeline composes weights correctly
- [ ] Performance acceptable for interactive use (< 100ms)

---

## Phase 6: Rholang Integration

### Goal

Connect MeTTaIL type checking to the Rholang compiler.

### Deliverables

1. **Type checker API**
   ```rust
   pub trait TypeChecker {
       type Error;

       /// Type check an AST
       fn check(&self, ast: &Proc) -> Result<TypedProc, Self::Error>;

       /// Infer types where not annotated
       fn infer(&self, ast: &Proc) -> Result<TypedProc, Self::Error>;
   }

   pub struct MettailTypeChecker {
       theory: GphTheory,
       predicates: PredicateEnv,
       behavioral: BehavioralChecker,
   }
   ```

2. **Compiler integration**
   ```rust
   // In f1r3node/rholang/src/rust/interpreter/compiler/compiler.rs

   pub fn compile_with_types(source: &str) -> Result<Par, CompileError> {
       let ast = parse(source)?;

       // Type check with MeTTaIL
       let checker = MettailTypeChecker::new(rholang_theory());
       let typed = checker.check(&ast)?;

       // Normalize type-checked AST
       normalize(&typed)
   }
   ```

3. **Behavioral type enforcement**
   ```rust
   impl MettailTypeChecker {
       /// Check behavioral type annotations
       fn check_behavioral(&self, proc: &Proc, annotation: &BehavioralType) -> Result<(), TypeError> {
           match annotation {
               BehavioralType::Terminating => {
                   let graph = self.build_graph(proc);
                   if !graph.satisfies(&self.predicates.terminates()) {
                       return Err(TypeError::NonTerminating(proc.span()));
                   }
               }
               BehavioralType::DeadlockFree => {
                   // Check progress property
               }
               BehavioralType::Responsive(channel) => {
                   // Check liveness on channel
               }
           }
           Ok(())
       }
   }
   ```

4. **Gradual typing support**
   ```rust
   pub enum TypingMode {
       Full,      // All code must type check
       Gradual,   // Annotated code checked, rest dynamic
       Infer,     // Infer where possible, dynamic otherwise
       Off,       // No type checking (current behavior)
   }

   impl MettailTypeChecker {
       pub fn with_mode(mode: TypingMode) -> Self {
           // Configure based on mode
       }
   }
   ```

### Validation

- [ ] Existing Rholang code compiles unchanged (mode: Off)
- [ ] Type annotations are parsed correctly
- [ ] Type errors produce clear messages
- [ ] Behavioral types detect violations
- [ ] Performance overhead acceptable

---

## Dependencies

### Phase Dependencies

```
Phase 6 (Rholang Integration)
    └── Phase 5 (WFST Integration) [optional]
    └── Phase 4 (Full OSLF) [optional]
    └── Phase 3 (Behavioral Types)
            └── Phase 2 (Predicates)
                    └── Phase 1 (Gph-theories)
                            └── Current (Basic Types)

Phase 5 (WFST Integration)
    └── Phase 3 (Behavioral Types) [for semantic filtering]
    └── liblevenshtein [external]
    └── MORK/PathMap [external]
```

### External Dependencies

| Dependency | Version | Used By |
|------------|---------|---------|
| Rust | 1.70+ | All phases |
| Ascent | Latest | Phases 2-4 |
| LALRPOP | Latest | Phase 1+ |
| liblevenshtein | Latest | Phase 5 |
| MORK | Latest | Phase 5 |
| PathMap | Latest | Phase 5 |
| f1r3node | main | Phase 6 |
| rholang-parser | main | Phase 6 |

---

## Validation Criteria

### Per-Phase Criteria

| Phase | Success Criteria |
|-------|------------------|
| 1 | SKI and MeTTa examples work, gas tracking correct |
| 2 | Predicates evaluate correctly, Datalog matches direct eval |
| 3 | Behavioral properties detect termination/deadlock |
| 4 | Type theory extraction produces valid rules |
| 5 | WFST pipeline produces correct, typed corrections in < 100ms |
| 6 | Rholang compiles with type checking, no regressions |

### Overall Success Metrics

1. **Correctness**: No false positives or negatives in type checking
2. **Completeness**: All OSLF features implementable
3. **Performance**: < 10% overhead vs untyped compilation
4. **Usability**: Clear error messages, gradual adoption path
5. **Integration**: Seamless Rholang compiler integration
6. **Correction Quality**: Semantic types improve correction accuracy by > 20%

---

## Summary

The implementation roadmap provides:

1. **Layered progression** from simple to complex
2. **Validation checkpoints** at each phase
3. **Clear dependencies** between components
4. **Flexibility** to stop at useful intermediate points
5. **WFST integration** for semantic-aware correction
6. **Rholang integration** as the final compilation target

### Recommended Implementation Order

**Core Path**: Phase 1 → Phase 2 → Phase 3 → Phase 6

This provides behavioral type checking in Rholang without full OSLF complexity.

**With Correction**: Phase 1 → Phase 2 → Phase 3 → Phase 5 → Phase 6

This adds semantic type-aware correction before Rholang integration.

**Full Implementation**: All phases in order

This provides maximum expressiveness including presheaf construction.

The recommended starting point is Phase 1 (Gph-theories) in mettail-rust, building
toward WFST integration in Phase 5 and Rholang integration in Phase 6.

---

## References

- See [gap-analysis.md](../reference/gap-analysis.md) for detailed gap analysis
- See [use-cases.md](../reference/use-cases.md) for validation examples
- See [bibliography.md](../reference/bibliography.md) for complete references
- See [correction-wfst/](../correction-wfst/) for WFST architecture details
