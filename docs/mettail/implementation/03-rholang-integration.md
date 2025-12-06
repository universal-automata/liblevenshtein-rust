# Rholang Integration

This document describes the current MeTTa-Rholang integration via the mettatron
crate and the architecture for MeTTaIL as Rholang's next-generation type system.

**Location**: `/home/dylon/Workspace/f1r3fly.io/f1r3node/` (branches: `new_parser`, `dylon/mettatron`)

---

## Table of Contents

1. [Current Architecture](#current-architecture)
2. [Existing MeTTa Integration](#existing-metta-integration)
3. [Type System Opportunity](#type-system-opportunity)
4. [Integration Architecture](#integration-architecture)
5. [Critical Files](#critical-files)
6. [Migration Path](#migration-path)

---

## Current Architecture

### Rholang Implementation Layers

The Rholang implementation in f1r3node follows a layered architecture:

```
┌─────────────────────────────────────────────────────────────────┐
│                     Layer 1: Parser & AST                       │
│  ┌──────────────────────────────────────────────────────────┐  │
│  │  rholang-rs/rholang-parser/                              │  │
│  │  - Tree-sitter based parser                              │  │
│  │  - AST with source span tracking                         │  │
│  │  - Types: Proc<'ast>, AnnProc                            │  │
│  └──────────────────────────────────────────────────────────┘  │
└─────────────────────────────────────────────────────────────────┘
                               │
                               ▼
┌─────────────────────────────────────────────────────────────────┐
│                  Layer 2: Compiler & Normalizer                 │
│  ┌──────────────────────────────────────────────────────────┐  │
│  │  f1r3node/rholang/src/rust/interpreter/compiler/         │  │
│  │  - normalize.rs (36,701 lines)                           │  │
│  │  - compiler.rs (5,260 lines)                             │  │
│  │  - Transforms AST to normalized Par representation       │  │
│  └──────────────────────────────────────────────────────────┘  │
└─────────────────────────────────────────────────────────────────┘
                               │
                               ▼
┌─────────────────────────────────────────────────────────────────┐
│                    Layer 3: Interpreter                         │
│  ┌──────────────────────────────────────────────────────────┐  │
│  │  f1r3node/rholang/src/rust/interpreter/                  │  │
│  │  - reduce.rs (3,962 lines) - DebruijnInterpreter         │  │
│  │  - system_processes.rs - Built-in contracts              │  │
│  │  - RHO calculus execution                                │  │
│  └──────────────────────────────────────────────────────────┘  │
└─────────────────────────────────────────────────────────────────┘
                               │
                               ▼
┌─────────────────────────────────────────────────────────────────┐
│                      Layer 4: RSpace                            │
│  ┌──────────────────────────────────────────────────────────┐  │
│  │  Tuple space for channel communication                   │  │
│  │  - Pattern matching on channels                          │  │
│  │  - Persistent storage                                    │  │
│  └──────────────────────────────────────────────────────────┘  │
└─────────────────────────────────────────────────────────────────┘
```

### Current Type System

Rholang currently uses **dynamic typing** with runtime extraction:

```rust
/// Type extractor trait (from rho_type.rs)
pub trait Extractor<RhoType> {
    type RustType;

    /// Try to extract a Rust value from a Par
    fn unapply(p: &Par) -> Option<Self::RustType>;
}
```

Built-in types include:

| Type | Description | Rust Mapping |
|------|-------------|--------------|
| `RhoBoolean` | Boolean values | `bool` |
| `RhoString` | String values | `String` |
| `RhoNumber` | Numeric values | Varies |
| `RhoByteArray` | Byte sequences | `Vec<u8>` |
| `RhoNil` | Nil value | `()` |
| `RhoUri` | URI references | `String` |
| `RhoName` | Channel names | `Par` |
| `RhoUnforgeable` | Private names | Generated |

**Key limitation**: No compile-time type checking. Type errors manifest as runtime
pattern match failures.

---

## Existing MeTTa Integration

The `dylon/mettatron` branch already integrates MeTTa with Rholang.

### System Process Imports

```rust
// From system_processes.rs
use mettatron::{
    backend::compile as metta_compile_src,
    metta_state_to_pathmap_par,
    metta_error_to_par
};
```

### Integration Points

| Component | Status | Purpose |
|-----------|--------|---------|
| `rho:metta:compile` | ✅ Active | Compile MeTTa source to Par |
| PathMap conversion | ✅ Active | MeTTa state ↔ Rholang Par |
| Pretty printer | ✅ Active | Large expression handling |
| Environment fields | ✅ Active | Multiplicities support |

### The `rho:metta:compile` Contract

This system contract compiles MeTTa source code:

```rholang
new compile(`rho:metta:compile`) in {
  compile!("(= (add $x $y) (+ $x $y))", *result) |
  for (@compiled <- result) {
    // compiled is the MeTTa knowledge base as Par
  }
}
```

### PathMap Bridge

PathMap provides bidirectional conversion between MeTTa states and Rholang:

```rust
/// Convert MeTTa state to Rholang Par via PathMap
pub fn metta_state_to_pathmap_par(state: &MettaState) -> Result<Par, Error> {
    let pathmap = state.to_pathmap()?;
    pathmap.to_par()
}

/// Convert Rholang Par back to MeTTa state
pub fn par_to_metta_state(par: &Par) -> Result<MettaState, Error> {
    let pathmap = PathMap::from_par(par)?;
    pathmap.to_metta_state()
}
```

This enables MeTTa and Rholang to share data seamlessly.

---

## Type System Opportunity

### Why MeTTaIL for Rholang?

Since MeTTaIL will become the next version of Rholang:

1. **Compile-time safety**: Catch type errors before execution
2. **Behavioral types**: Verify process properties (deadlock freedom, etc.)
3. **Namespace security**: Enforce channel access restrictions
4. **Performance**: Eliminate runtime type checks where possible

### Proposed Architecture

```
┌─────────────────────────────────────────────────────────────────┐
│                    MeTTaIL Type Layer                           │
│  ┌─────────────────┐  ┌─────────────────┐  ┌─────────────────┐ │
│  │ Gph-theories    │  │ OSLF Predicates │  │ Behavioral      │ │
│  │ (operational)   │  │ (structural)    │  │ Types           │ │
│  └────────┬────────┘  └────────┬────────┘  └────────┬────────┘ │
│           │                    │                     │          │
│           └────────────────────┼─────────────────────┘          │
│                                ▼                                │
│                    ┌───────────────────┐                        │
│                    │   Type Checker    │                        │
│                    │  (compile-time)   │                        │
│                    └─────────┬─────────┘                        │
└──────────────────────────────┼──────────────────────────────────┘
                               │
                               ▼
┌─────────────────────────────────────────────────────────────────┐
│                    Rholang Compilation                          │
│  ┌──────────────────────────────────────────────────────────┐  │
│  │  Type-checked AST → Normalizer → Par                     │  │
│  └──────────────────────────────────────────────────────────┘  │
└─────────────────────────────────────────────────────────────────┘
                               │
                               ▼
┌─────────────────────────────────────────────────────────────────┐
│                    Rholang Execution                            │
│  ┌──────────────────────────────────────────────────────────┐  │
│  │  DebruijnInterpreter (reduce.rs)                         │  │
│  │  - RHO calculus reduction                                │  │
│  │  - System processes                                      │  │
│  │  - RSpace integration                                    │  │
│  └──────────────────────────────────────────────────────────┘  │
└─────────────────────────────────────────────────────────────────┘
```

### Type Check Insertion Point

The type checker inserts between parsing and normalization:

```rust
// In compiler/compiler.rs

pub fn compile(source: &str) -> Result<Par, CompileError> {
    // 1. Parse to AST
    let ast = parse(source)?;

    // 2. NEW: Type check with MeTTaIL
    let typed_ast = mettail::type_check(&ast)?;

    // 3. Normalize to Par
    let par = normalize(&typed_ast)?;

    Ok(par)
}
```

---

## Integration Architecture

### Detailed Type Flow

```
┌──────────────────────────────────────────────────────────────────┐
│                          Source Code                             │
│  contract Foo(@x: Int, return: Name[Int]) = { return!(x + 1) }   │
└────────────────────────────┬─────────────────────────────────────┘
                             │ Parse
                             ▼
┌──────────────────────────────────────────────────────────────────┐
│                             AST                                  │
│  Contract { name: "Foo", params: [...], body: ... }              │
└────────────────────────────┬─────────────────────────────────────┘
                             │ Type Check (MeTTaIL)
                             ▼
┌──────────────────────────────────────────────────────────────────┐
│                         Typed AST                                │
│  Contract {                                                      │
│    name: "Foo",                                                  │
│    params: [(x, Int), (return, Name[Int])],                      │
│    body: ... : Unit,                                             │
│    well_typed: true                                              │
│  }                                                               │
└────────────────────────────┬─────────────────────────────────────┘
                             │ Normalize
                             ▼
┌──────────────────────────────────────────────────────────────────┐
│                            Par                                   │
│  (with type annotations stripped or preserved as needed)         │
└────────────────────────────┬─────────────────────────────────────┘
                             │ Execute
                             ▼
┌──────────────────────────────────────────────────────────────────┐
│                         RSpace                                   │
└──────────────────────────────────────────────────────────────────┘
```

### Type Annotations in Rholang Syntax

Proposed syntax extensions for typed Rholang:

```rholang
// Type-annotated parameters
contract transfer(@from: Address, @to: Address, @amount: Int, return: Name[Bool]) = {
  ...
}

// Channel types
new chan: Name[Int] in {
  chan!(42) | for(@x: Int <- chan) { ... }
}

// Behavioral type annotations
@deadlock-free
contract server(requests: Name[Request]) = {
  ...
}
```

### Behavioral Type Examples

```rholang
// Type: Always responds on return channel
@responsive
contract query(@key: String, return: Name[Option[Value]]) = {
  // Must send exactly one message on return
}

// Type: Never sends on channels outside namespace
@isolated(internal)
contract worker(internal: Namespace) = {
  // Can only communicate within internal.*
}

// Type: Terminates
@terminating
contract compute(@input: Data, return: Name[Result]) = {
  // Must reach a final state
}
```

---

## Critical Files

### Compiler Integration Points

| File | Lines | Role |
|------|-------|------|
| `compiler/compiler.rs` | 5,260 | Main compilation entry point |
| `compiler/normalize.rs` | 36,701 | AST to Par transformation |
| `reduce.rs` | 3,962 | Interpreter (DebruijnInterpreter) |
| `system_processes.rs` | Large | Built-in contracts, MeTTa bridge |
| `rho_type.rs` | — | Runtime type extractors |

### Key Modification Points

**compiler/compiler.rs**:
```rust
// Insert type checking phase
pub fn compile_typed(source: &str, types: &TypeEnv) -> Result<TypedPar, Error> {
    let ast = parse(source)?;
    let typed = mettail::check(&ast, types)?;  // NEW
    normalize_typed(&typed)
}
```

**compiler/normalize.rs**:
```rust
// Propagate type information during normalization
fn normalize_proc(&self, proc: &TypedProc) -> Result<Par, NormError> {
    // Type info available for optimization decisions
    match proc {
        TypedProc::Send { chan, data, ty } => {
            // Use type to optimize representation
        }
        ...
    }
}
```

**reduce.rs**:
```rust
// Runtime type enforcement (optional, for gradual typing)
fn reduce_send(&mut self, send: &Send) -> Result<(), ReduceError> {
    if let Some(expected_ty) = send.channel_type() {
        let actual_ty = self.infer_type(&send.data)?;
        if !self.is_subtype(&actual_ty, &expected_ty) {
            return Err(ReduceError::TypeMismatch { expected_ty, actual_ty });
        }
    }
    // Continue with normal reduction
    ...
}
```

---

## Migration Path

### Phase 1: Optional Type Annotations

Add syntax support without enforcement:

```rholang
// Types are parsed but not enforced
contract foo(@x: Int) = { ... }  // Works even if x is a string
```

### Phase 2: Type Inference

Infer types where annotations are missing:

```rholang
// x inferred as Int from usage
contract foo(@x) = { return!(x + 1) }
```

### Phase 3: Gradual Checking

Type check annotated code, allow untyped:

```rholang
// This is checked
contract foo(@x: Int): Int = { x + 1 }

// This runs dynamically
contract bar(@x) = { x + 1 }
```

### Phase 4: Full Enforcement

All code must type check:

```rholang
// Error: x must have type annotation or be inferable
contract foo(@x) = { return!(x + 1) }
```

### Compatibility Considerations

1. **Existing code**: Must continue to work (gradual migration)
2. **Runtime behavior**: Unchanged for well-typed code
3. **Error messages**: Clear, actionable type errors
4. **Performance**: No regression for untyped code

---

## Summary

Rholang integration with MeTTaIL involves:

1. **Existing mettatron bridge** for MeTTa ↔ Rholang conversion
2. **Type layer insertion** between parsing and normalization
3. **Gradual migration path** from dynamic to static typing
4. **Behavioral types** for process property verification

The infrastructure is largely in place; the main work is implementing the type
checker in mettail-rust and connecting it to the Rholang compiler.

---

## References

- f1r3node source: `/home/dylon/Workspace/f1r3fly.io/f1r3node/`
- rholang-rs parser: `/home/dylon/Workspace/f1r3fly.io/rholang-rs/rholang-parser/`
- mettatron crate: Integrated in `dylon/mettatron` branch
- See [bibliography.md](../reference/bibliography.md) for complete references.
