# Contributing to liblevenshtein-rust

Thank you for your interest in contributing to liblevenshtein-rust!

## Development Setup

### Prerequisites

- Rust 1.70 or later
- Git

### Building

The project requires CPU features (AES, SSE2) due to PathMap dependencies:

```bash
export RUSTFLAGS="-C target-cpu=native"
cargo build
```

Or use the provided script:

```bash
./scripts/build.sh  # If added
```

### Running Tests

```bash
RUSTFLAGS="-C target-cpu=native" cargo test
```

### Running Examples

```bash
RUSTFLAGS="-C target-cpu=native" cargo run --example spell_checker
```

### Benchmarks

```bash
RUSTFLAGS="-C target-cpu=native" cargo bench
```

## Code Style

- Follow Rust standard formatting (`cargo fmt`)
- Ensure clippy passes (`cargo clippy`)
- Add documentation for public APIs
- Include tests for new functionality

## Pull Request Process

1. Fork the repository
2. Create a feature branch (`git checkout -b feature/amazing-feature`)
3. Make your changes
4. Add tests
5. Ensure all tests pass
6. Update documentation as needed
7. Commit your changes (`git commit -m 'Add amazing feature'`)
8. Push to the branch (`git push origin feature/amazing-feature`)
9. Open a Pull Request

## Areas for Contribution

See [FUTURE_ENHANCEMENTS.md](FUTURE_ENHANCEMENTS.md) for planned features.

### High Priority

- Complete Transposition algorithm implementation
- Add priority queue for ordered results
- Improve test coverage
- Performance optimizations

### Medium Priority

- Alternative dictionary backends
- Serialization support
- Extended examples
- Benchmarking suite

### Documentation

- API documentation improvements
- Usage tutorials
- Performance guides
- Algorithm comparisons

## Questions?

Open an issue on GitHub!

## License

By contributing, you agree that your contributions will be licensed under the Apache License 2.0.
