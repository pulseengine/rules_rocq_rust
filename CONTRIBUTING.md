# Contributing to rules_rocq_rust

Thank you for your interest in contributing to rules_rocq_rust! This guide will help you get started.

## Getting Started

### Prerequisites

- Bazel 8.1.0+
- Basic understanding of Bazel rules
- Familiarity with Coq/Rocq theorem proving
- Knowledge of Rust (for coq-of-rust integration)

### Setting Up Your Development Environment

```bash
# Clone the repository
git clone https://github.com/pulseengine/rules_rocq_rust.git
cd rules_rocq_rust

# Install Bazel (if not already installed)
# Follow instructions at https://bazel.build/install

# Test the setup
bazel test //test:test_basic
```

## Development Workflow

### Making Changes

1. **Create a branch** for your changes:
   ```bash
   git checkout -b feature/your-feature-name
   ```

2. **Make your changes** following the existing patterns and style.

3. **Test your changes** thoroughly:
   ```bash
   bazel test //...
   ```

4. **Run the linter** to ensure code quality:
   ```bash
   bazel run @buildifier -- --lint=fix
   ```

5. **Update documentation** if your changes affect the API or usage.

### Submitting Changes

1. **Commit your changes** with a clear commit message:
   ```bash
   git commit -m "Add feature: brief description of changes"
   ```

2. **Push your branch** to GitHub:
   ```bash
   git push origin feature/your-feature-name
   ```

3. **Create a Pull Request** following the template.

## Code Style Guidelines

### Bazel Rules

- Follow the patterns established by `rules_rust` and `rules_wasm_component`
- Use providers for dependency management
- Prefer depsets for transitive dependencies
- Use explicit inputs/outputs for hermetic builds

### Naming Conventions

- Rule names: `snake_case` (e.g., `rocq_library`)
- Function names: `snake_case` (e.g., `rocq_library_impl`)
- Variable names: `snake_case` (e.g., `coq_sources`)
- Constants: `UPPER_SNAKE_CASE` (e.g., `DEFAULT_VERSION`)

### Documentation

- All public rules must have docstrings
- Use triple quotes for multi-line docstrings
- Include examples in documentation
- Document all parameters and return values

## Testing

### Test Structure

- **Unit tests**: Test individual rules in isolation
- **Integration tests**: Test rule combinations
- **Example tests**: Test complete workflows

### Adding Tests

```python
# Example test structure
def test_rocq_library_creation():
    """Test that rocq_library rule can be instantiated."""
    # Test implementation
    pass
```

### Running Tests

```bash
# Run all tests
bazel test //...

# Run specific test
bazel test //test:specific_test

# Run with verbose output
bazel test --verbose_failures //...
```

## Architecture Overview

### Core Components

1. **Rocq Rules**: Core Coq compilation and proof checking
2. **coq-of-rust Integration**: Rust to Coq translation
3. **Toolchain Management**: Hermetic tool downloads and management
4. **Module Extensions**: Bazel 8 bzlmod support

### Key Files

- `rocq/defs.bzl`: Public Rocq API
- `coq_of_rust/defs.bzl`: Public coq-of-rust API
- `toolchains/tool_registry.bzl`: Toolchain management
- `examples/`: Working examples

## Common Tasks

### Adding a New Rule

1. Create implementation in `private/` directory
2. Export public API in `defs.bzl`
3. Add tests in `test/` directory
4. Update documentation

### Adding a New Tool

1. Add tool info to `checksums/tools/<tool>.json`
2. Add URL pattern to `toolchains/tool_registry.bzl`
3. Create repository rule in `toolchains/<tool>_toolchain.bzl`
4. Add module extension

## Community

### Reporting Issues

- Use the GitHub issue tracker
- Provide reproduction steps
- Include error messages and logs
- Check existing issues before creating new ones

### Getting Help

- Check the documentation
- Look at existing examples
- Review similar projects (rules_rust, rules_wasm_component)
- Ask questions in pull requests

## Code of Conduct

This project follows the [Contributor Covenant](https://www.contributor-covenant.org/) code of conduct. Please be respectful and considerate in all interactions.

## License

By contributing to this project, you agree that your contributions will be licensed under the Apache License 2.0.

Thank you for contributing to rules_rocq_rust!