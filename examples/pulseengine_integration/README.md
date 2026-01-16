# PulseEngine Integration Examples

This directory contains comprehensive examples demonstrating how to integrate `rules_rocq_rust` with pulseengine repositories for formal verification.

## Overview

These examples show how to add formal verification capabilities to pulseengine's WebAssembly toolchain:

- **loom**: WebAssembly optimization algorithm verification
- **wsc**: Cryptographic algorithm verification with coq-of-rust
- **wrt2**: WebAssembly runtime verification (Bazel migration example)

## loom Integration Example

**Location**: `loom_example/`

**Purpose**: Demonstrates formal verification of WebAssembly optimization algorithms.

**Features**:
- Rocq proofs for optimization algorithm correctness
- Proof validation and testing
- Integration with loom's existing codebase

**Usage**:
```bash
bazel test //examples/pulseengine_integration/loom_example:test
```

## wsc Integration Example

**Location**: `wsc_example/`

**Purpose**: Demonstrates cryptographic algorithm verification using both pure Coq and coq-of-rust.

**Features**:
- Pure Coq proofs for cryptographic algorithms
- Rust code verification using coq-of-rust
- Proof automation with Ltac scripts
- Comprehensive validation workflows

**Usage**:
```bash
bazel test //examples/pulseengine_integration/wsc_example:test
```

## Integration Patterns

### Basic Rocq Integration

```bazel
# Add to your MODULE.bazel
bazel_dep(name = "rules_rocq_rust", version = "0.1.0")

rocq = use_extension("@rules_rocq_rust//rocq:extensions.bzl", "rocq")
rocq.toolchain(version = "2025.01.0")
use_repo(rocq, "rocq_toolchains")

# In your BUILD.bazel
rocq_library(
    name = "my_proofs",
    srcs = ["proofs.v"],
)

rocq_proof_test(
    name = "my_proofs_test",
    srcs = ["proofs.v"],
    deps = [":my_proofs"],
)
```

### Advanced Integration with coq-of-rust

```bazel
# Add coq-of-rust support
coq_of_rust = use_extension("@rules_rocq_rust//coq_of_rust:extensions.bzl", "coq_of_rust")
coq_of_rust.toolchain(version = "0.5.0")
use_repo(coq_of_rust, "coq_of_rust_toolchains")

# Translate Rust to Coq
coq_of_rust_library(
    name = "rust_code_translated",
    rust_sources = ["crypto.rs"],
    edition = "2021",
)

# Verify the generated proofs
rocq_proof_test(
    name = "rust_code_proofs_test",
    srcs = [":rust_code_translated"],
    deps = [":rust_code_compiled"],
)
```

## Testing

### Run All Integration Tests

```bash
bazel test //examples/pulseengine_integration:test_all
```

### Run Specific Repository Tests

```bash
# Test loom integration
bazel test //examples/pulseengine_integration:test_loom

# Test wsc integration
bazel test //examples/pulseengine_integration:test_wsc
```

## Best Practices

### For loom Repository

1. **Focus on optimization algorithms**: Verify critical optimization passes
2. **Start with simple proofs**: Begin with basic properties before complex ones
3. **Integrate with CI**: Add proof checking to your CI pipeline
4. **Document assumptions**: Clearly document what each proof assumes and guarantees

### For wsc Repository

1. **Prioritize security-critical code**: Focus on cryptographic operations first
2. **Use both approaches**: Combine pure Coq proofs with coq-of-rust verification
3. **Add proof automation**: Use Ltac scripts for common proof patterns
4. **Validate thoroughly**: Use comprehensive validation for security proofs

### For wrt2 Repository

1. **Migrate to Bazel first**: Complete Bazel migration before adding verification
2. **Start with core components**: Verify WebAssembly runtime core functionality
3. **Integrate gradually**: Add verification incrementally to existing codebase
4. **Document verification process**: Help contributors understand the verification workflow

## Next Steps

1. **Review the examples**: Study the provided examples for your specific repository
2. **Start small**: Begin with a single proof or verification target
3. **Integrate with CI**: Add proof checking to your continuous integration
4. **Expand gradually**: Add more verification as you gain experience
5. **Contribute back**: Share your integration patterns and improvements

## Support

If you encounter issues or have questions about integration:

1. Check the main [README](../../README.md)
2. Review the [CONTRIBUTING](../../CONTRIBUTING.md) guide
3. Look at existing examples in this directory
4. Create an issue in the GitHub repository

The pulseengine team is available to help with integration questions and provide guidance on formal verification best practices.