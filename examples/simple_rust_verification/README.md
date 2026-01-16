# Simple Rust Verification Example

This example demonstrates how to use rules_rocq_rust to verify Rust code using coq-of-rust.

## What This Example Shows

1. **Rust to Coq Translation**: The `simple.rs` file contains Rust functions that are translated to Coq
2. **coq-of-rust Integration**: Shows how to use the `coq_of_rust_library` rule
3. **Verification Workflow**: Demonstrates the complete verification process
4. **rules_rust Integration**: Shows how to connect with rules_rust (commented out)

## Files

- `simple.rs`: Rust source code with functions to verify
- `BUILD.bazel`: Build configuration showing different usage patterns
- `README.md`: This file

## Rust Functions Demonstrated

- `add()`: Simple arithmetic function
- `is_even()`: Boolean logic function
- `factorial()`: Recursive function
- `describe_number()`: Pattern matching function

## Usage Patterns Shown

### Basic Translation
```bazel
coq_of_rust_library(
    name = "simple_rust",
    rust_sources = ["simple.rs"],
    edition = "2021",
)
```

### With Include Path
```bazel
coq_of_rust_library(
    name = "rust_with_functions",
    rust_sources = ["simple.rs"],
    edition = "2021",
    include_path = ".",
)
```

### With rules_rust Integration (requires rules_rust setup)
```bazel
coq_of_rust_library(
    name = "rust_with_crates",
    rust_deps = [":some_rust_crate"],
    edition = "2021",
)
```

## Building

```bash
# Build the coq-of-rust translation
bazel build //examples/simple_rust_verification:simple_rust

# Build the verification
bazel build //examples/simple_rust_verification:simple_verification

# Run the proof tests
bazel test //examples/simple_rust_verification:simple_verification_test
```

## Key Features Demonstrated

- ✅ Rust to Coq translation with coq-of-rust
- ✅ Multiple function types (arithmetic, boolean, recursive, pattern matching)
- ✅ Edition specification (Rust 2021)
- ✅ Include path support
- ✅ Integration with Rocq verification
- ✅ Proof testing workflow

## Next Steps

1. Set up rules_rust for full integration
2. Try with more complex Rust projects
3. Explore advanced verification patterns
4. Add property-based testing with QuickChick

This example provides a foundation for Rust verification using rules_rocq_rust!
