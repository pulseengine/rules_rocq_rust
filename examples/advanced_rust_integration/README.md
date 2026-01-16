# Advanced Rust Integration Example

This example demonstrates **complex Rust patterns** that can be verified using rules_rocq_rust and coq-of-rust.

## What This Example Shows

### 1. Complex Rust Patterns
- **Modules**: Organized code structure with `math`, `data`, and `state_machine` modules
- **Enums**: `Result` and `Option` types with pattern matching
- **Structs**: `List` and `Node` for data structures
- **State Machines**: Traffic light controller with state transitions
- **Algorithms**: GCD, LCM, Fibonacci, prime checking

### 2. Verification Workflow
- **Modular Translation**: Each Rust module translated separately
- **Incremental Verification**: Verify modules individually before combining
- **Complete Testing**: Proof tests for each component
- **Integration**: Combine all verifications for final proof

### 3. Advanced Features
- **Error Handling**: Safe arithmetic with `Option` return types
- **Generic Types**: Generic `List<T>` implementation
- **State Management**: Traffic light state machine with timing
- **Property Testing**: Mathematical properties and algorithms

## Rust Code Structure

```
advanced_rust_integration/
├── lib.rs              # Main library with modules
├── BUILD.bazel         # Build configuration
└── README.md           # This documentation
```

### Modules

1. **`math`**: Mathematical operations
   - `safe_add()`, `safe_sub()`: Overflow-checked arithmetic
   - `gcd()`, `lcm()`: Number theory functions

2. **`data`**: Data structures
   - `Result<T, E>`, `Option<T>`: Custom enum types
   - `List<T>`: Generic linked list implementation

3. **`state_machine`**: State management
   - `TrafficLightController`: State machine with timing
   - State transitions: Red → Green → Yellow → Red

4. **`properties`**: Mathematical properties
   - `is_prime()`: Prime number checking
   - `fibonacci()`: Fibonacci sequence generation

## Build Configuration

### Basic Translation
```bazel
coq_of_rust_library(
    name = "advanced_rust",
    rust_sources = ["lib.rs"],
    edition = "2021",
    include_path = ".",
)
```

### Modular Verification
```bazel
# Translate individual modules
coq_of_rust_library(
    name = "math_module",
    rust_sources = ["lib.rs"],
    edition = "2021",
)

# Verify each module
rocq_library(
    name = "math_verification",
    srcs = [":math_module"],
)

# Test each module
rocq_proof_test(
    name = "math_proof_test",
    srcs = [":math_module"],
    deps = [":math_verification"],
)
```

### Complete Workflow
```bazel
# 1. Translate all Rust code
coq_of_rust_library(
    name = "advanced_rust",
    rust_sources = ["lib.rs"],
    edition = "2021",
)

# 2. Verify the generated Coq
rocq_library(
    name = "complete_verification",
    srcs = [":advanced_rust"],
)

# 3. Test the proofs
rocq_proof_test(
    name = "complete_proof_test",
    srcs = [":advanced_rust"],
    deps = [":complete_verification"],
)
```

## Building and Testing

### Build the translation
```bash
bazel build //examples/advanced_rust_integration:advanced_rust
```

### Build module verifications
```bash
bazel build //examples/advanced_rust_integration:math_verification
bazel build //examples/advanced_rust_integration:data_verification
bazel build //examples/advanced_rust_integration:state_machine_verification
```

### Run proof tests
```bash
bazel test //examples/advanced_rust_integration:math_proof_test
bazel test //examples/advanced_rust_integration:data_proof_test
bazel test //examples/advanced_rust_integration:state_machine_proof_test
bazel test //examples/advanced_rust_integration:complete_proof_test
```

### Run all tests
```bash
bazel test //examples/advanced_rust_integration/...
```

## Key Features Demonstrated

### Rust Language Features
- ✅ **Modules**: Organized code structure
- ✅ **Enums**: Custom result and option types
- ✅ **Structs**: Data structures with generics
- ✅ **Pattern Matching**: Comprehensive match expressions
- ✅ **Error Handling**: Safe arithmetic with Options
- ✅ **State Machines**: Complex state transitions
- ✅ **Algorithms**: Mathematical computations

### Verification Features
- ✅ **Modular Translation**: Focus on specific modules
- ✅ **Incremental Verification**: Verify step by step
- ✅ **Complete Testing**: Proof tests for all components
- ✅ **Integration**: Combine verifications
- ✅ **Configuration**: Custom build settings

### Advanced Patterns
- ✅ **Generic Types**: `List<T>` implementation
- ✅ **Overflow Checking**: Safe arithmetic operations
- ✅ **State Management**: Traffic light controller
- ✅ **Mathematical Properties**: Prime checking, Fibonacci
- ✅ **Data Structures**: Linked list with push/pop

## Best Practices

### 1. Modular Design
Break Rust code into logical modules for easier verification:
```rust
pub mod math { ... }
pub mod data { ... }
pub mod state_machine { ... }
```

### 2. Incremental Verification
Verify modules individually before combining:
```bazel
# Verify math module first
rocq_library(name = "math_verification", srcs = [":math_module"])

# Then verify data module
rocq_library(name = "data_verification", srcs = [":data_module"])

# Finally combine everything
rocq_library(name = "complete", srcs = [":all_modules"])
```

### 3. Comprehensive Testing
Test each component separately:
```bazel
rocq_proof_test(name = "math_test", srcs = [":math_module"])
rocq_proof_test(name = "data_test", srcs = [":data_module"])
rocq_proof_test(name = "complete_test", srcs = [":all_modules"])
```

### 4. Error Handling
Use safe arithmetic and proper error handling:
```rust
pub fn safe_add(a: i32, b: i32) -> Option<i32> {
    a.checked_add(b)  // Returns None on overflow
}
```

## Advanced Usage Patterns

### With rules_rust Integration
```bazel
# When you have rules_rust set up
coq_of_rust_library(
    name = "with_rules_rust",
    rust_deps = [":my_rust_crate"],  # rules_rust target
    edition = "2021",               # Auto-detected from crate
)
```

### Different Rust Editions
```bazel
coq_of_rust_library(
    name = "rust_2018",
    rust_sources = ["legacy.rs"],
    edition = "2018",
)
```

### Custom Configurations
```bazel
coq_of_rust_library(
    name = "custom",
    rust_sources = ["lib.rs"],
    edition = "2021",
    include_path = "src",
    # Other custom settings
)
```

## Troubleshooting

### Common Issues

**Issue**: `coq-of-rust not found`
**Solution**: Ensure coq-of-rust toolchain is set up in MODULE.bazel

**Issue**: `rules_rust not available`
**Solution**: Add rules_rust to your dependencies and register toolchains

**Issue**: `Verification failed`
**Solution**: Check the generated Coq code for syntax errors

**Issue**: `Proof test failed`
**Solution**: Ensure all proofs in the Coq code complete with Qed

## Next Steps

1. **Set up rules_rust** for full integration
2. **Try with real Rust crates** from your projects
3. **Explore more complex patterns** (async, traits, macros)
4. **Add property-based testing** with QuickChick
5. **Integrate with CI/CD** for automated verification

This example provides a **comprehensive foundation** for advanced Rust verification using rules_rocq_rust!
