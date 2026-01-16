# Rules Rocq Rust Examples

This directory contains comprehensive examples demonstrating how to use the rules_rocq_rust toolchain for formal verification of Rust code using Coq.

## Example Structure

### 1. Pure Rocq Example (`rocq_pure/`)

**Purpose**: Demonstrates basic Rocq theorem proving without Rust integration.

**Files**:
- `simple.v`: Basic Coq proofs about natural numbers
- `BUILD.bazel`: Shows how to compile and test Coq proofs

**Usage**:
```bash
bazel test //examples/rocq_pure:test
```

### 2. Rust Verification Example (`rust_verified/`)

**Purpose**: Demonstrates the complete Rust verification workflow:
1. Rust source code
2. Translation to Coq using coq-of-rust
3. Proof verification using Rocq
4. Manual verification proofs

**Files**:
- `simple_rust.rs`: Rust code to be verified
- `verification_proofs.v`: Manual proofs about the Rust code behavior
- `BUILD.bazel`: Complete build configuration

**Usage**:
```bash
# Test the full workflow (Rust -> Coq -> Proof verification)
bazel test //examples/rust_verified:test

# Test manual verification proofs
bazel test //examples/rust_verified:test_verification

# Test everything
bazel test //examples/rust_verified:test_all
```

## Workflow Overview

### Step 1: Write Rust Code
```rust
// simple_rust.rs
pub struct Point {
    pub x: i32,
    pub y: i32,
}

impl Point {
    pub fn new(x: i32, y: i32) -> Self {
        Point { x, y }
    }
    
    pub fn add(&self, other: &Point) -> Point {
        Point {
            x: self.x + other.x,
            y: self.y + other.y,
        }
    }
}
```

### Step 2: Translate to Coq
The `coq_of_rust_library` rule translates Rust code to Coq:

```bazel
coq_of_rust_library(
    name = "rust_code_translated",
    rust_sources = ["simple_rust.rs"],
    edition = "2021",
)
```

### Step 3: Compile Generated Coq
```bazel
rocq_library(
    name = "rust_code_compiled",
    srcs = [":rust_code_translated"],
    deps = [
        "@coq_of_rust_toolchains//:prelude",
        "@coq_of_rust_toolchains//:types",
    ],
)
```

### Step 4: Verify Proofs
```bazel
rocq_proof_test(
    name = "rust_code_proofs_test",
    srcs = [":rust_code_translated"],
    deps = [":rust_code_compiled"],
)
```

### Step 5: Add Manual Verification Proofs
```coq
(** verification_proofs.v *)
Require Import RustCode.

Theorem point_add_comm : forall p1 p2,
  p1.add(p2) = p2.add(p1).
Proof.
  (* Proof goes here *)
Qed.
```

## Toolchain Setup

To use these examples, ensure your `MODULE.bazel` includes:

```bazel
bazel_dep(name = "rules_rocq_rust", version = "0.1.0")

# Enable Rocq toolchain
rocq = use_extension("@rules_rocq_rust//rocq:extensions.bzl", "rocq")
rocq.toolchain(
    version = "2025.01.0",
    strategy = "download",
)
use_repo(rocq, "rocq_toolchains")

# Enable coq-of-rust toolchain
coq_of_rust = use_extension("@rules_rocq_rust//coq_of_rust:extensions.bzl", "coq_of_rust")
coq_of_rust.toolchain(
    version = "0.5.0",
    strategy = "build",
)
use_repo(coq_of_rust, "coq_of_rust_toolchains")

register_toolchains(
    "@rocq_toolchains//:rocq_toolchain",
    "@coq_of_rust_toolchains//:coq_of_rust_toolchain",
)
```

## Enterprise Deployment

For air-gap environments, use the vendor workflow:

```bash
# Download all toolchains
./scripts/vendor_toolchains.sh

# Set offline mode
export BAZEL_ROCQ_OFFLINE=1

# Build without internet
bazel build //examples/rust_verified:test
```

## Key Concepts Demonstrated

1. **Toolchain Integration**: How to set up Rocq and coq-of-rust toolchains
2. **Rust to Coq Translation**: Using coq-of-rust to translate Rust code
3. **Proof Verification**: Verifying generated and manual proofs
4. **Dependency Management**: Proper dependency handling between Rust and Coq
5. **Enterprise Support**: Air-gap and corporate mirror configurations

## Future Enhancements

As the coq-of-rust project matures, these examples will be updated to:
- Use the official coq-of-rust repository
- Support more complex Rust features
- Include more sophisticated verification patterns
- Add integration with other verification tools

## PulseEngine Integration Examples

**Location**: `pulseengine_integration/`

**Description**: Comprehensive examples for integrating with pulseengine repositories.

**Sub-examples**:
- `loom_example/`: WebAssembly optimization algorithm verification
- `wsc_example/`: Cryptographic algorithm verification with coq-of-rust
- `wrt2_example/`: WebAssembly runtime verification (Bazel migration)

**Features**:
- Repository-specific integration patterns
- Real-world verification scenarios
- Complete workflow demonstrations
- Best practices for each repository

**Usage**:
```bash
# Test all pulseengine integration examples
bazel test //examples/pulseengine_integration:test_all

# Test specific repository integration
bazel test //examples/pulseengine_integration:test_loom
bazel test //examples/pulseengine_integration:test_wsc
```

For more details, see the [pulseengine integration README](pulseengine_integration/README.md).