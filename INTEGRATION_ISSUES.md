# Rocq/coq-of-rust Integration Issues for pulseengine Repositories

This document contains the GitHub issues that should be created for each repository to adopt Rocq and coq-of-rust formal verification.

## Issue for loom Repository

**Title**: "Add Rocq formal verification support using rules_rocq_rust"

**Description**:
```markdown
### Context
The loom repository currently uses Rust for WebAssembly optimization. We should add formal verification capabilities using Rocq (Coq) to prove correctness of critical algorithms.

### Proposal
1. **Add rules_rocq_rust dependency** to MODULE.bazel:
   ```bazel
   bazel_dep(name = "rules_rocq_rust", version = "0.1.0")
   
   rocq = use_extension("@rules_rocq_rust//rocq:extensions.bzl", "rocq")
   rocq.toolchain(version = "2025.01.0")
   use_repo(rocq, "rocq_toolchains")
   ```

2. **Create Rocq proofs** for critical algorithms:
   - Add `proofs/` directory for Coq proofs
   - Create `.v` files proving algorithm correctness
   - Use `rocq_library` and `rocq_proof_test` rules

3. **Integrate with CI** to run proof checks

### Benefits
- Formal verification of optimization algorithms
- Mathematical proofs of correctness
- Integration with existing Rust codebase

### Priority
Medium - Important but not blocking current development
```

## Issue for wsc Repository

**Title**: "Add Rocq formal verification and coq-of-rust integration"

**Description**:
```markdown
### Context
WSC is a WebAssembly Signature Component that deals with cryptographic operations and security-critical code. This makes it an excellent candidate for formal verification using:
1. **Rocq** for pure Coq proofs of cryptographic algorithms
2. **coq-of-rust** for verifying Rust implementation correctness

### Proposal

#### Phase 1: Add Rocq support
1. **Add rules_rocq_rust dependency** to MODULE.bazel:
   ```bazel
   bazel_dep(name = "rules_rocq_rust", version = "0.1.0")
   
   rocq = use_extension("@rules_rocq_rust//rocq:extensions.bzl", "rocq")
   rocq.toolchain(version = "2025.01.0")
   use_repo(rocq, "rocq_toolchains")
   ```

2. **Create cryptographic proofs**:
   - Add `proofs/crypto/` directory
   - Prove signature algorithm correctness in Coq
   - Use `rocq_library` for compilation and `rocq_proof_test` for verification

#### Phase 2: Add coq-of-rust for Rust verification
1. **Enable optional OCaml support** (needed for QuickChick):
   ```bazel
   ocaml = use_extension("@rules_rocq_rust//toolchains:ocaml_extensions.bzl", "ocaml")
   ocaml.toolchain(version = "5.1.1")
   use_repo(ocaml, "ocaml_toolchains")
   ```

2. **Verify Rust code with coq-of-rust**:
   - Add `verified/` directory for Rust code with Coq proofs
   - Use `coq_of_rust_library` to translate Rust to Coq
   - Create end-to-end verification with `rocq_rust_proof`

### Benefits
- **Mathematical proofs** of cryptographic algorithm correctness
- **Formal verification** of Rust implementation
- **Enhanced security** through formal methods
- **Integration** with existing rules_wasm_component setup

### Priority
High - Security-critical code should have formal verification

### Dependencies
- rules_rocq_rust v0.1.0+
- Optional: OCaml toolchain for coq-of-rust features
```

## Issue for wrt2 Repository

**Title**: "Migrate to Bazel and add formal verification support"

**Description**:
```markdown
### Context
WRT2 is currently a Cargo-only project. To enable formal verification with Rocq/coq-of-rust, we need to:
1. Migrate to Bazel build system
2. Integrate with rules_rocq_rust

### Proposal

#### Phase 1: Bazel Migration
1. **Create MODULE.bazel** with rules_rust setup
2. **Create WORKSPACE** for legacy support
3. **Migrate Cargo dependencies** to Bazel targets
4. **Set up CI/CD** for Bazel builds

#### Phase 2: Add Rocq Support
1. **Add rules_rocq_rust dependency**
2. **Create proofs** for critical WebAssembly runtime components
3. **Integrate proof checking** into CI

### Benefits
- Enable formal verification capabilities
- Consistent build system with other pulseengine projects
- Future-proof for advanced verification needs

### Priority
Medium - First need Bazel migration, then can add Rocq

### Dependencies
- rules_rust
- rules_rocq_rust
```

## Implementation Recommendations

### For All Repositories

1. **Start with Rocq** (pure Coq proofs) before coq-of-rust
2. **Focus on critical algorithms** first (cryptography, optimization, etc.)
3. **Integrate with CI** to ensure proofs are checked
4. **Document verification process** for contributors

### Repository-Specific

- **loom**: Focus on optimization algorithm correctness
- **wsc**: Focus on cryptographic algorithm verification  
- **wrt2**: First migrate to Bazel, then add verification

## Next Steps

1. Create these issues in respective repositories
2. Prioritize wsc (highest impact for security)
3. Develop example proofs for each repository
4. Create documentation and contribution guides