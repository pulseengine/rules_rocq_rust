# rules_rocq_rust

Bazel rules for Rocq/Coq theorem proving and Rust formal verification with hermetic toolchain support via [Nix](https://nixos.org/).

## Features

- **Rust → Rocq → Proofs**: Complete pipeline from Rust code to verified proofs
- **rocq-of-rust Integration**: Translate Rust to Rocq via [rocq-of-rust](https://github.com/formal-land/rocq-of-rust)
- **Hermetic Toolchains**: Rocq 9.0, coqutil, Hammer, smpl via nixpkgs
- **Cross-Platform**: Linux, macOS (Intel & Apple Silicon)
- **Bazel 8 bzlmod**: Modern module system support

## Prerequisites

### Nix (Required)

Nix is required for the Rocq toolchain.

**macOS:**
```bash
sh <(curl -L https://nixos.org/nix/install)
. /nix/var/nix/profiles/default/etc/profile.d/nix-daemon.sh
nix --version
```

**Linux:**
```bash
sh <(curl -L https://nixos.org/nix/install) --daemon
nix --version
```

### Rust Nightly (Linux only)

On Linux, rocq-of-rust requires Rust nightly with rustc internals:

```bash
# Install nightly toolchain
rustup toolchain install nightly-2024-12-01

# Add required components
rustup component add rustc-dev rust-src --toolchain nightly-2024-12-01

# Set library path for LLVM (add to ~/.bashrc or ~/.zshrc)
export LIBRARY_PATH="$(rustc +nightly-2024-12-01 --print sysroot)/lib:$LIBRARY_PATH"
```

On macOS, Nix provides the complete Rust toolchain automatically.

## Quick Start

### 1. Add to MODULE.bazel

```starlark
bazel_dep(name = "rules_rocq_rust", version = "0.1.0")

git_override(
    module_name = "rules_rocq_rust",
    remote = "https://github.com/pulseengine/rules_rocq_rust.git",
    commit = "<latest-commit>",
)

# Configure Rocq toolchain
rocq = use_extension("@rules_rocq_rust//rocq:extensions.bzl", "rocq")
rocq.toolchain()
use_repo(rocq, "rocq_toolchains", "rocq_stdlib", "rocq_coqutil", "rocq_hammer", "rocq_hammer_tactics", "rocq_smpl")
register_toolchains("@rocq_toolchains//:all")

# Configure rocq-of-rust
rocq_of_rust = use_extension("@rules_rocq_rust//coq_of_rust:extensions.bzl", "rocq_of_rust")
rocq_of_rust.toolchain(use_real_library = True)
use_repo(rocq_of_rust, "rocq_of_rust_toolchains", "rocq_of_rust_source")
register_toolchains("@rocq_of_rust_toolchains//:all")
```

### 2. Create a Rust file to verify

```rust
// point.rs
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Point { pub x: i32, pub y: i32 }

impl Point {
    pub fn origin() -> Self { Point { x: 0, y: 0 } }
    pub fn new(x: i32, y: i32) -> Self { Point { x, y } }
}
```

### 3. Add BUILD.bazel

```starlark
load("@rules_rocq_rust//coq_of_rust:defs.bzl", "rocq_rust_verified_library")
load("@rules_rocq_rust//rocq:defs.bzl", "rocq_library")

# One-liner: translate and compile
rocq_rust_verified_library(
    name = "point_verified",
    rust_sources = ["point.rs"],
    extra_flags = ["-impredicative-set"],
)

# Write proofs about the Rust code
rocq_library(
    name = "point_proofs",
    srcs = ["point_proofs.v"],
    deps = [":point_verified"],
    extra_flags = ["-impredicative-set"],
)
```

### 4. Build and verify

```bash
bazel build //:point_proofs
```

## API Reference

### rocq_library

Compiles Rocq `.v` files to `.vo`.

```starlark
rocq_library(
    name = "my_proofs",
    srcs = ["proof.v"],
    deps = [":other_library"],
    include_path = "MyProject",      # Logical path prefix
    extra_flags = ["-impredicative-set"],
)
```

| Attribute | Description |
|-----------|-------------|
| `srcs` | Rocq source files (`.v`) |
| `deps` | Dependencies on other `rocq_library` targets |
| `include_path` | Logical path for this library (default: package path) |
| `extra_flags` | Extra flags passed to coqc |

### coq_of_rust_library

Translates Rust source files to Rocq.

```starlark
coq_of_rust_library(
    name = "translated",
    rust_sources = ["lib.rs"],
    edition = "2021",
)
```

| Attribute | Description |
|-----------|-------------|
| `rust_sources` | Rust source files to translate |
| `edition` | Rust edition (default: "2021") |

### rocq_rust_verified_library

Convenience macro: translates Rust to Rocq and compiles.

```starlark
rocq_rust_verified_library(
    name = "verified",
    rust_sources = ["lib.rs"],
    edition = "2021",
    deps = [],                       # Additional Rocq dependencies
    extra_flags = ["-impredicative-set"],
)
```

### rocq_proof_test

Test rule that verifies proofs compile successfully.

```starlark
rocq_proof_test(
    name = "proofs_test",
    srcs = ["proofs.v"],
    deps = [":proofs"],
)
```

## Configuration Options

### rocq_of_rust.toolchain()

```starlark
rocq_of_rust.toolchain(
    use_real_library = True,         # Use full RocqOfRust library (recommended)
    fail_on_error = True,            # Fail if rocq-of-rust build fails (default: True)
    rust_nightly = "nightly-2024-12-01",  # Rust nightly version
)
```

| Option | Description |
|--------|-------------|
| `use_real_library` | Use full RocqOfRust library with coqutil/hammer/smpl |
| `fail_on_error` | Fail build if rocq-of-rust cannot be built |
| `rust_nightly` | Rust nightly version for building rocq-of-rust |

## Troubleshooting

### "unable to find library -lLLVM-19-rust-*" (Linux)

The Rust nightly compiler bundles its own LLVM. Set `LIBRARY_PATH`:

```bash
export LIBRARY_PATH="$(rustc +nightly-2024-12-01 --print sysroot)/lib:$LIBRARY_PATH"
```

### "cargo not found"

Install Rust via rustup:

```bash
curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh
```

### "rustc-dev component not found"

Install the required nightly components:

```bash
rustup component add rustc-dev rust-src --toolchain nightly-2024-12-01
```

### Build fails silently with placeholder

By default, builds fail loudly. If you see placeholder output, check the build logs for the actual error. To debug, run:

```bash
bazel build @rocq_of_rust_source//:rocq_of_rust_main --verbose_failures
```

### Proofs fail with "reference not found"

Ensure the translated code compiled successfully first:

```bash
bazel build //:point_compiled
```

Then check that your proof imports match the generated module names.

## Example

See `examples/rust_to_rocq/` for a complete working example:

- `point.rs` - Rust source with Point and Rectangle structs
- `advanced.rs` - Generics, traits, lifetimes, enums
- `point_proofs.v` - Formal proofs about the translated code

```bash
# Build all examples
bazel build //examples/rust_to_rocq:point_proofs
bazel build //examples/rust_to_rocq:advanced_verified

# Run proof tests
bazel test //examples/rust_to_rocq:point_proofs_test
```

## How It Works

1. **rocq-of-rust** translates Rust source to Rocq using a deeply embedded monadic DSL
2. **coqc** compiles the translated `.v` files with the RocqOfRust library
3. You write proofs in Rocq that reason about the translated Rust semantics
4. Proofs are machine-checked by the Rocq type system

## Toolchain Contents

| Component | Description |
|-----------|-------------|
| Rocq 9.0 | Core theorem prover |
| coqutil | Utility library |
| Hammer | Automated proof tactics |
| smpl | Simplification tactics |
| rocq-of-rust | Rust-to-Rocq translator (pinned version) |

## Supported Platforms

| Platform | Status |
|----------|--------|
| Linux x86_64 | ✅ |
| Linux aarch64 | ✅ |
| macOS x86_64 | ✅ |
| macOS aarch64 | ✅ |

## License

Apache License 2.0 - See [LICENSE](LICENSE)

## Related Projects

- [rocq-of-rust](https://github.com/formal-land/rocq-of-rust) - Rust to Rocq translator
- [nixpkgs](https://github.com/NixOS/nixpkgs) - Nix packages
- [Rocq Prover](https://rocq-prover.org/) - The Rocq theorem prover
