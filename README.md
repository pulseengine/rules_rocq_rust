# rules_rocq_rust

Bazel rules for Rocq/Coq theorem proving and Rust formal verification with hermetic toolchain support via [Nix](https://nixos.org/).

## Features

- **Rust → Rocq → Proofs**: Complete pipeline from Rust code to verified proofs
- **rocq-of-rust Integration**: Translate Rust to Rocq via [rocq-of-rust](https://github.com/formal-land/rocq-of-rust)
- **Hermetic Toolchains**: Rocq 9.0, coqutil, Hammer, smpl via nixpkgs
- **Cross-Platform**: Linux, macOS (Intel & Apple Silicon)
- **Bazel 8 bzlmod**: Modern module system support

## Prerequisites: Installing Nix

**Nix is required** for the Rocq toolchain.

### macOS

```bash
sh <(curl -L https://nixos.org/nix/install)
. /nix/var/nix/profiles/default/etc/profile.d/nix-daemon.sh
nix --version
```

### Linux

```bash
sh <(curl -L https://nixos.org/nix/install) --daemon
nix --version
```

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
load("@rules_rocq_rust//coq_of_rust:defs.bzl", "coq_of_rust_library")
load("@rules_rocq_rust//rocq:defs.bzl", "rocq_library")

# Translate Rust to Rocq
coq_of_rust_library(
    name = "point_translated",
    rust_sources = ["point.rs"],
    edition = "2021",
)

# Compile translated Rocq code
rocq_library(
    name = "point_compiled",
    srcs = [":point_translated"],
    deps = ["@rocq_of_rust_source//:rocq_of_rust_main"],
    extra_flags = ["-impredicative-set"],
)

# Write proofs about the Rust code
rocq_library(
    name = "point_proofs",
    srcs = ["point_proofs.v"],
    deps = [":point_compiled", "@rocq_of_rust_source//:rocq_of_rust_main"],
    extra_flags = ["-impredicative-set"],
)
```

### 4. Build and verify

```bash
# Translate and compile
bazel build //:point_compiled

# Verify proofs
bazel build //:point_proofs
```

## Example

See `examples/rust_to_rocq/` for a complete working example with:
- `point.rs` - Rust source code
- Translated `point.v` (auto-generated)
- `point_proofs.v` - Formal proofs about the Rust code

```bash
# Build the example
bazel build //examples/rust_to_rocq:point_proofs
```

## How It Works

1. **rocq-of-rust** translates Rust source to Rocq using a deeply embedded monadic DSL
2. **coqc** compiles the translated `.v` files with the RocqOfRust library
3. You write proofs in Rocq that reason about the translated Rust semantics
4. Proofs are machine-checked by the Rocq type system

## Toolchain Contents

The nixpkgs-based toolchain provides:

| Component | Description |
|-----------|-------------|
| Rocq 9.0 | Core theorem prover |
| coqutil | Utility library |
| Hammer | Automated proof tactics |
| smpl | Simplification tactics |
| rocq-of-rust | Rust-to-Rocq translator |

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
