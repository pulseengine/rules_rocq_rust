<div align="center">

# rules_rocq_rust

<sup>Bazel rules for Rocq theorem proving and Rust formal verification</sup>

&nbsp;

![Bazel](https://img.shields.io/badge/Bazel-43A047?style=flat-square&logo=bazel&logoColor=white&labelColor=1a1b27)
![Rocq](https://img.shields.io/badge/Rocq-9.0-A44E9C?style=flat-square&labelColor=1a1b27)
![License: Apache-2.0](https://img.shields.io/badge/License-Apache--2.0-blue?style=flat-square&labelColor=1a1b27)

</div>

&nbsp;

Bazel rules for Rocq theorem proving and Rust formal verification with hermetic toolchain support via [Nix](https://nixos.org/).

> [!NOTE]
> Part of the PulseEngine toolchain. Powers the mechanized proofs in Meld, Loom, and PulseEngine verification infrastructure.

## Features

- **Rust to Rocq to Proofs**: Complete pipeline from Rust code to verified proofs
- **rocq-of-rust Integration**: Translate Rust to Rocq via [rocq-of-rust](https://github.com/formal-land/rocq-of-rust)
- **Hermetic Toolchains**: Rocq 9.0, coqutil, Hammer, smpl via nixpkgs
- **Cross-Platform**: Linux, macOS (Intel and Apple Silicon)
- **Bazel 8 bzlmod**: Modern module system support

## Prerequisites

### Nix (Required)

```bash
# macOS
sh <(curl -L https://nixos.org/nix/install)
. /nix/var/nix/profiles/default/etc/profile.d/nix-daemon.sh

# Linux
sh <(curl -L https://nixos.org/nix/install) --daemon
```

### Rust Nightly (Linux only)

On Linux, rocq-of-rust requires Rust nightly with rustc internals:

```bash
rustup toolchain install nightly-2024-12-07
rustup component add rustc-dev rust-src --toolchain nightly-2024-12-07
export LIBRARY_PATH="$(rustc +nightly-2024-12-07 --print sysroot)/lib:$LIBRARY_PATH"
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

# rocq-of-rust is built hermetically with rules_rust, so a consuming module
# must also instantiate the hermetic Rust nightly toolchain and the
# third-party crate set (see docs/rules_rust-migration.md).
bazel_dep(name = "rules_rust", version = "0.70.0")

rust_nightly = use_extension("@rules_rocq_rust//coq_of_rust:extensions.bzl", "rust_nightly_toolchain")
rust_nightly.toolchain(rust_nightly = "nightly-2024-12-07")
use_repo(rust_nightly, "rocq_of_rust_rust_nightly")
register_toolchains("@rocq_of_rust_rust_nightly//:rust_nightly")

crate = use_extension("@rules_rust//crate_universe:extensions.bzl", "crate")
crate.from_cargo(
    name = "rocq_of_rust_crates",
    cargo_lockfile = "@rules_rocq_rust//coq_of_rust/cargo:Cargo.lock",
    manifests = ["@rules_rocq_rust//coq_of_rust/cargo:Cargo.toml"],
)
use_repo(crate, "rocq_of_rust_crates")

# Configure rocq-of-rust
rocq_of_rust = use_extension("@rules_rocq_rust//coq_of_rust:extensions.bzl", "rocq_of_rust")
rocq_of_rust.toolchain(use_real_library = True)
use_repo(rocq_of_rust, "rocq_of_rust_toolchains", "rocq_of_rust_build")
register_toolchains("@rocq_of_rust_toolchains//:toolchain")
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

rocq_rust_verified_library(
    name = "point_verified",
    rust_sources = ["point.rs"],
    extra_flags = ["-impredicative-set"],
)

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

| Attribute | Description |
|-----------|-------------|
| `srcs` | Rocq source files (`.v`) |
| `deps` | Dependencies on other `rocq_library` targets |
| `include_path` | Logical path for this library (default: package path) |
| `extra_flags` | Extra flags passed to coqc |

### coq_of_rust_library

Translates Rust source files to Rocq.

| Attribute | Description |
|-----------|-------------|
| `rust_sources` | Rust source files to translate |
| `edition` | Rust edition (default: "2021") |

### rocq_rust_verified_library

Convenience macro: translates Rust to Rocq and compiles.

### rocq_proof_test

Test rule that verifies proofs compile successfully.

## Toolchain Contents

| Component | Description |
|-----------|-------------|
| Rocq 9.0.1 | Core theorem prover |
| coqutil | Utility library |
| Hammer | Automated proof tactics |
| smpl | Simplification tactics |
| Flocq | Floating-point formalization library |
| Coq-Interval | Interval arithmetic / approximation-error bounds, usable via `rocq_interval_proof` (see `rocq:defs.bzl`) -- Coq-Interval's real dependency closure (mathcomp, bignums, hierarchy-builder, coq-elpi) is resolved by a dedicated `coq_9_0.withPackages(...)` environment, not the primary toolchain |
| Coquelicot | Real analysis library (Coq-Interval's dependency) |
| Gappa | Rounding-error prover binary, kernel-checked via `gappa_proof` (see `rocq:defs.bzl`) |
| gappalib-coq | Gappa's Rocq support library (built from source against Flocq) |
| rocq-of-rust | Rust-to-Rocq translator (pinned version) |

## Supported Platforms

| Platform | Status |
|----------|--------|
| Linux x86_64 | Supported |
| Linux aarch64 | Supported |
| macOS x86_64 | Supported |
| macOS aarch64 | Supported |

## Troubleshooting

### "unable to find library -lLLVM-19-rust-*" (Linux)

```bash
export LIBRARY_PATH="$(rustc +nightly-2024-12-07 --print sysroot)/lib:$LIBRARY_PATH"
```

### "rustc-dev component not found"

```bash
rustup component add rustc-dev rust-src --toolchain nightly-2024-12-07
```

## Examples

See `examples/rust_to_rocq/` for a complete working example:

```bash
bazel build //examples/rust_to_rocq:point_proofs
bazel build //examples/rust_to_rocq:advanced_verified
bazel test //examples/rust_to_rocq:point_proofs_test
```

See `examples/gappa_proof/` for a machine-checked floating-point error-bound
proof (Gappa + Flocq), kernel-checked by Rocq:

```bash
bazel test //examples/gappa_proof:rounding_bound_test
```

See `examples/interval_proof/` for a smoke test proving Coq-Interval is
actually usable (`Require Import Interval.Tactic`), not just fetched:

```bash
bazel test //examples/interval_proof:smoke_test
```

## License

Apache-2.0 &mdash; see [LICENSE](LICENSE).

---

<div align="center">

<sub>Part of <a href="https://github.com/pulseengine">PulseEngine</a> &mdash; Bazel rules powering the Rocq theorem-proving toolchain</sub>

</div>
