# Migrate to Bazel and add formal verification support

## Context

WRT2 is currently a Cargo-only project. To enable formal verification with Rocq/coq-of-rust and align with pulseengine's build system strategy, we need to:

1. Migrate to Bazel build system
2. Integrate with rules_rocq_rust for formal verification

## Proposal

### Phase 1: Bazel Migration

#### 1. Create MODULE.bazel

```bazel
"""Bazel Module for WRT2 - WebAssembly Runtime"""

module(
    name = "wrt",
    version = "0.1.0",
)

# Core dependencies
bazel_dep(name = "rules_rust", version = "0.68.1")
bazel_dep(name = "bazel_skylib", version = "1.8.2")

# Rust toolchain setup
rust = use_extension("@rules_rust//rust:extensions.bzl", "rust")
rust.toolchain(
    edition = "2021",
    extra_target_triples = [
        "wasm32-wasip1",
        "wasm32-wasip2",
    ],
    versions = ["1.75.0"],
)
use_repo(rust, "rust_toolchains")

register_toolchains("@rust_toolchains//:all")

# Crate dependencies
crate = use_extension("@rules_rust//crate_universe:extension.bzl", "crate")
crate.from_cargo(
    name = "wrt_deps",
    cargo_lockfile = "//:Cargo.lock",
    manifests = ["//:Cargo.toml"],
    supported_platform_triples = [
        "x86_64-unknown-linux-gnu",
        "aarch64-unknown-linux-gnu",
        "aarch64-apple-darwin",
        "x86_64-apple-darwin",
        "wasm32-wasip1",
        "wasm32-wasip2",
    ],
)
use_repo(crate, "wrt_deps")
```

#### 2. Create WORKSPACE

```bazel
workspace(name = "wrt")

# Load rules_rust for legacy support
load("@bazel_tools//tools/build_defs/repo:http.bzl", "http_archive")

http_archive(
    name = "rules_rust",
    integrity = "sha256-...",
    urls = ["https://github.com/bazelbuild/rules_rust/releases/download/0.68.1/rules_rust-0.68.1.tar.gz"],
)

load("@rules_rust//rust:repositories.bzl", "rules_rust_dependencies", "rust_register_toolchains")

rules_rust_dependencies()

rust_register_toolchains(
    edition = "2021",
    versions = ["1.75.0"],
    extra_target_triples = [
        "wasm32-wasip1",
        "wasm32-wasip2",
    ],
)
```

#### 3. Migrate Cargo.toml dependencies

For each dependency in Cargo.toml, create a corresponding Bazel target or use crate_universe.

#### 4. Create BUILD.bazel files

Example for `wrt-core`:

```bazel
load("@rules_rust//rust:defs.bzl", "rust_library")

rust_library(
    name = "wrt_core",
    srcs = glob(["src/**/*.rs"]),
    deps = [
        "@wrt_deps//:anyhow",
        "@wrt_deps//:thiserror",
        "@wrt_deps//:wasmtime",
    ],
)
```

### Phase 2: Add Rocq Formal Verification

#### 1. Add rules_rocq_rust dependency

Update `MODULE.bazel`:

```bazel
# Add to dependencies
bazel_dep(name = "rules_rocq_rust", version = "0.1.0")

# Add toolchain setup
rocq = use_extension("@rules_rocq_rust//rocq:extensions.bzl", "rocq")
rocq.toolchain(version = "2025.01.0")
use_repo(rocq, "rocq_toolchains")

register_toolchains("@rocq_toolchains//:rocq_toolchain")
```

#### 2. Create proofs for critical components

```bash
mkdir -p proofs/runtime
mkdir -p proofs/wasm
```

Example: `proofs/runtime/memory.v`

```coq
(** Formal proof of WebAssembly memory model correctness *)
Require Import Arith List.

(** Define memory operations *)
Inductive mem_op : Type :=
  | Load : nat -> mem_op
  | Store : nat -> mem_op
  | Grow : nat -> mem_op.

(** Define memory safety properties *)
Definition safe_operation (op : mem_op) (mem_size : nat) : Prop :=
  match op with
  | Load addr => addr < mem_size
  | Store addr => addr < mem_size
  | Grow delta => True
  end.

(** Theorem: All operations preserve memory safety *)
Theorem memory_safety : forall op mem_size,
  safe_operation op mem_size ->
  (* After operation, memory remains in valid state *)
  True.
Proof.
  (* Proof would go here *)
  Admitted.
```

## Benefits

- **Consistent build system** with other pulseengine projects
- **Enable formal verification** capabilities
- **Better dependency management** with Bazel
- **Faster builds** with Bazel's caching
- **Multi-platform support** out of the box

## Priority

Medium - First need Bazel migration (foundational), then can add Rocq verification

## Implementation Order

1. Create MODULE.bazel and WORKSPACE
2. Migrate Cargo dependencies to Bazel
3. Create BUILD.bazel files for all components
4. Set up CI/CD for Bazel builds
5. Add rules_rocq_rust dependency
6. Create formal proofs for critical components
7. Integrate proof checking into CI

## Dependencies

- rules_rust 0.68.1+
- rules_rocq_rust 0.1.0+ (for Phase 2)
- Bazel 6.0+

## Related

- rules_rocq_rust repository: https://github.com/pulseengine/rules_rocq_rust
- rules_rust documentation: https://bazelbuild.github.io/rules_rust/
- Bazel documentation: https://bazel.build/