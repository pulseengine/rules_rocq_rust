# rules_rocq_rust

Bazel rules for Rocq theorem proving and coq-of-rust integration, following the exact patterns established by [rules_rust](https://github.com/bazelbuild/rules_rust) and [rules_wasm_component](https://github.com/pulseengine/rules_wasm_component).

## Features

- **Rocq Integration**: Compile Coq proofs with proper dependency management
- **coq-of-rust Support**: Translate Rust code to Coq for formal verification
- **Bazel 8 bzlmod**: Modern Bazel module system support
- **Hermetic Toolchains**: Download and verify all tools with checksums
- **Enterprise Ready**: Support for air-gap environments and corporate mirrors

## Quick Start

### 1. Add to your MODULE.bazel

```bazel
bazel_dep(name = "rules_rocq_rust", version = "0.1.0")

# Enable Rocq toolchain
rocq = use_extension("@rules_rocq_rust//rocq:extensions.bzl", "rocq")
rocq.toolchain(
    version = "2025.01.0",
    strategy = "download",
)
use_repo(rocq, "rocq_toolchains")

register_toolchains("@rocq_toolchains//:rocq_toolchain")
```

### 2. Use in your BUILD files

```bazel
load("@rules_rocq_rust//rocq:defs.bzl", "rocq_library", "rocq_proof_test")

rocq_library(
    name = "my_theorems",
    srcs = ["theorems.v"],
)

rocq_proof_test(
    name = "my_theorems_test",
    srcs = ["theorems.v"],
    deps = [":my_theorems"],
)
```

## Examples

See the [examples/](examples/) directory for complete working examples:

- `examples/rocq_pure/`: Pure Rocq proof compilation
- `examples/rust_verified/`: Rust code verified with coq-of-rust (coming soon)

## Toolchain Management

The repository uses a centralized JSON-based toolchain management system similar to rules_wasm_component:

- `checksums/tools/rocq.json`: Tool versions and checksums
- `toolchains/tool_registry.bzl`: Unified download and verification logic
- Enterprise support via environment variables:
  - `BAZEL_ROCQ_OFFLINE=1`: Use vendored tools
  - `BAZEL_ROCQ_VENDOR_DIR`: Custom vendor directory
  - `BAZEL_ROCQ_MIRROR`: Corporate mirror URL

## Development

### Testing

```bash
# Run the pure Rocq example
bazel test //examples/rocq_pure:test

# Test basic loading
bazel run //:test_basic
```

### Adding New Tools

1. Add tool information to `checksums/tools/<tool>.json`
2. Add URL pattern to `toolchains/tool_registry.bzl`
3. Create repository rule in `toolchains/<tool>_toolchain.bzl`
4. Add module extension to expose the toolchain

## License

Apache License 2.0 - See [LICENSE](LICENSE) file

## Related Projects

- [rules_rust](https://github.com/bazelbuild/rules_rust) - Rust rules that inspired this structure
- [rules_wasm_component](https://github.com/pulseengine/rules_wasm_component) - WebAssembly rules with similar toolchain patterns
- [Rocq Prover](https://github.com/rocq-prover/platform) - The Rocq theorem prover
- [coq-of-rust](https://github.com/coq-of-rust/coq-of-rust) - Rust to Coq translation tool