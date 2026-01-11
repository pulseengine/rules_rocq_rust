# rules_rocq_rust

Bazel rules for Rocq theorem proving and coq-of-rust integration, following the exact patterns established by [rules_rust](https://github.com/bazelbuild/rules_rust) and [rules_wasm_component](https://github.com/pulseengine/rules_wasm_component).

## Features

- **Rocq Platform Integration**: Complete Coq Platform support with binary installers
- **coq-of-rust Support**: Translate Rust code to Coq for formal verification
- **Bazel 8 bzlmod**: Modern Bazel module system support
- **Hermetic Toolchains**: Download and verify complete Coq Platform installers
- **Enterprise Ready**: Support for air-gap environments and corporate mirrors
- **Cross-Platform**: macOS (arm64), Windows (x86_64), Linux support

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

### Rocq Platform Details

The rules_rocq_rust implementation uses the official [Coq Platform](https://github.com/rocq-prover/platform) binary installers:

- **Complete packages**: Each installer contains Coq compiler, standard library, and tools
- **Multiple versions**: Supports Coq 8.20 (recommended), 8.19, 8.18, etc.
- **Cross-platform**: macOS (arm64), Windows (x86_64), Linux
- **No OCaml required**: The binaries are self-contained

### Enterprise Deployment

For air-gap environments, set these environment variables:

```bash
# Use vendored tools from third_party/toolchains/
export BAZEL_ROCQ_OFFLINE=1

# Or use a custom vendor directory
export BAZEL_ROCQ_VENDOR_DIR=/path/to/vendor

# Or use a corporate mirror
export BAZEL_ROCQ_MIRROR=https://mirror.company.com

### QuickChick Support

QuickChick is a randomized property-based testing framework for Coq that requires OCaml. Since the binary Coq Platform installers don't include OCaml, you need to enable OCaml support separately.

#### Enabling OCaml for QuickChick

Add this to your MODULE.bazel:

```bazel
# Optional OCaml toolchain for QuickChick support
ocaml = use_extension("@rules_rocq_rust//toolchains:ocaml_extensions.bzl", "ocaml")
ocaml.toolchain(
    version = "5.1.1",
        strategy = "download",  # only hermetic downloads supported
)
use_repo(ocaml, "ocaml_toolchains")

register_toolchains("@ocaml_toolchains//:ocaml_toolchain")
```

#### OCaml Strategy

- **download**: Downloads prebuilt OCaml binaries (only strategy supported for hermeticity)

### Enterprise Deployment

For air-gap environments, set these environment variables:

```bash
# Use vendored tools from third_party/toolchains/
export BAZEL_ROCQ_OFFLINE=1

# Or use a custom vendor directory
export BAZEL_ROCQ_VENDOR_DIR=/path/to/vendor

# Or use a corporate mirror
export BAZEL_ROCQ_MIRROR=https://mirror.company.com

# For OCaml (if using QuickChick)
export BAZEL_OCAML_OFFLINE=1
export BAZEL_OCAML_VENDOR_DIR=/path/to/vendor
export BAZEL_OCAML_MIRROR=https://mirror.company.com
```

## License

Apache License 2.0 - See [LICENSE](LICENSE) file

## Related Projects

- [rules_rust](https://github.com/bazelbuild/rules_rust) - Rust rules that inspired this structure
- [rules_wasm_component](https://github.com/pulseengine/rules_wasm_component) - WebAssembly rules with similar toolchain patterns
- [Rocq Prover](https://github.com/rocq-prover/platform) - The Rocq theorem prover
- [coq-of-rust](https://github.com/coq-of-rust/coq-of-rust) - Rust to Coq translation tool