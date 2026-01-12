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

# Enable coq-of-rust toolchain (builds from source)
coq_of_rust = use_extension("@rules_rocq_rust//coq_of_rust:extensions.bzl", "coq_of_rust")
coq_of_rust.toolchain(
    version = "0.5.0",
    strategy = "build",  # coq-of-rust must be built from source
)
use_repo(coq_of_rust, "coq_of_rust_toolchains")

# Optional: Enable OCaml toolchain for QuickChick support
ocaml = use_extension("@rules_rocq_rust//toolchains:ocaml_extensions.bzl", "ocaml")
ocaml.toolchain(
    version = "5.1.1",
    strategy = "download",
)
use_repo(ocaml, "ocaml_toolchains")

register_toolchains(
    "@rocq_toolchains//:rocq_toolchain",
    "@coq_of_rust_toolchains//:coq_of_rust_toolchain",
)
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

### Toolchain File Structure

The Rocq toolchain organizes files following the exact patterns established by rules_rust:

```
@rocq_toolchains//
├── bin/                  # Executables (public visibility)
│   ├── coqc              # Coq compiler (main executable)
│   ├── coqtop            # Coq toplevel (interactive REPL)
│   ├── coqide            # Coq IDE (graphical interface)
│   ├── coqdoc            # Documentation generator
│   └── coq*              # All Coq tools (coqtools filegroup)
├── lib/                  # Libraries and standard files
│   └── coq/              # Complete Coq standard library
│       ├── theories/     # Standard theories (.vo files)
│       ├── plugins/      # Coq plugins (.cmxs, .so, .dylib)
│       ├── user-contrib/ # User contributions
│       └── ...           # Other library files
└── BUILD.bazel           # Build file with filegroups
```

### Filegroup Organization

The toolchain provides comprehensive filegroups following rules_rust patterns:

| Filegroup | Contents | Visibility |
|-----------|----------|------------|
| `coqc` | Main Coq compiler | Public |
| `coqtop` | Coq toplevel | Public |
| `coqide` | Coq IDE | Public |
| `coqdoc` | Documentation generator | Public |
| `coqtools` | All Coq tools (`coq*`) | Public |
| `stdlib` | Standard library (.vo, .cmxs) | Public |
| `coq_libraries` | Complete library collection | Public |
| `coq_theories` | Coq theories (.v, .glob) | Public |
| `coq_plugins` | Coq plugins (.cmxs, .so, .dylib) | Public |

### Binary Discovery Process

The toolchain uses a robust binary discovery system:

1. **Primary Locations**: Looks in standard directories first
2. **Fallback Search**: Recursive search if primary fails
3. **Platform-Specific**: Handles macOS, Windows, Linux structures
4. **Comprehensive Logging**: Clear output during extraction

**Discovery Patterns:**
- `bin/` - Standard binary directory
- `Coq Platform.app/Contents/Resources/bin/` - macOS app bundle
- `Coq-Platform-release-*/bin/` - Version-specific directories
- Recursive search for any `coq*` or `rocq*` files

### Library Discovery Process

Library discovery follows the same robust approach:

1. **Multiple Patterns**: Supports various library structures
2. **Recursive Copying**: Preserves directory hierarchy
3. **Comprehensive Coverage**: Finds all library types
4. **Warning System**: Alerts if libraries missing

**Library Patterns:**
- `lib/` - Standard library directory
- `Coq Platform.app/Contents/Resources/lib/` - macOS app bundle
- `share/coq/` - Alternative library location
- `Coq-Platform-release-*/lib/` - Version-specific libraries

## Development

### Using the Toolchain in Your Project

Once the toolchain is set up, you can use the filegroups in your BUILD files:

```bazel
# Load the Rocq toolchain
load("@rocq_toolchains//:BUILD.bazel", "coqc", "stdlib")

# Use Coq compiler in your rules
rocq_library(
    name = "my_library",
    srcs = ["my_proof.v"],
    deps = [":stdlib"],
    toolchain = "@rocq_toolchains//:rocq_toolchain",
)

# Access specific tools
filegroup(
    name = "my_tools",
    srcs = [
        "@rocq_toolchains//:coqc",
        "@rocq_toolchains//:coqtop",
        "@rocq_toolchains//:coqide",
    ],
)

# Use standard library files
filegroup(
    name = "my_libs",
    srcs = ["@rocq_toolchains//:stdlib"],
)
```

### Toolchain File Access Patterns

**Direct Binary Access:**
```bazel
# Access the main compiler
alias(
    name = "coqc",
    actual = "@rocq_toolchains//:coqc",
)

# Use in your rules
ctx.actions.run(
    executable = "@rocq_toolchains//:coqc",
    arguments = ["-compile", src.path],
)
```

**Library File Access:**
```bazel
# Access standard library files
alias(
    name = "coq_stdlib",
    actual = "@rocq_toolchains//:stdlib",
)

# Use in your compilation
ctx.actions.run(
    inputs = ["@rocq_toolchains//:stdlib"],
    outputs = [output_file],
)
```

### Testing

The repository now includes comprehensive testing infrastructure:

```bash
# Run basic structure tests
bazel run //:test_basic

# Run toolchain functionality tests
bazel run //test:toolchain_test

# Run file mapping tests
bazel run //test:file_mapping_test

# Run integration tests
bazel run //test:integration_test

# Run all tests
bazel run //test:test_all

# Test the pure Rocq example
bazel test //examples/rocq_pure:test
```

### Test Categories

- **Basic Tests**: Verify file loading and rule instantiation
- **Toolchain Tests**: Verify toolchain components can be loaded
- **File Mapping Tests**: Verify proper file organization
- **Integration Tests**: Verify complete toolchain setup
- **Functionality Tests**: Verify actual toolchain functionality

### Adding New Tests

1. Add test functions to appropriate test modules
2. Add test targets to `test/BUILD.bazel`
3. Include the test in the `test_all` target

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

#### Vendor Workflow

To set up vendored toolchains for air-gap environments:

```bash
# 1. Run the vendor script to download all toolchains
./scripts/vendor_toolchains.sh

# 2. This creates third_party/toolchains/ with all required binaries
# 3. Set offline mode to use vendored tools
export BAZEL_ROCQ_OFFLINE=1

# 4. Build as normal - no internet access required
bazel build //examples/rocq_pure:test
```

#### Corporate Mirror Setup

For enterprise mirrors, the mirror should follow this structure:

```
https://mirror.company.com/
├── rocq/
│   ├── 2025.01.0/
│   │   ├── darwin_arm64/
│   │   │   └── Coq-Platform-release-2025.01.0-version.8.20.2025.01-MacOS-arm64.dmg
│   │   ├── linux_amd64/
│   │   │   └── Coq-Platform-release-2025.01.0-version.8.20.2025.01-Linux-x86_64.tar.gz
│   │   └── ...
│   └── ...
└── ocaml/
    ├── 5.1.1/
    │   ├── darwin_arm64/
    │   │   └── ocaml-5.1.1-aarch64-macos.tar.gz
    │   └── ...
    └── ...
```

Set the mirror URL:
```bash
export BAZEL_ROCQ_MIRROR=https://mirror.company.com
```

## License

Apache License 2.0 - See [LICENSE](LICENSE) file

## Related Projects

- [rules_rust](https://github.com/bazelbuild/rules_rust) - Rust rules that inspired this structure
- [rules_wasm_component](https://github.com/pulseengine/rules_wasm_component) - WebAssembly rules with similar toolchain patterns
- [Rocq Prover](https://github.com/rocq-prover/platform) - The Rocq theorem prover
- [coq-of-rust](https://github.com/coq-of-rust/coq-of-rust) - Rust to Coq translation tool