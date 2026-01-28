"""Module extensions for using rules_rocq with bzlmod.

Provides Rocq/Coq toolchain setup using nixpkgs for hermetic builds.
Supports Rocq 9.0+ and includes required external packages for rocq-of-rust.

NOTE: The root module MUST configure nixpkgs repository using rules_nixpkgs_core
and it must be named "@nixpkgs". See README.md for example configuration.
"""

load("@rules_nixpkgs_core//:nixpkgs.bzl", "nixpkgs_package")
load("//rocq/private:smpl_repository.bzl", "smpl_source")

# Tag classes for Rocq toolchain configuration
_RocqToolchainTag = tag_class(
    doc = "Tags for defining Rocq toolchains",
    attrs = {
        "version": attr.string(
            doc = "Rocq/Coq version to use (e.g., '9.0', '8.20')",
            default = "9.0",
        ),
        "strategy": attr.string(
            doc = "Tool acquisition strategy: 'nix' for hermetic nixpkgs",
            default = "nix",
            values = ["nix"],
        ),
        "nixpkgs": attr.string(
            doc = "Name of the nixpkgs repository (default: @nixpkgs)",
            default = "@nixpkgs",
        ),
        "with_rocq_of_rust_deps": attr.bool(
            doc = "Include dependencies for rocq-of-rust (coqutil, hammer, smpl)",
            default = True,
        ),
    },
)

def _get_rocq_attr(version):
    """Map Rocq/Coq version to nixpkgs attribute path."""
    version_map = {
        "9.0": "coq_9_0",
        "8.20": "coq_8_20",
        "8.19": "coq_8_19",
        "8.18": "coq_8_18",
        "8.17": "coq_8_17",
        "8.16": "coq_8_16",
        "latest": "coq",
    }
    return version_map.get(version, "coq_9_0")

# BUILD file content for the main Rocq toolchain package
# Note: For Rocq 9.0+, the stdlib is a separate package (@rocq_stdlib)
_ROCQ_BUILD_FILE = '''
load("@rules_rocq_rust//rocq:toolchain.bzl", "rocq_toolchain_info")

package(default_visibility = ["//visibility:public"])

# Rocq compiler - the main binary (rocq or coqc depending on version)
filegroup(
    name = "coqc_bin",
    srcs = glob(["bin/rocqc", "bin/coqc"], allow_empty = True),
)

# All Rocq/Coq binaries
filegroup(
    name = "coq_tools",
    srcs = glob(["bin/rocq*", "bin/coq*"], allow_empty = True),
)

# Rocq corelib (compiled .vo files from rocq-core package)
# This is NOT the full Stdlib - see @rocq_stdlib for that
filegroup(
    name = "corelib",
    srcs = glob([
        "lib/rocq/**/*.vo",
        "lib/rocq/**/*.glob",
        "lib/coq/**/*.vo",
        "lib/coq/**/*.glob",
    ], allow_empty = True),
)

# OCaml findlib packages for plugin resolution (needed for Hammer)
# coq-core META redirects to rocq-runtime for Rocq 9.0+
filegroup(
    name = "ocaml_libs",
    srcs = glob([
        "lib/coq-core/**",
        "lib/coqide-server/**",
        "lib/ocaml/**",
    ], allow_empty = True),
)

# Toolchain info wrapper - provides the coqc executable
# stdlib comes from @rocq_stdlib package for Rocq 9.0+
# External libraries (coqutil, hammer, hammer_tactics, smpl) included for real RocqOfRust library
rocq_toolchain_info(
    name = "rocq_toolchain_info",
    coqc = ":coqc_bin",
    coq_tools = ":coq_tools",
    stdlib = "@rocq_stdlib//:stdlib",
    coqutil = "@rocq_coqutil//:coqutil",
    hammer = "@rocq_hammer//:hammer",
    hammer_tactics = "@rocq_hammer_tactics//:hammer_tactics",
    hammer_ocaml_plugins = "@rocq_hammer//:ocaml_plugins",
    hammer_tactics_ocaml_plugins = "@rocq_hammer_tactics//:ocaml_plugins",
    smpl = "@rocq_smpl//:smpl",
    smpl_ocaml_plugins = "@rocq_smpl//:ocaml_plugins",
)

# Register as toolchain
toolchain(
    name = "rocq_toolchain",
    toolchain = ":rocq_toolchain_info",
    toolchain_type = "@rules_rocq_rust//rocq:toolchain_type",
)

# Alias for register_toolchains
alias(
    name = "all",
    actual = ":rocq_toolchain",
)
'''

# BUILD file for coqutil package
_COQUTIL_BUILD_FILE = '''
package(default_visibility = ["//visibility:public"])

filegroup(
    name = "coqutil",
    srcs = glob([
        "lib/coq/**/*.vo",
        "lib/coq/**/*.glob",
        "lib/rocq/**/*.vo",
        "lib/rocq/**/*.glob",
    ], allow_empty = True),
)

# Include path for -Q flag: coqutil theories are typically at coqutil.*
filegroup(
    name = "sources",
    srcs = glob([
        "lib/coq/**/*.v",
        "lib/rocq/**/*.v",
    ], allow_empty = True),
)
'''

# BUILD file for coq-hammer package (Plugin only)
_HAMMER_BUILD_FILE = '''
package(default_visibility = ["//visibility:public"])

filegroup(
    name = "hammer",
    srcs = glob([
        "lib/coq/**/*.vo",
        "lib/coq/**/*.glob",
        "lib/rocq/**/*.vo",
        "lib/rocq/**/*.glob",
    ], allow_empty = True),
)

# OCaml findlib plugin (needed for coqc to load Hammer ML plugins)
filegroup(
    name = "ocaml_plugins",
    srcs = glob(["lib/ocaml/**/site-lib/**"], allow_empty = True),
)

# Hammer external binaries
filegroup(
    name = "hammer_bins",
    srcs = glob(["bin/*"], allow_empty = True),
)
'''

# BUILD file for coq-hammer-tactics package (Tactics library)
_HAMMER_TACTICS_BUILD_FILE = '''
package(default_visibility = ["//visibility:public"])

filegroup(
    name = "hammer_tactics",
    srcs = glob([
        "lib/coq/**/*.vo",
        "lib/coq/**/*.glob",
        "lib/rocq/**/*.vo",
        "lib/rocq/**/*.glob",
    ], allow_empty = True),
)

# OCaml findlib plugin (needed for coqc to load Hammer Tactics ML plugins)
filegroup(
    name = "ocaml_plugins",
    srcs = glob(["lib/ocaml/**/site-lib/**"], allow_empty = True),
)
'''

# BUILD file for smpl package
_SMPL_BUILD_FILE = '''
package(default_visibility = ["//visibility:public"])

filegroup(
    name = "smpl",
    srcs = glob([
        "lib/coq/**/*.vo",
        "lib/coq/**/*.glob",
        "lib/rocq/**/*.vo",
        "lib/rocq/**/*.glob",
    ], allow_empty = True),
)
'''

# BUILD file for Rocq stdlib (separate from rocq-core in 9.0)
# Stdlib is at lib/coq/9.0/user-contrib/Stdlib
_STDLIB_BUILD_FILE = '''
package(default_visibility = ["//visibility:public"])

# Rocq stdlib compiled files (.vo)
# Path: lib/coq/9.0/user-contrib/Stdlib/**/*.vo
filegroup(
    name = "stdlib",
    srcs = glob([
        "lib/coq/*/user-contrib/**/*.vo",
        "lib/coq/*/user-contrib/**/*.glob",
    ], allow_empty = True),
)

# Root directory for -Q flag
# Usage: -Q lib/coq/9.0/user-contrib Stdlib
exports_files(["lib"])
'''

# Rocq module extension implementation
def _rocq_impl(module_ctx):
    """Implementation of Rocq toolchain extension.

    Uses nixpkgs to provide hermetic Rocq/Coq installation.
    Includes optional dependencies for rocq-of-rust (coqutil, hammer, smpl).
    The root module must configure @nixpkgs repository.
    """
    # Collect toolchain configurations from all modules
    toolchains = []
    for mod in module_ctx.modules:
        for toolchain in mod.tags.toolchain:
            toolchains.append(toolchain)

    # Use the first toolchain configuration
    if toolchains:
        config = toolchains[0]
        rocq_version = config.version
        nixpkgs_repo = config.nixpkgs
        with_deps = config.with_rocq_of_rust_deps
    else:
        rocq_version = "9.0"
        nixpkgs_repo = "@nixpkgs"
        with_deps = True

    rocq_attr = _get_rocq_attr(rocq_version)

    # Create main Rocq toolchain using nixpkgs_package
    # NOTE: This requires @nixpkgs to be defined in the root module
    nixpkgs_package(
        name = "rocq_toolchains",
        repository = nixpkgs_repo,
        attribute_path = rocq_attr,
        build_file_content = _ROCQ_BUILD_FILE,
    )

    # Create Rocq stdlib (needed for Rocq 9.0)
    # Rocq 9.0 has separate stdlib package
    if rocq_version == "9.0":
        nixpkgs_package(
            name = "rocq_stdlib",
            repository = nixpkgs_repo,
            attribute_path = "rocqPackages.stdlib",
            build_file_content = _STDLIB_BUILD_FILE,
        )

    # Create external dependencies for rocq-of-rust
    if with_deps:
        # coqutil - utility library from MIT PLV
        nixpkgs_package(
            name = "rocq_coqutil",
            repository = nixpkgs_repo,
            attribute_path = "coqPackages.coqutil",
            build_file_content = _COQUTIL_BUILD_FILE,
        )

        # coq-hammer - automated reasoning plugin
        nixpkgs_package(
            name = "rocq_hammer",
            repository = nixpkgs_repo,
            attribute_path = "coqPackages.coq-hammer",
            build_file_content = _HAMMER_BUILD_FILE,
        )

        # coq-hammer-tactics - Hammer.Tactics library (separate from plugin)
        nixpkgs_package(
            name = "rocq_hammer_tactics",
            repository = nixpkgs_repo,
            attribute_path = "coqPackages.coq-hammer-tactics",
            build_file_content = _HAMMER_TACTICS_BUILD_FILE,
        )

        # smpl - extensible simplification tactic (built from source for Rocq 9.0)
        # The nixpkgs version only supports up to Coq 8.15
        smpl_source(
            name = "rocq_smpl",
            branch = "rocq-9.0",
        )

    # Return extension metadata (reproducible for caching)
    return module_ctx.extension_metadata(reproducible = True)

# Rocq module extension
rocq = module_extension(
    doc = "Rocq/Coq toolchain extension using nixpkgs.",
    implementation = _rocq_impl,
    tag_classes = {
        "toolchain": _RocqToolchainTag,
    },
)
