"""Nix-based Rocq/Coq toolchain for hermetic builds.

This module uses rules_nixpkgs to provide a hermetic Coq installation
from nixpkgs. Works on Linux and macOS.
"""

load("@rules_nixpkgs_core//:nixpkgs.bzl", "nixpkgs_package")

def rocq_nix_toolchain_repository(name, coq_version = "8.20"):
    """Create a Rocq toolchain using nixpkgs.

    This provides a hermetic Coq installation from nixpkgs that works
    on Linux (x86_64, aarch64) and macOS (x86_64, aarch64).

    Args:
        name: Repository name for the toolchain
        coq_version: Coq version to use (e.g., "8.20", "8.19", "8.18")
    """
    # Map version to nixpkgs attribute
    coq_attr = _get_coq_attr(coq_version)

    # Import Coq from nixpkgs
    nixpkgs_package(
        name = name,
        repository = "@nixpkgs",
        attribute_path = coq_attr,
        build_file_content = _COQ_BUILD_FILE,
    )

def _get_coq_attr(version):
    """Map Coq version to nixpkgs attribute path.

    Args:
        version: Coq version string (e.g., "8.20")

    Returns:
        nixpkgs attribute path for the Coq package
    """
    # nixpkgs has versioned Coq packages
    version_map = {
        "8.20": "coq_8_20",
        "8.19": "coq_8_19",
        "8.18": "coq_8_18",
        "8.17": "coq_8_17",
        "8.16": "coq_8_16",
        "latest": "coq",
    }

    attr = version_map.get(version, "coq")
    return attr

# BUILD file content for the nixpkgs_package
_COQ_BUILD_FILE = '''
package(default_visibility = ["//visibility:public"])

# Coq compiler
filegroup(
    name = "coqc",
    srcs = glob(["bin/coqc"]),
)

# Coq top-level
filegroup(
    name = "coqtop",
    srcs = glob(["bin/coqtop"]),
)

# Coq documentation generator
filegroup(
    name = "coqdoc",
    srcs = glob(["bin/coqdoc"]),
)

# Coq checker
filegroup(
    name = "coqchk",
    srcs = glob(["bin/coqchk"]),
)

# All Coq binaries
filegroup(
    name = "coq_tools",
    srcs = glob(["bin/coq*"]),
)

# Coq standard library (compiled .vo files)
filegroup(
    name = "stdlib",
    srcs = glob([
        "lib/coq/**/*.vo",
        "lib/coq/**/*.glob",
    ]),
)

# Coq theories source files
filegroup(
    name = "coq_theories",
    srcs = glob(["lib/coq/**/*.v"]),
)

# All Coq libraries
filegroup(
    name = "coq_libraries",
    srcs = glob(["lib/coq/**/*"]),
)

# Toolchain target
toolchain(
    name = "rocq_toolchain",
    toolchain = ":coq_tools",
    toolchain_type = "@rules_rocq_rust//rocq:toolchain_type",
)

# Alias for register_toolchains
alias(
    name = "all",
    actual = ":rocq_toolchain",
)
'''
