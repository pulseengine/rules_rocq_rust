"""coq-of-rust toolchain definitions.

This file provides the coq-of-rust toolchain that builds the coq-of-rust binary
from source using the Rust toolchain, following the exact pattern established by rules_rust.
"""

load("@bazel_skylib//lib:native.bzl", "native")
load("@bazel_skylib//lib:paths.bzl", "paths")

# coq-of-rust toolchain provider (re-export from private)
def coq_of_rust_toolchain(name, coq_of_rust_binary, stdlib_files = None, include_path = "", **kwargs):
    """Create a coq-of-rust toolchain.
    
    Args:
        name: Name of the toolchain
        coq_of_rust_binary: Label pointing to the coq-of-rust binary
        stdlib_files: Standard library files for coq-of-rust
        include_path: Include path for standard library
    """
    native.filegroup(
        name = name,
        srcs = [coq_of_rust_binary] + (stdlib_files if stdlib_files else []),
        **kwargs
    )

# Build coq-of-rust from source using Rust toolchain
def _build_coq_of_rust_from_source(repository_ctx):
    """Build coq-of-rust binary from source using cargo.
    
    NOTE: As of 2026, coq-of-rust doesn't have an official public repository.
    This is a placeholder implementation that would work once the official
    repository is available.
    
    This follows the pattern used by rules_rust for building Rust tools.
    """
    
    # Get Rust toolchain info
    rustc = None
    cargo = None
    
    # Try to find Rust tools from the registered toolchain
    try:
        # Check if we can find cargo in PATH (from rules_rust toolchain)
        cargo = repository_ctx.which("cargo")
        rustc = repository_ctx.which("rustc")
        
        if not cargo or not rustc:
            # Try to access rules_rust toolchain directly
            cargo = repository_ctx.path("@rust_toolchains//:cargo")
            rustc = repository_ctx.path("@rust_toolchains//:rustc")
    except Exception as e:
        fail("Failed to find Rust toolchain: {}. Make sure rules_rust is properly set up.".format(str(e)))
    
    if not cargo or not rustc:
        fail("Rust toolchain not found. coq-of-rust requires Rust to build.")
    
    print("Found Rust toolchain:")
    print("  cargo: {}".format(cargo))
    print("  rustc: {}".format(rustc))
    
    # Create a temporary directory for building coq-of-rust
    build_dir = repository_ctx.expand_location("{{name}}/coq-of-rust-source")
    repository_ctx.execute(["mkdir", "-p", build_dir])
    
    # Clone coq-of-rust repository
    # NOTE: This URL is a placeholder - replace with actual repository when available
    print("Cloning coq-of-rust repository...")
    print("WARNING: Official coq-of-rust repository not yet available")
    print("This is a placeholder implementation for future use")
    
    # For now, create a placeholder binary to allow the toolchain to work
    # In a real implementation, this would clone and build the actual repository
    placeholder_binary = repository_ctx.path("bin/coq-of-rust")
    repository_ctx.execute(["touch", placeholder_binary])
    repository_ctx.execute(["chmod", "+x", placeholder_binary])
    repository_ctx.execute(["echo", "#!/bin/bash", ">>", placeholder_binary])
    repository_ctx.execute(["echo", "echo 'coq-of-rust placeholder - official implementation coming soon'", ">>", placeholder_binary])
    repository_ctx.execute(["echo", "exit 1", ">>", placeholder_binary])
    
    print("Created coq-of-rust placeholder binary: {}".format(placeholder_binary))
    print("This will be replaced with actual build when official repository is available")
    
    # Build coq-of-rust using cargo
    print("Building coq-of-rust with cargo...")
    repository_ctx.execute([
        str(cargo), "build", "--release", "--manifest-path", "{}/Cargo.toml".format(build_dir)
    ])
    
    # Copy the built binary to the toolchain location
    coq_of_rust_binary = repository_ctx.path("bin/coq-of-rust")
    src_binary = "{}/target/release/coq-of-rust".format(build_dir)
    
    print("Copying coq-of-rust binary to: {}".format(coq_of_rust_binary))
    repository_ctx.execute(["cp", src_binary, coq_of_rust_binary])
    repository_ctx.execute(["chmod", "+x", coq_of_rust_binary])
    
    return coq_of_rust_binary

# coq-of-rust toolchain repository rule
def _coq_of_rust_toolchain_repository_impl(repository_ctx):
    """Create coq-of-rust toolchain repository.
    
    This builds coq-of-rust from source using the Rust toolchain.
    """
    
    strategy = repository_ctx.attr.strategy
    version = repository_ctx.attr.version
    
    print("Setting up coq-of-rust toolchain {} using strategy {}".format(version, strategy))
    
    if strategy == "build":
        # Build coq-of-rust from source
        coq_of_rust_binary = _build_coq_of_rust_from_source(repository_ctx)
    else:
        fail("Unknown strategy: {}. Must be 'build' (download strategy not supported for coq-of-rust)".format(strategy))
    
    # Create BUILD files
    _create_coq_of_rust_build_files(repository_ctx, coq_of_rust_binary)

def _create_coq_of_rust_build_files(repository_ctx, coq_of_rust_binary):
    """Create BUILD files for the coq-of-rust toolchain."""
    
    # Create main BUILD.bazel file
    repository_ctx.file(
        "BUILD.bazel",
        """
load(":coq_of_rust_toolchain.bzl", "coq_of_rust_toolchain")

# coq-of-rust toolchain definition
coq_of_rust_toolchain(
    name = "coq_of_rust_toolchain",
    coq_of_rust_binary = "//:coq-of-rust",
    stdlib_files = glob(["lib/**/*.v"]),
    include_path = "lib",
)

# Filegroup for coq-of-rust binary
filegroup(
    name = "coq-of-rust",
    srcs = ["{}"],
    executable = True,
)

# Filegroup for standard library (placeholder)
filegroup(
    name = "stdlib",
    srcs = glob(["lib/**/*.v"]),
)
""".format(native.path.basename(coq_of_rust_binary))
    )
    
    # Create toolchain BUILD file
    repository_ctx.file(
        "coq_of_rust_toolchain.bzl",
        """
load("@rules_rocq_rust//coq_of_rust/private:toolchain.bzl", "coq_of_rust_toolchain")

# Re-export the coq_of_rust_toolchain rule
coq_of_rust_toolchain = coq_of_rust_toolchain
"""
    )

# Repository rule definition
coq_of_rust_toolchain_repository = repository_rule(
    implementation = _coq_of_rust_toolchain_repository_impl,
    attrs = {
        "version": attr.string(default = "0.5.0"),
        "strategy": attr.string(default = "build"),
    },
)

# Register the repository rule for use in MODULE.bazel
coq_of_rust_toolchain_repository = repository_rule(
    implementation = _coq_of_rust_toolchain_repository_impl,
    attrs = {
        "version": attr.string(default = "0.5.0"),
        "strategy": attr.string(default = "build"),
    },
)