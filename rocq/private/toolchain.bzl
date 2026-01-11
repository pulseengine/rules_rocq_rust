"""Rocq toolchain definitions - PRIVATE implementation.

Following the exact pattern used in rules_rust toolchain definitions.
"""

load("@bazel_skylib//lib:paths.bzl", "paths")

# Rocq toolchain provider
def _rocq_toolchain_impl(ctx):
    """Create Rocq toolchain info provider.
    
    This follows the rules_rust pattern for toolchain providers.
    """
    
    # Get toolchain files
    rocq_binary = ctx.file.rocq_binary
    coq_binary = ctx.file.coq_binary
    stdlib_files = ctx.files.stdlib_files
    
    # Create toolchain info
    toolchain_info = struct(
        rocq_binary = rocq_binary,
        coq_binary = coq_binary,
        stdlib_files = stdlib_files,
        include_paths = [ctx.attr.include_path] if ctx.attr.include_path else [],
    )
    
    return [toolchain_info]

# Rocq toolchain rule
rocq_toolchain = rule(
    implementation = _rocq_toolchain_impl,
    attrs = {
        "rocq_binary": attr.label(
            allow_single_file = True,
            executable = True,
            cfg = "exec",
            doc = "Rocq binary",
        ),
        "coq_binary": attr.label(
            allow_single_file = True,
            executable = True,
            cfg = "exec",
            doc = "Coq theorem prover binary",
        ),
        "stdlib_files": attr.label_list(
            allow_files = True,
            doc = "Rocq/Coq standard library files",
        ),
        "include_path": attr.string(
            doc = "Standard library include path",
        ),
    },
    doc = "Declares a Rocq toolchain pointing to Rocq/Coq binaries and standard library",
)

# Standard library filegroup (following rules_rust pattern)
def rocq_stdlib_filegroup(name, srcs = None, **kwargs):
    """Create a filegroup for Rocq standard library files."""
    native.filegroup(
        name = name,
        srcs = srcs,
        **kwargs
    )