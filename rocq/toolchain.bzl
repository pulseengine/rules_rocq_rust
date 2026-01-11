"""Rocq toolchain definitions.

This file provides the rocq_stdlib_filegroup rule for managing Rocq standard library files,
following the exact pattern established by rules_rust.
"""

load("@bazel_skylib//lib:paths.bzl", "paths")

# Rocq standard library filegroup
# This follows the exact pattern from rules_rust's rust_stdlib_filegroup
def _rocq_stdlib_filegroup_impl(ctx):
    """Implementation for Rocq standard library filegroup."""
    # This is a simple filegroup for now
    # In a full implementation, this would handle standard library discovery
    # and platform-specific libraries
    pass

rocq_stdlib_filegroup = rule(
    implementation = _rocq_stdlib_filegroup_impl,
    attrs = {
        "srcs": attr.label_list(
            allow_files = True,
            doc = "Rocq standard library files",
        ),
    },
    doc = "Creates a filegroup for Rocq standard library files",
)

# Additional toolchain-related functions can be added here
# as the implementation matures

def rocq_stdlib_filegroup(name, srcs = None, **kwargs):
    """Helper function to create standard library filegroups."""
    native.filegroup(
        name = name,
        srcs = srcs,
        **kwargs
    )