"""Rocq toolchain definitions.

This file provides toolchain info provider and rules for Rocq/Coq compilation.
"""

load("@bazel_skylib//lib:paths.bzl", "paths")

# Toolchain info provider - used by rocq_library to find coqc
RocqToolchainInfo = provider(
    doc = "Information about the Rocq/Coq toolchain",
    fields = {
        "coqc": "File for the coqc compiler",
        "coq_tools": "depset of all Coq tool binaries",
        "stdlib": "depset of standard library .vo files",
    },
)

def _rocq_toolchain_info_impl(ctx):
    """Create a RocqToolchainInfo provider for use with Bazel toolchains."""
    coqc_files = ctx.files.coqc
    coqc = coqc_files[0] if coqc_files else None

    toolchain_info = RocqToolchainInfo(
        coqc = coqc,
        coq_tools = depset(ctx.files.coq_tools),
        stdlib = depset(ctx.files.stdlib),
    )

    return [
        platform_common.ToolchainInfo(
            rocq_info = toolchain_info,
        ),
        DefaultInfo(
            files = depset(ctx.files.coq_tools),
        ),
    ]

rocq_toolchain_info = rule(
    implementation = _rocq_toolchain_info_impl,
    attrs = {
        "coqc": attr.label(
            allow_files = True,
            doc = "The coqc compiler binary",
        ),
        "coq_tools": attr.label(
            allow_files = True,
            doc = "All Coq tool binaries",
        ),
        "stdlib": attr.label(
            allow_files = True,
            doc = "Coq standard library files",
        ),
    },
    doc = "Provides Rocq toolchain information for compilation rules",
)

# Rocq standard library filegroup helper
def rocq_stdlib_filegroup(name, srcs = None, **kwargs):
    """Helper function to create standard library filegroups."""
    native.filegroup(
        name = name,
        srcs = srcs,
        **kwargs
    )
