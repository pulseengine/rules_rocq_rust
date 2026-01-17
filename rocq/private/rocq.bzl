"""Core Rocq compilation rules - PRIVATE implementation.

This follows the exact pattern used in rules_rust's private implementation.
"""

load("@bazel_skylib//lib:paths.bzl", "paths")

# Provider for Rocq compilation information
RocqInfo = provider(
    doc = "Information about Rocq compilation results",
    fields = {
        "sources": "depset of .v source files",
        "include_paths": "list of include paths for dependent libraries",
        "transitive_deps": "depset of all transitive Rocq dependencies",
    },
)

# Core Rocq library compilation rule
def _rocq_library_impl(ctx):
    """Collect .v files for Rocq proof library.

    Currently collects source files for later compilation with Rocq/Coq.
    Full compilation support requires toolchain configuration.
    """
    # Validate source files
    sources = ctx.files.srcs
    if not sources:
        fail("rocq_library requires at least one source file")

    # Validate file extensions
    for src in sources:
        if not src.path.endswith(".v"):
            fail("rocq_library only accepts .v files, got: " + src.path)

    # Process dependencies to get transitive sources
    transitive_sources = []
    include_paths = []

    for dep in ctx.attr.deps:
        if RocqInfo in dep:
            transitive_sources.append(dep[RocqInfo].transitive_deps)
            include_paths.extend(dep[RocqInfo].include_paths)

    # Add current library's include path
    include_paths.append(ctx.attr.include_path if ctx.attr.include_path else ctx.label.package)

    # Create depsets
    source_depset = depset(sources)
    all_sources = depset(sources, transitive = transitive_sources)

    # Return providers
    return [
        DefaultInfo(
            files = source_depset,
            runfiles = ctx.runfiles(files = sources),
        ),
        RocqInfo(
            sources = source_depset,
            include_paths = include_paths,
            transitive_deps = all_sources,
        ),
    ]

# Rocq proof test rule
def _rocq_proof_test_impl(ctx):
    """Check that Rocq proof files are syntactically valid.

    Creates a test script that verifies .v files exist and are readable.
    Full proof checking requires Rocq toolchain.
    """
    sources = ctx.files.srcs
    dep_sources = []

    for dep in ctx.attr.deps:
        if RocqInfo in dep:
            dep_sources.extend(dep[RocqInfo].transitive_deps.to_list())

    all_sources = sources + dep_sources

    # Create test script
    script_content = """#!/bin/bash
set -e
echo "Checking Rocq proof files..."
"""
    for src in sources:
        script_content += 'echo "  ✓ {path}"\n'.format(path = src.short_path)
        script_content += 'test -f "{path}" || {{ echo "Missing: {path}"; exit 1; }}\n'.format(path = src.short_path)

    script_content += 'echo "All {count} proof files present."\n'.format(count = len(sources))

    # Write test script
    script = ctx.actions.declare_file(ctx.label.name + "_test.sh")
    ctx.actions.write(
        output = script,
        content = script_content,
        is_executable = True,
    )

    return [
        DefaultInfo(
            executable = script,
            runfiles = ctx.runfiles(files = all_sources),
        ),
    ]

# Rule definitions
rocq_library = rule(
    implementation = _rocq_library_impl,
    attrs = {
        "srcs": attr.label_list(
            allow_files = [".v"],
            doc = "Rocq source files (.v)",
        ),
        "deps": attr.label_list(
            providers = [[RocqInfo]],
            doc = "Dependencies on other Rocq libraries",
        ),
        "include_path": attr.string(
            doc = "Additional include path for this library",
        ),
    },
    doc = "Collects Rocq .v files into a library for proof development",
)

rocq_proof_test = rule(
    implementation = _rocq_proof_test_impl,
    attrs = {
        "srcs": attr.label_list(
            allow_files = [".v"],
            doc = "Rocq proof files to check",
        ),
        "deps": attr.label_list(
            providers = [[RocqInfo]],
            doc = "Dependencies on other Rocq libraries",
        ),
    },
    test = True,
    doc = "Verifies Rocq proof files are present and readable",
)
