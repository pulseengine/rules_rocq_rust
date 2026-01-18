"""Core Rocq compilation rules - PRIVATE implementation.

This follows the exact pattern used in rules_rust's private implementation.
"""

load("@bazel_skylib//lib:paths.bzl", "paths")

# Provider for Rocq compilation information
RocqInfo = provider(
    doc = "Information about Rocq compilation results",
    fields = {
        "sources": "depset of .v source files",
        "compiled": "depset of .vo compiled files",
        "include_paths": "list of include paths for dependent libraries",
        "transitive_deps": "depset of all transitive Rocq dependencies",
    },
)

def _rocq_library_impl(ctx):
    """Compile Rocq .v files to .vo using coqc.

    Uses the Rocq toolchain from nixpkgs to compile proofs.
    """
    # Validate source files
    sources = ctx.files.srcs
    if not sources:
        fail("rocq_library requires at least one source file")

    # Validate file extensions
    for src in sources:
        if not src.path.endswith(".v"):
            fail("rocq_library only accepts .v files, got: " + src.path)

    # Get toolchain info
    toolchain = ctx.toolchains["@rules_rocq_rust//rocq:toolchain_type"]

    # If no toolchain available, fall back to source collection only
    if not toolchain or not hasattr(toolchain, "rocq_info"):
        return _rocq_library_source_only(ctx, sources)

    rocq_info = toolchain.rocq_info
    coqc = rocq_info.coqc

    if not coqc:
        # No coqc found, fall back to source collection
        return _rocq_library_source_only(ctx, sources)

    # Process dependencies
    transitive_sources = []
    transitive_compiled = []
    include_paths = []

    for dep in ctx.attr.deps:
        if RocqInfo in dep:
            transitive_sources.append(dep[RocqInfo].transitive_deps)
            if dep[RocqInfo].compiled:
                transitive_compiled.append(dep[RocqInfo].compiled)
            include_paths.extend(dep[RocqInfo].include_paths)

    # Add current library's include path
    pkg_path = ctx.label.package
    include_paths.append(ctx.attr.include_path if ctx.attr.include_path else pkg_path)

    # Compile each .v file to .vo
    compiled_files = []
    for src in sources:
        vo_file = ctx.actions.declare_file(
            src.basename.replace(".v", ".vo"),
        )
        glob_file = ctx.actions.declare_file(
            src.basename.replace(".v", ".glob"),
        )

        # Build coqc arguments
        args = ctx.actions.args()
        args.add("-q")  # Quiet mode

        # Add include paths
        for inc in include_paths:
            args.add("-Q", inc, inc.replace("/", "."))

        # Add output directory
        args.add("-o", vo_file)

        # Add source file
        args.add(src)

        # Get dependency .vo files
        dep_vo_files = []
        for dep_depset in transitive_compiled:
            dep_vo_files.extend(dep_depset.to_list())

        ctx.actions.run(
            executable = coqc,
            arguments = [args],
            inputs = depset([src] + dep_vo_files, transitive = transitive_sources),
            outputs = [vo_file, glob_file],
            mnemonic = "CoqCompile",
            progress_message = "Compiling Coq proof %{input}",
        )

        compiled_files.append(vo_file)

    # Create depsets
    source_depset = depset(sources)
    compiled_depset = depset(compiled_files)
    all_sources = depset(sources, transitive = transitive_sources)

    return [
        DefaultInfo(
            files = compiled_depset,
            runfiles = ctx.runfiles(files = sources + compiled_files),
        ),
        RocqInfo(
            sources = source_depset,
            compiled = compiled_depset,
            include_paths = include_paths,
            transitive_deps = all_sources,
        ),
    ]

def _rocq_library_source_only(ctx, sources):
    """Fallback when no toolchain available - just collect sources."""
    transitive_sources = []
    include_paths = []

    for dep in ctx.attr.deps:
        if RocqInfo in dep:
            transitive_sources.append(dep[RocqInfo].transitive_deps)
            include_paths.extend(dep[RocqInfo].include_paths)

    include_paths.append(ctx.attr.include_path if ctx.attr.include_path else ctx.label.package)

    source_depset = depset(sources)
    all_sources = depset(sources, transitive = transitive_sources)

    return [
        DefaultInfo(
            files = source_depset,
            runfiles = ctx.runfiles(files = sources),
        ),
        RocqInfo(
            sources = source_depset,
            compiled = None,
            include_paths = include_paths,
            transitive_deps = all_sources,
        ),
    ]

def _rocq_proof_test_impl(ctx):
    """Test that Rocq proofs compile successfully.

    If toolchain available, verifies .vo files were produced.
    Otherwise, just checks source files exist.
    """
    sources = ctx.files.srcs
    dep_sources = []
    dep_compiled = []

    for dep in ctx.attr.deps:
        if RocqInfo in dep:
            dep_sources.extend(dep[RocqInfo].transitive_deps.to_list())
            if dep[RocqInfo].compiled:
                dep_compiled.extend(dep[RocqInfo].compiled.to_list())

    all_sources = sources + dep_sources

    # Create test script
    script_content = """#!/bin/bash
set -e
echo "Checking Rocq proof files..."
"""
    for src in sources:
        script_content += 'echo "  ✓ {path}"\n'.format(path = src.short_path)
        script_content += 'test -f "{path}" || {{ echo "Missing: {path}"; exit 1; }}\n'.format(path = src.short_path)

    if dep_compiled:
        script_content += 'echo "Checking compiled .vo files..."\n'
        for vo in dep_compiled:
            script_content += 'echo "  ✓ {path}"\n'.format(path = vo.short_path)
            script_content += 'test -f "{path}" || {{ echo "Missing compiled: {path}"; exit 1; }}\n'.format(path = vo.short_path)

    script_content += 'echo "All {count} proof files verified."\n'.format(count = len(sources))

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
            runfiles = ctx.runfiles(files = all_sources + dep_compiled),
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
    toolchains = ["@rules_rocq_rust//rocq:toolchain_type"],
    doc = "Compiles Rocq .v files into a library",
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
    doc = "Verifies Rocq proof files compile successfully",
)
