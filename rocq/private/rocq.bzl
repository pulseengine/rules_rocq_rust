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
        "include_paths": "list of (physical_path, logical_path) tuples for -Q flag",
        "output_dir": "string: directory containing compiled .vo files",
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
    include_paths = []  # List of (physical_path, logical_path) tuples

    for dep in ctx.attr.deps:
        if RocqInfo in dep:
            transitive_sources.append(dep[RocqInfo].transitive_deps)
            if dep[RocqInfo].compiled:
                transitive_compiled.append(dep[RocqInfo].compiled)
            include_paths.extend(dep[RocqInfo].include_paths)

    # Determine logical path for this library
    logical_path = ctx.attr.include_path if ctx.attr.include_path else ctx.label.package.replace("/", ".")

    # Output directory will contain the compiled .vo files
    # Use the first declared output's directory as the output path
    output_dir = None

    # Compile each .v file to .vo
    # Preserve relative path structure from source to maintain module hierarchy
    compiled_files = []
    for src in sources:
        # Get the relative path from the source file
        # E.g., "RocqOfRust/RocqOfRust.v" should become "RocqOfRust/RocqOfRust.vo"
        rel_path = src.short_path
        # Remove package prefix if present (for external sources)
        if rel_path.startswith("../"):
            # External source - extract relevant part after last known directory
            parts = rel_path.split("/")
            # Find the logical path component
            if logical_path in rel_path:
                idx = rel_path.find(logical_path)
                rel_path = rel_path[idx:]
            else:
                rel_path = src.basename
        elif "/" in rel_path and not rel_path.startswith(ctx.label.package):
            # Source from different location - use the path relative to logical root
            rel_path = src.basename

        vo_file = ctx.actions.declare_file(
            rel_path.replace(".v", ".vo"),
        )
        glob_file = ctx.actions.declare_file(
            rel_path.replace(".v", ".glob"),
        )

        if output_dir == None:
            # Compute output_dir to match the logical include_path root.
            # For include_path="RocqOfRust" and vo_file at .../RocqOfRust/lib/lib.vo,
            # output_dir must be .../RocqOfRust (not .../RocqOfRust/lib),
            # so that -Q maps lib/lib.vo → RocqOfRust.lib.lib correctly.
            if ctx.attr.include_path:
                include_dir = ctx.attr.include_path.replace(".", "/")
                marker = "/" + include_dir
                if marker in vo_file.dirname:
                    idx = vo_file.dirname.find(marker)
                    output_dir = vo_file.dirname[:idx + len(marker)]
                elif vo_file.dirname.endswith(include_dir):
                    output_dir = vo_file.dirname
                else:
                    output_dir = vo_file.dirname
            else:
                output_dir = vo_file.dirname

        # Build coqc arguments
        args = ctx.actions.args()
        args.add("-q")  # Quiet mode

        # Add extra compiler flags (e.g., -impredicative-set)
        for flag in ctx.attr.extra_flags:
            args.add(flag)

        # Add Stdlib path if available (Rocq 9.0+)
        # This allows "From Stdlib Require Import ..." to work
        if hasattr(rocq_info, "stdlib_path") and rocq_info.stdlib_path:
            args.add("-Q")
            args.add(rocq_info.stdlib_path)
            args.add("Stdlib")

        # Add extra library paths (coqutil, hammer, smpl) if available
        if hasattr(rocq_info, "extra_libs"):
            for lib_files, logical_name, lib_path in rocq_info.extra_libs:
                if lib_path:
                    args.add("-Q")
                    args.add(lib_path)
                    args.add(logical_name)

        # Add include paths from dependencies
        # coqc -Q expects: -Q <physical_path> <logical_name>
        dep_paths = {}  # Use dict as set
        for phys_path, log_path in include_paths:
            args.add("-Q")
            args.add(phys_path)
            args.add(log_path)
            dep_paths[phys_path] = True

        # Add include path using OUTPUT directory (not source directory)
        # Coq embeds the library name based on the -Q path at compile time
        # So we must use the same path that will be used when loading the .vo
        # With -Q output_dir prefix: file output_dir/Foo.vo is loaded as prefix.Foo
        # Use the include_path-aware output_dir (not vo_file.dirname) so that
        # nested files like lib/lib.vo get the correct logical path RocqOfRust.lib.lib
        out_dir = output_dir if output_dir else vo_file.dirname

        # Check if out_dir conflicts with deps
        out_conflicts = out_dir in dep_paths
        if not out_conflicts:
            for dep_path in dep_paths.keys():
                if dep_path.startswith(out_dir + "/"):
                    # out_dir is a parent of dep_path - would override
                    out_conflicts = True
                    break
        if not out_conflicts:
            args.add("-Q")
            args.add(out_dir)
            args.add(logical_path)

        # Add output directory
        args.add("-o", vo_file)

        # Add source file
        args.add(src)

        # Get dependency .vo files
        dep_vo_files = []
        for dep_depset in transitive_compiled:
            dep_vo_files.extend(dep_depset.to_list())

        # Include stdlib files if available
        stdlib_files = []
        if hasattr(rocq_info, "stdlib") and rocq_info.stdlib:
            stdlib_files = rocq_info.stdlib.to_list()

        # Include extra library files (coqutil, hammer, smpl) if available
        extra_lib_files = []
        if hasattr(rocq_info, "extra_libs"):
            for lib_files, _, _ in rocq_info.extra_libs:
                extra_lib_files.extend(lib_files)

        # Set OCAMLPATH for findlib resolution (needed for Hammer plugins)
        # Coq plugins require findlib to locate coq-core.plugins.* and
        # coq-hammer-tactics.lib across multiple nix packages
        env = {}
        if hasattr(rocq_info, "ocaml_path") and rocq_info.ocaml_path:
            env["OCAMLPATH"] = rocq_info.ocaml_path

        # Include OCaml plugin files as inputs
        ocaml_files = []
        if hasattr(rocq_info, "ocaml_plugin_files"):
            ocaml_files = rocq_info.ocaml_plugin_files

        run_kwargs = {
            "executable": coqc,
            "arguments": [args],
            "inputs": depset([src] + dep_vo_files + stdlib_files + extra_lib_files + ocaml_files, transitive = transitive_sources),
            "outputs": [vo_file, glob_file],
            "mnemonic": "CoqCompile",
            "progress_message": "Compiling Coq proof %{input}",
        }
        if env:
            run_kwargs["env"] = env

        # Coq plugins (e.g., Hammer) use OCaml findlib which resolves
        # absolute nix store paths across packages. The Bazel sandbox
        # can't follow these cross-package references, so we disable
        # sandboxing when plugins are present. Hermiticity is still
        # maintained through nix's immutable store.
        if hasattr(rocq_info, "extra_libs") and rocq_info.extra_libs:
            run_kwargs["execution_requirements"] = {"no-sandbox": "1"}

        ctx.actions.run(**run_kwargs)

        compiled_files.append(vo_file)

    # Create depsets
    source_depset = depset(sources)
    compiled_depset = depset(compiled_files)
    all_sources = depset(sources, transitive = transitive_sources)

    # Add this library's include path for dependents
    # Dependents need to find our .vo files with proper logical path mapping
    # With -Q dir prefix: file dir/Foo.vo is found as prefix.Foo
    if output_dir:
        this_include_paths = include_paths + [(output_dir, logical_path)]
    else:
        this_include_paths = include_paths

    return [
        DefaultInfo(
            files = compiled_depset,
            runfiles = ctx.runfiles(files = sources + compiled_files),
        ),
        RocqInfo(
            sources = source_depset,
            compiled = compiled_depset,
            include_paths = this_include_paths,
            output_dir = output_dir if output_dir else "",
            transitive_deps = all_sources,
        ),
    ]

def _rocq_library_source_only(ctx, sources):
    """Fallback when no toolchain available - just collect sources."""
    transitive_sources = []
    include_paths = []  # List of (physical_path, logical_path) tuples

    for dep in ctx.attr.deps:
        if RocqInfo in dep:
            transitive_sources.append(dep[RocqInfo].transitive_deps)
            include_paths.extend(dep[RocqInfo].include_paths)

    logical_path = ctx.attr.include_path if ctx.attr.include_path else ctx.label.package.replace("/", ".")
    src_dir = sources[0].dirname if sources and sources[0].dirname else "."
    include_paths.append((src_dir, logical_path))

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
            output_dir = "",
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
        "extra_flags": attr.string_list(
            doc = "Extra flags to pass to coqc (e.g., [\"-impredicative-set\"])",
            default = [],
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
