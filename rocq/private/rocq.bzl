"""Core Rocq compilation rules - PRIVATE implementation.

This follows the exact pattern used in rules_rust's private implementation.
"""

load("@bazel_skylib//lib:paths.bzl", "paths")

# Provider for Rocq compilation information
RocqInfo = provider(
    doc = "Information about Rocq compilation results",
    fields = {
        "compiled_objects": "depset of .vo files",
        "include_paths": "list of include paths for dependent libraries",
        "transitive_deps": "depset of all transitive Rocq dependencies",
    }
)

# Core Rocq library compilation rule
def _rocq_library_impl(ctx):
    """Compile .v files to .vo using Rocq with proper dependency management.
    
    Follows rules_rust patterns:
    - Use depsets for transitive dependencies
    - Explicit inputs/outputs for hermetic builds
    - ctx.actions.args() for command-line construction
    """
    
    # Validate source files
    sources = ctx.files.srcs
    if not sources:
        fail("rocq_library requires at least one source file")
    
    # Validate file extensions
    for src in sources:
        if not src.path.endswith(".v"):
            fail("rocq_library only accepts .v files, got: " + src.path)
    
    # Check for rocq binary
    if not hasattr(ctx, "executable") or not hasattr(ctx.executable, "_rocq_binary"):
        fail("rocq_library requires Rocq toolchain to be configured")
    
    # Process dependencies to get transitive include paths and .vo files
    transitive_deps = depset()
    include_paths = []
    
    for dep in ctx.attr.deps:
        if hasattr(dep, "rocq"):
            transitive_deps = depset.union(transitive_deps, dep.rocq.transitive_deps)
            include_paths.extend(dep.rocq.include_paths)
    
    # Add current library's include path
    include_paths.append(ctx.attr.include_path if ctx.attr.include_path else ".")
    
    # Compile each .v file to .vo
    compiled_objects = depset()
    
    for src in sources:
        if src.path.endswith(".v"):
            output = src.basename + ".vo"
            output_file = ctx.actions.declare_file(output)
            
            # Use ctx.actions.run for hermetic execution
            ctx.actions.run(
                inputs = depset([src]) + transitive_deps,
                outputs = [output_file],
                executable = ctx.executable._rocq_binary,
                arguments = [
                    "--compile",
                    src.path,
                    "--output",
                    output_file.path,
                ] + ["--include-paths", ",".join(include_paths)] if include_paths else [],
                env = {
                    "ROCQ_LIBRARY_PATH": ":".join(include_paths),
                } if include_paths else {},
            )
            
            compiled_objects = depset.union(compiled_objects, depset([output_file]))
    
    # Return providers following rules_rust pattern
    return [
        DefaultInfo(
            files = compiled_objects,
            data_runfiles = ctx.runfiles(files = compiled_objects),
        ),
        RocqInfo(
            compiled_objects = compiled_objects,
            include_paths = include_paths,
            transitive_deps = transitive_deps + compiled_objects,
        ),
    ]

# Rocq proof test rule
def _rocq_proof_test_impl(ctx):
    """Run Rocq in proof-checking mode.
    
    Fails the build if proofs don't complete or Qed.
    """
    
    sources = ctx.files.srcs
    if not sources:
        return []
    
    # Collect dependencies
    transitive_deps = depset()
    include_paths = []
    
    for dep in ctx.attr.deps:
        if hasattr(dep, "rocq"):
            transitive_deps = depset.union(transitive_deps, dep.rocq.transitive_deps)
            include_paths.extend(dep.rocq.include_paths)
    
    # Run proof checking
    ctx.actions.run(
        inputs = depset(sources) + transitive_deps,
        outputs = [],  # Proof checking doesn't produce files, just validation
        executable = ctx.executable._rocq_binary,
        arguments = [
            "--proof-check",
            "--fail-on-incomplete",
        ] + [src.path for src in sources] + 
        ["--include-paths", ",".join(include_paths)] if include_paths else [],
        env = {
            "ROCQ_LIBRARY_PATH": ":".join(include_paths),
        } if include_paths else {},
    )
    
    return [DefaultInfo()]

# Rule definitions
rocq_library = rule(
    implementation = _rocq_library_impl,
    attrs = {
        "srcs": attr.label_list(
            allow_files = [".v"],
            doc = "Rocq source files (.v)",
        ),
        "deps": attr.label_list(
            doc = "Dependencies on other Rocq libraries",
        ),
        "include_path": attr.string(
            doc = "Additional include path for this library",
        ),
    },
    doc = "Compiles Rocq .v files into .vo files with proper dependency management",
)

rocq_proof_test = rule(
    implementation = _rocq_proof_test_impl,
    attrs = {
        "srcs": attr.label_list(
            allow_files = [".v"],
            doc = "Rocq proof files to check",
        ),
        "deps": attr.label_list(
            doc = "Dependencies on other Rocq libraries",
        ),
    },
    test = True,
    doc = "Runs Rocq in proof-checking mode, fails build if proofs don't complete",
)