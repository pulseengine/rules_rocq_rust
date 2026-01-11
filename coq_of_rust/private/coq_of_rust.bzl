"""Core coq-of-rust integration rules - PRIVATE implementation.

This follows the exact pattern used in rules_rust's private implementation.
"""

load("@bazel_skylib//lib:deps.bzl", "deps")

# Provider for coq-of-rust translation results
CoqOfRustInfo = provider(
    doc = "Information about coq-of-rust translation results",
    fields = {
        "generated_sources": "depset of generated .v files",
        "rust_sources": "depset of original Rust source files",
        "transitive_deps": "depset of all transitive dependencies",
    }
)

# Core coq-of-rust translation rule
def _coq_of_rust_library_impl(ctx):
    """Translate Rust code to Coq using coq-of-rust.
    
    Follows rules_rust patterns:
    - Use depsets for transitive dependencies
    - Explicit inputs/outputs for hermetic builds
    - ctx.actions.args() for command-line construction
    """
    
    # Get Rust sources and coq-of-rust tool
    rust_sources = ctx.files.rust_sources
    if not rust_sources:
        return []
    
    # Process Rust dependencies
    transitive_deps = depset()
    for dep in ctx.attr.rust_deps:
        if hasattr(dep, "rust"):
            transitive_deps = depset.union(transitive_deps, dep.rust.transitive_deps)
    
    # Translate each Rust file to Coq
    generated_sources = depset()
    
    for rust_src in rust_sources:
        if rust_src.path.endswith(".rs"):
            output = rust_src.basename + ".v"
            output_file = ctx.actions.declare_file(output)
            
            # Use ctx.actions.run for hermetic execution
            ctx.actions.run(
                inputs = depset([rust_src]) + transitive_deps,
                outputs = [output_file],
                executable = ctx.executable._coq_of_rust_binary,
                arguments = [
                    "translate",
                    rust_src.path,
                    "--output",
                    output_file.path,
                    "--edition",
                    ctx.attr.edition if ctx.attr.edition else "2021",
                ],
            )
            
            generated_sources = depset.union(generated_sources, depset([output_file]))
    
    # Return providers following rules_rust pattern
    return [
        DefaultInfo(
            files = generated_sources,
            data_runfiles = ctx.runfiles(files = generated_sources),
        ),
        CoqOfRustInfo(
            generated_sources = generated_sources,
            rust_sources = depset(rust_sources),
            transitive_deps = transitive_deps + generated_sources,
        ),
    ]

# coq-of-rust library rule
coq_of_rust_library = rule(
    implementation = _coq_of_rust_library_impl,
    attrs = {
        "rust_sources": attr.label_list(
            allow_files = [".rs"],
            doc = "Rust source files to translate",
        ),
        "rust_deps": attr.label_list(
            doc = "Dependencies on Rust libraries",
        ),
        "edition": attr.string(
            doc = "Rust edition to use",
            default = "2021",
        ),
    },
    doc = "Translates Rust code to Coq using coq-of-rust and compiles with Rocq",
)