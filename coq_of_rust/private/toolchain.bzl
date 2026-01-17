"""coq-of-rust toolchain definitions - PRIVATE implementation.

Following the exact pattern used in rules_rust toolchain definitions.
"""

# coq-of-rust toolchain provider
def _coq_of_rust_toolchain_impl(ctx):
    """Create coq-of-rust toolchain info provider."""
    
    # Get toolchain files
    coq_of_rust_binary = ctx.file.coq_of_rust_binary
    stdlib_files = ctx.files.stdlib_files
    
    # Create toolchain info
    toolchain_info = struct(
        coq_of_rust_binary = coq_of_rust_binary,
        stdlib_files = stdlib_files,
        include_paths = [ctx.attr.include_path] if ctx.attr.include_path else [],
    )
    
    return [toolchain_info]

# coq-of-rust toolchain rule
coq_of_rust_toolchain = rule(
    implementation = _coq_of_rust_toolchain_impl,
    attrs = {
        "coq_of_rust_binary": attr.label(
            allow_single_file = True,
            executable = True,
            cfg = "exec",
            cfg = "exec",
            doc = "coq-of-rust binary",
        ),
        "stdlib_files": attr.label_list(
            allow_files = True,
            doc = "coq-of-rust standard library files",
        ),
        "include_path": attr.string(
            doc = "Standard library include path",
        ),
    },
    doc = "Declares a coq-of-rust toolchain pointing to the translator binary",
)

# Standard library filegroup
def coq_of_rust_stdlib_filegroup(name, srcs = None, **kwargs):
    """Create a filegroup for coq-of-rust standard library files."""
    native.filegroup(
        name = name,
        srcs = srcs,
        **kwargs
    )