"""Public entry point to all coq-of-rust integration rules.

Following the exact pattern established by rules_rust.
"""

load(
    "//coq_of_rust:toolchain.bzl",
    _coq_of_rust_stdlib_filegroup = "coq_of_rust_stdlib_filegroup",
)
load(
    "//coq_of_rust/private:coq_of_rust.bzl",
    _coq_of_rust_library = "coq_of_rust_library",
)
load(
    "//coq_of_rust/private:toolchain.bzl",
    _coq_of_rust_toolchain = "coq_of_rust_toolchain",
)

# Public API - following rules_rust naming conventions
coq_of_rust_library = _coq_of_rust_library
# Translates Rust code to Coq using coq-of-rust and compiles with Rocq

coq_of_rust_toolchain = _coq_of_rust_toolchain
# Declares a coq-of-rust toolchain pointing to the translator binary

# Symbolic macro for end-to-end verification (Bazel 8 pattern)
def rocq_rust_proof(name, rust_target, **kwargs):
    """Symbolic macro for end-to-end Rust verification.
    
    This follows the Bazel 8 symbolic macro pattern for higher-level composition.
    """
    native.module_extension(
        implementation = _rocq_rust_proof_impl,
        name = name,
        rust_target = rust_target,
        **kwargs
    )

# Implementation of the symbolic macro
def _rocq_rust_proof_impl(module_ctx):
    """Implementation of rocq_rust_proof symbolic macro."""
    
    # This would create the actual targets in a real implementation
    # For now, we return an empty extension metadata
    return module_ctx.extension_metadata(reproducible = True)