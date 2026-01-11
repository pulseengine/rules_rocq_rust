"""coq-of-rust module extensions.

Basic extension framework for coq-of-rust toolchain configuration.
This will be enhanced as the implementation matures.
"""

load("@bazel_features//:features.bzl", "bazel_features")

# Basic tag class for coq-of-rust configuration
_CoqOfRustToolchainTag = tag_class(
    doc = "Tags for defining coq-of-rust toolchains",
    attrs = {
        "version": attr.string(
            doc = "coq-of-rust version to use",
            default = "0.5.0",
        ),
        "strategy": attr.string(
            doc = "Tool acquisition strategy",
            default = "download",
            values = ["download"],
        ),
    }
)

# Basic implementation - will be enhanced
# Currently just creates an empty repository as placeholder
def _coq_of_rust_impl(module_ctx):
    """Basic implementation of coq-of-rust toolchain extension."""
    
    # For now, create empty repository
    # This will be replaced with full implementation
    _empty_repository(name = "coq_of_rust_toolchains")
    
    return module_ctx.extension_metadata(reproducible = True)

# Empty repository helper (from rules_rust)
def _empty_repository_impl(repository_ctx):
    repository_ctx.file("WORKSPACE.bazel", 'workspace(name = "{}")'.format(repository_ctx.name))
    repository_ctx.file("BUILD.bazel", "")

_empty_repository = repository_rule(
    doc = "Declare an empty repository.",
    implementation = _empty_repository_impl,
)

# coq-of-rust module extension
coq_of_rust = module_extension(
    doc = "coq-of-rust toolchain extension (placeholder - will be enhanced).",
    implementation = _coq_of_rust_impl,
    tag_classes = {
        "toolchain": _CoqOfRustToolchainTag,
    },
)