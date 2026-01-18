"""Module extensions for using rules_rocq with bzlmod.

Provides Rocq/Coq toolchain setup using nixpkgs for hermetic builds.
"""

load("//toolchains:rocq_nix_toolchain.bzl", "rocq_nix_toolchain_repository")

# Tag classes for Rocq toolchain configuration
_RocqToolchainTag = tag_class(
    doc = "Tags for defining Rocq toolchains",
    attrs = {
        "version": attr.string(
            doc = "Coq version to use (e.g., '8.20', '8.19')",
            default = "8.20",
        ),
        "strategy": attr.string(
            doc = "Tool acquisition strategy: 'nix' for hermetic nixpkgs",
            default = "nix",
            values = ["nix"],
        ),
    },
)

# Rocq module extension implementation
def _rocq_impl(module_ctx):
    """Implementation of Rocq toolchain extension.

    Uses nixpkgs to provide hermetic Coq installation.
    """
    # Collect toolchain configurations from all modules
    toolchains = []
    for mod in module_ctx.modules:
        for toolchain in mod.tags.toolchain:
            toolchains.append(toolchain)

    # Use the first toolchain configuration
    if toolchains:
        config = toolchains[0]
        coq_version = config.version
    else:
        # Default configuration
        coq_version = "8.20"

    # Create nix-based toolchain repository
    rocq_nix_toolchain_repository(
        name = "rocq_toolchains",
        coq_version = coq_version,
    )

    # Return extension metadata (reproducible for caching)
    return module_ctx.extension_metadata(reproducible = True)

# Rocq module extension
rocq = module_extension(
    doc = "Rocq/Coq toolchain extension using nixpkgs.",
    implementation = _rocq_impl,
    tag_classes = {
        "toolchain": _RocqToolchainTag,
    },
)
