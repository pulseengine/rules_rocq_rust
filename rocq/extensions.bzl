"""Module extensions for using rules_rocq with bzlmod.

Following the exact pattern established by rules_rust extensions.
"""

load("//toolchains:rocq_toolchain.bzl", "rocq_toolchain_repository")

# Tag classes for Rocq toolchain configuration
_RocqToolchainTag = tag_class(
    doc = "Tags for defining Rocq toolchains",
    attrs = {
        "version": attr.string(
            doc = "Rocq version to use",
            default = "2025.01.0",
        ),
        "strategy": attr.string(
            doc = "Tool acquisition strategy",
            default = "download",
            values = ["download"],
        ),
        "editions": attr.string_list(
            doc = "Supported Coq/Rocq editions",
            default = ["2021"],
        ),
    }
)

# Rocq module extension implementation
def _rocq_impl(module_ctx):
    """Implementation of Rocq toolchain extension.

    This follows the exact pattern from rules_rust.
    """
    # Collect toolchain configurations from all modules
    toolchains = []
    for mod in module_ctx.modules:
        for toolchain in mod.tags.toolchain:
            toolchains.append(toolchain)
    
    # Use the first toolchain configuration (following rules_rust pattern)
    if toolchains:
        config = toolchains[0]
        
        # Create toolchain repository using our repository rule
        rocq_toolchain_repository(
            name = "rocq_toolchains",
            version = config.version,
            strategy = config.strategy,
        )
    else:
        # Default configuration
        rocq_toolchain_repository(
            name = "rocq_toolchains",
            version = "2025.01.0",
            strategy = "download",
        )
    
    # Return extension metadata (reproducible for caching)
    return module_ctx.extension_metadata(reproducible = True)

# Empty repository helper (from rules_rust) for fallback
def _empty_repository_impl(repository_ctx):
    repository_ctx.file("WORKSPACE.bazel", 'workspace(name = "{}")'.format(repository_ctx.name))
    repository_ctx.file("BUILD.bazel", "")

_empty_repository = repository_rule(
    doc = "Declare an empty repository.",
    implementation = _empty_repository_impl,
)

# Rocq module extension
rocq = module_extension(
    doc = "Rocq toolchain extension.",
    implementation = _rocq_impl,
    tag_classes = {
        "toolchain": _RocqToolchainTag,
    },
)