"""Module extensions for optional OCaml toolchain support.

This provides OCaml toolchain setup for users who need QuickChick
or other OCaml-based Coq plugins.
"""

load("//toolchains:ocaml_toolchain.bzl", "ocaml_toolchain_repository")

# Tag classes for OCaml toolchain configuration
_OcamlToolchainTag = tag_class(
    doc = "Tags for defining OCaml toolchains",
    attrs = {
        "version": attr.string(
            doc = "OCaml version to use",
            default = "5.1.1",
        ),
        "strategy": attr.string(
            doc = "Tool acquisition strategy",
            default = "download",
            values = ["download"],
        ),
    }
)

# OCaml module extension implementation
def _ocaml_impl(module_ctx):
    """Implementation of OCaml toolchain extension."""
    
    # Collect toolchain configurations from all modules
    toolchains = []
    for mod in module_ctx.modules:
        for toolchain in mod.tags.toolchain:
            toolchains.append(toolchain)
    
    # Use the first toolchain configuration
    if toolchains:
        config = toolchains[0]
        
        # Create OCaml toolchain repository
        ocaml_toolchain_repository(
            name = "ocaml_toolchains",
            version = config.version,
            strategy = config.strategy,
        )
    else:
        # Default configuration
        ocaml_toolchain_repository(
            name = "ocaml_toolchains",
            version = "5.1.1",
            strategy = "download",
        )
    
    # Return extension metadata (reproducible for caching)
    return module_ctx.extension_metadata(reproducible = True)

# OCaml module extension
ocaml = module_extension(
    doc = "OCaml toolchain extension for QuickChick support.",
    implementation = _ocaml_impl,
    tag_classes = {
        "toolchain": _OcamlToolchainTag,
    },
)