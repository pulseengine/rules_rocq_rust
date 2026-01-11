"""OCaml toolchain definitions for QuickChick support.

This provides optional OCaml toolchain setup for users who need QuickChick
or other OCaml-based Coq plugins.
"""

load("//checksums:registry.bzl", "get_tool_info", "get_tool_checksum")
load("//toolchains:tool_registry.bzl", "detect_platform", "download_and_verify")

def _ocaml_toolchain_repository_impl(repository_ctx):
    """Create OCaml toolchain repository.
    
    This is only needed for advanced features like QuickChick.
    Always uses hermetic downloads for reproducibility.
    """
    
    strategy = repository_ctx.attr.strategy
    platform = detect_platform(repository_ctx)
    version = repository_ctx.attr.version
    
    print("Setting up OCaml toolchain {} for platform {} using strategy {}".format(
        version, platform, strategy
    ))
    
    # Only support download strategy for hermeticity
    if strategy == "download":
        _setup_downloaded_ocaml_tools(repository_ctx)
    else:
        fail("Unknown strategy: {}. Must be 'download' (only hermetic downloads supported)".format(strategy))
    
    # Create BUILD files
    _create_ocaml_build_files(repository_ctx)

def _setup_downloaded_ocaml_tools(repository_ctx):
    """Download prebuilt OCaml tools."""
    
    platform = detect_platform(repository_ctx)
    version = repository_ctx.attr.version
    
    # Download OCaml toolchain
    ocaml_tool_path = download_and_verify(
        repository_ctx, "ocaml", version, platform
    )
    
    # Extract the toolchain
    if ocaml_tool_path.endswith(".tar.gz") or ocaml_tool_path.endswith(".tar.xz"):
        repository_ctx.execute([
            "tar", "-xzf", ocaml_tool_path, "-C", repository_ctx.expand_location("{{name}}")
        ])
        
        # Find and setup OCaml binaries
        ocaml_bin_dir = native.path.join(repository_ctx.expand_location("{{name}}"), "bin")
        if native.path.exists(ocaml_bin_dir):
            for bin_file in ["ocaml", "ocamlc", "ocamlopt", "ocamlrun"]:
                src = native.path.join(ocaml_bin_dir, bin_file)
                if native.path.exists(src):
                    dst = repository_ctx.path("bin", bin_file)
                    repository_ctx.execute(["cp", src, dst])
                    repository_ctx.execute(["chmod", "+x", dst])

def _setup_system_ocaml_tools(repository_ctx):
    """System strategy is not supported - use download for hermeticity."""
    fail("System OCaml strategy is not supported. Use 'download' strategy for hermetic builds.")

def _create_ocaml_build_files(repository_ctx):
    """Create BUILD files for OCaml toolchain."""
    
    # Create main BUILD.bazel file
    repository_ctx.file(
        "BUILD.bazel",
        """
# OCaml toolchain for QuickChick support

filegroup(
    name = "ocaml",
    srcs = ["bin/ocaml"],
    executable = True,
)

filegroup(
    name = "ocamlc",
    srcs = ["bin/ocamlc"],
    executable = True,
)

filegroup(
    name = "ocamlopt",
    srcs = ["bin/ocamlopt"],
    executable = True,
)

filegroup(
    name = "ocamlrun",
    srcs = ["bin/ocamlrun"],
    executable = True,
)

filegroup(
    name = "ocaml_tools",
    srcs = glob(["bin/ocaml*"]),
    executable = True,
)
"""
    )

# OCaml toolchain repository rule
def ocaml_toolchain_repository(name, version, strategy="download"):
    """Create an OCaml toolchain repository.
    
    Args:
        name: Name for the repository
        version: OCaml version to download
        strategy: Acquisition strategy ('download' or 'system')
    """
    native.repository_rule(
        name = name,
        implementation = _ocaml_toolchain_repository_impl,
        attrs = {
            "version": attr.string(default = version),
            "strategy": attr.string(default = "download"),
        },
    )

# Register the repository rule
ocaml_toolchain_repository = repository_rule(
    implementation = _ocaml_toolchain_repository_impl,
    attrs = {
        "version": attr.string(default = "5.1.1"),
        "strategy": attr.string(default = "download"),
    },
)