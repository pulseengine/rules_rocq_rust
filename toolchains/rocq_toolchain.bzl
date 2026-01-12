"""Rocq toolchain definitions with enhanced tool management

Following the exact pattern established by rules_wasm_component.
"""

load("//checksums:registry.bzl", "get_tool_info", "get_tool_checksum")
load("//:toolchains/tool_registry.bzl", "detect_platform", "download_and_verify")
load("@bazel_skylib//lib:native.bzl", "native")

# Rocq Toolchain Implementation
def _rocq_toolchain_repository_impl(repository_ctx):
    """Create Rocq toolchain repository.
    
    This is the main implementation following rules_rust patterns.
    Always uses hermetic downloads for reproducibility.
    """
    
    strategy = repository_ctx.attr.strategy
    platform = detect_platform(repository_ctx)
    version = repository_ctx.attr.version
    
    print("Setting up Rocq toolchain {} for platform {} using strategy {}".format(
        version, platform, strategy
    ))
    
    # Only support download strategy for hermeticity
    if strategy == "download":
        _setup_downloaded_rocq_tools(repository_ctx)
    else:
        fail("Unknown strategy: {}. Must be 'download' (only hermetic downloads supported)".format(strategy))
    
    # Create BUILD files
    _create_build_files(repository_ctx)

def _setup_downloaded_rocq_tools(repository_ctx):
    """Download prebuilt Rocq tools."""
    
    platform = detect_platform(repository_ctx)
    version = repository_ctx.attr.version
    
    # Download Rocq toolchain
    rocq_tool_path = download_and_verify(
        repository_ctx, "rocq", version, platform
    )
    
    # Extract the toolchain
    if rocq_tool_path.endswith(".tar.gz") or rocq_tool_path.endswith(".tar.xz"):
        repository_ctx.execute([
            "tar", "-xzf", rocq_tool_path, "-C", repository_ctx.expand_location("{{name}}")
        ])
        
        # Find and setup Rocq binaries
        rocq_bin_dir = native.path.join(repository_ctx.expand_location("{{name}}"), "bin")
        if native.path.exists(rocq_bin_dir):
            for bin_file in ["coqc", "coqtop", "coqide", "coqdoc"]:
                src = native.path.join(rocq_bin_dir, bin_file)
                if native.path.exists(src):
                    dst = repository_ctx.path("bin", bin_file)
                    repository_ctx.execute(["cp", src, dst])
                    repository_ctx.execute(["chmod", "+x", dst])

def _create_build_files(repository_ctx):
    """Create BUILD files for Rocq toolchain."""
    
    # Create main BUILD.bazel file
    repository_ctx.file(
        "BUILD.bazel",
        """
# Rocq toolchain

filegroup(
    name = "coqc",
    srcs = ["bin/coqc"],
    executable = True,
)

filegroup(
    name = "coqtop",
    srcs = ["bin/coqtop"],
    executable = True,
)

filegroup(
    name = "coqide",
    srcs = ["bin/coqide"],
    executable = True,
)

filegroup(
    name = "coqdoc",
    srcs = ["bin/coqdoc"],
    executable = True,
)

filegroup(
    name = "coq_tools",
    srcs = glob(["bin/coq*"]),
    executable = True,
)
"""
    )

# Rocq toolchain repository rule
def rocq_toolchain_repository(name, version, strategy="download"):
    """Create a Rocq toolchain repository.
    
    Args:
        name: Name for the repository
        version: Rocq version to download
        strategy: Acquisition strategy ('download' or 'system')
    """
    native.repository_rule(
        name = name,
        implementation = _rocq_toolchain_repository_impl,
        attrs = {
            "version": attr.string(default = version),
            "strategy": attr.string(default = "download"),
        },
    )

