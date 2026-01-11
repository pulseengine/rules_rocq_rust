"""Rocq toolchain definitions with enhanced tool management

Following the exact pattern established by rules_wasm_component.
"""

load("//checksums:registry.bzl", "get_tool_info", "get_tool_checksum")
load("//toolchains:tool_registry.bzl", "detect_platform", "download_and_verify")

# =============================================================================
# Rocq Toolchain Implementation
# =============================================================================

def _rocq_toolchain_repository_impl(repository_ctx):
    """Create Rocq toolchain repository with enhanced tool management.
    
    This follows the exact pattern from rules_wasm_component.
    """
    
    strategy = repository_ctx.attr.strategy
    platform = detect_platform(repository_ctx)
    version = repository_ctx.attr.version
    
    # Log diagnostic information (following rules_wasm_component pattern)
    print("Setting up Rocq toolchain {} for platform {} using strategy {}".format(
        version, platform, strategy
    ))
    
    # Use download strategy for fast, hermetic builds with prebuilt binaries
    if strategy == "download":
        _setup_downloaded_rocq_tools(repository_ctx)
    else:
        fail("Unknown strategy: {}. Must be 'download' (other strategies not yet implemented)".format(strategy))
    
    # Create BUILD files
    _create_build_files(repository_ctx)

def _setup_downloaded_rocq_tools(repository_ctx):
    """Download prebuilt Rocq tools with enhanced error handling and caching."""
    
    platform = detect_platform(repository_ctx)
    version = repository_ctx.attr.version
    
    # Download Rocq toolchain
    rocq_tool_path = download_and_verify(
        repository_ctx, "rocq", version, platform
    )
    
    # Extract the toolchain
    if rocq_tool_path.endswith(".tar.gz") or rocq_tool_path.endswith(".tar.xz"):
        # Extract archive
        extracted_dir = repository_ctx.expand_location("{{name}}")
        repository_ctx.execute([
            "tar",
            "-xzf",
            rocq_tool_path,
            "-C",
            extracted_dir,
        ])
        
        # Find the actual binary (following rules_wasm_component pattern)
        rocq_binary = None
        for root, dirs, files in native.path.walk(extracted_dir):
            for file in files:
                if file.startswith("rocq") and not file.endswith(".txt") and not file.endswith(".md"):
                    rocq_binary = native.path.join(root, file)
                    break
            if rocq_binary:
                break
        
        if not rocq_binary:
            fail("Could not find rocq binary in extracted archive")
        
        # Make binary executable
        repository_ctx.execute(["chmod", "+x", rocq_binary])
        
        # Symlink to standard location
        repository_ctx.symlink(
            rocq_binary,
            repository_ctx.path("bin/rocq")
        )
    else:
        # Single binary file
        repository_ctx.symlink(
            rocq_tool_path,
            repository_ctx.path("bin/rocq")
        )

def _create_build_files(repository_ctx):
    """Create BUILD files for the toolchain."""
    
    # Create main BUILD.bazel file
    repository_ctx.file(
        "BUILD.bazel",
        """
load(":rocq_toolchain.bzl", "rocq_toolchain")

# Rocq toolchain definition
rocq_toolchain(
    name = "rocq_toolchain",
    rocq_binary = "//:rocq",
    coq_binary = "//:coq",  # Would be set up similarly
    stdlib_files = glob(["stdlib/**/*.vo"]),
    include_path = "stdlib",
)

# Filegroup for the rocq binary
filegroup(
    name = "rocq",
    srcs = ["bin/rocq"],
    executable = True,
)

# Filegroup for coq binary (placeholder)
filegroup(
    name = "coq",
    srcs = ["bin/coq"],  # Would be downloaded similarly
    executable = True,
)
"""
    )
    
    # Create toolchain BUILD file
    repository_ctx.file(
        "rocq_toolchain.bzl",
        """
load("@rules_rocq_rust//rocq:toolchain.bzl", "rocq_toolchain")

# Re-export the rocq_toolchain rule
rocq_toolchain = rocq_toolchain
"""
    )

# =============================================================================
# Repository Rule Definition
# =============================================================================

def rocq_toolchain_repository(name, version, strategy="download"):
    """Create a Rocq toolchain repository.
    
    Args:
        name: Name for the repository
        version: Rocq version to download
        strategy: Acquisition strategy (currently only "download" supported)
    """
    native.repository_rule(
        name = name,
        implementation = _rocq_toolchain_repository_impl,
        attrs = {
            "version": attr.string(default = version),
            "strategy": attr.string(default = strategy),
        },
    )

# Register the repository rule for use in MODULE.bazel
rocq_toolchain_repository = repository_rule(
    implementation = _rocq_toolchain_repository_impl,
    attrs = {
        "version": attr.string(default = "2025.01.0"),
        "strategy": attr.string(default = "download"),
    },
)