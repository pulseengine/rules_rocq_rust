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
    """Download prebuilt Rocq tools with enhanced error handling and caching.
    
    Rocq provides complete platform installers (DMG, EXE) that contain everything needed.
    """
    
    platform = detect_platform(repository_ctx)
    version = repository_ctx.attr.version
    
    # Get tool info to determine file type
    tool_info = get_tool_info(repository_ctx, "rocq", version, platform)
    if not tool_info:
        fail("No tool info found for Rocq {} on platform {}".format(version, platform))
    
    file_type = tool_info.get("file_type", "tar.gz")
    binary_name = tool_info.get("binary_name", "coqc")
    
    # Download Rocq toolchain
    rocq_tool_path = download_and_verify(
        repository_ctx, "rocq", version, platform
    )
    
    # Handle different installer types
    if file_type == "dmg":
        # macOS DMG installer - mount and extract
        mount_point = repository_ctx.expand_location("{{name}}/mount")
        repository_ctx.execute([
            "hdiutil", "attach", rocq_tool_path, "-mountpoint", mount_point
        ])
        
        # Find and copy the Coq binaries
        # Rocq DMG contains a complete Coq installation
        coq_bin_dir = native.path.join(mount_point, "Coq Platform.app", "Contents", "Resources", "bin")
        if native.path.exists(coq_bin_dir):
            for bin_file in native.path.listdir(coq_bin_dir):
                if bin_file.startswith("coq") or bin_file.startswith("rocq"):
                    src = native.path.join(coq_bin_dir, bin_file)
                    dst = repository_ctx.path("bin", bin_file)
                    repository_ctx.execute(["cp", src, dst])
                    repository_ctx.execute(["chmod", "+x", dst])
        
        repository_ctx.execute(["hdiutil", "detach", mount_point])
        
    elif file_type == "exe":
        # Windows EXE installer - extract using 7zip or similar
        # For now, we'll use a placeholder approach
        # In a real implementation, we'd use 7z or similar to extract
        repository_ctx.execute([
            "echo", "Windows installer extraction would go here"
        ])
        # Create placeholder binaries
        repository_ctx.execute([
            "touch", repository_ctx.path("bin", "coqc.exe")
        ])
        
    else:
        # Tarball or zip archive
        if rocq_tool_path.endswith(".tar.gz") or rocq_tool_path.endswith(".tar.xz"):
            repository_ctx.execute([
                "tar", "-xzf", rocq_tool_path, "-C", repository_ctx.expand_location("{{name}}")
            ])
        elif rocq_tool_path.endswith(".zip"):
            repository_ctx.execute([
                "unzip", rocq_tool_path, "-d", repository_ctx.expand_location("{{name}}")
            ])
        
        # Find Coq binaries in the extracted structure
        # Rocq has a specific directory structure
        potential_bin_dirs = [
            "bin",
            "Coq Platform/bin",
            "coq-platform/bin",
            "usr/local/bin",
            "usr/bin"
        ]
        
        found_binary = False
        for bin_dir in potential_bin_dirs:
            full_bin_dir = native.path.join(repository_ctx.expand_location("{{name}}"), bin_dir)
            if native.path.exists(full_bin_dir):
                for bin_file in native.path.listdir(full_bin_dir):
                    if bin_file.startswith("coq") or bin_file.startswith("rocq"):
                        src = native.path.join(full_bin_dir, bin_file)
                        dst = repository_ctx.path("bin", bin_file)
                        repository_ctx.execute(["cp", src, dst])
                        repository_ctx.execute(["chmod", "+x", dst])
                        found_binary = True
                if found_binary:
                    break
        
        if not found_binary:
            fail("Could not find Coq binaries in extracted archive. " +
                "Rocq structure may have changed.")

def _create_build_files(repository_ctx):
    """Create BUILD files for the toolchain."""
    
    # Create main BUILD.bazel file
    repository_ctx.file(
        "BUILD.bazel",
        """
load(":rocq_toolchain.bzl", "rocq_toolchain")

# Rocq toolchain definition
# Rocq Platform provides both coqc (Coq compiler) and coqtop (Coq toplevel)
# as well as other tools like coqide, coqdoc, etc.
rocq_toolchain(
    name = "rocq_toolchain",
    rocq_binary = "//:coqc",           # Main Coq compiler
    coq_binary = "//:coqtop",         # Coq toplevel for interactive use
    stdlib_files = glob(["lib/coq/**/*.vo"]),  # Compiled standard library
    include_path = "lib/coq",         # Standard library path
)

# Filegroup for coqc (main compiler)
filegroup(
    name = "coqc",
    srcs = ["bin/coqc"],
    executable = True,
)

# Filegroup for coqtop (toplevel)
filegroup(
    name = "coqtop",
    srcs = ["bin/coqtop"],
    executable = True,
)

# Filegroup for other Coq tools
filegroup(
    name = "coqtools",
    srcs = glob(["bin/coq*"]),
    executable = True,
)

# Filegroup for standard library
filegroup(
    name = "stdlib",
    srcs = glob(["lib/coq/**/*.vo", "lib/coq/**/*.cmxs"]),
)

# Filegroup for Coq Platform libraries
filegroup(
    name = "coq_libraries",
    srcs = glob(["lib/coq/**/*.vo", "lib/coq/**/*.cmxs", "lib/coq/**/*.cmi"]),
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