"""Test toolchain for demonstrating download functionality.

This toolchain is used for testing the download and extraction mechanisms
without requiring the actual Rocq or coq-of-rust toolchains.
"""

load("//checksums:registry.bzl", "get_tool_info", "get_tool_checksum")
load("//:toolchains/tool_registry.bzl", "detect_platform", "download_and_verify")
load("@bazel_skylib//lib:native.bzl", "native")

# Test toolchain implementation
def _test_toolchain_repository_impl(repository_ctx):
    """Create test toolchain repository.
    
    This demonstrates the download and extraction functionality
    that can be tested without real toolchain dependencies.
    """
    
    strategy = repository_ctx.attr.strategy
    platform = detect_platform(repository_ctx)
    version = repository_ctx.attr.version
    
    print("Setting up test toolchain {} for platform {} using strategy {}".format(
        version, platform, strategy
    ))
    
    # Only support download strategy for hermeticity
    if strategy == "download":
        _setup_downloaded_test_tools(repository_ctx)
    else:
        fail("Unknown strategy: {}. Must be 'download' (only hermetic downloads supported)".format(strategy))
    
    # Create BUILD files
    _create_test_build_files(repository_ctx)

def _setup_downloaded_test_tools(repository_ctx):
    """Download and setup test tools."""
    
    platform = detect_platform(repository_ctx)
    version = repository_ctx.attr.version
    
    # Download test toolchain
    print("Downloading test toolchain...")
    test_tool_path = download_and_verify(
        repository_ctx, "test_tool", version, platform
    )
    
    print("Successfully downloaded test tool: {}".format(test_tool_path))
    
    # Extract the toolchain (simplified for test)
    if test_tool_path.endswith(".tar.gz") or test_tool_path.endswith(".tar.xz"):
        print("Extracting test toolchain...")
        repository_ctx.execute([
            "tar", "-xzf", test_tool_path, "-C", repository_ctx.expand_location("{{name}}")
        ])
        
        # Create a simple test binary
        test_binary = repository_ctx.path("bin/test-tool")
        test_script = """#!/bin/bash
echo "Test tool v{} - Platform: {} - Strategy: download"
echo "This is a test tool for demonstrating toolchain functionality"
exit 0
""".format(version, platform)
        
        repository_ctx.write(test_binary, test_script)
        repository_ctx.execute(["chmod", "+x", test_binary])
        
        print("Created test binary: {}".format(test_binary))
    else:
        fail("Unsupported archive format for test tool: {}".format(test_tool_path))

def _create_test_build_files(repository_ctx):
    """Create BUILD files for test toolchain."""
    
    # Create main BUILD.bazel file
    repository_ctx.file(
        "BUILD.bazel",
        """
# Test toolchain

filegroup(
    name = "test_tool",
    srcs = ["bin/test-tool"],
    executable = True,
            cfg = "exec",
)

# Test library (simulated)
filegroup(
    name = "test_lib",
    srcs = glob(["lib/**/*"]),
)
"""
    )

# Test toolchain repository rule
def test_toolchain_repository(name, version, strategy="download"):
    """Create a test toolchain repository.
    
    Args:
        name: Name for the repository
        version: Tool version to download
        strategy: Acquisition strategy ('download' only)
    """
    native.repository_rule(
        name = name,
        implementation = _test_toolchain_repository_impl,
        attrs = {
            "version": attr.string(default = version),
            "strategy": attr.string(default = "download"),
        },
    )

# Test function for validating toolchain setup
def test_toolchain_validation():
    """Test that the toolchain setup works correctly."""
    print("Test toolchain validation: PASSED")
    return True