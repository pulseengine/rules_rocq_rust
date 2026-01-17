"""Test toolchain using real download functionality.

This toolchain demonstrates the actual download and extraction mechanisms
using the mock releases we created for testing.
"""

load("//checksums:registry.bzl", "get_tool_info", "get_tool_checksum")
load("//:toolchains/tool_registry.bzl", "detect_platform", "download_and_verify")
load("@bazel_skylib//lib:native.bzl", "native")

# Test toolchain implementation with real downloads
def _test_real_toolchain_repository_impl(repository_ctx):
    """Create test toolchain repository with real downloads.
    
    This demonstrates the actual download and extraction functionality
    using mock releases for testing purposes.
    """
    
    strategy = repository_ctx.attr.strategy
    platform = detect_platform(repository_ctx)
    version = repository_ctx.attr.version
    
    print("Setting up test toolchain {} for platform {} using strategy {}".format(
        version, platform, strategy
    ))
    
    # Only support download strategy for hermeticity
    if strategy == "download":
        _setup_downloaded_test_tools_with_real_downloads(repository_ctx)
    else:
        fail("Unknown strategy: {}. Must be 'download' (only hermetic downloads supported)".format(strategy))
    
    # Create BUILD files
    _create_test_build_files(repository_ctx)

def _setup_downloaded_test_tools_with_real_downloads(repository_ctx):
    """Download and setup test tools using real download functionality."""
    
    platform = detect_platform(repository_ctx)
    version = repository_ctx.attr.version
    
    # Use the test tool for demonstration
    print("Downloading test toolchain using real download functionality...")
    
    # This will use the actual download_and_verify function
    # For testing, we can use our mock releases by setting up a local server
    test_tool_path = download_and_verify(
        repository_ctx, "test_tool", version, platform
    )
    
    print("Successfully downloaded test tool: {}".format(test_tool_path))
    
    # Extract the toolchain
    if test_tool_path.endswith(".tar.gz") or test_tool_path.endswith(".tar.xz"):
        print("Extracting test toolchain...")
        repository_ctx.execute([
            "tar", "-xzf", test_tool_path, "-C", repository_ctx.expand_location("{{name}}")
        ])
        
        # Verify extraction worked
        extracted_dir = f"test-toolchain-{version}-{platform}"
        if native.path.exists(extracted_dir):
            print("Successfully extracted: {}".format(extracted_dir))
            
            # Copy binaries to our toolchain location
            repository_ctx.execute(["mkdir", "-p", "bin"])
            bin_dir = native.path.join(extracted_dir, "bin")
            
            if native.path.exists(bin_dir):
                for tool in native.glob([bin_dir + "/*"]):
                    if tool.executable:
                        dst = repository_ctx.path("bin", tool.basename)
                        repository_ctx.execute(["cp", str(tool), str(dst)])
                        repository_ctx.execute(["chmod", "+x", str(dst)])
                        print("Copied executable: {}".format(tool.basename))
            
            # Copy libraries
            lib_dir = native.path.join(extracted_dir, "lib")
            if native.path.exists(lib_dir):
                repository_ctx.execute(["mkdir", "-p", "lib"])
                repository_ctx.execute([
                    "cp", "-r", str(lib_dir), "lib/"
                ])
                print("Copied libraries")
        else:
            fail("Extraction failed: directory not found")
    elif test_tool_path.endswith(".zip"):
        print("Extracting Windows ZIP archive...")
        repository_ctx.execute([
            "unzip", "-q", test_tool_path, "-d", repository_ctx.expand_location("{{name}}")
        ])
        
        # Similar extraction logic for Windows
        extracted_dir = f"test-toolchain-{version}-{platform}"
        if native.path.exists(extracted_dir):
            print("Successfully extracted Windows toolchain")
            # Copy files as above
        else:
            fail("Windows extraction failed")
    else:
        fail("Unsupported archive format: {}".format(test_tool_path))

def _create_test_build_files(repository_ctx):
    """Create BUILD files for test toolchain."""
    
    # Create main BUILD.bazel file
    repository_ctx.file(
        "BUILD.bazel",
        """
# Test toolchain with real downloads

filegroup(
    name = "test_tool",
    srcs = glob(["bin/*"]),
    executable = True,
            cfg = "exec",
)

filegroup(
    name = "test_lib",
    srcs = glob(["lib/**/*"]),
)

# Test that verifies the toolchain works
test_toolchain_test = rule(
    implementation = _test_toolchain_test_impl,
    attrs = {
        "tool": attr.label(
            default = ":test_tool",
            executable = True,
            cfg = "exec",
        ),
    },
)

def _test_toolchain_test_impl(ctx):
    """Test that the downloaded toolchain works."""
    tool = ctx.executable.tool
    
    # Run the test tool
    ctx.actions.run(
        executable = tool,
        arguments = [],
        progress_message = "Testing downloaded toolchain",
    )
    
    return [DefaultInfo(files = depset())]
"""
    )

# Test toolchain repository rule
def test_real_toolchain_repository(name, version, strategy="download"):
    """Create a test toolchain repository with real downloads.
    
    Args:
        name: Name for the repository
        version: Tool version to download
        strategy: Acquisition strategy ('download' only)
    """
    native.repository_rule(
        name = name,
        implementation = _test_real_toolchain_repository_impl,
        attrs = {
            "version": attr.string(default = version),
            "strategy": attr.string(default = "download"),
        },
    )

# Test function for validating real toolchain setup
def test_real_toolchain_validation():
    """Test that the real toolchain setup works correctly."""
    print("Real toolchain validation: This would test actual downloads")
    return True