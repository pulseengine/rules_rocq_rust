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
    
    # Extract the toolchain with enhanced error handling
    if rocq_tool_path.endswith(".tar.gz") or rocq_tool_path.endswith(".tar.xz"):
        print("Extracting Rocq toolchain from: {}".format(rocq_tool_path))
        repository_ctx.execute([
            "tar", "-xzf", rocq_tool_path, "-C", repository_ctx.expand_location("{{name}}")
        ])
        
        # Enhanced binary discovery with multiple patterns
        rocq_bin_dirs = [
            native.path.join(repository_ctx.expand_location("{{name}}"), "bin"),
            native.path.join(repository_ctx.expand_location("{{name}}"), "Coq Platform.app", "Contents", "Resources", "bin"),
            native.path.join(repository_ctx.expand_location("{{name}}"), "Coq-Platform-release-*", "bin"),
        ]
        
        binaries_found = []
        for bin_dir in rocq_bin_dirs:
            if native.path.exists(bin_dir):
                for bin_file in ["coqc", "coqtop", "coqide", "coqdoc"]:
                    src = native.path.join(bin_dir, bin_file)
                    if native.path.exists(src):
                        dst = repository_ctx.path("bin", bin_file)
                        repository_ctx.execute(["cp", src, dst])
                        repository_ctx.execute(["chmod", "+x", dst])
                        binaries_found.append(bin_file)
                        print("Found and copied: {}".format(bin_file))
        
        if not binaries_found:
            print("Warning: No Rocq binaries found in extracted archive")
            print("Attempting recursive search for coq* binaries...")
            
            # Recursive search for any coq* binaries
            find_result = repository_ctx.execute([
                "find", repository_ctx.expand_location("{{name}}"), 
                "-name", "coq*", 
                "-type", "f", 
                "-executable"
            ])
            
            if find_result.return_code == 0 and find_result.stdout:
                for found_file in find_result.stdout.strip().split('\n'):
                    if found_file:
                        bin_name = native.path.basename(found_file)
                        dst = repository_ctx.path("bin", bin_name)
                        repository_ctx.execute(["cp", found_file, dst])
                        repository_ctx.execute(["chmod", "+x", dst])
                        binaries_found.append(bin_name)
                        print("Found via recursive search: {}".format(bin_name))
            else:
                fail("No Rocq binaries found in downloaded archive. The archive structure may have changed.")
    elif rocq_tool_path.endswith(".dmg"):
        # macOS DMG extraction
        print("Extracting macOS DMG: {}".format(rocq_tool_path))
        mount_point = repository_ctx.expand_location("{{name}}/dmg_mount")
        repository_ctx.execute(["mkdir", "-p", mount_point])
        
        # Mount DMG and copy contents
        repository_ctx.execute([
            "hdiutil", "attach", "-mountpoint", mount_point, rocq_tool_path
        ])
        
        # Copy binaries from DMG
        dmg_bin_dir = native.path.join(mount_point, "Coq Platform.app", "Contents", "Resources", "bin")
        if native.path.exists(dmg_bin_dir):
            for bin_file in ["coqc", "coqtop", "coqide", "coqdoc"]:
                src = native.path.join(dmg_bin_dir, bin_file)
                if native.path.exists(src):
                    dst = repository_ctx.path("bin", bin_file)
                    repository_ctx.execute(["cp", src, dst])
                    repository_ctx.execute(["chmod", "+x", dst])
                    print("Found and copied from DMG: {}".format(bin_file))
        
        # Unmount DMG
        repository_ctx.execute(["hdiutil", "detach", mount_point])
     elif rocq_tool_path.endswith(".exe"):
        # Windows EXE extraction using 7zip
        print("Windows EXE installer detected: {}".format(rocq_tool_path))
        
        # Try to extract using 7zip if available
        try:
            # Check if 7zip is available
            seven_zip = repository_ctx.which("7z")
            if seven_zip:
                print("Extracting Windows EXE using 7zip: {}".format(seven_zip))
                repository_ctx.execute([
                    str(seven_zip), "x", rocq_tool_path, 
                    "-o" + repository_ctx.expand_location("{{name}}")
                ])
                
                # Look for extracted binaries
                extracted_dir = repository_ctx.expand_location("{{name}}")
                for bin_file in ["coqc.exe", "coqtop.exe", "coqide.exe", "coqdoc.exe"]:
                    src = native.path.join(extracted_dir, bin_file)
                    if native.path.exists(src):
                        dst = repository_ctx.path("bin", bin_file)
                        repository_ctx.execute(["cp", src, dst])
                        repository_ctx.execute(["chmod", "+x", dst])
                        print("Found and copied: {}".format(bin_file))
            else:
                print("Warning: 7zip not found for Windows EXE extraction")
                fail("Windows EXE extraction requires 7zip (7z) tool to be available in PATH")
        except Exception as e:
            fail("Windows EXE extraction failed: {}. Ensure 7zip is installed and available.".format(str(e)))
    else:
        fail("Unsupported archive format: {}".format(rocq_tool_path))
    
    # Extract libraries and standard files
    _extract_rocq_libraries(repository_ctx)

def _extract_rocq_libraries(repository_ctx):
    """Extract Rocq libraries and standard files."""
    
    print("Extracting Rocq libraries and standard files...")
    
    # Library discovery patterns
    lib_dirs = [
        native.path.join(repository_ctx.expand_location("{{name}}"), "lib"),
        native.path.join(repository_ctx.expand_location("{{name}}"), "Coq Platform.app", "Contents", "Resources", "lib"),
        native.path.join(repository_ctx.expand_location("{{name}}"), "Coq-Platform-release-*", "lib"),
        native.path.join(repository_ctx.expand_location("{{name}}"), "share", "coq"),
    ]
    
    # Copy libraries
    repository_ctx.execute(["mkdir", "-p", "lib"])
    
    for lib_dir in lib_dirs:
        if native.path.exists(lib_dir):
            print("Copying libraries from: {}".format(lib_dir))
            repository_ctx.execute([
                "cp", "-r", lib_dir, "lib/"
            ])
            break
    
    # Verify we have the standard library
    stdlib_check = repository_ctx.path("lib/coq/theories")
    if not stdlib_check.exists:
        print("Warning: Standard library not found in expected location")
        print("Attempting recursive search for Coq libraries...")
        
        # Recursive search for Coq libraries
        find_result = repository_ctx.execute([
            "find", repository_ctx.expand_location("{{name}}"), 
            "-name", "*coq*", 
            "-type", "d"
        ])
        
        if find_result.return_code == 0 and find_result.stdout:
            for found_dir in find_result.stdout.strip().split('\n'):
                if found_dir and "theories" in found_dir:
                    repository_ctx.execute([
                        "cp", "-r", found_dir, "lib/"
                    ])
                    print("Found and copied library: {}".format(found_dir))
                    break

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
    
    # Add library filegroups
    repository_ctx.append(
        "BUILD.bazel",
        """

# Standard library
filegroup(
    name = "stdlib",
    srcs = glob(["lib/**/*.vo", "lib/**/*.cmxs", "lib/**/*.so", "lib/**/*.dylib"]),
)

# Coq theories
filegroup(
    name = "coq_theories",
    srcs = glob(["lib/**/*.v", "lib/**/*.glob"]),
)

# Complete libraries
filegroup(
    name = "coq_libraries",
    srcs = glob(["lib/**/*"]),
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

