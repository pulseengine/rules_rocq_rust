"""Rocq toolchain definitions for hermetic Coq/Rocq builds.

This module provides repository rules for downloading and setting up
the Rocq (Coq) toolchain for use with Bazel.
"""

load("//toolchains:tool_registry.bzl", "detect_platform", "download_and_verify")

# =============================================================================
# Rocq Toolchain Repository Implementation
# =============================================================================

def _rocq_toolchain_repository_impl(repository_ctx):
    """Create Rocq toolchain repository.

    Downloads the Rocq Platform and extracts binaries for use in builds.
    """
    version = repository_ctx.attr.version
    platform = detect_platform(repository_ctx)

    print("Setting up Rocq toolchain {} for platform {}".format(version, platform))

    # Check if platform is supported
    supported = ["darwin_arm64", "windows_amd64"]
    if platform not in supported:
        # Create stub repository for unsupported platforms
        print("WARNING: Rocq Platform binaries not available for {}".format(platform))
        print("Supported platforms: {}".format(", ".join(supported)))
        print("Creating stub toolchain - proofs will not compile")
        _create_stub_repository(repository_ctx)
        return

    # Download the toolchain
    tool_path = download_and_verify(repository_ctx, "rocq", version, platform)
    print("Downloaded toolchain to: {}".format(tool_path))

    # Extract based on format
    if tool_path.endswith(".dmg"):
        _extract_dmg(repository_ctx, tool_path)
    elif tool_path.endswith(".tar.gz"):
        _extract_tar_gz(repository_ctx, tool_path)
    elif tool_path.endswith(".exe"):
        _extract_windows_exe(repository_ctx, tool_path)
    else:
        fail("Unsupported archive format: {}".format(tool_path))

    # Create BUILD file
    _create_build_file(repository_ctx)

def _create_stub_repository(repository_ctx):
    """Create a stub repository for unsupported platforms."""
    repository_ctx.file("BUILD.bazel", """
# Stub Rocq toolchain for unsupported platform
# Proofs will not compile - use a supported platform or install Coq manually

filegroup(
    name = "coqc",
    srcs = [],
    visibility = ["//visibility:public"],
)

filegroup(
    name = "coq_tools",
    srcs = [],
    visibility = ["//visibility:public"],
)

filegroup(
    name = "stdlib",
    srcs = [],
    visibility = ["//visibility:public"],
)
""")
    repository_ctx.file("WORKSPACE.bazel", 'workspace(name = "{}")'.format(repository_ctx.name))

def _extract_dmg(repository_ctx, dmg_path):
    """Extract Coq tools from macOS DMG."""
    print("Extracting macOS DMG: {}".format(dmg_path))

    # Create directories
    repository_ctx.execute(["mkdir", "-p", "bin", "lib"])

    # Mount DMG
    mount_point = "dmg_mount"
    repository_ctx.execute(["mkdir", "-p", mount_point])

    mount_result = repository_ctx.execute([
        "hdiutil", "attach", "-mountpoint", mount_point, "-nobrowse", dmg_path,
    ])

    if mount_result.return_code != 0:
        fail("Failed to mount DMG: {}".format(mount_result.stderr))

    # Find and copy binaries
    # Coq Platform structure: "Coq-Platform*.app/Contents/Resources/bin/"
    find_result = repository_ctx.execute([
        "find", mount_point, "-type", "f", "-name", "coqc",
    ])

    if find_result.return_code == 0 and find_result.stdout.strip():
        coqc_path = find_result.stdout.strip().split("\n")[0]
        bin_dir = coqc_path.rsplit("/", 1)[0]

        # Copy all binaries
        for binary in ["coqc", "coqtop", "coqdoc", "coqchk", "coq_makefile"]:
            src = "{}/{}".format(bin_dir, binary)
            dst = "bin/{}".format(binary)
            cp_result = repository_ctx.execute(["cp", src, dst])
            if cp_result.return_code == 0:
                repository_ctx.execute(["chmod", "+x", dst])
                print("Copied: {}".format(binary))

        # Copy libraries (find lib/coq or similar)
        lib_result = repository_ctx.execute([
            "find", mount_point, "-type", "d", "-name", "coq", "-path", "*/lib/*",
        ])
        if lib_result.return_code == 0 and lib_result.stdout.strip():
            lib_path = lib_result.stdout.strip().split("\n")[0]
            repository_ctx.execute(["cp", "-r", lib_path, "lib/"])
            print("Copied Coq libraries")
    else:
        print("WARNING: Could not find coqc in DMG")

    # Unmount DMG
    repository_ctx.execute(["hdiutil", "detach", mount_point, "-force"])
    repository_ctx.execute(["rm", "-rf", mount_point])

def _extract_tar_gz(repository_ctx, tar_path):
    """Extract Coq tools from tar.gz archive."""
    print("Extracting tar.gz: {}".format(tar_path))

    # Create directories
    repository_ctx.execute(["mkdir", "-p", "bin", "lib", "extracted"])

    # Extract archive
    extract_result = repository_ctx.execute([
        "tar", "-xzf", tar_path, "-C", "extracted",
    ])

    if extract_result.return_code != 0:
        fail("Failed to extract tar.gz: {}".format(extract_result.stderr))

    # Find and copy binaries
    find_result = repository_ctx.execute([
        "find", "extracted", "-type", "f", "-name", "coqc",
    ])

    if find_result.return_code == 0 and find_result.stdout.strip():
        coqc_path = find_result.stdout.strip().split("\n")[0]
        bin_dir = coqc_path.rsplit("/", 1)[0]

        # Copy all binaries
        for binary in ["coqc", "coqtop", "coqdoc", "coqchk", "coq_makefile"]:
            src = "{}/{}".format(bin_dir, binary)
            dst = "bin/{}".format(binary)
            cp_result = repository_ctx.execute(["cp", src, dst])
            if cp_result.return_code == 0:
                repository_ctx.execute(["chmod", "+x", dst])
                print("Copied: {}".format(binary))

        # Copy libraries
        lib_result = repository_ctx.execute([
            "find", "extracted", "-type", "d", "-name", "coq", "-path", "*/lib/*",
        ])
        if lib_result.return_code == 0 and lib_result.stdout.strip():
            lib_path = lib_result.stdout.strip().split("\n")[0]
            repository_ctx.execute(["cp", "-r", lib_path, "lib/"])
            print("Copied Coq libraries")
    else:
        print("WARNING: Could not find coqc in archive")

    # Clean up extracted directory
    repository_ctx.execute(["rm", "-rf", "extracted"])

def _extract_windows_exe(repository_ctx, exe_path):
    """Extract Coq tools from Windows installer."""
    print("Windows installer: {}".format(exe_path))

    # Create directories
    repository_ctx.execute(["mkdir", "-p", "bin", "lib"])

    # Try to extract with 7z if available
    seven_zip = repository_ctx.which("7z")
    if seven_zip:
        repository_ctx.execute(["mkdir", "-p", "extracted"])
        extract_result = repository_ctx.execute([
            str(seven_zip), "x", exe_path, "-oextracted", "-y",
        ])

        if extract_result.return_code == 0:
            # Find and copy binaries
            find_result = repository_ctx.execute([
                "find", "extracted", "-type", "f", "-name", "coqc.exe",
            ])

            if find_result.return_code == 0 and find_result.stdout.strip():
                coqc_path = find_result.stdout.strip().split("\n")[0]
                bin_dir = coqc_path.rsplit("/", 1)[0]

                # Copy all binaries
                for binary in ["coqc.exe", "coqtop.exe", "coqdoc.exe", "coqchk.exe"]:
                    src = "{}/{}".format(bin_dir, binary)
                    dst = "bin/{}".format(binary)
                    repository_ctx.execute(["cp", src, dst])
                    print("Copied: {}".format(binary))

        repository_ctx.execute(["rm", "-rf", "extracted"])
    else:
        print("WARNING: 7z not available for Windows installer extraction")
        print("Install 7-Zip and ensure 7z is in PATH")

def _create_build_file(repository_ctx):
    """Create BUILD file for Rocq toolchain."""
    repository_ctx.file("BUILD.bazel", """
# Rocq/Coq toolchain
package(default_visibility = ["//visibility:public"])

filegroup(
    name = "coqc",
    srcs = glob(["bin/coqc*"]),
)

filegroup(
    name = "coqtop",
    srcs = glob(["bin/coqtop*"]),
)

filegroup(
    name = "coqdoc",
    srcs = glob(["bin/coqdoc*"]),
)

filegroup(
    name = "coq_tools",
    srcs = glob(["bin/*"]),
)

filegroup(
    name = "stdlib",
    srcs = glob(["lib/**/*.vo", "lib/**/*.glob"]),
)

filegroup(
    name = "coq_theories",
    srcs = glob(["lib/**/*.v"]),
)

filegroup(
    name = "coq_libraries",
    srcs = glob(["lib/**/*"]),
)

# Toolchain target for register_toolchains
toolchain(
    name = "rocq_toolchain",
    toolchain = ":coq_tools",
    toolchain_type = "@rules_rocq_rust//rocq:toolchain_type",
)

# Export all toolchains
alias(
    name = "all",
    actual = ":rocq_toolchain",
)
""")

    repository_ctx.file("WORKSPACE.bazel", 'workspace(name = "{}")'.format(repository_ctx.name))

# =============================================================================
# Repository Rule Definition
# =============================================================================

_rocq_toolchain_repository = repository_rule(
    implementation = _rocq_toolchain_repository_impl,
    attrs = {
        "version": attr.string(
            default = "2025.01.0",
            doc = "Rocq Platform version to download",
        ),
        "strategy": attr.string(
            default = "download",
            doc = "Acquisition strategy (currently only 'download' supported)",
            values = ["download"],
        ),
    },
    doc = "Download and configure Rocq/Coq toolchain",
)

def rocq_toolchain_repository(name, version = "2025.01.0", strategy = "download"):
    """Create a Rocq toolchain repository.

    Args:
        name: Name for the repository
        version: Rocq Platform version to download
        strategy: Acquisition strategy ('download' only for now)
    """
    _rocq_toolchain_repository(
        name = name,
        version = version,
        strategy = strategy,
    )
