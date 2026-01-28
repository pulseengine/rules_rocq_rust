"""Rocq toolchain definitions."""

load("//rocq/private:rocq.bzl", "RocqInfo")

# Provider for Rocq toolchain information
RocqToolchainInfo = provider(
    doc = "Information about a Rocq/Coq toolchain",
    fields = {
        "coqc": "File: The coqc compiler binary",
        "coq_tools": "depset of File: All Coq binaries",
        "stdlib": "depset of File: Standard library .vo files",
        "stdlib_path": "String: Physical path to Stdlib for -Q flag (Rocq 9.0+)",
        "extra_libs": "list of (files, logical_name, pattern): External library packages",
    },
)

def _find_lib_path(files, pattern, logical_name):
    """Find the base path for a library from its .vo files."""
    for f in files:
        if pattern in f.path:
            # Extract path up to and including the pattern
            idx = f.path.find(pattern)
            return f.path[:idx + len(pattern)]
    return ""

def _rocq_toolchain_info_impl(ctx):
    """Create a RocqToolchainInfo provider for the toolchain."""
    coqc_files = ctx.files.coqc
    coqc = coqc_files[0] if coqc_files else None

    # Get stdlib files and compute the path
    stdlib_files = ctx.files.stdlib
    stdlib_path = ""
    if stdlib_files:
        # Find the Stdlib directory path from the first .vo file
        for f in stdlib_files:
            if "/Stdlib/" in f.path:
                # Extract path up to and including Stdlib
                idx = f.path.find("/Stdlib/")
                stdlib_path = f.path[:idx + len("/Stdlib")]
                break

    # Collect external library info (files, logical_name, path)
    extra_libs = []

    # coqutil
    if ctx.files.coqutil:
        path = _find_lib_path(ctx.files.coqutil, "/coqutil/", "coqutil")
        if path:
            extra_libs.append((ctx.files.coqutil, "coqutil", path))

    # hammer (Plugin)
    if ctx.files.hammer:
        path = _find_lib_path(ctx.files.hammer, "/Hammer/", "Hammer")
        if path:
            extra_libs.append((ctx.files.hammer, "Hammer", path))

    # hammer_tactics (Tactics library - separate package in nixpkgs)
    if ctx.files.hammer_tactics:
        path = _find_lib_path(ctx.files.hammer_tactics, "/Hammer/", "Hammer")
        if path:
            extra_libs.append((ctx.files.hammer_tactics, "Hammer", path))

    # smpl
    if ctx.files.smpl:
        path = _find_lib_path(ctx.files.smpl, "/smpl/", "smpl")
        if path:
            extra_libs.append((ctx.files.smpl, "smpl", path))

    # Compute OCAMLPATH for findlib resolution (needed for Hammer plugins)
    # Includes the coq lib path and all OCaml plugin site-lib paths
    ocaml_paths = []
    ocaml_plugin_files = []

    # Add coqc lib path (has coq-core META)
    if coqc:
        bin_dir = coqc.dirname
        if bin_dir.endswith("/bin"):
            ocaml_paths.append(bin_dir[:-4] + "/lib")

    # Add OCaml plugin paths from hammer, hammer_tactics, and smpl
    for plugin_files in [ctx.files.hammer_ocaml_plugins, ctx.files.hammer_tactics_ocaml_plugins, ctx.files.smpl_ocaml_plugins]:
        if plugin_files:
            ocaml_plugin_files.extend(plugin_files)
            # Find site-lib directory from the META file paths
            for f in plugin_files:
                if "/site-lib/" in f.path:
                    idx = f.path.find("/site-lib/")
                    site_lib_path = f.path[:idx + len("/site-lib")]
                    if site_lib_path not in ocaml_paths:
                        ocaml_paths.append(site_lib_path)
                    break

    ocaml_path_str = ":".join(ocaml_paths) if ocaml_paths else ""

    # Create a simpler info structure that can be passed via toolchain
    rocq_info = struct(
        coqc = coqc,
        coq_tools = depset(ctx.files.coq_tools),
        stdlib = depset(stdlib_files),
        stdlib_path = stdlib_path,
        extra_libs = extra_libs,
        ocaml_path = ocaml_path_str,
        ocaml_plugin_files = ocaml_plugin_files,
    )

    return [
        platform_common.ToolchainInfo(
            rocq_info = rocq_info,
        ),
    ]

rocq_toolchain_info = rule(
    implementation = _rocq_toolchain_info_impl,
    attrs = {
        "coqc": attr.label(
            allow_files = True,
            doc = "The coqc compiler binary",
        ),
        "coq_tools": attr.label(
            allow_files = True,
            doc = "All Coq binaries",
        ),
        "stdlib": attr.label(
            allow_files = True,
            doc = "Standard library .vo files (Rocq 9.0+ Stdlib package)",
        ),
        "coqutil": attr.label(
            allow_files = True,
            doc = "coqutil library .vo files (optional)",
        ),
        "hammer": attr.label(
            allow_files = True,
            doc = "coq-hammer plugin .vo files (optional)",
        ),
        "hammer_tactics": attr.label(
            allow_files = True,
            doc = "coq-hammer-tactics library .vo files (optional)",
        ),
        "hammer_ocaml_plugins": attr.label(
            allow_files = True,
            doc = "coq-hammer OCaml findlib plugin files (optional)",
        ),
        "hammer_tactics_ocaml_plugins": attr.label(
            allow_files = True,
            doc = "coq-hammer-tactics OCaml findlib plugin files (optional)",
        ),
        "smpl": attr.label(
            allow_files = True,
            doc = "smpl library .vo files (optional)",
        ),
        "smpl_ocaml_plugins": attr.label(
            allow_files = True,
            doc = "smpl OCaml findlib plugin files (optional)",
        ),
    },
    doc = "Provides Rocq toolchain information",
)
