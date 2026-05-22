"""Implementation of coq_of_rust_library rule.

Stage 4 of the rules_rust migration (see docs/rules_rust-migration.md) rewired
the toolchain onto the hermetic rules_rust build: `rocq_of_rust_binary` is now a
rules_rust `rust_binary` (from `@rocq_of_rust_build`), not a wrapper script.

`rocq-of-rust translate` runs `rustc --print=sysroot` in-process during
translation, so the translation action must carry the hermetic nightly sysroot
(`rust_sysroot`) in its inputs and put `<sysroot>/bin` on PATH.
"""

load("//rocq/private:rocq.bzl", "RocqInfo")

# Provider for rocq-of-rust toolchain info
RocqOfRustToolchainInfo = provider(
    doc = "Information about the rocq-of-rust toolchain",
    fields = {
        "rocq_of_rust_binary": "The rocq-of-rust executable (rust_binary target)",
        "rocq_of_rust_lib": "RocqOfRust Rocq library sources",
        "lib_include_path": "Include path for the RocqOfRust library",
        "rust_sysroot": "Hermetic Rust nightly sysroot (filegroup target); " +
                        "its rustc must be on PATH at translation time",
    },
)

def _find_sysroot_bin(sysroot_files):
    """Locate the `bin/` directory of the hermetic nightly sysroot.

    The rust_sysroot filegroup globs `sysroot/**` in @rocq_of_rust_rust_nightly.
    Find the `rustc` binary inside it and return its dirname (the bin/ dir whose
    parent is the sysroot). Returns None if no rustc is present.
    """
    for f in sysroot_files:
        # Match `.../sysroot/bin/rustc` (binary_ext is "" on linux/darwin).
        if f.basename == "rustc" and f.dirname.endswith("/bin"):
            return f.dirname
    return None

def _sysroot_dylib_dirs(sysroot_files):
    """Directories in the hermetic sysroot that hold shared libraries the
    rocq-of-rust binary dlopen()s at runtime (librustc_driver, libLLVM,
    libstd, ...).

    The rules_rust `rust_binary` links those sysroot dylibs but carries no
    LC_RPATH for them, so the translation action must surface them on
    DYLD_LIBRARY_PATH / LD_LIBRARY_PATH.
    """
    dirs = {}
    for f in sysroot_files:
        n = f.basename
        if n.endswith(".dylib") or n.endswith(".so") or ".so." in n:
            dirs[f.dirname] = True
    return sorted(dirs)

def _coq_of_rust_library_impl(ctx):
    """Translate Rust source files to Rocq using rocq-of-rust."""

    # Get toolchain
    toolchain = ctx.toolchains["@rules_rocq_rust//coq_of_rust:toolchain_type"]
    if not toolchain or not hasattr(toolchain, "rocq_of_rust_info"):
        fail("rocq-of-rust toolchain not configured")

    info = toolchain.rocq_of_rust_info

    # rocq_of_rust_binary is a rules_rust rust_binary (Stage 4): take its
    # executable from FilesToRunProvider and its runfiles (shared libs, etc.).
    binary_target = info.rocq_of_rust_binary
    rocq_of_rust = binary_target[DefaultInfo].files_to_run.executable
    if not rocq_of_rust:
        fail("rocq-of-rust binary target exposes no executable")
    binary_runfiles = binary_target[DefaultInfo].default_runfiles.files

    # Hermetic nightly sysroot. `rocq-of-rust translate` shells out to
    # `rustc --print=sysroot` in-process, so the sysroot's rustc must be in the
    # action sandbox and on PATH at translation time (see docs Stage 4).
    if not info.rust_sysroot:
        fail("rocq-of-rust toolchain: rust_sysroot not configured; the " +
             "translator needs the hermetic nightly rustc on PATH. " +
             "See docs/rules_rust-migration.md (Stage 4).")
    sysroot_depset = info.rust_sysroot.files
    sysroot_files = sysroot_depset.to_list()
    sysroot_bin = _find_sysroot_bin(sysroot_files)
    if not sysroot_bin:
        fail("rocq-of-rust toolchain: hermetic Rust sysroot (with bin/rustc) " +
             "not found; the translator needs nightly rustc on PATH. " +
             "See docs/rules_rust-migration.md (Stage 4).")

    # The rocq-of-rust rust_binary dynamically links librustc_driver / libLLVM
    # from the sysroot but carries no rpath for them, so the translation action
    # must surface those dylib dirs on DYLD_LIBRARY_PATH / LD_LIBRARY_PATH.
    # The dirs are exec-relative; `cd ... && pwd` makes them absolute before the
    # action cd's into the source directory.
    dyld_expr = ":".join([
        '$(cd "{}" && pwd)'.format(d)
        for d in _sysroot_dylib_dirs(sysroot_files)
    ])

    # Process each Rust source file
    output_files = []
    for src in ctx.files.rust_sources:
        # Output .v file with same name as input .rs
        output_v = ctx.actions.declare_file(
            src.basename.replace(".rs", ".v"),
        )
        output_files.append(output_v)

        # rocq-of-rust preserves the input path structure in output.
        # E.g., --path a/b/c.rs --output-path /out creates /out/a/b/c.v
        # To get flat output, we cd to source directory and use basename.
        #
        # We need to compute paths that work after cd:
        # - binary path relative to src.dirname
        # - output dir relative to src.dirname (go up then into bazel-out)
        # - sysroot bin dir, made absolute so PATH survives the cd.
        src_dir = src.dirname
        src_basename = src.basename

        # Calculate how many levels up we need to go from src_dir to execroot
        # e.g., "examples/rust_to_rocq" -> 2 levels up
        depth = len(src_dir.split("/"))
        prefix = "/".join([".."] * depth)

        # The translation action needs: the source, the rust_binary and its
        # runfiles, and the whole nightly sysroot (rustc + std libs).
        inputs = depset(
            [src, rocq_of_rust],
            transitive = [binary_runfiles, sysroot_depset],
        )

        # Use run_shell to change directory before running. After the cd,
        # exec-root-relative paths are reached via {prefix}. The nightly bin/
        # dir is resolved to an absolute path *before* the cd so PATH stays
        # valid; `rocq-of-rust translate` then finds `rustc` there in-process.
        ctx.actions.run_shell(
            command = """
                _ROCQ_RUSTC_BIN="$(cd "{sysroot_bin}" && pwd)" && \\
                _ROCQ_DYLD="{dyld_expr}" && \\
                cd "{src_dir}" && \\
                mkdir -p "{prefix}/{out_dir}" && \\
                PATH="$_ROCQ_RUSTC_BIN:$PATH" \\
                DYLD_LIBRARY_PATH="$_ROCQ_DYLD" \\
                LD_LIBRARY_PATH="$_ROCQ_DYLD" \\
                "{prefix}/{binary}" translate --path "{src_basename}" --output-path "{prefix}/{out_dir}"
            """.format(
                sysroot_bin = sysroot_bin,
                dyld_expr = dyld_expr,
                src_dir = src_dir,
                prefix = prefix,
                binary = rocq_of_rust.path,
                src_basename = src_basename,
                out_dir = output_v.dirname,
            ),
            inputs = inputs,
            outputs = [output_v],
            mnemonic = "RocqOfRust",
            progress_message = "Translating %{input} to Rocq",
        )

    return [
        DefaultInfo(files = depset(output_files)),
        RocqInfo(
            sources = depset(output_files),
            compiled = None,
            include_paths = [],
            output_dir = "",
            transitive_deps = depset(output_files),
        ),
    ]

coq_of_rust_library = rule(
    implementation = _coq_of_rust_library_impl,
    attrs = {
        "rust_sources": attr.label_list(
            allow_files = [".rs"],
            mandatory = True,
            doc = "Rust source files to translate",
        ),
        "edition": attr.string(
            default = "2021",
            doc = "Rust edition (2015, 2018, 2021)",
        ),
    },
    toolchains = ["@rules_rocq_rust//coq_of_rust:toolchain_type"],
    doc = "Translates Rust source files to Rocq using rocq-of-rust",
)
