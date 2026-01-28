"""Implementation of coq_of_rust_library rule."""

load("//rocq/private:rocq.bzl", "RocqInfo")

# Provider for rocq-of-rust toolchain info
RocqOfRustToolchainInfo = provider(
    doc = "Information about the rocq-of-rust toolchain",
    fields = {
        "rocq_of_rust_binary": "The rocq-of-rust executable files",
        "rocq_of_rust_lib": "RocqOfRust Rocq library sources",
        "lib_include_path": "Include path for the RocqOfRust library",
    },
)

def _coq_of_rust_library_impl(ctx):
    """Translate Rust source files to Rocq using rocq-of-rust."""

    # Get toolchain
    toolchain = ctx.toolchains["@rules_rocq_rust//coq_of_rust:toolchain_type"]
    if not toolchain or not hasattr(toolchain, "rocq_of_rust_info"):
        fail("rocq-of-rust toolchain not configured")

    info = toolchain.rocq_of_rust_info

    # Get the wrapper script (first file in the binary filegroup)
    binary_files = info.rocq_of_rust_binary.files.to_list()
    wrapper = None
    real_binary = None
    for f in binary_files:
        if f.basename == "rocq-of-rust" and "bin" in f.path:
            wrapper = f
        elif f.basename in ["rocq-of-rust", "rocq_of_rust"] and "target/release" in f.path:
            real_binary = f

    if not wrapper:
        fail("rocq-of-rust wrapper not found in toolchain")

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
        # - wrapper path relative to src.dirname
        # - output dir relative to src.dirname (go up then into bazel-out)
        src_dir = src.dirname
        src_basename = src.basename

        # Calculate how many levels up we need to go from src_dir to execroot
        # e.g., "examples/rust_to_rocq" -> 2 levels up
        depth = len(src_dir.split("/"))
        prefix = "/".join([".."] * depth)

        inputs = [src, wrapper]
        if real_binary:
            inputs.append(real_binary)

        # Use run_shell to change directory before running
        # Paths need to be relative to src_dir after cd
        ctx.actions.run_shell(
            command = """
                cd "{src_dir}" && \\
                mkdir -p "{prefix}/{out_dir}" && \\
                "{prefix}/{wrapper}" translate --path "{src_basename}" --output-path "{prefix}/{out_dir}"
            """.format(
                src_dir = src_dir,
                prefix = prefix,
                wrapper = wrapper.path,
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
