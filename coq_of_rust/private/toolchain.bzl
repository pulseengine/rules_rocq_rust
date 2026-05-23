"""Toolchain rule for rocq-of-rust."""

load("//coq_of_rust/private:coq_of_rust.bzl", "RocqOfRustToolchainInfo")

def _rocq_of_rust_toolchain_impl(ctx):
    """Implementation of rocq_of_rust_toolchain rule."""
    toolchain_info = platform_common.ToolchainInfo(
        rocq_of_rust_info = RocqOfRustToolchainInfo(
            rocq_of_rust_binary = ctx.attr.rocq_of_rust_binary,
            rocq_of_rust_lib = ctx.attr.rocq_of_rust_lib,
            lib_include_path = ctx.attr.lib_include_path,
            rust_sysroot = ctx.attr.rust_sysroot,
        ),
    )
    return [toolchain_info]

rocq_of_rust_toolchain = rule(
    implementation = _rocq_of_rust_toolchain_impl,
    attrs = {
        "rocq_of_rust_binary": attr.label(
            mandatory = True,
            doc = "The rocq-of-rust executable (a rules_rust rust_binary).",
        ),
        "rocq_of_rust_lib": attr.label_list(
            doc = "RocqOfRust Rocq library sources",
        ),
        "lib_include_path": attr.string(
            default = "RocqOfRust",
            doc = "Include path for the RocqOfRust library",
        ),
        "rust_sysroot": attr.label(
            doc = "Hermetic Rust nightly sysroot filegroup. rocq-of-rust's " +
                  "`translate` shells out to `rustc --print=sysroot` " +
                  "in-process, so the nightly rustc + sysroot must be in the " +
                  "translation action sandbox and on PATH. See " +
                  "docs/rules_rust-migration.md (Stage 4).",
        ),
    },
    doc = "Defines a rocq-of-rust toolchain",
)
