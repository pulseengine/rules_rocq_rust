"""Module extensions for rocq-of-rust toolchain setup."""

load("//coq_of_rust/private:rocq_of_rust_build.bzl", "rocq_of_rust_build")
load("//coq_of_rust/private:rust_nightly.bzl", "DEFAULT_NIGHTLY")
load("//coq_of_rust/private:rust_toolchain_repo.bzl", "rust_toolchain_repo")
load("//coq_of_rust/private:toolchain.bzl", "rocq_of_rust_toolchain")

_RocqOfRustToolchainTag = tag_class(
    doc = "Tags for defining rocq-of-rust toolchains",
    attrs = {
        "commit": attr.string(
            doc = "Git commit hash or branch of rocq-of-rust",
            default = "",  # Empty means use pinned default
        ),
        "sha256": attr.string(
            doc = "SHA256 of the source archive",
            default = "",
        ),
        "rust_nightly": attr.string(
            doc = "Rust nightly version to use",
            default = "nightly-2024-12-07",
        ),
        "use_real_library": attr.bool(
            doc = "Use real RocqOfRust library (requires nixpkgs deps: coqutil, hammer, smpl)",
            default = False,
        ),
        "fail_on_error": attr.bool(
            doc = "Fail build if rocq-of-rust cannot be built (recommended for production)",
            default = True,
        ),
    },
)

def _rocq_of_rust_impl(module_ctx):
    """Implementation of rocq-of-rust toolchain extension."""

    # Only commit/sha256 affect the hermetic rules_rust build. The
    # rust_nightly / use_real_library / fail_on_error tag attrs remain for
    # backward compatibility but no longer influence anything -- the old
    # imperative cargo path they configured was removed in Stage 5.
    commit = ""
    sha256 = ""
    for mod in module_ctx.modules:
        for toolchain in mod.tags.toolchain:
            if toolchain.commit:
                commit = toolchain.commit
            if toolchain.sha256:
                sha256 = toolchain.sha256

    # Fetch the rocq-of-rust source for the hermetic rules_rust build
    # (docs/rules_rust-migration.md). The rust_library/rust_binary targets
    # that consume it live in //coq_of_rust/rocq_of_rust.
    build_kwargs = {"name": "rocq_of_rust_build"}
    if commit:
        build_kwargs["commit"] = commit
    if sha256:
        build_kwargs["sha256"] = sha256
    rocq_of_rust_build(**build_kwargs)

    # Create toolchain repository
    _create_toolchain_repo(name = "rocq_of_rust_toolchains")

    return module_ctx.extension_metadata(reproducible = True)

def _create_toolchain_repo(name):
    """Create the toolchain repository with BUILD.bazel."""

    _toolchain_repo(name = name)

def _toolchain_repo_impl(repository_ctx):
    """Implementation of toolchain repository rule.

    Stage 4 of the rules_rust migration (see docs/rules_rust-migration.md):
    the toolchain now consumes the hermetic rules_rust build
    (@rocq_of_rust_build) -- the rust_binary CLI and the RocqOfRust .v library
    -- instead of the imperatively cargo-built @rocq_of_rust_source. The
    nightly sysroot from @rocq_of_rust_rust_nightly is threaded through so the
    translator can find `rustc` on PATH at translation time.
    """

    build_content = '''# Generated toolchain BUILD.bazel for rocq-of-rust.
# Stage 4 of the rules_rust migration; see docs/rules_rust-migration.md.

load("@rules_rocq_rust//coq_of_rust/private:toolchain.bzl", "rocq_of_rust_toolchain")

package(default_visibility = ["//visibility:public"])

rocq_of_rust_toolchain(
    name = "rocq_of_rust_toolchain_impl",
    # The CLI rust_binary built hermetically by rules_rust. It lives in a
    # checked-in package (not @rocq_of_rust_build) so it can reference
    # @rocq_of_rust_crates -- see coq_of_rust/rocq_of_rust/BUILD.bazel.
    rocq_of_rust_binary = "@rules_rocq_rust//coq_of_rust/rocq_of_rust:rocq-of-rust",
    # The RocqOfRust .v library, exposed from the fetched-source repo (Stage 4).
    rocq_of_rust_lib = ["@rocq_of_rust_build//:rocq_of_rust_rocq_lib"],
    lib_include_path = "RocqOfRust",
    # Hermetic nightly sysroot (Stage 2). `rocq-of-rust translate` shells out
    # to `rustc --print=sysroot` in-process, so its rustc must be on PATH.
    rust_sysroot = "@rocq_of_rust_rust_nightly//:sysroot",
)

toolchain(
    name = "toolchain",
    toolchain = ":rocq_of_rust_toolchain_impl",
    toolchain_type = "@rules_rocq_rust//coq_of_rust:toolchain_type",
)
'''
    repository_ctx.file("BUILD.bazel", build_content)

_toolchain_repo = repository_rule(
    implementation = _toolchain_repo_impl,
)

rocq_of_rust = module_extension(
    doc = "rocq-of-rust toolchain extension.",
    implementation = _rocq_of_rust_impl,
    tag_classes = {
        "toolchain": _RocqOfRustToolchainTag,
    },
)

# -----------------------------------------------------------------------------
# Hermetic Rust nightly + rustc-dev toolchain (Stage 2 of the rules_rust
# migration -- see docs/rules_rust-migration.md).
# -----------------------------------------------------------------------------

_RustNightlyToolchainTag = tag_class(
    doc = "Configures the hermetic Rust nightly (+rustc-dev) rust_toolchain.",
    attrs = {
        "rust_nightly": attr.string(
            doc = "Rust nightly version to download, e.g. 'nightly-2024-12-07'.",
            default = DEFAULT_NIGHTLY,
        ),
    },
)

def _rust_nightly_toolchain_impl(module_ctx):
    """Instantiate the hermetic nightly+rustc-dev rust_toolchain repository."""
    rust_nightly = DEFAULT_NIGHTLY
    for mod in module_ctx.modules:
        for tag in mod.tags.toolchain:
            rust_nightly = tag.rust_nightly

    rust_toolchain_repo(
        name = "rocq_of_rust_rust_nightly",
        rust_nightly = rust_nightly,
    )

    return module_ctx.extension_metadata(reproducible = True)

rust_nightly_toolchain = module_extension(
    doc = "Hermetic Rust nightly (incl. rustc-dev) rules_rust toolchain " +
          "for the rocq-of-rust build. See docs/rules_rust-migration.md.",
    implementation = _rust_nightly_toolchain_impl,
    tag_classes = {
        "toolchain": _RustNightlyToolchainTag,
    },
)
