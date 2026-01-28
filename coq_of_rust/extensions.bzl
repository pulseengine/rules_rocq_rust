"""Module extensions for rocq-of-rust toolchain setup."""

load("//coq_of_rust/private:repository.bzl", "rocq_of_rust_source")
load("//coq_of_rust/private:toolchain.bzl", "rocq_of_rust_toolchain")

_RocqOfRustToolchainTag = tag_class(
    doc = "Tags for defining rocq-of-rust toolchains",
    attrs = {
        "commit": attr.string(
            doc = "Git commit hash or branch of rocq-of-rust",
            default = "main",
        ),
        "sha256": attr.string(
            doc = "SHA256 of the source archive",
            default = "",
        ),
        "rust_nightly": attr.string(
            doc = "Rust nightly version to use",
            default = "nightly-2024-12-01",
        ),
        "use_real_library": attr.bool(
            doc = "Use real RocqOfRust library (requires nixpkgs deps: coqutil, hammer, smpl)",
            default = False,
        ),
    },
)

def _rocq_of_rust_impl(module_ctx):
    """Implementation of rocq-of-rust toolchain extension."""

    # Collect configurations
    configs = []
    for mod in module_ctx.modules:
        for toolchain in mod.tags.toolchain:
            configs.append(toolchain)

    # Use first configuration or defaults
    if configs:
        config = configs[0]
        commit = config.commit
        sha256 = config.sha256
        rust_nightly = config.rust_nightly
        use_real_library = config.use_real_library
    else:
        commit = "main"
        sha256 = ""
        rust_nightly = "nightly-2024-12-01"
        use_real_library = False

    # Create source repository that downloads and builds rocq-of-rust
    rocq_of_rust_source(
        name = "rocq_of_rust_source",
        commit = commit,
        sha256 = sha256,
        rust_nightly = rust_nightly,
        use_real_library = use_real_library,
    )

    # Create toolchain repository
    _create_toolchain_repo(name = "rocq_of_rust_toolchains")

    return module_ctx.extension_metadata(reproducible = True)

def _create_toolchain_repo(name):
    """Create the toolchain repository with BUILD.bazel."""

    _toolchain_repo(name = name)

def _toolchain_repo_impl(repository_ctx):
    """Implementation of toolchain repository rule."""

    build_content = '''# Generated toolchain BUILD.bazel for rocq-of-rust

load("@rules_rocq_rust//coq_of_rust/private:toolchain.bzl", "rocq_of_rust_toolchain")

package(default_visibility = ["//visibility:public"])

rocq_of_rust_toolchain(
    name = "rocq_of_rust_toolchain_impl",
    rocq_of_rust_binary = "@rocq_of_rust_source//:rocq_of_rust",
    rocq_of_rust_lib = ["@rocq_of_rust_source//:rocq_of_rust_rocq_lib"],
    lib_include_path = "RocqOfRust",
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
