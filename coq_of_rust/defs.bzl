"""Public API for rocq-of-rust translation rules."""

load("//coq_of_rust/private:coq_of_rust.bzl", _coq_of_rust_library = "coq_of_rust_library")
load("//rocq:defs.bzl", "rocq_library")

coq_of_rust_library = _coq_of_rust_library
rocq_of_rust_library = _coq_of_rust_library

def rocq_rust_verified_library(
        name,
        rust_sources,
        edition = "2021",
        deps = [],
        **kwargs):
    """Translate Rust to Rocq and compile.

    Args:
        name: Target name
        rust_sources: Rust source files to translate
        edition: Rust edition (default: 2021)
        deps: Additional Rocq dependencies
        **kwargs: Additional arguments passed to rocq_library
    """
    # Step 1: Translate Rust to Rocq
    coq_of_rust_library(
        name = name + "_generated",
        rust_sources = rust_sources,
        edition = edition,
    )

    # Step 2: Compile with rocq_library
    rocq_library(
        name = name,
        srcs = [":" + name + "_generated"],
        deps = ["@rocq_of_rust_source//:rocq_of_rust_rocq_lib"] + deps,
        **kwargs
    )
