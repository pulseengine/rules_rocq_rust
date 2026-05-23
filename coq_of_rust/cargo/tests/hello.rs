//! Trivial smoke target for the hermetic Rust nightly toolchain.
//!
//! `bazel build //coq_of_rust/cargo/tests:hello` proves the Stage 2
//! `rust_toolchain` (`@rocq_of_rust_rust_nightly`) can compile ordinary Rust.
//! See docs/rules_rust-migration.md.

fn main() {}
