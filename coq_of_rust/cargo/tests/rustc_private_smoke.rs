//! Stretch smoke target: prove the `rustc-dev` crates are reachable from the
//! hermetic toolchain sysroot.
//!
//! `extern crate rustc_driver` only resolves if the `rustc-dev` component's
//! `librustc_driver-*` is present in the toolchain `rust_std` filegroup. This
//! is the wiring Stage 3 (`rocq-of-rust-rustc`) depends on.
//!
//! Building this needs `RUSTC_BOOTSTRAP=1` (set via `rustc_env` in BUILD.bazel)
//! because `#![feature(rustc_private)]` is a nightly-gated, normally
//! compiler-internal feature.
#![feature(rustc_private)]

extern crate rustc_driver;

fn main() {}
