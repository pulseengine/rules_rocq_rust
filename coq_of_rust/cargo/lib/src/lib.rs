//! Stub source for the vendored `rocq_of_rust_lib` manifest.
//!
//! crate_universe (see MODULE.bazel) only runs `cargo metadata` against the
//! vendored workspace to resolve the third-party dependency graph — it never
//! compiles this file. The real `rocq-of-rust` source is fetched from the
//! pinned upstream commit at build time. This stub exists solely so cargo can
//! discover a `[lib]` target for the workspace member.
