# Migrating the `rocq-of-rust` toolchain to `rules_rust`

Status: **planned** — design accepted, implementation staged.
Tracking: pulseengine/rules_rocq_rust epic issue (see "Stages" below).

## Motivation

The `rocq_of_rust_source` repository rule (`coq_of_rust/private/repository.bzl`)
currently builds the `rocq-of-rust` binaries with an imperative `cargo build`
invoked through `repository_ctx.execute`. It downloads a hermetic Rust nightly
sysroot from `static.rust-lang.org` first, but **falls back to the host's
`rustup`/`cargo`** if that download is unavailable.

That fallback is the problem:

- it makes the build non-hermetic and host-dependent, and
- it was the proximate cause of the LOOM "Rocq Formal Proofs" CI breakage
  (`rust-lld: error: unable to find library -lLLVM-19-rust-1.85.0-nightly`) on
  `rules_rocq_rust` pins that predated the `LIBRARY_PATH` fix.

`rules_verus` already builds its Rust component through `rules_rust` with a
registered Bazel toolchain. This document plans the equivalent move so the
`rocq-of-rust` build is hermetic and reproducible inside Bazel's action graph —
"no outside Rust".

## What makes this non-trivial

`rocq-of-rust` is **not an ordinary Rust program**. `rocq-of-rust-rustc` is a
`rustc` *driver*: it `extern crate rustc_driver / rustc_interface / ...` under
`#![feature(rustc_private)]`. Building it requires:

- a **nightly** toolchain — `nightly-2024-12-07`, pinned by rocq-of-rust's
  `rust-toolchain` file;
- the **`rustc-dev`** component — the precompiled `rustc_*` crates — present in
  the toolchain sysroot;
- `RUSTC_BOOTSTRAP=1`;
- link access to `librustc_driver-*.so` and `libLLVM-*-rust-*.so`.

`rules_rust`'s stock `rust` module extension downloads official Rust releases
and does **not** ship `rustc-dev`. So the migration cannot simply be
`crate_universe` + `rust_binary`; it needs a **custom `rust_toolchain` whose
sysroot includes `rustc-dev`**. This is the research crux (Stage 3).

## Source facts (`rocq-of-rust` @ `877dd65`)

- Cargo workspace, `members = ["lib", "cli"]`, `resolver = "2"`.
- `lib/` → crate `rocq_of_rust_lib`: a library plus two binaries,
  `rocq-of-rust-rustc` (the `rustc_private` driver) and `cargo-rocq-of-rust`.
  9 direct dependencies (chrono, clap, itertools, pretty, rpds, serde,
  serde_json, toml, walkdir).
- `cli/` → crate `rocq_of_rust_cli`: binary `rocq-of-rust` (`src/main.rs`),
  path-depends on `rocq_of_rust_lib`.
- `Cargo.lock`: 71 packages total.
- 9 git submodules (`ink`, `third-party/*`) are translation corpora / examples,
  **not** build dependencies — the repository rule already strips them.

## Target architecture

```
MODULE.bazel
  bazel_dep(rules_rust)
  crate = use_extension(... crate_universe ...)   # 3rd-party deps from Cargo.lock
  rust nightly+rustc-dev toolchain  --> register_toolchains(...)

coq_of_rust/
  private/rust_toolchain.bzl   # repo rule: hermetic nightly sysroot incl. rustc-dev,
                               # exposed as a rules_rust rust_toolchain
  BUILD targets                # rust_binary x3 (rocq-of-rust, rocq-of-rust-rustc,
                               # cargo-rocq-of-rust) built against that toolchain
  private/toolchain.bzl        # rocq_of_rust_toolchain consumes the rust_binary
```

The pinned `rocq-of-rust` source tarball is still fetched by a repository rule
(unchanged); only the **build** moves from imperative `cargo` to `rules_rust`.

## Stages

Each stage is an independent PR that leaves `main` green.

1. **crate_universe scaffold** — add the `rules_rust` `bazel_dep`; vendor
   `rocq-of-rust`'s `Cargo.lock`; generate the third-party crate repo.
   Verified by `bazel query @crates//...`.
2. **hermetic nightly + rustc-dev `rust_toolchain`** — repurpose
   `_download_rust_nightly` into a repository rule that registers a `rust_toolchain`
   whose sysroot contains `rustc-dev`. Verified by building a trivial `rust_binary`.
3. **build the `rocq-of-rust` crates** — `rust_binary` targets for the three
   binaries; wire `RUSTC_BOOTSTRAP`, the `rustc_private` extern paths, and the
   `libLLVM` link. *(research crux)*
4. **rewire the toolchain** — `rocq_of_rust_toolchain` consumes the `rust_binary`
   instead of the repository-rule-built binary; the RocqOfRust `.v` library
   handling is unchanged.
5. **delete the imperative path** — remove the `cargo build` / `rustup` fallback
   from `repository.bzl` and the now-redundant Rust-install + `LIBRARY_PATH`
   steps from `.github/workflows/ci.yml`.

## Risks / open questions

- `rustc_private` under `rules_rust` is not a documented path; Stage 3 may need
  a bespoke `rust_toolchain` attribute set or `extra_rustc_flags` to surface the
  `rustc-dev` crates and the `libLLVM` link directory.
- `crate_universe` needs `Cargo.lock`; the vendored lock must stay in sync with
  the pinned `rocq-of-rust` `commit`.
- No local Nix in the dev environment — Rocq-side verification stays in CI.
- Stages 1–2 are low risk and verifiable; Stage 3 will likely need several CI
  iterations.
