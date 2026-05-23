"""Shared helpers for hermetically downloading a Rust nightly sysroot.

This module factors out the platform detection and the
`static.rust-lang.org` download logic so it can be reused by:

  * `repository.bzl` -- the (legacy) imperative `cargo build` repository rule;
  * `rust_toolchain_repo.bzl` -- the hermetic `rules_rust` `rust_toolchain`
    introduced in Stage 2 of the rules_rust migration
    (see `docs/rules_rust-migration.md`).

The downloaded sysroot always includes the `rustc-dev` component: the
precompiled `rustc_*` crates are copied into
`rust_sysroot/lib/rustlib/<triple>/lib/` so that a `rustc_private` driver
(`extern crate rustc_driver`) can resolve them from the sysroot.
"""

# Default pinned Rust nightly -- matches rocq-of-rust's `rust-toolchain` file.
DEFAULT_NIGHTLY = "nightly-2024-12-07"

# Map (os_name, arch) to Rust platform triple for hermetic downloads.
# os_name comes from repository_ctx.os.name (lowercased),
# arch comes from repository_ctx.os.arch.
RUST_PLATFORM_MAP = {
    ("mac os x", "aarch64"): "aarch64-apple-darwin",
    ("mac os x", "x86_64"): "x86_64-apple-darwin",
    ("linux", "amd64"): "x86_64-unknown-linux-gnu",
    ("linux", "x86_64"): "x86_64-unknown-linux-gnu",
    ("linux", "aarch64"): "aarch64-unknown-linux-gnu",
}

def detect_rust_platform(repository_ctx):
    """Detect the host platform as a Rust triple, or None if unknown."""
    os_name = repository_ctx.os.name.lower()
    os_arch = repository_ctx.os.arch
    for (os_key, arch_key), triple in RUST_PLATFORM_MAP.items():
        if os_key in os_name and arch_key == os_arch:
            return triple
    return None

def download_rust_nightly(repository_ctx, rust_nightly, platform, output = "rust_sysroot"):
    """Download Rust nightly components hermetically and merge into `output`/.

    Downloads rustc, cargo, rust-std, and rustc-dev from static.rust-lang.org
    and lays them out as a single sysroot directory:

      <output>/bin/            rustc, rustdoc, cargo, ...
      <output>/lib/            libLLVM-*, librustc_driver-*, ...
      <output>/lib/rustlib/<triple>/lib/   libstd-*, rustc_*  (rustc-dev)

    `rust-std` and `rustc-dev` rlibs/.so end up side by side under
    `lib/rustlib/<triple>/lib/`, so the toolchain `rust_std` filegroup that
    globs that directory automatically picks up the `rustc-dev` crates.

    Returns the absolute path to `<output>/`.
    """

    # Extract date from nightly version (e.g. "nightly-2024-12-07" -> "2024-12-07").
    nightly_date = rust_nightly.replace("nightly-", "")
    base_url = "https://static.rust-lang.org/dist/{}".format(nightly_date)

    # 1. rustc (compiler binary + libLLVM + librustc_driver).
    repository_ctx.report_progress("Downloading rustc nightly ({})".format(nightly_date))
    repository_ctx.download_and_extract(
        url = "{}/rustc-nightly-{}.tar.xz".format(base_url, platform),
        output = output,
        stripPrefix = "rustc-nightly-{}/rustc".format(platform),
    )

    # 2. cargo.
    repository_ctx.report_progress("Downloading cargo nightly")
    repository_ctx.download_and_extract(
        url = "{}/cargo-nightly-{}.tar.xz".format(base_url, platform),
        output = "cargo_tmp",
        stripPrefix = "cargo-nightly-{}/cargo".format(platform),
    )
    repository_ctx.execute(["cp", "-R", "cargo_tmp/bin/.", "{}/bin/".format(output)])
    repository_ctx.execute(["rm", "-rf", "cargo_tmp"])

    # 3. rust-std (libstd, libcore, liballoc, ...).
    repository_ctx.report_progress("Downloading rust-std nightly")
    repository_ctx.download_and_extract(
        url = "{}/rust-std-nightly-{}.tar.xz".format(base_url, platform),
        output = "rust_std_tmp",
        stripPrefix = "rust-std-nightly-{}/rust-std-{}".format(platform, platform),
    )
    repository_ctx.execute(["cp", "-R", "rust_std_tmp/lib/rustlib/.", "{}/lib/rustlib/".format(output)])
    repository_ctx.execute(["rm", "-rf", "rust_std_tmp"])

    # 4. rustc-dev (the precompiled rustc_* crates, for rustc_private linking).
    repository_ctx.report_progress("Downloading rustc-dev nightly")
    repository_ctx.download_and_extract(
        url = "{}/rustc-dev-nightly-{}.tar.xz".format(base_url, platform),
        output = "rustc_dev_tmp",
        stripPrefix = "rustc-dev-nightly-{}/rustc-dev".format(platform),
    )
    repository_ctx.execute(["cp", "-R", "rustc_dev_tmp/lib/rustlib/.", "{}/lib/rustlib/".format(output)])
    repository_ctx.execute(["rm", "-rf", "rustc_dev_tmp"])

    # 5. Make libLLVM reachable by the linker. The `rustc` component ships
    #    libLLVM-*-rust-* only in <output>/lib/, but when linking a
    #    rustc_private binary rustc only puts lib/rustlib/<triple>/lib/ on the
    #    linker search path -- so `-lLLVM-*-rust-*` fails to resolve there
    #    (notably on Linux). Copy it alongside the rustc-dev crates. `cp -a`
    #    preserves the linker-name symlink and its versioned target.
    repository_ctx.execute([
        "bash",
        "-c",
        "cp -a {out}/lib/libLLVM* {out}/lib/rustlib/{triple}/lib/ 2>/dev/null || true".format(
            out = output,
            triple = platform,
        ),
    ])

    # Make binaries executable.
    repository_ctx.execute(["chmod", "+x", "{}/bin/cargo".format(output)])
    repository_ctx.execute(["chmod", "+x", "{}/bin/rustc".format(output)])

    # On macOS, remove quarantine attributes so the binaries can run.
    if "mac" in repository_ctx.os.name.lower():
        repository_ctx.execute(["xattr", "-cr", output], timeout = 60)

    return str(repository_ctx.path(output))
