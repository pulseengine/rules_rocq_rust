"""Repository rule for building gappalib-coq from source using nix.

gappalib-coq is Gappa's Rocq/Coq support library: Gappa's `-Bcoq` backend
emits a proof script that `Require Import Gappa.Gappa_library`, built on top
of Flocq. nixpkgs has no `coq-gappa`/`gappalib-coq` package -- only the
standalone `gappa` binary -- so this is built from source the same way
`smpl` is (see smpl_repository.bzl), for the same reason: nixpkgs's Coq
package set doesn't cover it for this Rocq version.

The interactive `gappa` tactic plugin (src/Gappa_tactic.v, an OCaml ML
plugin invoked as `Declare ML Module "coq-gappa.tactic"`) is intentionally
excluded from the build. This toolchain drives Gappa as an external CLI
(`gappa -Bcoq`) whose emitted proof term is always replayed through the Rocq
kernel by a normal rocq_library compile (see rivet CC-002) -- it never needs
the in-Coq tactic, and building the ML plugin would require the same
findlib/META/.cmxs machinery as the Hammer and smpl plugins for no payoff.

Source: https://gitlab.inria.fr/gappa/coq
"""

_GAPPALIB_REPO = "https://gitlab.inria.fr/gappa/coq"
_DEFAULT_VERSION = "1.10.0"

# Nix expression to build gappalib-coq against the toolchain's pinned Flocq.
_GAPPALIB_NIX_EXPR = '''
{ pkgs ? import <nixpkgs> {} }:

let
  # Use coq_9_0 to match the exact Rocq toolchain version, and its matching
  # Flocq build (coqPackages.flocq is built against the same coq_9_0 in this
  # nixpkgs snapshot -- see rocq/extensions.bzl's rocq_flocq package).
  coq = pkgs.coq_9_0;
  flocq = pkgs.coqPackages.flocq;
in
pkgs.stdenv.mkDerivation {
  pname = "gappalib-coq";
  version = "1.10.0";

  src = ./.;

  nativeBuildInputs = [ coq ];
  buildInputs = [ coq flocq ];

  buildPhase = \'\'
    export COQBIN="${coq}/bin/"
    {
      echo "-R src Gappa"
      echo "-I src"
      echo "-Q ${flocq}/lib/coq/${coq.coq-version}/user-contrib/Flocq Flocq"
      for f in src/*.v; do
        [ "$(basename "$f")" = "Gappa_tactic.v" ] && continue
        echo "$f"
      done
    } > _CoqProject
    ${coq}/bin/coq_makefile -f _CoqProject -o Makefile.coq
    make -f Makefile.coq -j$NIX_BUILD_CORES
  \'\';

  installPhase = \'\'
    mkdir -p $out/lib/coq/${coq.coq-version}/user-contrib/Gappa
    cp src/*.vo src/*.glob $out/lib/coq/${coq.coq-version}/user-contrib/Gappa/
  \'\';
}
'''

def _gappalib_source_impl(repository_ctx):
    """Download and build gappalib-coq from source using nix-build.

    gappalib-coq is a pure .v theory library (no ML plugin needed for our
    use), so unlike smpl this only needs a .vo build, not a native plugin.
    """
    version = repository_ctx.attr.version
    sha256 = repository_ctx.attr.sha256
    nixpkgs_commit = repository_ctx.attr.nixpkgs_commit

    repository_ctx.report_progress("Downloading gappalib-coq source ({})".format(version))

    url = "{}/-/archive/gappalib-coq-{v}/coq-gappalib-coq-{v}.tar.gz".format(
        _GAPPALIB_REPO,
        v = version,
    )

    download_kwargs = {
        "url": url,
        "stripPrefix": "coq-gappalib-coq-{}".format(version),
    }
    if sha256:
        download_kwargs["sha256"] = sha256

    repository_ctx.download_and_extract(**download_kwargs)

    nix_build = repository_ctx.which("nix-build")
    if not nix_build:
        fail(
            "gappalib_source requires nix-build to compile gappalib-coq " +
            "against this toolchain's pinned Flocq. Install Nix (see README " +
            "Prerequisites) -- there is no non-Nix fallback for this package.",
        )

    repository_ctx.file("default.nix", _GAPPALIB_NIX_EXPR)

    repository_ctx.report_progress(
        "Building gappalib-coq with nix-build (nixpkgs {})".format(nixpkgs_commit[:12]),
    )

    nix_expr = "import ./default.nix {{ pkgs = import (fetchTarball \"https://github.com/NixOS/nixpkgs/archive/{}.tar.gz\") {{}}; }}".format(nixpkgs_commit)

    build_result = repository_ctx.execute(
        [str(nix_build), "--no-out-link", "-E", nix_expr],
        timeout = 600,
    )

    if build_result.return_code != 0:
        fail("nix-build failed for gappalib-coq: {}".format(build_result.stderr))

    nix_store_path = build_result.stdout.strip()
    repository_ctx.report_progress("gappalib-coq built at {}".format(nix_store_path))

    repository_ctx.symlink(nix_store_path, "nix-out")

    build_content = '''# Generated BUILD.bazel for gappalib-coq (nix-built)
# gappalib-coq is Gappa's Rocq/Coq support library, built on top of Flocq.

package(default_visibility = ["//visibility:public"])

filegroup(
    name = "gappalib",
    srcs = glob([
        "nix-out/lib/coq/**/*.vo",
        "nix-out/lib/coq/**/*.glob",
    ], allow_empty = True),
)

filegroup(
    name = "theories_src",
    srcs = glob(["src/**/*.v"]),
)
'''
    repository_ctx.file("BUILD.bazel", build_content)

gappalib_source = repository_rule(
    implementation = _gappalib_source_impl,
    attrs = {
        "version": attr.string(
            default = _DEFAULT_VERSION,
            doc = "gappalib-coq release tag to use",
        ),
        "sha256": attr.string(
            default = "",
            doc = "SHA256 of the source archive",
        ),
        "nixpkgs_commit": attr.string(
            default = "6201e203d09599479a3b3450ed24fa81537ebc4e",
            doc = "Nixpkgs commit hash for reproducible builds",
        ),
    },
    doc = "Downloads and builds gappalib-coq from source, against this toolchain's pinned Flocq.",
)
