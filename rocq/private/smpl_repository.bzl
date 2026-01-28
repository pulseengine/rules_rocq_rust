"""Repository rule for building smpl from source using nix.

smpl is a Coq/Rocq plugin providing an extensible tactic.
The nixpkgs version only supports up to Coq 8.15, so we build from source
for Rocq 9.0 compatibility using nix-build.

Source: https://github.com/uds-psl/smpl
"""

_SMPL_REPO = "https://github.com/uds-psl/smpl"
_DEFAULT_BRANCH = "rocq-9.0"

# Nix expression to build smpl
_SMPL_NIX_EXPR = '''
{ pkgs ? import <nixpkgs> {} }:

let
  # Use coq_9_0 to match the exact Rocq toolchain version
  # coqPackages.coq may use a different default version
  coq = pkgs.coq_9_0;
  ocamlPackages = coq.ocamlPackages;
in
pkgs.stdenv.mkDerivation {
  pname = "smpl";
  version = "rocq-9.0";

  src = ./.;

  nativeBuildInputs = [
    coq
    ocamlPackages.ocaml
    ocamlPackages.findlib
  ];

  buildInputs = [
    coq
    ocamlPackages.ocaml
  ];

  buildPhase = ''
    export COQBIN="${coq}/bin/"
    export PATH="${ocamlPackages.ocaml}/bin:$PATH"
    # Remove Demo.v from _CoqProject (it needs Stdlib which complicates the build)
    sed -i '/Demo.v/d' _CoqProject
    ${coq}/bin/rocq makefile -f _CoqProject -o Makefile.coq || \
      ${coq}/bin/coq_makefile -f _CoqProject -o Makefile.coq
    make -j$NIX_BUILD_CORES
  '';

  installPhase = ''
    mkdir -p $out/lib/coq/${coq.coq-version}/user-contrib/smpl
    cp -r theories/*.vo theories/*.glob $out/lib/coq/${coq.coq-version}/user-contrib/smpl/ || true
    if [ -d src ]; then
      cp -r src/*.cmxs $out/lib/coq/${coq.coq-version}/user-contrib/smpl/ 2>/dev/null || true
    fi

    # Install OCaml findlib META for ML plugin resolution
    # Coq uses findlib to locate "smpl.smpl" when Declare ML Module is used
    mkdir -p $out/lib/ocaml/${ocamlPackages.ocaml.version}/site-lib/smpl
    if [ -f src/META.smpl ]; then
      cp src/META.smpl $out/lib/ocaml/${ocamlPackages.ocaml.version}/site-lib/smpl/META
      # Symlink the plugin into the findlib directory so it can be found
      ln -sf $out/lib/coq/${coq.coq-version}/user-contrib/smpl/smpl_plugin.cmxs \
        $out/lib/ocaml/${ocamlPackages.ocaml.version}/site-lib/smpl/smpl_plugin.cmxs
    fi
  '';
}
'''

def _smpl_source_impl(repository_ctx):
    """Download and build smpl from source using nix-build.

    smpl is an ML plugin, so it needs to be compiled with Coq's build system
    to produce both .vo files and the .cmxs plugin.
    """

    branch = repository_ctx.attr.branch
    sha256 = repository_ctx.attr.sha256
    nixpkgs_commit = repository_ctx.attr.nixpkgs_commit

    repository_ctx.report_progress("Downloading smpl source ({})".format(branch))

    # Download source archive
    url = "{}/archive/refs/heads/{}.tar.gz".format(_SMPL_REPO, branch)

    download_kwargs = {
        "url": url,
        "stripPrefix": "smpl-{}".format(branch),
    }
    if sha256:
        download_kwargs["sha256"] = sha256

    repository_ctx.download_and_extract(**download_kwargs)

    # Check for nix-build
    nix_build = repository_ctx.which("nix-build")
    if not nix_build:
        repository_ctx.report_progress("nix-build not found, exposing sources only")
        _generate_sources_only_build(repository_ctx)
        return

    # Write nix expression
    repository_ctx.file("default.nix", _SMPL_NIX_EXPR)

    # Build with nix-build using pinned nixpkgs commit for reproducibility
    repository_ctx.report_progress("Building smpl with nix-build (nixpkgs {})".format(nixpkgs_commit[:12]))

    # Use pinned nixpkgs commit to ensure smpl is compiled against
    # the exact same Rocq corelib as our toolchain
    nix_expr = "import ./default.nix {{ pkgs = import (fetchTarball \"https://github.com/NixOS/nixpkgs/archive/{}.tar.gz\") {{}}; }}".format(nixpkgs_commit)

    build_result = repository_ctx.execute(
        [str(nix_build), "--no-out-link", "-E", nix_expr],
        timeout = 600,
    )

    if build_result.return_code != 0:
        print("nix-build failed: {}".format(build_result.stderr))
        # Fall back to trying with system rocqc/coqc
        _try_system_build(repository_ctx)
        return

    # Get the output path from nix-build
    nix_store_path = build_result.stdout.strip()
    repository_ctx.report_progress("smpl built at {}".format(nix_store_path))

    # Symlink the nix store output
    repository_ctx.symlink(nix_store_path, "nix-out")
    _generate_nix_build(repository_ctx)

def _try_system_build(repository_ctx):
    """Try building with system rocqc/coqc."""
    rocqc = repository_ctx.which("rocqc")
    if not rocqc:
        rocqc = repository_ctx.which("coqc")

    if not rocqc:
        repository_ctx.report_progress("rocqc/coqc not found, exposing sources only")
        _generate_sources_only_build(repository_ctx)
        return

    coqbin = str(rocqc.dirname) + "/"
    repository_ctx.report_progress("Building smpl with {}".format(rocqc))

    # Generate Makefile.coq
    makefile_result = repository_ctx.execute(
        [str(rocqc.dirname) + "/rocq", "makefile", "-f", "_CoqProject", "-o", "Makefile.coq"],
        timeout = 60,
        environment = {"COQBIN": coqbin},
    )

    if makefile_result.return_code != 0:
        makefile_result = repository_ctx.execute(
            [str(rocqc.dirname) + "/coq_makefile", "-f", "_CoqProject", "-o", "Makefile.coq"],
            timeout = 60,
            environment = {"COQBIN": coqbin},
        )

    if makefile_result.return_code != 0:
        print("Failed to generate Makefile.coq: {}".format(makefile_result.stderr))
        _generate_sources_only_build(repository_ctx)
        return

    build_result = repository_ctx.execute(
        ["make", "-j4"],
        timeout = 300,
        environment = {"COQBIN": coqbin},
    )

    if build_result.return_code != 0:
        print("Failed to build smpl: {}".format(build_result.stderr))
        _generate_sources_only_build(repository_ctx)
        return

    repository_ctx.report_progress("smpl built successfully")
    _generate_compiled_build(repository_ctx)

def _generate_sources_only_build(repository_ctx):
    """Generate BUILD.bazel exposing only sources (when compilation fails)."""
    build_content = '''# Generated BUILD.bazel for smpl (sources only - compilation failed)

package(default_visibility = ["//visibility:public"])

filegroup(
    name = "theories",
    srcs = glob(["theories/**/*.v"]),
)

filegroup(
    name = "src",
    srcs = glob(["src/**"]),
)

filegroup(
    name = "all_sources",
    srcs = [":theories", ":src", "_CoqProject", "Makefile"],
)
'''
    repository_ctx.file("BUILD.bazel", build_content)

def _generate_compiled_build(repository_ctx):
    """Generate BUILD.bazel exposing compiled smpl."""
    build_content = '''# Generated BUILD.bazel for smpl (compiled)
# smpl is a Coq/Rocq ML plugin with compiled .vo and .cmxs files

package(default_visibility = ["//visibility:public"])

# Compiled theory files (.vo)
filegroup(
    name = "compiled",
    srcs = glob([
        "theories/**/*.vo",
        "theories/**/*.glob",
    ]),
)

# ML plugin (compiled .cmxs)
filegroup(
    name = "plugin",
    srcs = glob(["src/**/*.cmxs"]),
)

# All compiled artifacts
filegroup(
    name = "smpl",
    srcs = [
        ":compiled",
        ":plugin",
    ],
)

# Source files (for reference)
filegroup(
    name = "theories_src",
    srcs = glob(["theories/**/*.v"]),
)
'''
    repository_ctx.file("BUILD.bazel", build_content)

def _generate_nix_build(repository_ctx):
    """Generate BUILD.bazel exposing nix-built smpl."""
    build_content = '''# Generated BUILD.bazel for smpl (nix-built)
# smpl is a Coq/Rocq ML plugin built with nix-build

package(default_visibility = ["//visibility:public"])

# Compiled theory files (.vo) and plugin (.cmxs) from nix store
filegroup(
    name = "smpl",
    srcs = glob([
        "nix-out/lib/coq/**/*.vo",
        "nix-out/lib/coq/**/*.glob",
        "nix-out/lib/coq/**/*.cmxs",
    ], allow_empty = True),
)

# OCaml findlib plugin (needed for coqc to load smpl ML plugin)
filegroup(
    name = "ocaml_plugins",
    srcs = glob(["nix-out/lib/ocaml/**/site-lib/**"], allow_empty = True),
)

# Source files (for reference)
filegroup(
    name = "theories_src",
    srcs = glob(["theories/**/*.v"]),
)
'''
    repository_ctx.file("BUILD.bazel", build_content)

smpl_source = repository_rule(
    implementation = _smpl_source_impl,
    attrs = {
        "branch": attr.string(
            default = _DEFAULT_BRANCH,
            doc = "Git branch of smpl to use",
        ),
        "sha256": attr.string(
            default = "",
            doc = "SHA256 of the source archive",
        ),
        "nixpkgs_commit": attr.string(
            default = "88d3861acdd3d2f0e361767018218e51810df8a1",
            doc = "Nixpkgs commit hash for reproducible builds",
        ),
    },
    doc = "Downloads and builds smpl from source for Rocq 9.0 using nix.",
)
