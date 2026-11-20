#!/usr/bin/env bash
# Planted control for #60 (ci-controls.toml: dangling-coqc).
#
# Overrides the Rocq toolchain repository with a copy whose bin/coqc is a
# dangling symlink -- the state a restored Bazel cache or a Nix garbage
# collection leaves behind -- and runs a rocq_proof_test. The test must FAIL:
# before #60 it passed by collecting sources without compiling anything.
#
# Usage: ci-controls/dangling-coqc/run.sh   (from the repository root, after
# the toolchain has been fetched by a normal build)
set -euo pipefail

output_base="$(bazel info output_base)"
repo="$output_base/external/+rocq+rocq_toolchains"
[ -d "$repo" ] || { echo "dangling-coqc: $repo not fetched; run a build first" >&2; exit 2; }

scratch="$(mktemp -d)"
trap 'rm -rf "$scratch"' EXIT
cp -RP "$repo/." "$scratch/"
rm -rf "$scratch/bin"
mkdir "$scratch/bin"
ln -s /nonexistent/planted/coqc "$scratch/bin/coqc"

exec bazel test //examples/assumptions_check:clean_test \
  --override_repository=+rocq+rocq_toolchains="$scratch" \
  --test_output=errors
