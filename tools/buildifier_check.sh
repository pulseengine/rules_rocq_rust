#!/usr/bin/env bash
# Formatting gate: buildifier --mode=check over every Starlark file in the
# tree, excluding .git, bazel-* output symlinks and ci-controls/ (planted bad
# inputs live there). Fails if buildifier reports anything, and fails if it
# finds no files to check. Usage: BUILDIFIER=/path/to/buildifier tools/buildifier_check.sh
set -euo pipefail
: "${BUILDIFIER:?set BUILDIFIER to the buildifier binary (v8.5.1, see .github/workflows/ci.yml)}"

files=()
while IFS= read -r -d '' f; do files+=("$f"); done < <(
  find . \( -name .git -o -name 'bazel-*' -o -path ./ci-controls \) -prune -o \
    -type f \( -name BUILD -o -name BUILD.bazel -o -name '*.bzl' -o -name MODULE.bazel -o -name WORKSPACE -o -name WORKSPACE.bazel \) \
    -print0
)

if [ "${#files[@]}" -eq 0 ]; then
  echo "buildifier_check: no Starlark files found; refusing to pass" >&2
  exit 1
fi

echo "buildifier_check: checking ${#files[@]} file(s)"
"$BUILDIFIER" --mode=check "${files[@]}"
