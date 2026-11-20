#!/usr/bin/env bash
# Lockfile gate: every lockfile is committed, consistent with its manifests,
# and every Cargo.lock is audited.
#
# Usage: tools/lockfile_check.sh [ROOT]   (default: the repository root)
#
# Scans the git-tracked files under ROOT (ci-controls/ is skipped when ROOT is
# the repository root) and fails if:
#   1. a MODULE.bazel has no tracked MODULE.bazel.lock beside it, or a
#      Cargo.toml has no tracked Cargo.lock in its directory or an ancestor;
#   2. `bazel mod deps --lockfile_mode=error` fails for a MODULE.bazel.lock,
#      or `cargo metadata --locked` fails for a Cargo.lock;
#   3. `cargo audit` reports a vulnerability in any Cargo.lock;
#   4. no lockfile was found at all (a scan that measured nothing).
#
# Environment: CARGO_AUDIT (default `cargo-audit`), BAZEL (default `bazel`).
# Planted controls: ci-controls.toml, ids lockfile-*.
set -euo pipefail

root="${1:-$(git rev-parse --show-toplevel)}"
cd "$root"
repo_root="$(git rev-parse --show-toplevel)"
exclude=()
if [ "$(pwd -P)" = "$(cd "$repo_root" && pwd -P)" ]; then
  exclude=(':!:ci-controls')
fi

CARGO_AUDIT="${CARGO_AUDIT:-cargo-audit}"
BAZEL="${BAZEL:-bazel}"

tracked() { git ls-files -- "$@" ${exclude[@]+"${exclude[@]}"}; }
is_tracked() { [ -n "$(git ls-files -- "$1")" ]; }

failures=0
fail() { echo "FAIL: $*" >&2; failures=$((failures + 1)); }

# 1. Presence.
while IFS= read -r m; do
  [ -n "$m" ] || continue
  d="$(dirname "$m")"
  is_tracked "$d/MODULE.bazel.lock" || fail "$m has no committed $d/MODULE.bazel.lock"
done < <(tracked 'MODULE.bazel' '**/MODULE.bazel')

while IFS= read -r m; do
  [ -n "$m" ] || continue
  d="$(dirname "$m")"
  found=""
  while :; do
    if is_tracked "$d/Cargo.lock"; then found=1; break; fi
    [ "$d" = "." ] && break
    d="$(dirname "$d")"
  done
  [ -n "$found" ] || fail "$m has no committed Cargo.lock in its directory or any ancestor"
done < <(tracked 'Cargo.toml' '**/Cargo.toml')

# 2 and 3. Locked resolution and audit.
mod_locks=()
while IFS= read -r l; do [ -n "$l" ] && mod_locks+=("$l"); done < <(tracked 'MODULE.bazel.lock' '**/MODULE.bazel.lock')
cargo_locks=()
while IFS= read -r l; do [ -n "$l" ] && cargo_locks+=("$l"); done < <(tracked 'Cargo.lock' '**/Cargo.lock')

for l in ${mod_locks[@]+"${mod_locks[@]}"}; do
  d="$(dirname "$l")"
  echo "== bazel mod deps --lockfile_mode=error ($d)"
  (cd "$d" && "$BAZEL" mod deps --lockfile_mode=error >/dev/null) || fail "$l is out of date with $d/MODULE.bazel (run \`bazel mod deps --lockfile_mode=update\` in $d)"
done

for l in ${cargo_locks[@]+"${cargo_locks[@]}"}; do
  d="$(dirname "$l")"
  if [ -f "$d/Cargo.toml" ]; then
    echo "== cargo metadata --locked ($d)"
    cargo metadata --locked --format-version 1 --manifest-path "$d/Cargo.toml" >/dev/null || fail "$l is out of date with $d/Cargo.toml"
  else
    fail "$l has no Cargo.toml beside it"
  fi
  echo "== cargo audit ($l)"
  "$CARGO_AUDIT" audit --file "$l" || fail "cargo audit reported a vulnerability in $l"
done

total=$(( ${#mod_locks[@]} + ${#cargo_locks[@]} ))
if [ "$total" -eq 0 ]; then
  fail "no lockfile found under $root: the gate measured nothing"
fi

echo "lockfiles: ${#mod_locks[@]} MODULE.bazel.lock, ${#cargo_locks[@]} Cargo.lock; failures: $failures"
[ "$failures" -eq 0 ]
