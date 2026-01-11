"""Public entry point to all Rocq rules and supported APIs.

Following the exact pattern established by rules_rust.
"""

load(
    "//rocq:toolchain.bzl",
    _rocq_stdlib_filegroup = "rocq_stdlib_filegroup",
)
load(
    "//rocq/private:rocq.bzl",
    _rocq_library = "rocq_library",
    _rocq_proof_test = "rocq_proof_test",
)
load(
    "//rocq/private:toolchain.bzl",
    _rocq_toolchain = "rocq_toolchain",
)

# Public API - following rules_rust naming conventions
rocq_library = _rocq_library
# Compiles Rocq .v files into .vo files with proper dependency management

rocq_proof_test = _rocq_proof_test
# Runs Rocq in proof-checking mode, fails build if proofs don't complete

rocq_toolchain = _rocq_toolchain
# Declares a Rocq toolchain pointing to Rocq/Coq binaries and standard library