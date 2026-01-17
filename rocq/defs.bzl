"""Public entry point to all Rocq rules and supported APIs.

Following the exact pattern established by rules_rust.
"""

# Core Rocq compilation rules
load(
    "//rocq/private:rocq.bzl",
    _rocq_library = "rocq_library",
    _rocq_proof_test = "rocq_proof_test",
)

# Public API - following rules_rust naming conventions
rocq_library = _rocq_library
# Compiles Rocq .v files into .vo files with proper dependency management

rocq_proof_test = _rocq_proof_test
# Runs Rocq in proof-checking mode, fails build if proofs don't complete