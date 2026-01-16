"""Public entry point to all Rocq rules and supported APIs.

Following the exact pattern established by rules_rust.
"""

# Note: toolchain.bzl removed temporarily until full implementation
# _rocq_stdlib_filegroup will be added when toolchain support is complete
load(
    "//rocq:private/rocq.bzl",
    _rocq_library = "rocq_library",
    _rocq_proof_test = "rocq_proof_test",
)
load(
    "//rocq:private/toolchain.bzl",
    _rocq_toolchain = "rocq_toolchain",
)
load(
    "//rocq:validation.bzl",
    _rocq_proof_validation = "rocq_proof_validation",
    _rocq_proof_coverage = "rocq_proof_coverage",
    _rocq_complete_validation = "rocq_complete_validation",
    _rocq_proof_automation = "rocq_proof_automation",
    _rocq_coq_of_rust_validation = "rocq_coq_of_rust_validation",
)
load(
    "//rocq_integration:defs.bzl",
    _rocq_integration = "rocq_integration",
)

# Public API - following rules_rust naming conventions
rocq_library = _rocq_library
# Compiles Rocq .v files into .vo files with proper dependency management

rocq_proof_test = _rocq_proof_test
# Runs Rocq in proof-checking mode, fails build if proofs don't complete

rocq_toolchain = _rocq_toolchain
# Declares a Rocq toolchain pointing to Rocq/Coq binaries and standard library

# Proof validation rules
rocq_proof_validation = _rocq_proof_validation
# Performs comprehensive proof validation with coverage analysis

rocq_proof_coverage = _rocq_proof_coverage
# Analyzes proof coverage of Coq files

rocq_complete_validation = _rocq_complete_validation
# Performs complete validation including proof checking and coverage analysis

rocq_proof_automation = _rocq_proof_automation
# Applies proof automation using Ltac scripts

rocq_coq_of_rust_validation = _rocq_coq_of_rust_validation
# Validates coq-of-rust generated proofs

rocq_integration = _rocq_integration
# Module extension for Rocq integration functionality