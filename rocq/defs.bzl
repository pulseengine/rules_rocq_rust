"""Public API for Rocq compilation rules."""

load("//rocq/private:rocq.bzl", _rocq_library = "rocq_library", _rocq_proof_test = "rocq_proof_test")

rocq_library = _rocq_library
rocq_proof_test = _rocq_proof_test
