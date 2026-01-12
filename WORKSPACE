"""Legacy WORKSPACE file for rules_rocq_rust.

This provides compatibility for projects not yet using Bazel 8 bzlmod.
Following the pattern established by rules_rust and rules_wasm_component.
"""

# Load the bzlmod-generated WORKSPACE for compatibility
load("@bazel_tools//tools/build_defs/repo:http.bzl", "http_archive")

# Legacy repository rules for non-bzlmod users
# These would be used when not using MODULE.bazel

# For bzlmod users, this WORKSPACE is mostly empty since everything is in MODULE.bazel
# The actual toolchain setup happens automatically via the module extensions