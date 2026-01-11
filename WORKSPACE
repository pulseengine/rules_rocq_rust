"""Legacy WORKSPACE file for rules_rocq_rust.

This provides compatibility for projects not yet using Bazel 8 bzlmod.
Following the pattern established by rules_rust and rules_wasm_component.
"""

# Load the bzlmod-generated WORKSPACE for compatibility
load("@bazel_tools//tools/build_defs/repo:http.bzl", "http_archive")

# Legacy repository rules for non-bzlmod users
# These would be used when not using MODULE.bazel

# Rules for setting up Rocq toolchain in legacy mode
def rocq_repositories(version = "2025.01.0", strategy = "download"):
    """Legacy repository setup for Rocq toolchain.
    
    Args:
        version: Rocq version to use
        strategy: Acquisition strategy (currently only "download" supported)
    """
    # In a real implementation, this would call the actual repository rules
    # For now, we provide a placeholder that tells users to use bzlmod
    native.print("WARNING: Legacy repository rules are not fully implemented.")
    native.print("Please use Bazel 8 bzlmod with MODULE.bazel for full functionality.")

# Rules for setting up coq-of-rust toolchain in legacy mode  
def coq_of_rust_repositories(version = "0.5.0", strategy = "download"):
    """Legacy repository setup for coq-of-rust toolchain.
    
    Args:
        version: coq-of-rust version to use
        strategy: Acquisition strategy (currently only "download" supported)
    """
    # Placeholder for legacy support
    native.print("WARNING: Legacy repository rules are not fully implemented.")
    native.print("Please use Bazel 8 bzlmod with MODULE.bazel for full functionality.")

# Register toolchains in legacy mode
def register_rocq_toolchains():
    """Register Rocq toolchains in legacy WORKSPACE mode."""
    native.print("WARNING: Toolchain registration requires bzlmod. Please use MODULE.bazel.")

# For bzlmod users, this WORKSPACE is mostly empty since everything is in MODULE.bazel
# The actual toolchain setup happens automatically via the module extensions