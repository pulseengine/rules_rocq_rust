"""Simple test that doesn't use try/except.

This test verifies basic functionality without using Python-style exception handling.
"""

def test_simple():
    """Simple test that loads core modules."""
    print("Running simple test...")
    
    # This will work if all modules load correctly
    # If any fail, Bazel will show the error
    load("//rocq:defs.bzl", "rocq_library", "rocq_proof_test")
    load("//coq_of_rust:defs.bzl", "coq_of_rust_library")
    load("//checksums:registry.bzl", "get_tool_checksum")
    load("//toolchains:tool_registry.bzl", "detect_platform")
    
    print("✓ All modules loaded successfully")
    return True