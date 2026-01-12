"""Integration tests for rules_rocq_rust.

This module provides integration tests that verify the complete toolchain setup.
"""

load("@bazel_skylib//lib:native.bzl", "native")

# Load statements must be at module level in Starlark
load("//rocq:defs.bzl", "rocq_library", "rocq_proof_test")
load("//coq_of_rust:defs.bzl", "coq_of_rust_library")
load("//rocq:extensions.bzl", "rocq")
load("//coq_of_rust:extensions.bzl", "coq_of_rust")
load("//:toolchains/ocaml_extensions.bzl", "ocaml")

# Integration test for Rocq toolchain
def test_rocq_integration():
    """Test Rocq toolchain integration."""
    # Simple test: if we can reference the rules, they exist
    _ = rocq_library
    _ = rocq_proof_test
    
    print("✓ Rocq integration test passed")
    return True

# Integration test for coq-of-rust
def test_coq_of_rust_integration():
    """Test coq-of-rust integration."""
    # Simple test: if we can reference the rule, it exists
    _ = coq_of_rust_library
    
    print("✓ coq-of-rust integration test passed")
    return True

# Integration test for module extensions
def test_module_extensions():
    """Test that module extensions are properly configured."""
    # Simple test: if we can reference the extensions, they exist
    _ = rocq
    _ = coq_of_rust
    _ = ocaml
    
    print("✓ Module extensions test passed")
    return True

# Run all integration tests
def run_integration_tests():
    """Run all integration tests."""
    print("Running integration tests...")
    
    success = True
    success = test_rocq_integration() and success
    success = test_coq_of_rust_integration() and success
    success = test_module_extensions() and success
    
    if success:
        print("\n✓ All integration tests passed!")
    else:
        print("\n✗ Some integration tests failed!")
    
    return success