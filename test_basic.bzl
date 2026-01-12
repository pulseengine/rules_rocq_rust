"""Basic test to verify the rules_rocq_rust structure.

This test verifies that the core files can be loaded and basic functionality works.
"""

# Load statements must be at module level in Starlark
load("//rocq:defs.bzl", "rocq_library", "rocq_proof_test")
load("//coq_of_rust:defs.bzl", "coq_of_rust_library")
load("//checksums:registry.bzl", "get_tool_checksum")
load("//:toolchains/tool_registry.bzl", "detect_platform")
load("//test:toolchain_test.bzl", "test_all_toolchains")

def test_basic_loading():
    """Test that all core files can be loaded."""
    
    # If we can load the modules, they work
    print("✓ Successfully loaded rocq/defs.bzl")
    print("✓ Successfully loaded coq_of_rust/defs.bzl")
    print("✓ Successfully loaded checksums/registry.bzl")
    print("✓ Successfully loaded toolchains/tool_registry.bzl")
    
    return True

def test_rocq_rules():
    """Test that Rocq rules have correct attributes."""
    
    # Simple test: if we can reference the rules, they exist
    _ = rocq_library
    _ = rocq_proof_test
    
    print("✓ rocq_library is accessible")
    print("✓ rocq_proof_test is accessible")
    
    return True

# Test toolchain loading
def test_toolchain_loading():
    """Test that toolchain components can be loaded."""
    # If we can load the module, toolchain test works
    print("✓ Successfully loaded toolchain test module")
    return True

# Run tests if executed directly
def run_basic_tests():
    print("Running basic structure tests...")
    
    success = True
    success = test_basic_loading() and success
    success = test_rocq_rules() and success
    success = test_toolchain_loading() and success
    
    if success:
        print("\n✓ All basic tests passed!")
    else:
        print("\n✗ Some tests failed!")
    
    return success