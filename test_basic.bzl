"""Basic test to verify the rules_rocq_rust structure.

This test verifies that the core files can be loaded and basic functionality works.
"""

def test_basic_loading():
    """Test that all core files can be loaded."""
    
    # Test loading core modules
    try:
        load("//rocq:defs.bzl", "rocq_library", "rocq_proof_test")
        print("✓ Successfully loaded rocq/defs.bzl")
    except Exception as e:
        print("✗ Failed to load rocq/defs.bzl:", str(e))
        return False
    
    try:
        load("//coq_of_rust:defs.bzl", "coq_of_rust_library")
        print("✓ Successfully loaded coq_of_rust/defs.bzl")
    except Exception as e:
        print("✗ Failed to load coq_of_rust/defs.bzl:", str(e))
        return False
    
    try:
        load("//checksums:registry.bzl", "get_tool_checksum")
        print("✓ Successfully loaded checksums/registry.bzl")
    except Exception as e:
        print("✗ Failed to load checksums/registry.bzl:", str(e))
        return False
    
    try:
        load("//toolchains:tool_registry.bzl", "detect_platform")
        print("✓ Successfully loaded toolchains/tool_registry.bzl")
    except Exception as e:
        print("✗ Failed to load toolchains/tool_registry.bzl:", str(e))
        return False
    
    return True

def test_rocq_rules():
    """Test that Rocq rules have correct attributes."""
    
    load("//rocq:defs.bzl", "rocq_library", "rocq_proof_test")
    
    # Check that rules are callable
    if callable(rocq_library):
        print("✓ rocq_library is callable")
    else:
        print("✗ rocq_library is not callable")
        return False
    
    if callable(rocq_proof_test):
        print("✓ rocq_proof_test is callable")
    else:
        print("✗ rocq_proof_test is not callable")
        return False
    
    return True

# Run tests if executed directly
if __name__ == "__main__":
    print("Running basic structure tests...")
    
    success = True
    success = test_basic_loading() and success
    success = test_rocq_rules() and success
    
    if success:
        print("\n✓ All basic tests passed!")
    else:
        print("\n✗ Some tests failed!")
        exit(1)