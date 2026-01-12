"""Simple test to verify toolchain loading works."""

# Test loading all toolchain components
def test_toolchain_loading():
    """Test that all toolchain components can be loaded."""
    
    print("Testing toolchain loading...")
    
    # Test Rocq toolchain
    try:
        load("//rocq:defs.bzl", "rocq_library", "rocq_proof_test")
        print("✓ Rocq toolchain loaded successfully")
    except Exception as e:
        print("✗ Failed to load Rocq toolchain: {}".format(str(e)))
        return False
    
    # Test coq-of-rust toolchain
    try:
        load("//coq_of_rust:defs.bzl", "coq_of_rust_library")
        print("✓ coq-of-rust toolchain loaded successfully")
    except Exception as e:
        print("✗ Failed to load coq-of-rust toolchain: {}".format(str(e)))
        return False
    
    # Test tool registry
    try:
        load("//toolchains:tool_registry.bzl", "detect_platform", "download_and_verify")
        print("✓ Tool registry loaded successfully")
    except Exception as e:
        print("✗ Failed to load tool registry: {}".format(str(e)))
        return False
    
    # Test checksums
    try:
        load("//checksums:registry.bzl", "get_tool_checksum", "get_tool_info")
        print("✓ Checksums registry loaded successfully")
    except Exception as e:
        print("✗ Failed to load checksums registry: {}".format(str(e)))
        return False
    
    print("✓ All toolchain components loaded successfully!")
    return True

# Run test if executed directly
if __name__ == "__main__":
    test_toolchain_loading()