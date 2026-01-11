"""Test that verifies Rocq rules can be loaded.

This test checks that the basic rule definitions work correctly.
"""

def test_rocq_rules_loading():
    """Test that all Rocq rules can be loaded."""
    try:
        load("//rocq:defs.bzl", "rocq_library", "rocq_proof_test", "rocq_toolchain")
        print("✓ Rocq rules loaded successfully")
        return True
    except Exception as e:
        print("✗ Failed to load Rocq rules:", str(e))
        return False

def test_toolchain_loading():
    """Test that toolchain files can be loaded."""
    try:
        load("//rocq:toolchain.bzl", "rocq_stdlib_filegroup")
        print("✓ Toolchain rules loaded successfully")
        return True
    except Exception as e:
        print("✗ Failed to load toolchain rules:", str(e))
        return False

def run_tests():
    """Run all loading tests."""
    print("Running Rocq rule loading tests...")
    
    success = True
    success = test_rocq_rules_loading() and success
    success = test_toolchain_loading() and success
    
    if success:
        print("✅ All loading tests passed!")
    else:
        print("❌ Some loading tests failed!")
    
    return success

if __name__ == "__main__":
    run_tests()