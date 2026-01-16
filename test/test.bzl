"""Main test entry point for rules_rocq_rust."""

# This file is used to test that the repository structure is correct
# and that files can be loaded properly.

def test_loading():
    """Test that this file can be loaded."""
    return True

# Run all tests
def run_all_tests():
    """Run all tests in the repository."""
    print("Running all rules_rocq_rust tests...")
    
    # Test basic loading
    if not test_loading():
        print("❌ Basic loading test failed")
        return False
    
    # Test Rocq rules
    try:
        load("//test/rocq:test_loading.bzl", "run_tests")
        if not run_tests():
            print("❌ Rocq tests failed")
            return False
    except Exception as e:
        print("❌ Failed to run Rocq tests:", str(e))
        return False
    
    # Test coq-of-rust rules
    try:
        load("//test:coq_of_rust_test.bzl", "run_coq_of_rust_tests")
        if not run_coq_of_rust_tests():
            print("❌ coq-of-rust tests failed")
            return False
    except Exception as e:
        print("❌ Failed to run coq-of-rust tests:", str(e))
        return False
    
    print("✅ All tests passed!")
    return True

if __name__ == "__main__":
    run_all_tests()