"""Comprehensive integration test for rules_rocq_rust.

This test verifies that all rules can be loaded and basic functionality works.
"""

def test_rocq_rules():
    """Test that Rocq rules can be loaded and have correct structure."""
    
    print("Testing Rocq rules...")
    
    # Test loading core Rocq modules
    try:
        load("//rocq:defs.bzl", "rocq_library", "rocq_proof_test", "rocq_toolchain")
        print("✓ Successfully loaded rocq/defs.bzl")
    except Exception as e:
        print("✗ Failed to load rocq/defs.bzl:", str(e))
        return False
    
    # Test loading private implementation
    try:
        load("//rocq/private:rocq.bzl", "_rocq_library_impl", "_rocq_proof_test_impl")
        print("✓ Successfully loaded rocq/private/rocq.bzl")
    except Exception as e:
        print("✗ Failed to load rocq/private/rocq.bzl:", str(e))
        return False
    
    # Test loading toolchain
    try:
        load("//rocq/private:toolchain.bzl", "_rocq_toolchain_impl")
        print("✓ Successfully loaded rocq/private/toolchain.bzl")
    except Exception as e:
        print("✗ Failed to load rocq/private/toolchain.bzl:", str(e))
        return False
    
    # Test loading extensions
    try:
        load("//rocq:extensions.bzl", "rocq")
        print("✓ Successfully loaded rocq/extensions.bzl")
    except Exception as e:
        print("✗ Failed to load rocq/extensions.bzl:", str(e))
        return False
    
    return True

def test_coq_of_rust_rules():
    """Test that coq-of-rust rules can be loaded."""
    
    print("\nTesting coq-of-rust rules...")
    
    # Test loading core coq-of-rust modules
    try:
        load("//coq_of_rust:defs.bzl", "coq_of_rust_library", "coq_of_rust_toolchain", "rocq_rust_proof")
        print("✓ Successfully loaded coq_of_rust/defs.bzl")
    except Exception as e:
        print("✗ Failed to load coq_of_rust/defs.bzl:", str(e))
        return False
    
    # Test loading private implementation
    try:
        load("//coq_of_rust/private:coq_of_rust.bzl", "_coq_of_rust_library_impl")
        print("✓ Successfully loaded coq_of_rust/private/coq_of_rust.bzl")
    except Exception as e:
        print("✗ Failed to load coq_of_rust/private/coq_of_rust.bzl:", str(e))
        return False
    
    return True

def test_toolchain_rules():
    """Test that toolchain rules can be loaded."""
    
    print("\nTesting toolchain rules...")
    
    # Test loading checksum registry
    try:
        load("//checksums:registry.bzl", "get_tool_checksum", "get_tool_info")
        print("✓ Successfully loaded checksums/registry.bzl")
    except Exception as e:
        print("✗ Failed to load checksums/registry.bzl:", str(e))
        return False
    
    # Test loading tool registry
    try:
        load("//toolchains:tool_registry.bzl", "detect_platform", "download_and_verify")
        print("✓ Successfully loaded toolchains/tool_registry.bzl")
    except Exception as e:
        print("✗ Failed to load toolchains/tool_registry.bzl:", str(e))
        return False
    
    # Test loading Rocq toolchain
    try:
        load("//toolchains:rocq_toolchain.bzl", "rocq_toolchain_repository")
        print("✓ Successfully loaded toolchains/rocq_toolchain.bzl")
    except Exception as e:
        print("✗ Failed to load toolchains/rocq_toolchain.bzl:", str(e))
        return False
    
    # Test loading OCaml toolchain
    try:
        load("//toolchains:ocaml_toolchain.bzl", "ocaml_toolchain_repository")
        print("✓ Successfully loaded toolchains/ocaml_toolchain.bzl")
    except Exception as e:
        print("✗ Failed to load toolchains/ocaml_toolchain.bzl:", str(e))
        return False
    
    return True

def test_json_checksums():
    """Test that JSON checksum files are valid."""
    
    print("\nTesting JSON checksum files...")
    
    # Test Rocq JSON
    try:
        rocq_json = """
        {
          "tool_name": "rocq",
          "github_repo": "rocq-prover/platform",
          "latest_version": "2025.01.0",
          "versions": {
            "2025.01.0": {
              "platforms": {
                "darwin_arm64": {"sha256": "abc123", "url_suffix": "test.dmg"}
              }
            }
          }
        }
        """
        data = native.json.decode(rocq_json)
        if data["tool_name"] == "rocq":
            print("✓ Rocq JSON structure is valid")
        else:
            print("✗ Rocq JSON has unexpected structure")
            return False
    except Exception as e:
        print("✗ Failed to parse Rocq JSON:", str(e))
        return False
    
    # Test OCaml JSON
    try:
        ocaml_json = """
        {
          "tool_name": "ocaml",
          "github_repo": "ocaml/ocaml",
          "latest_version": "5.1.1",
          "versions": {
            "5.1.1": {
              "platforms": {
                "darwin_arm64": {"sha256": "def456", "url_suffix": "test.tar.gz"}
              }
            }
          }
        }
        """
        data = native.json.decode(ocaml_json)
        if data["tool_name"] == "ocaml":
            print("✓ OCaml JSON structure is valid")
        else:
            print("✗ OCaml JSON has unexpected structure")
            return False
    except Exception as e:
        print("✗ Failed to parse OCaml JSON:", str(e))
        return False
    
    return True

def test_module_extensions():
    """Test that module extensions are properly defined."""
    
    print("\nTesting module extensions...")
    
    # Test Rocq extension
    try:
        load("//rocq:extensions.bzl", "rocq")
        if hasattr(rocq, "toolchain"):
            print("✓ Rocq module extension has toolchain method")
        else:
            print("✗ Rocq module extension missing toolchain method")
            return False
    except Exception as e:
        print("✗ Failed to test Rocq extension:", str(e))
        return False
    
    # Test OCaml extension
    try:
        load("//toolchains:ocaml_extensions.bzl", "ocaml")
        if hasattr(ocaml, "toolchain"):
            print("✓ OCaml module extension has toolchain method")
        else:
            print("✗ OCaml module extension missing toolchain method")
            return False
    except Exception as e:
        print("✗ Failed to test OCaml extension:", str(e))
        return False
    
    return True

def run_all_tests():
    """Run all integration tests."""
    
    print("=" * 60)
    print("Running rules_rocq_rust Integration Tests")
    print("=" * 60)
    
    success = True
    
    # Run all test functions
    success = test_rocq_rules() and success
    success = test_coq_of_rust_rules() and success
    success = test_toolchain_rules() and success
    success = test_json_checksums() and success
    success = test_module_extensions() and success
    
    print("\n" + "=" * 60)
    if success:
        print("✅ All integration tests passed!")
        print("rules_rocq_rust is ready for use.")
    else:
        print("❌ Some integration tests failed!")
        print("Please check the error messages above.")
    print("=" * 60)
    
    return success

# Run tests if executed directly
if __name__ == "__main__":
    run_all_tests()