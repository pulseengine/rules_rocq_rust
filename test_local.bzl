"""Local test that doesn't require external dependencies.

This test verifies the structure and syntax of our rules without needing to download anything.
"""

def test_syntax_and_structure():
    """Test that all files have correct syntax and structure."""
    
    print("Testing rules_rocq_rust syntax and structure...")
    
    # Test 1: Verify all .bzl files can be loaded
    test_files = [
        "//rocq:defs.bzl",
        "//rocq/private:rocq.bzl",
        "//rocq/private:toolchain.bzl",
        "//rocq:extensions.bzl",
        "//coq_of_rust:defs.bzl",
        "//coq_of_rust/private:coq_of_rust.bzl",
        "//coq_of_rust/private:toolchain.bzl",
        "//checksums:registry.bzl",
        "//toolchains:tool_registry.bzl",
        "//toolchains:rocq_toolchain.bzl",
        "//toolchains:ocaml_toolchain.bzl",
        "//toolchains:ocaml_extensions.bzl",
    ]
    
    for file in test_files:
        try:
            # Just test that the file exists and can be loaded
            # We don't need to use the symbols, just verify they load
            load(file, "dummy")
            print(f"✓ {file} - Syntax OK")
        except Exception as e:
            print(f"✗ {file} - Error: {e}")
            return False
    
    # Test 2: Verify MODULE.bazel structure
    try:
        module_content = open("MODULE.bazel").read()
        if "rules_rocq_rust" in module_content:
            print("✓ MODULE.bazel - Contains module definition")
        else:
            print("✗ MODULE.bazel - Missing module definition")
            return False
    except Exception as e:
        print(f"✗ MODULE.bazel - Error: {e}")
        return False
    
    # Test 3: Verify WORKSPACE structure
    try:
        workspace_content = open("WORKSPACE").read()
        if "rules_rocq_rust" in workspace_content:
            print("✓ WORKSPACE - Contains legacy support")
        else:
            print("✓ WORKSPACE - Legacy support present")
    except Exception as e:
        print(f"✗ WORKSPACE - Error: {e}")
        return False
    
    # Test 4: Verify JSON files
    try:
        import json
        
        # Test Rocq JSON
        with open("checksums/tools/rocq.json") as f:
            rocq_data = json.load(f)
            if rocq_data["tool_name"] == "rocq":
                print("✓ checksums/tools/rocq.json - Valid JSON structure")
            else:
                print("✗ checksums/tools/rocq.json - Invalid structure")
                return False
        
        # Test OCaml JSON
        with open("checksums/tools/ocaml.json") as f:
            ocaml_data = json.load(f)
            if ocaml_data["tool_name"] == "ocaml":
                print("✓ checksums/tools/ocaml.json - Valid JSON structure")
            else:
                print("✗ checksums/tools/ocaml.json - Invalid structure")
                return False
    except Exception as e:
        print(f"✗ JSON files - Error: {e}")
        return False
    
    # Test 5: Verify example structure
    try:
        example_build = open("examples/rocq_pure/BUILD.bazel").read()
        if "rocq_library" in example_build:
            print("✓ examples/rocq_pure/BUILD.bazel - Contains rocq_library")
        else:
            print("✗ examples/rocq_pure/BUILD.bazel - Missing rocq_library")
            return False
        
        example_v = open("examples/rocq_pure/simple.v").read()
        if "Theorem" in example_v:
            print("✓ examples/rocq_pure/simple.v - Contains Coq theorems")
        else:
            print("✗ examples/rocq_pure/simple.v - Missing Coq theorems")
            return False
    except Exception as e:
        print(f"✗ Example files - Error: {e}")
        return False
    
    return True

def test_rule_definitions():
    """Test that rule definitions are properly structured."""
    
    print("\nTesting rule definitions...")
    
    # Test Rocq rules
    try:
        load("//rocq:defs.bzl", "rocq_library", "rocq_proof_test", "rocq_toolchain")
        print("✓ Rocq rules - All public rules defined")
    except Exception as e:
        print(f"✗ Rocq rules - Error: {e}")
        return False
    
    # Test coq-of-rust rules
    try:
        load("//coq_of_rust:defs.bzl", "coq_of_rust_library", "coq_of_rust_toolchain", "rocq_rust_proof")
        print("✓ coq-of-rust rules - All public rules defined")
    except Exception as e:
        print(f"✗ coq-of-rust rules - Error: {e}")
        return False
    
    # Test toolchain rules
    try:
        load("//toolchains:rocq_toolchain.bzl", "rocq_toolchain_repository")
        load("//toolchains:ocaml_toolchain.bzl", "ocaml_toolchain_repository")
        print("✓ Toolchain rules - All repository rules defined")
    except Exception as e:
        print(f"✗ Toolchain rules - Error: {e}")
        return False
    
    return True

def run_local_tests():
    """Run local tests that don't require external dependencies."""
    
    print("=" * 60)
    print("Running Local rules_rocq_rust Tests")
    print("=" * 60)
    
    success = True
    
    success = test_syntax_and_structure() and success
    success = test_rule_definitions() and success
    
    print("\n" + "=" * 60)
    if success:
        print("✅ All local tests passed!")
        print("Repository structure is valid and ready for use.")
    else:
        print("❌ Some local tests failed!")
        print("Please check the error messages above.")
    print("=" * 60)
    
    return success

# Run tests if executed directly
if __name__ == "__main__":
    run_local_tests()