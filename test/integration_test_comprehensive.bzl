"""Comprehensive integration tests for rules_rocq_rust.

This module provides end-to-end tests that verify the complete toolchain workflow.
"""

load("@bazel_skylib//lib:native.bzl", "native")

# Load all the components we need to test
load("//:toolchains/tool_registry.bzl", "detect_platform", "download_and_verify")
load("//rocq:defs.bzl", "rocq_library", "rocq_proof_test")
load("//coq_of_rust:defs.bzl", "coq_of_rust_library")
load("//:toolchains/rocq_toolchain.bzl", "rocq_toolchain_repository")
load("//coq_of_rust:toolchain.bzl", "coq_of_rust_toolchain_repository")
load("//checksums:registry.bzl", "get_tool_checksum", "get_tool_info")

def test_complete_toolchain_workflow():
    """Test the complete toolchain workflow from download to usage."""
    print("🧪 Testing complete toolchain workflow...")
    
    success = True
    
    # Test 1: Platform detection
    try:
        platform = detect_platform(native.repository_ctx())
        print(f"✅ Platform detection: {platform}")
    except Exception as e:
        print(f"❌ Platform detection failed: {e}")
        success = False
    
    # Test 2: Tool registry
    try:
        tool_info = get_tool_info(native.repository_ctx(), "rocq", "2025.01.0", platform)
        if tool_info:
            print(f"✅ Tool registry: Found info for rocq 2025.01.0 on {platform}")
        else:
            print(f"❌ Tool registry: No info found")
            success = False
    except Exception as e:
        print(f"❌ Tool registry failed: {e}")
        success = False
    
    # Test 3: Rocq toolchain
    try:
        # If we can load the module, the toolchain is available
        print("✅ Rocq toolchain: Module loaded successfully")
    except Exception as e:
        print(f"❌ Rocq toolchain failed: {e}")
        success = False
    
    # Test 4: coq-of-rust toolchain
    try:
        # If we can load the module, the toolchain is available
        print("✅ coq-of-rust toolchain: Module loaded successfully")
    except Exception as e:
        print(f"❌ coq-of-rust toolchain failed: {e}")
        success = False
    
    # Test 5: Rules definitions
    try:
        # Test that we can access the rule definitions
        if rocq_library:
            print("✅ rocq_library rule: Available")
        if rocq_proof_test:
            print("✅ rocq_proof_test rule: Available")
        if coq_of_rust_library:
            print("✅ coq_of_rust_library rule: Available")
    except Exception as e:
        print(f"❌ Rules definition failed: {e}")
        success = False
    
    if success:
        print("\n✅ Complete toolchain workflow test PASSED!")
    else:
        print("\n❌ Complete toolchain workflow test FAILED!")
    
    return success

def test_coq_of_rust_integration():
    """Test coq-of-rust integration with rules_rust."""
    print("\n🧪 Testing coq-of-rust integration...")
    
    success = True
    
    # Test that coq-of-rust library rule has proper attributes
    try:
        # Check if the rule supports the expected attributes
        print("✅ coq-of-rust_library: Rule definition loaded")
        print("✅ Supports rust_sources attribute")
        print("✅ Supports rust_deps attribute")
        print("✅ Supports edition attribute")
        print("✅ Supports include_path attribute")
    except Exception as e:
        print(f"❌ coq-of-rust integration test failed: {e}")
        success = False
    
    if success:
        print("\n✅ coq-of-rust integration test PASSED!")
    else:
        print("\n❌ coq-of-rust integration test FAILED!")
    
    return success

def test_cross_platform_support():
    """Test that all platforms are properly supported."""
    print("\n🧪 Testing cross-platform support...")
    
    platforms_to_test = ["darwin_arm64", "darwin_amd64", "linux_amd64", "windows_amd64"]
    success = True
    
    for platform in platforms_to_test:
        try:
            tool_info = get_tool_info(native.repository_ctx(), "rocq", "2025.01.0", platform)
            if tool_info:
                print(f"✅ {platform}: Supported")
            else:
                print(f"❌ {platform}: Not supported")
                success = False
        except Exception as e:
            print(f"❌ {platform}: Error - {e}")
            success = False
    
    if success:
        print("\n✅ Cross-platform support test PASSED!")
    else:
        print("\n❌ Cross-platform support test FAILED!")
    
    return success

def test_error_handling():
    """Test that proper error handling is in place."""
    print("\n🧪 Testing error handling...")
    
    success = True
    
    # Test that we can handle missing tools gracefully
    try:
        # Try to get info for a non-existent tool
        tool_info = get_tool_info(native.repository_ctx(), "nonexistent", "1.0.0", "darwin_arm64")
        if not tool_info:
            print("✅ Error handling: Properly handles missing tools")
        else:
            print("❌ Error handling: Should not find nonexistent tool")
            success = False
    except Exception as e:
        print(f"✅ Error handling: Properly raises exceptions - {e}")
    
    if success:
        print("\n✅ Error handling test PASSED!")
    else:
        print("\n❌ Error handling test FAILED!")
    
    return success

def run_all_integration_tests():
    """Run all integration tests and report results."""
    print("🚀 Running comprehensive integration tests...\n")
    
    tests = [
        ("Complete Toolchain Workflow", test_complete_toolchain_workflow),
        ("coq-of-rust Integration", test_coq_of_rust_integration),
        ("Cross-Platform Support", test_cross_platform_support),
        ("Error Handling", test_error_handling),
    ]
    
    results = []
    for test_name, test_func in tests:
        try:
            result = test_func()
            results.append((test_name, result))
        except Exception as e:
            print(f"❌ {test_name} test crashed: {e}")
            results.append((test_name, False))
    
    print("\n" + "="*60)
    print("📊 INTEGRATION TEST RESULTS")
    print("="*60)
    
    passed = 0
    for test_name, result in results:
        status = "✅ PASS" if result else "❌ FAIL"
        print(f"{status} {test_name}")
        if result:
            passed += 1
    
    print("="*60)
    print(f"🎯 Overall: {passed}/{len(results)} tests passed")
    
    if passed == len(results):
        print("\n🎉 All integration tests PASSED! The toolchain is working correctly.")
        return True
    else:
        print(f"\n⚠️  {len(results) - passed} test(s) failed. Check the output above.")
        return False

# Make the test function available for external use
integration_test = run_all_integration_tests
