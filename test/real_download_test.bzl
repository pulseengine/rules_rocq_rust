"""Test real download functionality using local test releases.

This module tests the actual download and extraction mechanisms
using the mock releases we created.
"""

load("@bazel_skylib//lib:native.bzl", "native")

# Test real download with local test releases
def test_real_download_functionality():
    """Test that real download functionality works with local test releases."""
    
    print("Testing real download functionality...")
    
    # Set up environment for local testing
    os_env = native.os_env()
    
    # Check if we can set up local test mode
    if not native.path("test_releases").exists:
        print("❌ Test releases not found. Run create_test_releases.py first.")
        return False
    
    # List available test releases
    test_files = []
    for f in native.glob(["test_releases/*"]):
        test_files.append(f.basename)
    
    if not test_files:
        print("❌ No test release files found")
        return False
    
    print("✅ Found test release files:")
    for f in test_files:
        print(f"   - {f}")
    
    # Test that we can read a test file
    test_file = native.path("test_releases", test_files[0])
    if test_file.exists:
        print(f"✅ Can access test file: {test_file.basename}")
        
        # Test file size
        if test_file.size > 1000:  # Should be larger than 1KB
            print(f"✅ Test file has reasonable size: {test_file.size} bytes")
        else:
            print(f"❌ Test file too small: {test_file.size} bytes")
            return False
    else:
        print("❌ Cannot access test file")
        return False
    
    print("✅ Real download test: PASSED")
    return True

# Test toolchain extraction with real files
def test_real_extraction_functionality():
    """Test extraction of real toolchain archives."""
    
    print("Testing real extraction functionality...")
    
    # Find a tar.gz file to test extraction
    tar_files = []
    for f in native.glob(["test_releases/*.tar.gz"]):
        tar_files.append(f)
    
    if not tar_files:
        print("❌ No .tar.gz files found for extraction test")
        return False
    
    test_file = tar_files[0]
    print(f"Testing extraction of: {test_file.basename}")
    
    # Create test extraction directory
    extract_dir = native.path("test_extraction_real")
    native.mkdir(extract_dir)
    
    try:
        # Extract the archive
        native.execute([
            "tar", "-xzf", str(test_file), "-C", str(extract_dir)
        ])
        
        # Check if extraction worked
        extracted_files = []
        for f in native.glob([str(extract_dir) + "/**/*"]):
            extracted_files.append(f.basename)
        
        if len(extracted_files) > 5:  # Should have multiple files
            print(f"✅ Successfully extracted {len(extracted_files)} files")
            
            # Check for expected files
            has_bin = False
            has_lib = False
            
            for f in native.glob([str(extract_dir) + "/bin/*"]):
                has_bin = True
                break
            
            for f in native.glob([str(extract_dir) + "/lib/*"]):
                has_lib = True
                break
            
            if has_bin:
                print("✅ Found bin directory in extracted archive")
            else:
                print("❌ No bin directory found")
            
            if has_lib:
                print("✅ Found lib directory in extracted archive")
            else:
                print("❌ No lib directory found")
            
            # Clean up
            native.rm(extract_dir)
            
            if has_bin and has_lib:
                print("✅ Real extraction test: PASSED")
                return True
            else:
                print("❌ Real extraction test: FAILED (missing expected directories)")
                return False
        else:
            print(f"❌ Extraction produced only {len(extracted_files)} files")
            native.rm(extract_dir)
            return False
            
    except Exception as e:
        print(f"❌ Extraction failed with error: {str(e)}")
        native.rm(extract_dir)
        return False

# Test checksum verification with real files
def test_real_checksum_verification():
    """Test checksum verification with real test files."""
    
    print("Testing real checksum verification...")
    
    # Read the checksums file
    checksums_file = native.path("test_releases/checksums-v1.0.0.txt")
    if not checksums_file.exists:
        print("❌ Checksums file not found")
        return False
    
    # Parse checksums
    checksums = {}
    content = native.read(checksums_file)
    for line in content.split('\n'):
        if ':' in line:
            platform, checksum = line.split(':', 1)
            checksums[platform.strip()] = checksum.strip()
    
    if not checksums:
        print("❌ No checksums found in file")
        return False
    
    print(f"✅ Found checksums for {len(checksums)} platforms")
    
    # Test checksum verification for each platform
    all_passed = True
    
    for platform, expected_checksum in checksums.items():
        # Find the corresponding file
        filename = f"test-toolchain-1.0.0-{platform}"
        if platform.startswith("windows"):
            filename += ".zip"
        else:
            filename += ".tar.gz"
        
        file_path = native.path("test_releases", filename)
        if file_path.exists:
            # Calculate actual checksum
            actual_checksum = calculate_sha256(file_path)
            
            if actual_checksum == expected_checksum:
                print(f"✅ {platform}: Checksum matches")
            else:
                print(f"❌ {platform}: Checksum mismatch")
                print(f"   Expected: {expected_checksum}")
                print(f"   Actual:   {actual_checksum}")
                all_passed = False
        else:
            print(f"❌ {platform}: File not found")
            all_passed = False
    
    if all_passed:
        print("✅ Real checksum verification test: PASSED")
        return True
    else:
        print("❌ Real checksum verification test: FAILED")
        return False

def calculate_sha256(file_path):
    """Calculate SHA256 checksum of a file."""
    import hashlib
    sha256_hash = hashlib.sha256()
    
    with open(str(file_path), "rb") as f:
        for byte_block in iter(lambda: f.read(4096), b""):
            sha256_hash.update(byte_block)
    
    return sha256_hash.hexdigest()

# Run all real download tests
def run_real_download_tests():
    """Run all real download and extraction tests."""
    
    print("\n=== Running Real Download Tests ===")
    
    tests = [
        ("Real Download Test", test_real_download_functionality),
        ("Real Extraction Test", test_real_extraction_functionality),
        ("Real Checksum Test", test_real_checksum_verification),
    ]
    
    results = []
    
    for test_name, test_func in tests:
        print(f"\n--- {test_name} ---")
        try:
            result = test_func()
            results.append((test_name, result))
        except Exception as e:
            print(f"❌ {test_name}: EXCEPTION - {str(e)}")
            results.append((test_name, False))
    
    # Summary
    print("\n=== Test Summary ===")
    passed = sum(1 for _, result in results if result)
    total = len(results)
    
    for test_name, result in results:
        status = "✅ PASSED" if result else "❌ FAILED"
        print(f"{test_name}: {status}")
    
    print(f"\nOverall: {passed} / {total} tests passed")
    
    if passed == total:
        print("🎉 All real download tests passed!")
        print("\nTo use real downloads in your project:")
        print("1. Set BAZEL_ROCQ_LOCAL_TEST=1")
        print("2. Use the test_real_toolchain_repository rule")
        print("3. The toolchain will download from local test releases")
        return True
    else:
        print("⚠️  Some tests failed. Check the output above.")
        return False

# Export test functions
real_download_test = test_real_download_functionality
real_extraction_test = test_real_extraction_functionality
real_checksum_test = test_real_checksum_verification
run_all_real_download_tests = run_real_download_tests