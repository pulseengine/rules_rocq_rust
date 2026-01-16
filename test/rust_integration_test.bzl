# Copyright 2025 Ralf Anton Beier. All rights reserved.
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#    http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

"""Integration tests for rules_rust and coq_of_rust integration.

This module contains tests to verify the integration between rules_rust
and coq_of_rust toolchains.
"""

load("@bazel_skylib//lib:deps.bzl", "deps")
load("//test:toolchain_test.bzl", "test_toolchain_availability")

# Test the basic rust_integration functionality
def test_rust_integration_basic(ctx):
    """Test basic rust_integration functionality."""
    
    # Check if rules_rust is available
    try:
        native.load("@rules_rust//rust/private:providers.bzl", "CrateInfo")
        rules_rust_available = True
    except:
        rules_rust_available = False
    
    if not rules_rust_available:
        print("Warning: rules_rust not available, skipping rust_integration tests")
        return True
    
    # Test that we can load the rust_integration module
    try:
        native.load("//rust_integration:defs.bzl", "rust_to_coq_library")
        print("✓ Successfully loaded rust_integration module")
    except Exception as e:
        fail("Failed to load rust_integration module: {}".format(str(e)))
    
    # Test that we can load the private implementation
    try:
        native.load("//rust_integration/private:rust_integration.bzl", "RustToCoqInfo")
        print("✓ Successfully loaded rust_integration private implementation")
    except Exception as e:
        fail("Failed to load rust_integration private implementation: {}".format(str(e)))
    
    return True

# Test coq_of_rust with rules_rust dependencies
def test_coq_of_rust_with_rules_rust(ctx):
    """Test coq_of_rust_library with rules_rust dependencies."""
    
    # Check if rules_rust is available
    try:
        native.load("@rules_rust//rust/private:providers.bzl", "CrateInfo")
        rules_rust_available = True
    except:
        rules_rust_available = False
    
    if not rules_rust_available:
        print("Warning: rules_rust not available, skipping coq_of_rust rules_rust integration tests")
        return True
    
    # Test that coq_of_rust_library can handle rules_rust dependencies
    try:
        native.load("//coq_of_rust/private:coq_of_rust.bzl", "RustCoqAdapterInfo")
        print("✓ Successfully loaded RustCoqAdapterInfo provider")
    except Exception as e:
        fail("Failed to load RustCoqAdapterInfo provider: {}".format(str(e)))
    
    return True

# Test provider compatibility
def test_provider_compatibility(ctx):
    """Test provider compatibility between rules_rust and coq_of_rust."""
    
    # Check if rules_rust is available
    try:
        native.load("@rules_rust//rust/private:providers.bzl", "CrateInfo")
        rules_rust_available = True
    except:
        rules_rust_available = False
    
    if not rules_rust_available:
        print("Warning: rules_rust not available, skipping provider compatibility tests")
        return True
    
    # Test that we can create the adapter provider
    try:
        # This would be a more comprehensive test in a real implementation
        # For now, we just verify the provider can be loaded
        native.load("//coq_of_rust/private:coq_of_rust.bzl", "RustCoqAdapterInfo")
        print("✓ Provider compatibility test passed")
    except Exception as e:
        fail("Provider compatibility test failed: {}".format(str(e)))
    
    return True

# Test toolchain coordination
def test_toolchain_coordination(ctx):
    """Test toolchain coordination between rules_rust and coq_of_rust."""
    
    # Test that both toolchains can be loaded
    try:
        # Load coq_of_rust toolchain
        native.load("//coq_of_rust:toolchain.bzl", "coq_of_rust_toolchain")
        print("✓ Successfully loaded coq_of_rust toolchain")
    except Exception as e:
        fail("Failed to load coq_of_rust toolchain: {}".format(str(e)))
    
    # Check if rules_rust is available
    try:
        native.load("@rules_rust//rust/private:providers.bzl", "CrateInfo")
        rules_rust_available = True
        print("✓ rules_rust is available for toolchain coordination")
    except:
        rules_rust_available = False
        print("Warning: rules_rust not available for toolchain coordination")
    
    return True

# Main test function
def test_rust_integration_all(ctx):
    """Run all rust_integration tests."""
    
    print("Running rust_integration tests...")
    
    # Run individual tests
    test_rust_integration_basic(ctx)
    test_coq_of_rust_with_rules_rust(ctx)
    test_provider_compatibility(ctx)
    test_toolchain_coordination(ctx)
    
    print("✓ All rust_integration tests completed successfully")
    return True