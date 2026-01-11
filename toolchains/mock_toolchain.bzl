"""Mock toolchain for testing purposes.

This provides a mock Rocq toolchain that can be used for testing
without requiring actual Rocq binaries.
"""

load("@bazel_skylib//lib:paths.bzl", "paths")

# Mock Rocq toolchain for testing
def rocq_mock_toolchain(name, **kwargs):
    """Creates a mock Rocq toolchain for testing."""
    native.filegroup(
        name = name,
        srcs = [],
        **kwargs
    )

# Mock coqc binary for testing
def rocq_mock_binary(name, **kwargs):
    """Creates a mock coqc binary for testing."""
    native.filegroup(
        name = name,
        srcs = [],
        **kwargs
    )

# Mock standard library for testing
def rocq_mock_stdlib(name, **kwargs):
    """Creates a mock standard library for testing."""
    native.filegroup(
        name = name,
        srcs = [],
        **kwargs
    )

# Test toolchain that can be used without real binaries
def create_mock_rocq_toolchain():
    """Creates a complete mock Rocq toolchain for testing."""
    # Create mock binaries
    rocq_mock_binary(name = "mock_coqc")
    rocq_mock_binary(name = "mock_coqtop")
    
    # Create mock standard library
    rocq_mock_stdlib(name = "mock_stdlib")
    
    # Create mock toolchain
    rocq_mock_toolchain(name = "mock_rocq_toolchain")