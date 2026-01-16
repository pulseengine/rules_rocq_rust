"""
Test file for rocq_integration module functionality.
"""

load("@bazel_skylib//lib:paths.bzl", "paths")
load("@bazel_skylib//lib:unittest.bzl", "analysistest")
load("//rocq_integration:defs.bzl", "rocq_integration")

# Test the rocq_integration module extension
def rocq_integration_test():
    """Test the rocq_integration module extension."""
    analysistest(
        name = "rocq_integration_test",
        srcs = ["//test:rocq_integration_test.bzl"],
        deps = [
            "@rules_rocq//rocq",
            "@bazel_skylib",
        ],
    )

# Test rocq_library rule
def test_rocq_library():
    """Test the rocq_library rule."""
    analysistest(
        name = "test_rocq_library",
        srcs = ["//test:test_rocq_library.bzl"],
        deps = [
            "@rules_rocq//rocq",
            "@bazel_skylib",
        ],
        tags = ["rocq_integration"],
    )

# Test rocq_proof rule
def test_rocq_proof():
    """Test the rocq_proof rule."""
    analysistest(
        name = "test_rocq_proof",
        srcs = ["//test:test_rocq_proof.bzl"],
        deps = [
            "@rules_rocq//rocq",
            "@bazel_skylib",
        ],
        tags = ["rocq_integration"],
    )

# Test rocq_validation rule
def test_rocq_validation():
    """Test the rocq_validation rule."""
    analysistest(
        name = "test_rocq_validation",
        srcs = ["//test:test_rocq_validation.bzl"],
        deps = [
            "@rules_rocq//rocq",
            "@bazel_skylib",
        ],
        tags = ["rocq_integration"],
    )

# Test rocq_coverage rule
def test_rocq_coverage():
    """Test the rocq_coverage rule."""
    analysistest(
        name = "test_rocq_coverage",
        srcs = ["//test:test_rocq_coverage.bzl"],
        deps = [
            "@rules_rocq//rocq",
            "@bazel_skylib",
        ],
        tags = ["rocq_integration"],
    )

# Test rocq_automation rule
def test_rocq_automation():
    """Test the rocq_automation rule."""
    analysistest(
        name = "test_rocq_automation",
        srcs = ["//test:test_rocq_automation.bzl"],
        deps = [
            "@rules_rocq//rocq",
            "@bazel_skylib",
        ],
        tags = ["rocq_integration"],
    )

# Test rocq_metrics rule
def test_rocq_metrics():
    """Test the rocq_metrics rule."""
    analysistest(
        name = "test_rocq_metrics",
        srcs = ["//test:test_rocq_metrics.bzl"],
        deps = [
            "@rules_rocq//rocq",
            "@bazel_skylib",
        ],
        tags = ["rocq_integration"],
    )

# Test rocq_visualization rule
def test_rocq_visualization():
    """Test the rocq_visualization rule."""
    analysistest(
        name = "test_rocq_visualization",
        srcs = ["//test:test_rocq_visualization.bzl"],
        deps = [
            "@rules_rocq//rocq",
            "@bazel_skylib",
        ],
        tags = ["rocq_integration"],
    )

# Test rocq_reporting rule
def test_rocq_reporting():
    """Test the rocq_reporting rule."""
    analysistest(
        name = "test_rocq_reporting",
        srcs = ["//test:test_rocq_reporting.bzl"],
        deps = [
            "@rules_rocq//rocq",
            "@bazel_skylib",
        ],
        tags = ["rocq_integration"],
    )

# Test complete rocq_integration workflow
def test_rocq_integration_workflow():
    """Test the complete rocq_integration workflow."""
    analysistest(
        name = "test_rocq_integration_workflow",
        srcs = ["//test:test_rocq_integration_workflow.bzl"],
        deps = [
            "@rules_rocq//rocq",
            "@bazel_skylib",
        ],
        tags = ["rocq_integration", "workflow"],
    )

# Export all test functions
rocq_integration_test = rocq_integration_test
test_rocq_library = test_rocq_library
test_rocq_proof = test_rocq_proof
test_rocq_validation = test_rocq_validation
test_rocq_coverage = test_rocq_coverage
test_rocq_automation = test_rocq_automation
test_rocq_metrics = test_rocq_metrics
test_rocq_visualization = test_rocq_visualization
test_rocq_reporting = test_rocq_reporting
test_rocq_integration_workflow = test_rocq_integration_workflow