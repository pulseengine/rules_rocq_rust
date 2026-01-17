"""
Rocq Integration Module - Public API

This module provides rules for direct Rocq theorem proving and integration
with the Rocq proof assistant.
"""

load(
    "//rocq_integration/private:rocq_integration.bzl",
    _rocq_integration = "rocq_integration",
)

# Export the rocq_integration module extension
rocq_integration = _rocq_integration