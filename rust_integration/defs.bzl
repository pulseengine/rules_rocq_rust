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

"""Public entry point for rules_rust integration with coq_of_rust.

This module provides integration between rules_rust and coq_of_rust,
allowing Rust libraries to be translated to Coq for formal verification.
"""

load(
    "//rust_integration:private/rust_integration.bzl",
    _rust_to_coq_library = "rust_to_coq_library",
)

# Public API for rules_rust integration
rust_to_coq_library = _rust_to_coq_library
# Translates rules_rust libraries to Coq using coq-of-rust

# Symbolic macro for complete Rust verification workflow
# This follows the Bazel 8 pattern for higher-level composition
def rocq_rust_verification(name, rust_target, **kwargs):
    """Symbolic macro for complete Rust verification workflow.
    
    This macro creates a complete verification pipeline from Rust source
    through coq-of-rust translation to Coq proof verification.
    
    Args:
        name: Name of the verification target
        rust_target: Label of the rules_rust target to verify
        **kwargs: Additional arguments for the verification process
    """
    native.module_extension(
        implementation = _rocq_rust_verification_impl,
        name = name,
        rust_target = rust_target,
        **kwargs
    )

def _rocq_rust_verification_impl(module_ctx):
    """Implementation of rocq_rust_verification symbolic macro."""
    # This would create the actual targets in a full implementation
    # For now, we return an empty extension metadata
    return module_ctx.extension_metadata(reproducible = True)