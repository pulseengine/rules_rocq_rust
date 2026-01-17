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

"""Public entry point for rules_wasm_component integration with coq_of_rust.

This module provides integration between rules_wasm_component and coq_of_rust,
allowing WebAssembly components to be verified using Coq for formal verification.
"""

load(
    "//wasm_integration/private:wasm_integration.bzl",
    _wasm_to_coq_library = "wasm_to_coq_library",
    _wasm_component_verification = "wasm_component_verification",
)

# Public API for WASM integration
wasm_to_coq_library = _wasm_to_coq_library
# Translates WebAssembly components to Coq using coq-of-rust

wasm_component_verification = _wasm_component_verification
# Verifies WebAssembly component properties using Coq

# Symbolic macro for complete WASM verification workflow
def rocq_wasm_verification(name, wasm_target, **kwargs):
    """Symbolic macro for complete WASM verification workflow.
    
    This macro creates a complete verification pipeline from WASM components
    through coq-of-rust translation to Coq proof verification.
    
    Args:
        name: Name of the verification target
        wasm_target: Label of the rules_wasm_component target to verify
        **kwargs: Additional arguments for the verification process
    """
    native.module_extension(
        implementation = _rocq_wasm_verification_impl,
        name = name,
        wasm_target = wasm_target,
        **kwargs
    )

def _rocq_wasm_verification_impl(module_ctx):
    """Implementation of rocq_wasm_verification symbolic macro."""
    # This would create the actual targets in a full implementation
    # For now, we return an empty extension metadata
    return module_ctx.extension_metadata(reproducible = True)