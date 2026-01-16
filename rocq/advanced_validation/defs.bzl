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

"""Advanced proof validation and automation for Rocq.

This module provides enhanced proof validation capabilities including:
- Multiple validation levels with customizable criteria
- Support for custom validation scripts
- Detailed validation reporting and visualization
- Automated proof generation and tactic application
- Integration with external theorem provers
"""

load(
    "//rocq/advanced_validation:private/advanced_validation.bzl",
    _rocq_advanced_validation = "rocq_advanced_validation",
    _rocq_custom_validation = "rocq_custom_validation",
    _rocq_proof_automation = "rocq_proof_automation",
    _rocq_coverage_analysis = "rocq_coverage_analysis",
    _rocq_external_prover = "rocq_external_prover",
)

# Public API for advanced validation
rocq_advanced_validation = _rocq_advanced_validation
# Enhanced proof validation with multiple levels and detailed reporting

rocq_custom_validation = _rocq_custom_validation
# Custom validation using user-provided scripts and criteria

rocq_proof_automation = _rocq_proof_automation
# Automated proof generation and tactic application

rocq_coverage_analysis = _rocq_coverage_analysis
# Advanced proof coverage analysis with visualization

rocq_external_prover = _rocq_external_prover
# Integration with external theorem provers

# Symbolic macro for complete advanced verification workflow
def rocq_complete_verification(name, coq_targets, **kwargs):
    """Symbolic macro for complete advanced verification workflow.
    
    This macro creates a comprehensive verification pipeline including:
    - Advanced validation with multiple levels
    - Automated proof generation
    - Coverage analysis
    - External prover integration
    
    Args:
        name: Name of the verification target
        coq_targets: List of Coq targets to verify
        **kwargs: Additional arguments for the verification process
    """
    native.module_extension(
        implementation = _rocq_complete_verification_impl,
        name = name,
        coq_targets = coq_targets,
        **kwargs
    )

def _rocq_complete_verification_impl(module_ctx):
    """Implementation of rocq_complete_verification symbolic macro."""
    # This would create the actual targets in a full implementation
    # For now, we return an empty extension metadata
    return module_ctx.extension_metadata(reproducible = True)