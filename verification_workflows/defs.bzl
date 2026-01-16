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

"""End-to-end verification workflows for complete verification pipelines.

This module provides symbolic macros and workflows for complete verification
pipelines from source code to formal proofs, integrating all the components
built in previous phases.
"""

load(
    "//verification_workflows:private/verification_workflows.bzl",
    _rocq_rust_proof_impl = "rocq_rust_proof_impl",
    _rocq_wasm_proof_impl = "rocq_wasm_proof_impl",
    _complete_verification_pipeline_impl = "complete_verification_pipeline_impl",
)

# Symbolic macro for complete Rust verification workflow
def rocq_rust_proof(name, rust_target, **kwargs):
    """Symbolic macro for complete Rust verification workflow.
    
    This macro creates a complete verification pipeline from Rust source
    through coq-of-rust translation to Coq proof verification.
    
    Args:
        name: Name of the verification target
        rust_target: Label of the rules_rust target to verify
        **kwargs: Additional arguments for the verification process
    
    The pipeline includes:
    1. Rust to Coq translation using coq-of-rust
    2. Coq compilation and proof checking
    3. Advanced validation with coverage analysis
    4. Proof automation for common patterns
    5. Comprehensive reporting and metrics
    """
    native.module_extension(
        implementation = _rocq_rust_proof_impl,
        name = name,
        rust_target = rust_target,
        **kwargs
    )

# Symbolic macro for complete WASM verification workflow
def rocq_wasm_proof(name, wasm_target, **kwargs):
    """Symbolic macro for complete WASM verification workflow.
    
    This macro creates a complete verification pipeline from WASM components
    through coq-of-rust translation to Coq proof verification.
    
    Args:
        name: Name of the verification target
        wasm_target: Label of the rules_wasm_component target to verify
        **kwargs: Additional arguments for the verification process
    
    The pipeline includes:
    1. WASM to Coq translation using coq-of-rust
    2. Coq compilation and proof checking
    3. Component property verification
    4. Advanced validation with coverage analysis
    5. Comprehensive reporting and metrics
    """
    native.module_extension(
        implementation = _rocq_wasm_proof_impl,
        name = name,
        wasm_target = wasm_target,
        **kwargs
    )

# Symbolic macro for complete verification pipeline
def complete_verification_pipeline(name, source_targets, **kwargs):
    """Symbolic macro for complete verification pipeline.
    
    This macro creates a comprehensive verification pipeline that can handle
    both Rust and WASM sources, providing end-to-end verification from
    source code to formal proofs.
    
    Args:
        name: Name of the verification pipeline
        source_targets: List of source targets (Rust or WASM) to verify
        **kwargs: Additional arguments for the pipeline
    
    The pipeline includes:
    1. Source code translation (Rust/WASM to Coq)
    2. Coq compilation and proof checking
    3. Advanced validation with multiple levels
    4. Proof automation and coverage analysis
    5. External prover integration (optional)
    6. Comprehensive reporting and visualization
    """
    native.module_extension(
        implementation = _complete_verification_pipeline_impl,
        name = name,
        source_targets = source_targets,
        **kwargs
    )

# Provider for complete verification results
CompleteVerificationInfo = provider(
    doc = "Information about complete verification pipeline results",
    fields = {
        "translation_results": "depset of translation result files",
        "validation_results": "depset of validation result files",
        "automation_results": "depset of automation result files",
        "coverage_reports": "depset of coverage report files",
        "verification_metrics": "dict of verification metrics",
        "verification_success": "boolean indicating overall success",
        "verification_time": "string indicating total verification time",
    }
)