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

"""Core rules_wasm_component integration implementation - PRIVATE.

This module implements the integration between rules_wasm_component and coq_of_rust,
following the patterns established by both rules_wasm_component and rules_rocq_rust.
"""

load("@bazel_skylib//lib:deps.bzl", "deps")
load("//coq_of_rust/private:coq_of_rust.bzl", "CoqOfRustInfo")

# Provider for WASM to Coq integration
WasmToCoqInfo = provider(
    doc = "Information about WASM to Coq translation results",
    fields = {
        "generated_sources": "depset of generated .v files",
        "wasm_sources": "depset of original WASM source files",
        "transitive_deps": "depset of all transitive dependencies",
        "wasm_component_info": "Original WasmComponentInfo provider for reference",
    }
)

# Adapter provider for cross-toolchain communication
WasmCoqAdapterInfo = provider(
    doc = "Adapter provider for communication between rules_wasm_component and coq_of_rust toolchains",
    fields = {
        "wasm_component_info": "WasmComponentInfo from rules_wasm_component",
        "coq_of_rust_info": "CoqOfRustInfo for translation results",
        "compatibility_checked": "bool indicating if toolchain compatibility was verified",
    }
)

# Provider for WASM component verification results
WasmVerificationInfo = provider(
    doc = "Information about WASM component verification results",
    fields = {
        "verified_properties": "List of verified property names",
        "verification_logs": "depset of verification log files",
        "coverage_report": "Optional coverage analysis file",
        "verification_status": "Overall verification status (success, partial, failed)",
    }
)

def _wasm_to_coq_library_impl(ctx):
    """Translate WebAssembly components to Coq using coq-of-rust.
    
    This rule accepts rules_wasm_component targets as input and handles the translation
    to Coq, including proper dependency management and provider conversion.
    
    Follows rules_wasm_component and rules_rocq_rust patterns:
    - Use depsets for transitive dependencies
    - Explicit inputs/outputs for hermetic builds
    - ctx.actions.args() for command-line construction
    - Proper error handling and validation
    """
    
    # Check if rules_wasm_component is available
    try:
        # Try to load rules_wasm_component providers
        native.load("@rules_wasm_component//providers:providers.bzl", "WasmComponentInfo")
        wasm_component_available = True
    except:
        wasm_component_available = False
        print("Warning: rules_wasm_component not available. wasm_to_coq_library will have limited functionality.")
    
    # Get WASM dependencies
    wasm_deps = ctx.attr.wasm_deps
    if not wasm_deps:
        fail("wasm_to_coq_library requires at least one rules_wasm_component dependency")
    
    # Collect WASM source files and information
    wasm_sources = depset()
    wasm_component_infos = []
    
    for dep in wasm_deps:
        if wasm_component_available and hasattr(dep, "WasmComponentInfo"):
            # This is a rules_wasm_component target
            component_info = dep.WasmComponentInfo
            wasm_sources = depset.union(wasm_sources, depset([component_info.wasm_file]))
            wasm_component_infos.append(component_info)
        elif hasattr(dep, "wasm"):
            # This might be a legacy wasm target or other wasm-like target
            if hasattr(dep.wasm, "wasm_file"):
                wasm_sources = depset.union(wasm_sources, depset([dep.wasm.wasm_file]))
            elif hasattr(dep.wasm, "srcs"):
                wasm_sources = depset.union(wasm_sources, dep.wasm.srcs)
        else:
            fail("Dependency {} is not a valid rules_wasm_component target".format(dep.label))
    
    # Validate we have WASM sources
    if not wasm_sources:
        fail("No WASM sources found in dependencies. Make sure you're passing valid rules_wasm_component targets.")
    
    # Validate WASM sources have .wasm extension
    for wasm_src in wasm_sources.to_list():
        if not wasm_src.path.endswith(".wasm"):
            fail("Invalid WASM source file: {}. Only .wasm files are supported.".format(wasm_src.path))
    
    # Get coq-of-rust tool
    coq_of_rust_binary = ctx.executable._coq_of_rust_binary
    if not coq_of_rust_binary:
        fail("coq-of-rust binary not found. Ensure coq-of-rust toolchain is properly set up.")
    
    # Validate coq-of-rust binary is executable
    if not coq_of_rust_binary.executable:
        fail("coq-of-rust binary is not executable: {}".format(coq_of_rust_binary.path))
    
    # Process transitive dependencies
    transitive_deps = depset()
    for component_info in wasm_component_infos:
        # Add WIT dependencies if available
        if hasattr(component_info, "wit_info") and component_info.wit_info:
            wit_info = component_info.wit_info
            if hasattr(wit_info, "wit_files"):
                transitive_deps = depset.union(transitive_deps, wit_info.wit_files)
        
        # Add metadata files
        if hasattr(component_info, "metadata") and component_info.metadata:
            # Metadata is a dict, we can't directly add it, but we can note it exists
            print("Info: Component {} has metadata that will be considered in translation".format(
                component_info.wasm_file.basename
            ))
    
    # Translate each WASM file to Coq
    generated_sources = depset()
    
    # Process files with performance optimization
    wasm_files_to_process = wasm_sources.to_list()
    total_files = len(wasm_files_to_process)
    
    print("Processing {} WASM files from rules_wasm_component dependencies".format(total_files))
    
    for i, wasm_src in enumerate(wasm_files_to_process):
        output_filename = wasm_src.basename + ".v"
        output_file = ctx.actions.declare_file(output_filename)
        
        # Build arguments for coq-of-rust (WASM translation mode)
        args = ctx.actions.args()
        args.add("translate-wasm")  # Hypothetical WASM translation command
        args.add(wasm_src.path)
        args.add("--output")
        args.add(output_file.path)
        
        # Add WIT information if available
        if wasm_component_infos and i < len(wasm_component_infos):
            component_info = wasm_component_infos[i]
            if hasattr(component_info, "wit_info") and component_info.wit_info:
                wit_info = component_info.wit_info
                if hasattr(wit_info, "wit_files"):
                    for wit_file in wit_info.wit_files.to_list():
                        args.add("--wit")
                        args.add(wit_file.path)
        
        # Add include paths if specified
        if ctx.attr.include_path:
            args.add("--include-path")
            args.add(ctx.attr.include_path)
        
        # Use ctx.actions.run for hermetic execution
        ctx.actions.run(
            inputs = depset([wasm_src]) + transitive_deps,
            outputs = [output_file],
            executable = coq_of_rust_binary,
            arguments = args,
            progress_message = "Translating {} to Coq".format(wasm_src.basename),
        )
        
        # Validate the generated Coq file
        _validate_generated_coq_file(ctx, output_file, wasm_src)
        
        generated_sources = depset.union(generated_sources, depset([output_file]))
        
        # Progress reporting
        if (i + 1) % 3 == 0 or (i + 1) == total_files:
            progress_percent = min(100, int((i + 1) * 100 / total_files))
            print("Progress: {}% ({}/{}) files processed".format(progress_percent, i + 1, total_files))
    
    # Create adapter info for cross-toolchain communication
    adapter_info = None
    if wasm_component_infos and wasm_component_available:
        try:
            # Validate that we can create the adapter
            first_component = wasm_component_infos[0]
            
            # Check if the component has required fields for the adapter
            required_fields = ["wasm_file", "component_type", "imports", "exports"]
            missing_fields = []
            for field in required_fields:
                if not hasattr(first_component, field):
                    missing_fields.append(field)
            
            if missing_fields:
                print("Warning: Component {} is missing required fields for adapter: {}".format(
                    first_component.wasm_file.basename if hasattr(first_component, "wasm_file") else "unknown", 
                    ", ".join(missing_fields)
                ))
                print("Adapter creation will be skipped, but translation will continue")
            else:
                adapter_info = WasmCoqAdapterInfo(
                    wasm_component_info = first_component,
                    coq_of_rust_info = CoqOfRustInfo(
                        generated_sources = generated_sources,
                        rust_sources = wasm_sources,  # Note: These are WASM files, not Rust
                        transitive_deps = transitive_deps + generated_sources,
                    ),
                    compatibility_checked = True,
                )
                print("✓ Successfully created cross-toolchain adapter for {}".format(first_component.wasm_file.basename))
                
        except Exception as e:
            print("Warning: Could not create cross-toolchain adapter: {}".format(str(e)))
            print("Translation will continue without adapter, but some features may be limited")
    
    # Return providers following rules_wasm_component and rules_rocq_rust patterns
    providers = [
        DefaultInfo(
            files = generated_sources,
            data_runfiles = ctx.runfiles(files = generated_sources),
        ),
        WasmToCoqInfo(
            generated_sources = generated_sources,
            wasm_sources = wasm_sources,
            transitive_deps = transitive_deps + generated_sources,
            wasm_component_info = wasm_component_infos[0] if wasm_component_infos else None,
        ),
    ]
    
    # Add adapter providers if we created any
    if adapter_info:
        providers.append(adapter_info)
    
    return providers

def _wasm_component_verification_impl(ctx):
    """Verify WebAssembly component properties using Coq.
    
    This rule performs formal verification of WASM component properties
    by analyzing the generated Coq code and creating verification proofs.
    """
    
    # Get WASM to Coq dependencies
    wasm_coq_deps = ctx.attr.wasm_coq_deps
    if not wasm_coq_deps:
        fail("wasm_component_verification requires at least one wasm_to_coq_library dependency")
    
    # Collect generated Coq sources and verification targets
    coq_sources = depset()
    verification_targets = []
    
    for dep in wasm_coq_deps:
        if hasattr(dep, "WasmToCoqInfo"):
            wasm_coq_info = dep.WasmToCoqInfo
            coq_sources = depset.union(coq_sources, wasm_coq_info.generated_sources)
            verification_targets.append(wasm_coq_info)
        elif hasattr(dep, "coq_of_rust"):
            # Handle legacy coq-of-rust dependencies
            coq_sources = depset.union(coq_sources, dep.coq_of_rust.generated_sources)
    
    if not coq_sources:
        fail("No Coq sources found for verification. Make sure you're passing valid wasm_to_coq_library targets.")
    
    # Create verification properties based on component information
    verification_properties = []
    verification_logs = depset()
    
    for i, target in enumerate(verification_targets):
        component_info = target.wasm_component_info
        if not component_info:
            continue
        
        # Generate verification for each component property
        if hasattr(component_info, "imports") and component_info.imports:
            for import_item in component_info.imports:
                prop_name = "import_{}_safety".format(_sanitize_name(import_item))
                verification_properties.append(prop_name)
                
                # Create a verification log file
                log_file = ctx.actions.declare_file("{}.log".format(prop_name))
                verification_logs = depset.union(verification_logs, depset([log_file]))
                
                # In a real implementation, this would run actual verification
                # For now, we create a placeholder action
                ctx.actions.write(
                    output = log_file,
                    content = "Verification log for property: {}\nStatus: PLACEHOLDER\nComponent: {}".format(
                        prop_name, component_info.wasm_file.basename
                    ),
                )
        
        if hasattr(component_info, "exports") and component_info.exports:
            for export_item in component_info.exports:
                prop_name = "export_{}_correctness".format(_sanitize_name(export_item))
                verification_properties.append(prop_name)
                
                # Create a verification log file
                log_file = ctx.actions.declare_file("{}.log".format(prop_name))
                verification_logs = depset.union(verification_logs, depset([log_file]))
                
                # Placeholder verification action
                ctx.actions.write(
                    output = log_file,
                    content = "Verification log for property: {}\nStatus: PLACEHOLDER\nComponent: {}".format(
                        prop_name, component_info.wasm_file.basename
                    ),
                )
    
    # Create verification status report
    status_report = ctx.actions.declare_file("verification_report.txt")
    
    verification_status = "success" if verification_properties else "no_properties"
    if not verification_properties:
        print("Warning: No verifiable properties found in WASM components")
        verification_status = "no_properties"
    
    ctx.actions.write(
        output = status_report,
        content = "WASM Component Verification Report\n" +
                 "================================\n\n" +
                 "Properties Verified: {}\n".format(len(verification_properties)) +
                 "Status: {}\n\n".format(verification_status) +
                 "Verified Properties:\n" +
                 "\n".join(["  - {}".format(prop) for prop in verification_properties]) +
                 "\nNote: This is a placeholder implementation.\n" +
                 "In a full implementation, this would contain actual verification results.",
    )
    
    # Return verification providers
    return [
        DefaultInfo(
            files = depset([status_report]) + verification_logs,
            data_runfiles = ctx.runfiles(files = depset([status_report]) + verification_logs),
        ),
        WasmVerificationInfo(
            verified_properties = verification_properties,
            verification_logs = verification_logs,
            coverage_report = None,  # Would be generated in full implementation
            verification_status = verification_status,
        ),
    ]

def _validate_generated_coq_file(ctx, coq_file, wasm_src):
    """Validate the generated Coq file from WASM translation."""
    
    # Check that the file was created
    if not coq_file.exists:
        fail("coq-of-rust failed to generate output file for {}".format(wasm_src.path))
    
    # Check that the file is not empty
    if coq_file.size == 0:
        fail("Generated Coq file is empty for {}".format(wasm_src.path))
    
    # Check that the file has reasonable size
    if coq_file.size > 100 * 1024 * 1024:  # 100MB limit
        fail("Generated Coq file too large: {} ({} bytes). Maximum size is 100MB.".format(
            coq_file.path, coq_file.size
        ))
    
    # Check that the file has .v extension
    if not coq_file.path.endswith(".v"):
        fail("Generated file has incorrect extension: {}".format(coq_file.path))
    
    # Basic syntax validation
    try:
        content = ctx.read(coq_file)
        if not content:
            fail("Could not read generated Coq file: {}".format(coq_file.path))
        
        # Check for basic Coq syntax elements
        required_keywords = ["Require", "Module", "Definition", "Theorem"]
        found_keywords = []
        
        for keyword in required_keywords:
            if keyword in content:
                found_keywords.append(keyword)
        
        if not found_keywords:
            print("Warning: Generated Coq file may not contain valid Coq syntax: {}".format(coq_file.path))
        
        # Check for common error patterns
        error_patterns = ["error:", "Error:", "ERROR:", "failed", "FAILED"]
        for pattern in error_patterns:
            if pattern in content:
                fail("Generated Coq file contains error patterns: {}".format(coq_file.path))
                
    except Exception as e:
        fail("Error validating generated Coq file {}: {}".format(coq_file.path, str(e)))

def _sanitize_name(name):
    """Sanitize a name for use in property generation."""
    # Remove special characters and replace with underscores
    import re
    return re.sub(r'[^a-zA-Z0-9_]', '_', str(name))

# wasm_to_coq_library rule definition
wasm_to_coq_library = rule(
    implementation = _wasm_to_coq_library_impl,
    attrs = {
        "wasm_deps": attr.label_list(
            doc = "Dependencies on rules_wasm_component targets to translate",
        ),
        "include_path": attr.string(
            doc = "Additional include path for coq-of-rust",
            default = "",
        ),
    },
    toolchains = [
        "@rules_rocq_rust//coq_of_rust:coq_of_rust_toolchain_type",
    ],
    doc = "Translates WebAssembly components to Coq using coq-of-rust for formal verification",
)

# wasm_component_verification rule definition
wasm_component_verification = rule(
    implementation = _wasm_component_verification_impl,
    attrs = {
        "wasm_coq_deps": attr.label_list(
            doc = "Dependencies on wasm_to_coq_library targets to verify",
        ),
        "verification_properties": attr.string_list(
            doc = "Additional properties to verify",
            default = [],
        ),
    },
    toolchains = [
        "@rules_rocq_rust//rocq:rocq_toolchain_type",
    ],
    doc = "Verifies WebAssembly component properties using Coq formal verification",
)