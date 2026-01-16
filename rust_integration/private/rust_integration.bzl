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

"""Core rules_rust integration implementation - PRIVATE.

This module implements the integration between rules_rust and coq_of_rust,
following the patterns established by both rules_rust and rules_rocq_rust.
"""

load("@bazel_skylib//lib:deps.bzl", "deps")
load("//coq_of_rust/private:coq_of_rust.bzl", "CoqOfRustInfo")

# Provider for Rust to Coq integration
RustToCoqInfo = provider(
    doc = "Information about Rust to Coq translation results",
    fields = {
        "generated_sources": "depset of generated .v files",
        "rust_sources": "depset of original Rust source files",
        "transitive_deps": "depset of all transitive dependencies",
        "rust_info": "Original RustInfo provider for reference",
    }
)

# Adapter provider for cross-toolchain communication
RustCoqAdapterInfo = provider(
    doc = "Adapter provider for communication between rules_rust and coq_of_rust toolchains",
    fields = {
        "rust_crate_info": "CrateInfo from rules_rust",
        "coq_of_rust_info": "CoqOfRustInfo for translation results",
        "compatibility_checked": "bool indicating if toolchain compatibility was verified",
    }
)

def _rust_to_coq_library_impl(ctx):
    """Translate rules_rust libraries to Coq using coq-of-rust.
    
    This rule accepts rules_rust targets as input and handles the translation
    to Coq, including proper dependency management and provider conversion.
    
    Follows rules_rust and rules_rocq_rust patterns:
    - Use depsets for transitive dependencies
    - Explicit inputs/outputs for hermetic builds
    - ctx.actions.args() for command-line construction
    - Proper error handling and validation
    """
    
    # Check if rules_rust is available
    try:
        # Try to load rules_rust providers
        native.load("@rules_rust//rust/private:providers.bzl", "CrateInfo")
        rules_rust_available = True
    except:
        rules_rust_available = False
        print("Warning: rules_rust not available. rust_to_coq_library will have limited functionality.")
    
    # Get Rust dependencies
    rust_deps = ctx.attr.rust_deps
    if not rust_deps:
        fail("rust_to_coq_library requires at least one rules_rust dependency")
    
    # Collect Rust source files and information
    rust_sources = depset()
    rust_crate_infos = []
    
    for dep in rust_deps:
        if rules_rust_available and hasattr(dep, "CrateInfo"):
            # This is a rules_rust target
            crate_info = dep.CrateInfo
            
            # Validate the crate info
            if not hasattr(crate_info, "srcs") or not crate_info.srcs:
                fail("rules_rust dependency {} has no source files".format(dep.label))
            
            if not hasattr(crate_info, "name") or not crate_info.name:
                fail("rules_rust dependency {} has no crate name".format(dep.label))
            
            if not hasattr(crate_info, "type") or not crate_info.type:
                fail("rules_rust dependency {} has no crate type".format(dep.label))
            
            # Check if this is a valid crate type for translation
            valid_crate_types = ["lib", "rlib", "dylib", "proc-macro"]
            if crate_info.type not in valid_crate_types:
                fail("rules_rust dependency {} has unsupported crate type '{}' for coq-of-rust translation. Valid types are: {}".format(
                    dep.label, crate_info.type, ", ".join(valid_crate_types)
                ))
            
            rust_sources = depset.union(rust_sources, crate_info.srcs)
            rust_crate_infos.append(crate_info)
            
        elif hasattr(dep, "rust"):
            # This might be a legacy rust target or other rust-like target
            if not hasattr(dep.rust, "srcs") or not dep.rust.srcs:
                fail("Legacy rust dependency {} has no source files".format(dep.label))
            rust_sources = depset.union(rust_sources, dep.rust.srcs)
        else:
            fail("Dependency {} is not a valid rules_rust target. It must provide either CrateInfo (rules_rust) or rust provider (legacy)".format(dep.label))
    
    # Validate we have Rust sources
    if not rust_sources:
        fail("No Rust sources found in dependencies. Make sure you're passing valid rules_rust targets.")
    
    # Check for potential cross-toolchain dependency issues
    if rust_crate_infos:
        for crate_info in rust_crate_infos:
            # Check for proc-macro dependencies that might not translate well
            if hasattr(crate_info, "proc_macro_deps") and crate_info.proc_macro_deps:
                print("Warning: Crate {} has proc-macro dependencies. These may not translate correctly to Coq.".format(
                    crate_info.name if hasattr(crate_info, "name") else dep.label.name
                ))
            
            # Check for no_std crates
            if hasattr(crate_info, "cfgs") and crate_info.cfgs:
                if "no_std" in crate_info.cfgs or "no-core" in crate_info.cfgs:
                    print("Warning: Crate {} appears to be no_std. Some standard library features may not be available in Coq.".format(
                        crate_info.name if hasattr(crate_info, "name") else dep.label.name
                    ))
    
    # Validate Rust sources have .rs extension
    for rust_src in rust_sources.to_list():
        if not rust_src.path.endswith(".rs"):
            fail("Invalid Rust source file: {}. Only .rs files are supported.".format(rust_src.path))
    
    # Get coq-of-rust tool
    coq_of_rust_binary = ctx.executable._coq_of_rust_binary
    if not coq_of_rust_binary:
        fail("coq-of-rust binary not found. Ensure coq-of-rust toolchain is properly set up.")
    
    # Validate coq-of-rust binary is executable
    if not coq_of_rust_binary.executable:
        fail("coq-of-rust binary is not executable: {}".format(coq_of_rust_binary.path))
    
    # Enhanced toolchain validation and compatibility checks
    if rust_crate_infos and rules_rust_available:
        # Comprehensive toolchain compatibility validation
        try:
            first_crate = rust_crate_infos[0]
            
            # 1. Rust edition compatibility check
            if hasattr(first_crate, "edition"):
                rust_edition = first_crate.edition
                print("Info: Translating Rust {} code to Coq".format(rust_edition))
                
                # Check if coq-of-rust supports the Rust edition
                supported_editions = ["2015", "2018", "2021", "2024"]
                if rust_edition not in supported_editions:
                    print("Warning: Rust edition {} may not be fully supported by coq-of-rust. Supported editions: {}".format(
                        rust_edition, ", ".join(supported_editions)
                    ))
            
            # 2. Crate type compatibility check
            if hasattr(first_crate, "type"):
                crate_type = first_crate.type
                compatible_types = ["lib", "rlib", "dylib"]
                if crate_type not in compatible_types:
                    print("Warning: Crate type '{}' may have limited coq-of-rust support. Recommended types: {}".format(
                        crate_type, ", ".join(compatible_types)
                    ))
            
            # 3. Toolchain feature compatibility check
            if hasattr(first_crate, "cfgs") and first_crate.cfgs:
                unsupported_features = []
                for cfg in first_crate.cfgs:
                    # Check for features that might not translate well
                    if cfg.startswith("unstable_") or cfg.startswith("nightly_"):
                        unsupported_features.append(cfg)
                
                if unsupported_features:
                    print("Warning: Crate uses potentially unsupported features: {}".format(", ".join(unsupported_features)))
            
            # 4. Check for external dependencies that might not translate
            if hasattr(first_crate, "transitive_noncrates") and first_crate.transitive_noncrates:
                print("Info: Crate has external (non-Rust) dependencies. These will be included in the translation context.")
            
            print("✓ Toolchain compatibility validation completed")
            
        except Exception as e:
            print("Warning: Could not complete toolchain compatibility validation: {}".format(str(e)))
            print("Translation will continue, but some compatibility issues may not be detected")
    
    # Process transitive dependencies with cross-toolchain resolution
    transitive_deps = depset()
    
    def _resolve_transitive_dependencies(crate_info, depth=0, max_depth=5):
        """Recursively resolve transitive dependencies with depth limiting."""
        
        if depth > max_depth:
            print("Warning: Maximum dependency resolution depth {} reached for {}".format(max_depth, crate_info.name if hasattr(crate_info, "name") else "unknown"))
            return depset()
        
        resolved_deps = depset()
        
        # Add direct crate dependencies
        if hasattr(crate_info, "transitive_crates"):
            for dep_crate in crate_info.transitive_crates.to_list():
                resolved_deps = depset.union(resolved_deps, depset([dep_crate]))
                # Recursively resolve dependencies of dependencies
                resolved_deps = depset.union(resolved_deps, _resolve_transitive_dependencies(dep_crate, depth + 1, max_depth))
        
        # Add data dependencies
        if hasattr(crate_info, "transitive_data"):
            resolved_deps = depset.union(resolved_deps, crate_info.transitive_data)
        
        # Add build info dependencies
        if hasattr(crate_info, "transitive_build_infos"):
            resolved_deps = depset.union(resolved_deps, crate_info.transitive_build_infos)
        
        # Add non-crate dependencies (C/C++ libraries)
        if hasattr(crate_info, "transitive_noncrates"):
            resolved_deps = depset.union(resolved_deps, crate_info.transitive_noncrates)
        
        return resolved_deps
    
    for crate_info in rust_crate_infos:
        crate_deps = _resolve_transitive_dependencies(crate_info)
        transitive_deps = depset.union(transitive_deps, crate_deps)
        
        # Add direct dependencies from this crate
        if hasattr(crate_info, "deps"):
            transitive_deps = depset.union(transitive_deps, crate_info.deps)
        
        # Add compile data
        if hasattr(crate_info, "compile_data"):
            transitive_deps = depset.union(transitive_deps, crate_info.compile_data)
    
    # Translate each Rust file to Coq
    generated_sources = depset()
    
    # Process files with performance optimization
    rust_files_to_process = rust_sources.to_list()
    total_files = len(rust_files_to_process)
    
    print("Processing {} Rust files from rules_rust dependencies".format(total_files))
    
    for i, rust_src in enumerate(rust_files_to_process):
        output_filename = rust_src.basename + ".v"
        output_file = ctx.actions.declare_file(output_filename)
        
        # Build arguments for coq-of-rust
        args = ctx.actions.args()
        args.add("translate")
        args.add(rust_src.path)
        args.add("--output")
        args.add(output_file.path)
        
        # Add edition from crate info if available
        edition = "2021"  # default
        if rust_crate_infos and hasattr(rust_crate_infos[0], "edition"):
            edition = rust_crate_infos[0].edition
        args.add("--edition")
        args.add(edition)
        
        # Add include paths if specified
        if ctx.attr.include_path:
            args.add("--include-path")
            args.add(ctx.attr.include_path)
        
        # Use ctx.actions.run for hermetic execution
        ctx.actions.run(
            inputs = depset([rust_src]) + transitive_deps,
            outputs = [output_file],
            executable = coq_of_rust_binary,
            arguments = args,
            progress_message = "Translating {} to Coq".format(rust_src.basename),
        )
        
        # Validate the generated Coq file
        _validate_generated_coq_file(ctx, output_file, rust_src)
        
        generated_sources = depset.union(generated_sources, depset([output_file]))
        
        # Progress reporting
        if (i + 1) % 5 == 0 or (i + 1) == total_files:
            progress_percent = min(100, int((i + 1) * 100 / total_files))
            print("Progress: {}% ({}/{}) files processed".format(progress_percent, i + 1, total_files))
    
    # Create adapter info for cross-toolchain communication with validation
    adapter_info = None
    if rules_rust_available and rust_crate_infos:
        try:
            # Validate that we can create the adapter
            first_crate = rust_crate_infos[0]
            
            # Check if the crate has required fields for the adapter
            required_fields = ["name", "type", "srcs", "output"]
            missing_fields = []
            for field in required_fields:
                if not hasattr(first_crate, field):
                    missing_fields.append(field)
            
            if missing_fields:
                print("Warning: Crate {} is missing required fields for adapter: {}".format(
                    first_crate.name if hasattr(first_crate, "name") else "unknown", 
                    ", ".join(missing_fields)
                ))
                print("Adapter creation will be skipped, but translation will continue")
            else:
                adapter_info = RustCoqAdapterInfo(
                    rust_crate_info = first_crate,
                    coq_of_rust_info = CoqOfRustInfo(
                        generated_sources = generated_sources,
                        rust_sources = rust_sources,
                        transitive_deps = transitive_deps + generated_sources,
                    ),
                    compatibility_checked = True,
                )
                print("✓ Successfully created cross-toolchain adapter for {}".format(first_crate.name))
                
        except Exception as e:
            print("Warning: Could not create cross-toolchain adapter: {}".format(str(e)))
            print("Translation will continue without adapter, but some features may be limited")
    
    # Return providers following rules_rust and rules_rocq_rust patterns
    providers = [
        DefaultInfo(
            files = generated_sources,
            data_runfiles = ctx.runfiles(files = generated_sources),
        ),
        RustToCoqInfo(
            generated_sources = generated_sources,
            rust_sources = rust_sources,
            transitive_deps = transitive_deps + generated_sources,
            rust_info = rust_crate_infos[0] if rust_crate_infos else None,
        ),
    ]
    
    if adapter_info:
        providers.append(adapter_info)
    
    return providers

def _validate_generated_coq_file(ctx, coq_file, rust_src):
    """Validate the generated Coq file."""
    
    # Check that the file was created
    if not coq_file.exists:
        fail("coq-of-rust failed to generate output file for {}".format(rust_src.path))
    
    # Check that the file is not empty
    if coq_file.size == 0:
        fail("Generated Coq file is empty for {}".format(rust_src.path))
    
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

# rust_to_coq_library rule definition
rust_to_coq_library = rule(
    implementation = _rust_to_coq_library_impl,
    attrs = {
        "rust_deps": attr.label_list(
            doc = "Dependencies on rules_rust libraries to translate",
        ),
        "include_path": attr.string(
            doc = "Additional include path for coq-of-rust",
            default = "",
        ),
        "edition": attr.string(
            doc = "Rust edition to use (overrides crate edition)",
            default = "",
        ),
    },
    toolchains = [
        "@rules_rocq_rust//coq_of_rust:coq_of_rust_toolchain_type",
    ],
    doc = "Translates rules_rust libraries to Coq using coq-of-rust for formal verification",
)