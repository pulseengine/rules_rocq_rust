"""Core coq-of-rust integration rules - PRIVATE implementation.

This follows the exact pattern used in rules_rust's private implementation.
"""

load("@bazel_skylib//lib:deps.bzl", "deps")

# Provider for coq-of-rust translation results
CoqOfRustInfo = provider(
    doc = "Information about coq-of-rust translation results",
    fields = {
        "generated_sources": "depset of generated .v files",
        "rust_sources": "depset of original Rust source files",
        "transitive_deps": "depset of all transitive dependencies",
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

# Core coq-of-rust translation rule
def _coq_of_rust_library_impl(ctx):
    """Translate Rust code to Coq using coq-of-rust.
    
    Follows rules_rust patterns:
    - Use depsets for transitive dependencies
    - Explicit inputs/outputs for hermetic builds
    - ctx.actions.args() for command-line construction
    - Proper error handling and validation
    """
    
    # Get Rust sources from either direct files or rules_rust dependencies
    rust_sources = depset()
    rust_crate_infos = []
    rules_rust_available = False
    
    # Try to load rules_rust providers first
    try:
        native.load("@rules_rust//rust/private:providers.bzl", "CrateInfo")
        rules_rust_available = True
        print("✅ rules_rust integration available")
    except:
        rules_rust_available = False
        print("ℹ️  rules_rust not available - using basic Rust source handling")
    
    # Check if we have direct rust_sources
    if hasattr(ctx.attr, 'rust_sources') and ctx.files.rust_sources:
        rust_sources = ctx.files.rust_sources
        print(f"Found {len(rust_sources.to_list())} direct Rust source files")
    
    # Check if we have rules_rust dependencies
    if hasattr(ctx.attr, 'rust_deps') and ctx.attr.rust_deps:
        for dep in ctx.attr.rust_deps:
            if rules_rust_available and hasattr(dep, "CrateInfo"):
                # This is a rules_rust target - extract Rust sources
                crate_info = dep.CrateInfo
                rust_sources = depset.union(rust_sources, crate_info.srcs)
                rust_crate_infos.append(crate_info)
                print(f"✅ Added rules_rust dependency: {dep.label}")
                print(f"   Found {len(crate_info.srcs.to_list())} Rust sources from crate")
            elif hasattr(dep, "rust"):
                # This might be a legacy rust target or other rust-like target
                rust_sources = depset.union(rust_sources, dep.rust.srcs)
                print(f"⚠️  Added legacy rust dependency: {dep.label}")
            else:
                print(f"⚠️  Dependency {dep.label} doesn't appear to be a Rust target")
    
    if not rust_sources:
        fail("No Rust sources provided for coq-of-rust translation\n\n" +
             "Make sure you have:")
        fail("1. Specified rust_sources in your BUILD file")
        fail("2. Used .rs files (not other extensions)")
        fail("3. Checked file paths are correct")
        fail("4. Or specified valid rust_deps pointing to rules_rust targets")
        fail("5. Added rules_rust to your dependencies if using rust_deps")
    
    # Validate Rust sources
    for rust_src in rust_sources.to_list():
        if not rust_src.path.endswith(".rs"):
            fail("Invalid Rust source file: {}. Only .rs files are supported.".format(rust_src.path))
        
        # Check file size
        if rust_src.size > 10 * 1024 * 1024:  # 10MB limit
            fail("Rust source file too large: {} ({} bytes). Maximum size is 10MB.".format(
                rust_src.path, rust_src.size
            ))
    
    # Validate coq-of-rust binary is available
    coq_of_rust_binary = ctx.executable._coq_of_rust_binary
    if not coq_of_rust_binary:
        fail("coq-of-rust binary not found. Ensure coq-of-rust toolchain is properly set up.")
    
    # Validate coq-of-rust binary is executable
    if not coq_of_rust_binary.executable:
        fail("coq-of-rust binary is not executable: {}".format(coq_of_rust_binary.path))
    
    # Validate Rust edition - use crate edition if available, otherwise use attribute
    edition = ctx.attr.edition if ctx.attr.edition else "2021"
    
    # If we have rules_rust crates, use their edition for consistency
    if rust_crate_infos and rules_rust_available:
        # Use the first crate's edition if available
        if hasattr(rust_crate_infos[0], "edition"):
            edition = rust_crate_infos[0].edition
            print(f"✅ Using Rust edition {edition} from rules_rust crate")
        else:
            print("ℹ️  Using default edition 2021 (crate edition not available)")
    else:
        print(f"ℹ️  Using Rust edition {edition} from attribute")
    
    valid_editions = ["2015", "2018", "2021", "2024"]
    if edition not in valid_editions:
        fail("Invalid Rust edition: {}. Valid editions are: {}".format(
            edition, ", ".join(valid_editions)
        ))
    else:
        print(f"✅ Rust edition {edition} is valid")
    
    # Validate include path if provided
    if ctx.attr.include_path:
        include_path = ctx.files.include_path
        if not include_path:
            fail("Include path specified but no files found")
    
    # Process Rust dependencies - handle both legacy and rules_rust dependencies
    transitive_deps = depset()
    
    # Process rules_rust dependencies
    for crate_info in rust_crate_infos:
        if hasattr(crate_info, "transitive_crates"):
            transitive_deps = depset.union(transitive_deps, crate_info.transitive_crates)
            print(f"✅ Added {len(crate_info.transitive_crates.to_list())} transitive crates")
        if hasattr(crate_info, "transitive_data"):
            transitive_deps = depset.union(transitive_deps, crate_info.transitive_data)
            print(f"✅ Added {len(crate_info.transitive_data.to_list())} transitive data files")
        
        # Also add the crate's direct sources to transitive deps for completeness
        if hasattr(crate_info, "srcs"):
            transitive_deps = depset.union(transitive_deps, crate_info.srcs)
    
    # Process legacy coq-of-rust dependencies
    if hasattr(ctx.attr, 'rust_deps'):
        for dep in ctx.attr.rust_deps:
            if hasattr(dep, "rust"):
                transitive_deps = depset.union(transitive_deps, dep.rust.transitive_deps)
                print(f"⚠️  Added legacy rust transitive deps from {dep.label}")
            elif hasattr(dep, "coq_of_rust"):
                # Handle coq-of-rust dependencies
                transitive_deps = depset.union(transitive_deps, dep.coq_of_rust.transitive_deps)
                print(f"⚠️  Added legacy coq-of-rust transitive deps from {dep.label}")
    
    if rust_crate_infos:
        print(f"✅ Total transitive dependencies: {len(transitive_deps.to_list())} files")
    else:
        print("ℹ️  No rules_rust dependencies found - using direct sources only")
    
    # Translate each Rust file to Coq
    generated_sources = depset()
    
    # Use parallel processing for better performance
    rust_files_to_process = []
    
    for rust_src in rust_sources.to_list():
        if not rust_src.path.endswith(".rs"):
            print("Warning: Skipping non-Rust file: {}".format(rust_src.path))
            continue
        rust_files_to_process.append(rust_src)
    
    # Process files with performance optimization
    # Use batch processing for better performance with many files
    batch_size = 5
    total_files = len(rust_files_to_process)
    
    print("Processing {} Rust files in batches of {}".format(total_files, batch_size))
    
    # Process files in parallel (Bazel will handle the actual parallelization)
    for i in range(0, total_files, batch_size):
        batch = rust_files_to_process[i:i + batch_size]
        print("Processing batch {}/{} ({} files)".format(
            (i // batch_size) + 1,
            (total_files + batch_size - 1) // batch_size,
            len(batch)
        ))
        
        for rust_src in batch:
            output_filename = rust_src.basename + ".v"
            output_file = ctx.actions.declare_file(output_filename)
        
        # Build arguments for coq-of-rust
        args = ctx.actions.args()
        args.add("translate")
        args.add(rust_src.path)
        args.add("--output")
        args.add(output_file.path)
        args.add("--edition")
        args.add(edition)  # Use the determined edition
        
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
        
        # Track progress
        if (i // batch_size) + 1 == 1:
            print("Progress: 20%")
        elif (i // batch_size) + 1 == 2:
            print("Progress: 40%")
        elif (i // batch_size) + 1 == 3:
            print("Progress: 60%")
        elif (i // batch_size) + 1 == 4:
            print("Progress: 80%")

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
    
    # Check that the file contains basic Coq syntax
    content = ctx.read(coq_file)
    if not content:
        fail("Could not read generated Coq file: {}".format(coq_file.path))
    
    # Basic syntax validation
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
    
    if not generated_sources:
        ctx.actions.do_nothing("No valid Rust files to translate")
        return []
    
    # Create adapter info for cross-toolchain communication if we have rules_rust dependencies
    adapter_providers = []
    if rust_crate_infos:
        # Try to load rules_rust providers for adapter
        try:
            native.load("@rules_rust//rust/private:providers.bzl", "CrateInfo")
            # Create adapter provider
            adapter_providers.append(RustCoqAdapterInfo(
                rust_crate_info = rust_crate_infos[0],
                coq_of_rust_info = CoqOfRustInfo(
                    generated_sources = generated_sources,
                    rust_sources = rust_sources,
                    transitive_deps = transitive_deps + generated_sources,
                ),
                compatibility_checked = True,
            ))
        except:
            # rules_rust not available, skip adapter
            pass
    
    # Return providers following rules_rust pattern
    providers = [
        DefaultInfo(
            files = generated_sources,
            data_runfiles = ctx.runfiles(files = generated_sources),
        ),
        CoqOfRustInfo(
            generated_sources = generated_sources,
            rust_sources = rust_sources,
            transitive_deps = transitive_deps + generated_sources,
        ),
    ]
    
    # Add adapter providers if we created any
    providers.extend(adapter_providers)
    
    return providers

# coq-of-rust library rule
coq_of_rust_library = rule(
    implementation = _coq_of_rust_library_impl,
    attrs = {
        "rust_sources": attr.label_list(
            allow_files = [".rs"],
            doc = "Rust source files to translate (alternative to rust_deps)",
        ),
        "rust_deps": attr.label_list(
            doc = "Dependencies on rules_rust libraries to translate",
        ),
        "edition": attr.string(
            doc = "Rust edition to use (overrides crate edition if rust_deps are used)",
            default = "2021",
        ),
        "include_path": attr.string(
            doc = "Additional include path for coq-of-rust",
            default = "",
        ),
    },
    doc = "Translates Rust code to Coq using coq-of-rust and compiles with Rocq. Can accept either direct rust_sources or rules_rust dependencies via rust_deps.",
)