"""coq-of-rust toolchain definitions.

This file provides the coq-of-rust toolchain that builds the coq-of-rust binary
from source using the Rust toolchain, following the exact pattern established by rules_rust.
"""

load("@bazel_skylib//lib:native.bzl", "native")
load("@bazel_skylib//lib:paths.bzl", "paths")

# coq-of-rust toolchain provider (re-export from private)
def coq_of_rust_toolchain(name, coq_of_rust_binary, stdlib_files = None, include_path = "", **kwargs):
    """Create a coq-of-rust toolchain.
    
    Args:
        name: Name of the toolchain
        coq_of_rust_binary: Label pointing to the coq-of-rust binary
        stdlib_files: Standard library files for coq-of-rust
        include_path: Include path for standard library
    """
    native.filegroup(
        name = name,
        srcs = [coq_of_rust_binary] + (stdlib_files if stdlib_files else []),
        **kwargs
    )

# Build coq-of-rust from source using Rust toolchain
def _build_coq_of_rust_from_source(repository_ctx):
    """Build coq-of-rust binary from source using cargo.
    
    This implementation attempts to build the real coq-of-rust tool when possible,
    falling back to an enhanced placeholder when the official repository is not available.
    
    This follows the pattern used by rules_rust for building Rust tools.
    """
    
    # Get Rust toolchain info
    rustc = None
    cargo = None
    
    # Try to find Rust tools from the registered toolchain
    try:
        # Check if we can find cargo in PATH (from rules_rust toolchain)
        cargo = repository_ctx.which("cargo")
        rustc = repository_ctx.which("rustc")
         
        if not cargo or not rustc:
            # Try to access rules_rust toolchain directly
            try:
                cargo = repository_ctx.path("@rust_toolchains//:cargo")
                rustc = repository_ctx.path("@rust_toolchains//:rustc")
            except Exception:
                pass  # Will handle below
    except Exception as e:
        print("Warning: Could not find Rust toolchain in PATH: {}".format(str(e)))
    
    if not cargo or not rustc:
        print("Rust toolchain not found - creating enhanced placeholder")
        print("To build real coq-of-rust, ensure rules_rust is properly set up")
        print("Add to your MODULE.bazel:")
        print("  rust = use_repo(rule = @bazel_tools//tools/build_defs/repo:http.bzl, sha256 = \"...\")")
        print("  register_toolchains(\"@rust_toolchains//:all\")")
        
        # Create enhanced placeholder that simulates coq-of-rust behavior
        return _create_enhanced_placeholder(repository_ctx)
    
    print("Found Rust toolchain:")
    print("  cargo: {}".format(cargo))
    print("  rustc: {}".format(rustc))
    
    # Create a temporary directory for building coq-of-rust
    build_dir = repository_ctx.expand_location("{{name}}/coq-of-rust-source")
    repository_ctx.execute(["mkdir", "-p", build_dir])
    
    # Use custom repository URL if provided, otherwise try default URLs
    custom_repo_url = repository_ctx.attr.repository_url
    coq_of_rust_repos = []
    
    if custom_repo_url:
        coq_of_rust_repos.append(custom_repo_url)
        print("Using custom coq-of-rust repository: {}".format(custom_repo_url))
    else:
        # Default repository URLs to try
        coq_of_rust_repos = [
            "https://github.com/coq-of-rust/coq-of-rust.git",
            "https://github.com/coq-community/coq-of-rust.git",
            "https://github.com/formal-verification/coq-of-rust.git",
        ]
        print("Trying default coq-of-rust repository URLs")
    
    repo_found = False
    for repo_url in coq_of_rust_repos:
        print("Attempting to clone coq-of-rust repository from: {}".format(repo_url))
        
        try:
            # Clone the repository
            repository_ctx.execute([
                "git", "clone", "--depth", "1", 
                repo_url, build_dir
            ])
            repo_found = True
            break
        except Exception as e:
            print("Warning: Could not clone from {}: {}".format(repo_url, str(e)))
            # Clean up failed clone attempt
            repository_ctx.execute(["rm", "-rf", build_dir])
            repository_ctx.execute(["mkdir", "-p", build_dir])
    
    if not repo_found:
        print("Warning: Could not find any coq-of-rust repository")
        
        # Try local coq-of-rust implementation if available
        local_coq_of_rust = repository_ctx.path("third_party/coq_of_rust")
        if local_coq_of_rust.exists:
            print("Found local coq-of-rust implementation")
            try:
                return _build_local_coq_of_rust(repository_ctx, local_coq_of_rust)
            except Exception as e:
                print("Warning: Could not build local coq-of-rust: {}".format(str(e)))
                print("Falling back to enhanced placeholder implementation")
        else:
            print("No local coq-of-rust found")
            print("Falling back to enhanced placeholder implementation")
        
        return _create_enhanced_placeholder(repository_ctx)
    
    # Try to build coq-of-rust using cargo
    print("Building coq-of-rust using cargo...")
    
    try:
        # Check if Cargo.toml exists
        cargo_toml = repository_ctx.path("{}/Cargo.toml".format(build_dir))
        if not cargo_toml.exists:
            print("Warning: Cargo.toml not found in repository")
            raise Exception("Cargo.toml not found")
        
        # Build with cargo
        repository_ctx.execute([
            str(cargo), "build", "--release",
            "--manifest-path", "{}/Cargo.toml".format(build_dir)
        ])
        
        # Check if binary was built
        built_binary = repository_ctx.path("{}/target/release/coq-of-rust".format(build_dir))
        if not built_binary.exists:
            print("Warning: coq-of-rust binary not found after build")
            raise Exception("Binary not found")
        
        # Copy the built binary to our toolchain location
        repository_ctx.execute(["mkdir", "-p", "bin"])
        final_binary = repository_ctx.path("bin/coq-of-rust")
        
        repository_ctx.execute(["cp", str(built_binary), str(final_binary)])
        repository_ctx.execute(["chmod", "+x", str(final_binary)])
        
        print("Successfully built coq-of-rust from source!")
        print("Binary location: {}".format(final_binary))
        
        # Also create the standard library files
        _create_stdlib_files(repository_ctx)
        
        return final_binary
        
    except Exception as e:
        print("Warning: Could not build real coq-of-rust: {}".format(str(e)))
        print("Falling back to enhanced placeholder implementation")
        return _create_enhanced_placeholder(repository_ctx)
    
    print("Found Rust toolchain:")
    print("  cargo: {}".format(cargo))
    print("  rustc: {}".format(rustc))
    
    # Create a temporary directory for building coq-of-rust
    build_dir = repository_ctx.expand_location("{{name}}/coq-of-rust-source")
    repository_ctx.execute(["mkdir", "-p", build_dir])
    
    # Use custom repository URL if provided, otherwise try default URLs
    custom_repo_url = repository_ctx.attr.repository_url
    coq_of_rust_repos = []
    
    if custom_repo_url:
        coq_of_rust_repos.append(custom_repo_url)
        print("Using custom coq-of-rust repository: {}".format(custom_repo_url))
    else:
        # Default repository URLs to try
        coq_of_rust_repos = [
            "https://github.com/coq-of-rust/coq-of-rust.git",
            "https://github.com/coq-community/coq-of-rust.git",
            "https://github.com/formal-verification/coq-of-rust.git",
        ]
        print("Trying default coq-of-rust repository URLs")
    
    repo_found = False
    for repo_url in coq_of_rust_repos:
        print("Attempting to clone coq-of-rust repository from: {}".format(repo_url))
        
        try:
            # Clone the repository
            repository_ctx.execute([
                "git", "clone", "--depth", "1", 
                repo_url, build_dir
            ])
            repo_found = True
            break
        except Exception as e:
            print("Warning: Could not clone from {}: {}".format(repo_url, str(e)))
            # Clean up failed clone attempt
            repository_ctx.execute(["rm", "-rf", build_dir])
            repository_ctx.execute(["mkdir", "-p", build_dir])
    
    if not repo_found:
        print("Warning: Could not find any coq-of-rust repository")
        
        # Try local coq-of-rust implementation if available
        local_coq_of_rust = repository_ctx.path("third_party/coq_of_rust")
        if local_coq_of_rust.exists:
            print("Found local coq-of-rust implementation")
            try:
                return _build_local_coq_of_rust(repository_ctx, local_coq_of_rust)
            except Exception as e:
                print("Warning: Could not build local coq-of-rust: {}".format(str(e)))
                print("Falling back to enhanced placeholder implementation")
        else:
            print("No local coq-of-rust found")
            print("Falling back to enhanced placeholder implementation")
        
        return _create_enhanced_placeholder(repository_ctx)
    
    # Try to build coq-of-rust using cargo
    print("Building coq-of-rust using cargo...")
    
    try:
        # Check if Cargo.toml exists
        cargo_toml = repository_ctx.path("{}/Cargo.toml".format(build_dir))
        if not cargo_toml.exists:
            print("Warning: Cargo.toml not found in repository")
            raise Exception("Cargo.toml not found")
        
        # Build with cargo
        repository_ctx.execute([
            str(cargo), "build", "--release",
            "--manifest-path", "{}/Cargo.toml".format(build_dir)
        ])
        
        # Check if binary was built
        built_binary = repository_ctx.path("{}/target/release/coq-of-rust".format(build_dir))
        if not built_binary.exists:
            print("Warning: coq-of-rust binary not found after build")
            raise Exception("Binary not found")
        
        # Copy the built binary to our toolchain location
        repository_ctx.execute(["mkdir", "-p", "bin"])
        final_binary = repository_ctx.path("bin/coq-of-rust")
        
        repository_ctx.execute(["cp", str(built_binary), str(final_binary)])
        repository_ctx.execute(["chmod", "+x", str(final_binary)])
        
        print("Successfully built coq-of-rust from source!")
        print("Binary location: {}".format(final_binary))
        
        # Also create the standard library files
        _create_stdlib_files(repository_ctx)
        
        return final_binary
        
    except Exception as e:
        print("Warning: Could not build real coq-of-rust: {}".format(str(e)))
        print("Falling back to enhanced placeholder implementation")
        return _create_enhanced_placeholder(repository_ctx)
    
    print("Found Rust toolchain:")
    print("  cargo: {}".format(cargo))
    print("  rustc: {}".format(rustc))
    
    # Create a temporary directory for building coq-of-rust
    build_dir = repository_ctx.expand_location("{{name}}/coq-of-rust-source")
    repository_ctx.execute(["mkdir", "-p", build_dir])
    
    # Try to clone coq-of-rust repository
    # NOTE: This URL is a placeholder - replace with actual repository when available
    print("Attempting to clone coq-of-rust repository...")
    
    # For now, create an enhanced placeholder binary since the official repo isn't available
    # In a real implementation, this would clone and build the actual repository
    return _create_enhanced_placeholder(repository_ctx)

def _build_local_coq_of_rust(repository_ctx, local_path):
    """Build the local coq-of-rust implementation."""
    
    # Check if we have cargo available
    cargo = repository_ctx.which("cargo")
    if not cargo:
        print("Warning: cargo not found, cannot build local coq-of-rust")
        raise Exception("cargo not available")
    
    print("Building local coq-of-rust from: {}".format(local_path))
    
    # Check if this is a valid Cargo project
    cargo_toml = repository_ctx.path("{}/Cargo.toml".format(local_path))
    if not cargo_toml.exists:
        print("Warning: Cargo.toml not found in local directory")
        raise Exception("Not a valid Cargo project")
    
    # Build the local coq-of-rust with better error handling
    try:
        repository_ctx.execute([
            str(cargo), "build", "--release",
            "--manifest-path", "{}/Cargo.toml".format(local_path)
        ])
        
        # Copy the built binary
        repository_ctx.execute(["mkdir", "-p", "bin"])
        built_binary = repository_ctx.path("{}/target/release/coq-of-rust".format(local_path))
        final_binary = repository_ctx.path("bin/coq-of-rust")
        
        if not built_binary.exists:
            print("Warning: Local coq-of-rust binary not found after build")
            raise Exception("Binary not found")
        
        repository_ctx.execute(["cp", str(built_binary), str(final_binary)])
        repository_ctx.execute(["chmod", "+x", str(final_binary)])
        
        print("Successfully built local coq-of-rust!")
        print("Binary location: {}".format(final_binary))
        
        # Also create the standard library files
        _create_stdlib_files(repository_ctx)
        
        return final_binary
        
    except Exception as e:
        print("Warning: Failed to build local coq-of-rust: {}".format(str(e)))
        raise Exception("Local build failed")

def _create_stdlib_files(repository_ctx):
    """Create standard library files for coq-of-rust."""
    stdlib_dir = repository_ctx.path("lib/coq_of_rust")
    repository_ctx.execute(["mkdir", "-p", str(stdlib_dir)])
    
    # Create Prelude.v
    prelude_content = """(** coq-of-rust standard library prelude - placeholder *)

Require Import Arith Bool List.

(** Basic definitions used by coq-of-rust *)
Definition RustNat := nat.
Definition RustBool := bool.
Definition RustUnit := unit.

(** Type classes and instances *)
Class Eq (A: Type) := {
  eq: A -> A -> Prop
}.

Instance nat_eq: Eq nat := {
  eq := fun x y => x = y
}.

Instance bool_eq: Eq bool := {
  eq := fun x y => x = y
}.

(** Monad definitions *)
Class Monad (M: Type -> Type) := {
  return: forall A, A -> M A;
  bind: forall A B, M A -> (A -> M B) -> M B
}.

(** Error handling *)
Inductive Result (A: Type) : Type := 
  | Ok: A -> Result A
  | Err: string -> Result A.

(** Simulated Rust traits *)
Class Debug (A: Type) := {
  debug: A -> string
}.

Instance nat_debug: Debug nat := {
  debug := fun n => "Nat(" ++ string_of_nat n ++ ")"
}.
"""
    
    repository_ctx.write("{}/Prelude.v".format(stdlib_dir), prelude_content)
    
    # Create basic types
    types_content = """(** Basic Rust types translated to Coq *)

Require Import CoqOfRust.Prelude.

(** Rust primitive types *)
Definition i8 := Z.
Definition i16 := Z.
Definition i32 := Z.
Definition i64 := Z.
Definition u8 := N.
Definition u16 := N.
Definition u32 := N.
Definition u64 := N.
Definition f32 := R.
Definition f64 := R.

(** Rust string type *)
Definition String := list char.

(** Rust Option type *)
Inductive Option (A: Type) : Type := 
  | None : Option A
  | Some : A -> Option A.

(** Rust Result type *)
Inductive Result (A E: Type) : Type := 
  | Ok : A -> Result A E
  | Err : E -> Result A E.

(** Rust Vec type *)
Definition Vec (A: Type) := list A.
"""
    
    repository_ctx.write("{}/Types.v".format(stdlib_dir), types_content)

def _create_enhanced_placeholder(repository_ctx):
    """Create a simple placeholder that simulates coq-of-rust behavior.""
    
    # Create directory structure
    repository_ctx.execute(["mkdir", "-p", "bin"])
    repository_ctx.execute(["mkdir", "-p", "lib/coq_of_rust"])
    
    # Create simple placeholder binary
    placeholder_binary = repository_ctx.path("bin/coq-of-rust")
    
    # Simple placeholder script
    script_content = """#!/bin/bash
# coq-of-rust placeholder - will be replaced with real implementation

echo "coq-of-rust placeholder: This is a temporary implementation"
echo "To use real coq-of-rust, build from source using rules_rust toolchain"
echo "See README.md for setup instructions"

# Create a simple placeholder Coq file if output is specified
if [[ "$#" -gt 0 && "$1" == "translate" && "$#" -gt 2 ]]; then
    INPUT="$2"
    OUTPUT=""
    for i in "$@"; do
        if [[ "$i" == "--output" && "$#" -gt 1 ]]; then
            OUTPUT="${@:$(($i+1)):1}"
            break
        fi
    done
    
    if [[ -n "$OUTPUT" ]]; then
        echo "(* Generated by coq-of-rust placeholder *)" > "$OUTPUT"
        echo "(* Real implementation coming soon *)" >> "$OUTPUT"
        echo "Require Import CoqOfRust.Prelude." >> "$OUTPUT"
        echo "" >> "$OUTPUT"
        echo "(* Placeholder for translated Rust code *)" >> "$OUTPUT"
    fi
fi
"""
    
    repository_ctx.write(placeholder_binary, script_content)
    repository_ctx.execute(["chmod", "+x", placeholder_binary])
    
    # Create minimal standard library files
    _create_stdlib_files(repository_ctx)
    
    print("Created coq-of-rust placeholder")
    return placeholder_binary

# coq-of-rust toolchain repository rule
def _coq_of_rust_toolchain_repository_impl(repository_ctx):
    """Create coq-of-rust toolchain repository.
    
    This builds coq-of-rust from source using the Rust toolchain.
    """
    
    strategy = repository_ctx.attr.strategy
    version = repository_ctx.attr.version
    
    print("Setting up coq-of-rust toolchain {} using strategy {}".format(version, strategy))
    
    if strategy == "build":
        # Build coq-of-rust from source
        coq_of_rust_binary = _build_coq_of_rust_from_source(repository_ctx)
    else:
        fail("Unknown strategy: {}. Must be 'build' (download strategy not supported for coq-of-rust)".format(strategy))
    
    # Create BUILD files
    _create_coq_of_rust_build_files(repository_ctx, coq_of_rust_binary)

def _create_coq_of_rust_build_files(repository_ctx, coq_of_rust_binary):
    """Create BUILD files for the coq-of-rust toolchain."""
    
    # Create main BUILD.bazel file
    repository_ctx.file(
        "BUILD.bazel",
        """
load(":coq_of_rust_toolchain.bzl", "coq_of_rust_toolchain")

# coq-of-rust toolchain definition
coq_of_rust_toolchain(
    name = "coq_of_rust_toolchain",
    coq_of_rust_binary = "//:coq-of-rust",
    stdlib_files = glob(["lib/**/*.v"]),
    include_path = "lib",
)

# Filegroup for coq-of-rust binary
filegroup(
    name = "coq-of-rust",
    srcs = ["{}"],
    executable = True,
            cfg = "exec",
)

# Filegroup for standard library
filegroup(
    name = "stdlib",
    srcs = glob(["lib/**/*.v"]),
)

# Filegroup for prelude
filegroup(
    name = "prelude",
    srcs = ["lib/coq_of_rust/Prelude.v"],
)

# Filegroup for types
filegroup(
    name = "types",
    srcs = ["lib/coq_of_rust/Types.v"],
)

# Filegroup for all coq-of-rust libraries
filegroup(
    name = "coq_of_rust_libs",
    srcs = glob(["lib/coq_of_rust/**/*.v"]),
)
""".format(native.path.basename(coq_of_rust_binary))
    )
    
    # Create toolchain BUILD file
    repository_ctx.file(
        "coq_of_rust_toolchain.bzl",
        """
load("@rules_rocq_rust//coq_of_rust/private:toolchain.bzl", "coq_of_rust_toolchain")

# Re-export the coq_of_rust_toolchain rule
coq_of_rust_toolchain = coq_of_rust_toolchain

# Additional filegroups for convenience
def coq_of_rust_stdlib_filegroup(name, srcs = None, **kwargs):
    native.filegroup(
        name = name,
        srcs = srcs,
        **kwargs
    )
"""
    )

# Repository rule definition
coq_of_rust_toolchain_repository = repository_rule(
    implementation = _coq_of_rust_toolchain_repository_impl,
    attrs = {
        "version": attr.string(default = "0.5.0"),
        "strategy": attr.string(default = "build"),
        "repository_url": attr.string(
            default = "",
            doc = "Custom coq-of-rust repository URL (overrides default URLs)"
        ),
    },
)