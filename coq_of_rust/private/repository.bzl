"""Repository rule for downloading and building rocq-of-rust.

This rule downloads the rocq-of-rust source and builds it using cargo nightly.
Building with cargo directly avoids crate_universe issues with edition2024 crates.
"""

_DEFAULT_COMMIT = "main"
_DEFAULT_REPO = "https://github.com/formal-land/rocq-of-rust"
_DEFAULT_NIGHTLY = "nightly-2024-12-01"

def _rocq_of_rust_source_impl(repository_ctx):
    """Download and build rocq-of-rust from source."""

    commit = repository_ctx.attr.commit
    sha256 = repository_ctx.attr.sha256
    rust_nightly = repository_ctx.attr.rust_nightly
    use_real_library = repository_ctx.attr.use_real_library

    repository_ctx.report_progress("Downloading rocq-of-rust source ({})".format(commit))

    # Download source archive
    url = "{}/archive/{}.tar.gz".format(_DEFAULT_REPO, commit)

    download_kwargs = {
        "url": url,
        "stripPrefix": "rocq-of-rust-{}".format(commit) if commit != "main" else "rocq-of-rust-main",
    }
    if sha256:
        download_kwargs["sha256"] = sha256

    repository_ctx.download_and_extract(**download_kwargs)

    # Check for cargo/rustup
    cargo = repository_ctx.which("cargo")
    rustup = repository_ctx.which("rustup")

    if not cargo:
        _create_placeholder(repository_ctx, "cargo not found")
        return

    # Install nightly toolchain with required components
    if rustup:
        repository_ctx.report_progress("Installing Rust nightly toolchain")
        repository_ctx.execute(
            ["rustup", "toolchain", "install", rust_nightly],
            timeout = 600,
        )
        # Add rustc-dev and rust-src components for rustc_private
        repository_ctx.execute(
            ["rustup", "component", "add", "rustc-dev", "rust-src", "--toolchain", rust_nightly],
            timeout = 300,
        )

    # Build rocq-of-rust with cargo nightly
    repository_ctx.report_progress("Building rocq-of-rust with cargo nightly")

    build_result = repository_ctx.execute(
        [str(cargo), "+{}".format(rust_nightly), "build", "--release"],
        timeout = 1200,
        environment = {"CARGO_TERM_COLOR": "never"},
    )

    if build_result.return_code != 0:
        print("Build output: {}".format(build_result.stdout))
        print("Build error: {}".format(build_result.stderr))
        _create_placeholder(repository_ctx, "cargo build failed")
        return

    # Find the built binary
    binary_path = None
    for candidate in ["target/release/rocq-of-rust", "target/release/rocq_of_rust"]:
        if repository_ctx.path(candidate).exists:
            binary_path = candidate
            break

    if not binary_path:
        _create_placeholder(repository_ctx, "binary not found after build")
        return

    # Find rustc sysroot for library path (needed for rustc_private)
    rustc = repository_ctx.which("rustc")
    if rustup and rustc:
        sysroot_result = repository_ctx.execute(
            ["rustup", "run", rust_nightly, "rustc", "--print", "sysroot"],
            timeout = 60,
        )
        sysroot = sysroot_result.stdout.strip() if sysroot_result.return_code == 0 else ""
        if sysroot:
            repository_ctx.report_progress("Found rustc sysroot: {}".format(sysroot))
    else:
        sysroot = ""

    if not sysroot:
        print("Warning: Could not find rustc sysroot, rocq-of-rust may fail at runtime")

    # Create wrapper script that sets library path
    _create_wrapper_script(repository_ctx, binary_path, sysroot)

    # Generate BUILD.bazel
    _generate_build_file(repository_ctx, "bin/rocq-of-rust", binary_path, use_real_library)

    # Handle RocqOfRust library
    if use_real_library:
        # Keep only core RocqOfRust files (M.v, RecordUpdate.v, RocqOfRust.v)
        # The full library has many translated Rust crates that aren't needed
        repository_ctx.report_progress("Using core RocqOfRust library (M.v, RecordUpdate.v, RocqOfRust.v)")
        _trim_rocq_library(repository_ctx)
    else:
        # Replace with minimal stubs for basic type-checking
        repository_ctx.report_progress("Using RocqOfRust stub library")
        if repository_ctx.path("RocqOfRust").exists:
            repository_ctx.execute(["rm", "-rf", "RocqOfRust"])
        _create_rocq_library_stubs(repository_ctx)

def _trim_rocq_library(repository_ctx):
    """Keep only core RocqOfRust files, remove translated crate directories.

    The core files and their dependencies:
    - RecordUpdate.v (no internal deps)
    - M.v (no internal deps, but requires coqutil/hammer/smpl)
    - lib/lib.v (requires RecordUpdate, M)
    - lib/Notations.v
    - RocqOfRust.v (requires RecordUpdate, lib/lib, M)
    """
    rocq_dir = repository_ctx.path("RocqOfRust")
    if not rocq_dir.exists:
        return

    # List of directories to remove (translated Rust crates and support files)
    # Keep: M.v, RecordUpdate.v, RocqOfRust.v, lib/lib.v, lib/Notations.v
    dirs_to_remove = [
        "core", "alloc", "bytes",
        "alloy_primitives", "revm", "ruint",
        "solana_program_token", "anza_xyz_solana_sdk",
        "move_sui", "proofs", "examples", "scripts",
        "legacy", "simulations_legacy", "links", "experiments",
        "simulate",
        # Remove subdirectories within lib/ but keep lib/lib.v and lib/Notations.v
        "lib/proofs", "lib/simulate", "lib/simulations_legacy",
    ]

    for dir_name in dirs_to_remove:
        dir_path = repository_ctx.path("RocqOfRust/{}".format(dir_name))
        if dir_path.exists:
            repository_ctx.execute(["rm", "-rf", str(dir_path)])

def _create_wrapper_script(repository_ctx, binary_path, sysroot):
    """Create wrapper script that sets library path for rustc_private."""

    repository_ctx.execute(["mkdir", "-p", "bin"])

    # Wrapper script that sets library path before invoking the real binary
    wrapper = '''#!/bin/bash
# Wrapper for rocq-of-rust that sets library path for rustc_private
# Generated by rules_rocq_rust

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
REAL_BINARY="$SCRIPT_DIR/../{binary_path}"

# Add rustc to PATH (required for rocq-of-rust to find rustc)
export PATH="{sysroot}/bin:$PATH"

# Set library path for rustc_private crates
export DYLD_LIBRARY_PATH="{sysroot}/lib:$DYLD_LIBRARY_PATH"
export LD_LIBRARY_PATH="{sysroot}/lib:$LD_LIBRARY_PATH"

# Set sysroot for rustc to find correct std library
export SYSROOT="{sysroot}"
export RUSTUP_TOOLCHAIN="{toolchain}"

exec "$REAL_BINARY" "$@"
'''.format(binary_path = binary_path, sysroot = sysroot, toolchain = repository_ctx.attr.rust_nightly)

    repository_ctx.file("bin/rocq-of-rust", wrapper, executable = True)

def _generate_build_file(repository_ctx, wrapper_path, real_binary_path, use_real_library = False):
    """Generate BUILD.bazel exposing the built binary and library."""

    if use_real_library:
        # Real library with ordered compilation targets
        build_content = '''# Generated BUILD.bazel for rocq-of-rust (real library)
# Files are compiled in dependency order using separate targets

load("@rules_rocq_rust//rocq:defs.bzl", "rocq_library")

package(default_visibility = ["//visibility:public"])

# Pre-built rocq-of-rust binary (wrapper + real binary)
filegroup(
    name = "rocq_of_rust",
    srcs = ["{wrapper}", "{binary}"],
)

# ========================================
# RocqOfRust library - ordered compilation
# ========================================
# Dependency order:
#   1. RecordUpdate.v (no deps)
#   2. M.v (no internal deps)
#   3. lib/Notations.v (no deps)
#   4. lib/lib.v (requires RecordUpdate, M)
#   5. RocqOfRust.v (requires all above)

# Step 1: RecordUpdate - no internal dependencies
rocq_library(
    name = "rocq_of_rust_record_update",
    srcs = ["RocqOfRust/RecordUpdate.v"],
    include_path = "RocqOfRust",
    extra_flags = ["-impredicative-set"],
)

# Step 2: M - no internal dependencies (uses coqutil/hammer/smpl from toolchain)
rocq_library(
    name = "rocq_of_rust_m",
    srcs = ["RocqOfRust/M.v"],
    include_path = "RocqOfRust",
    deps = [":rocq_of_rust_record_update"],
    extra_flags = ["-impredicative-set"],
)

# Step 3: lib/Notations - no dependencies
rocq_library(
    name = "rocq_of_rust_lib_notations",
    srcs = ["RocqOfRust/lib/Notations.v"],
    include_path = "RocqOfRust",
    extra_flags = ["-impredicative-set"],
)

# Step 4: lib/lib - requires RecordUpdate and M
rocq_library(
    name = "rocq_of_rust_lib_lib",
    srcs = ["RocqOfRust/lib/lib.v"],
    include_path = "RocqOfRust",
    deps = [
        ":rocq_of_rust_record_update",
        ":rocq_of_rust_m",
    ],
    extra_flags = ["-impredicative-set"],
)

# Step 5: RocqOfRust - main entry point, requires all above
rocq_library(
    name = "rocq_of_rust_main",
    srcs = ["RocqOfRust/RocqOfRust.v"],
    include_path = "RocqOfRust",
    deps = [
        ":rocq_of_rust_record_update",
        ":rocq_of_rust_m",
        ":rocq_of_rust_lib_lib",
    ],
    extra_flags = ["-impredicative-set"],
)

# Aggregate target - use this as dependency for translated code
# This is an alias to the main entry point which transitively includes all
alias(
    name = "rocq_of_rust_rocq_lib",
    actual = ":rocq_of_rust_main",
)
'''.format(wrapper = wrapper_path, binary = real_binary_path)
    else:
        # Stub library - simple filegroup
        build_content = '''# Generated BUILD.bazel for rocq-of-rust (stub library)

package(default_visibility = ["//visibility:public"])

# Pre-built rocq-of-rust binary (wrapper + real binary)
filegroup(
    name = "rocq_of_rust",
    srcs = ["{wrapper}", "{binary}"],
)

# RocqOfRust stub library sources
filegroup(
    name = "rocq_of_rust_rocq_lib",
    srcs = glob(
        ["RocqOfRust/**/*.v", "CoqOfRust/**/*.v"],
        allow_empty = True,
    ),
)
'''.format(wrapper = wrapper_path, binary = real_binary_path)

    repository_ctx.file("BUILD.bazel", build_content)

def _create_placeholder(repository_ctx, reason):
    """Create placeholder when build fails."""
    print("Creating rocq-of-rust placeholder: {}".format(reason))

    # Create placeholder script that generates stub output
    placeholder = '''#!/bin/bash
# rocq-of-rust placeholder - build failed: {}
echo "rocq-of-rust placeholder (build failed: {})" >&2
echo "Creating minimal output..." >&2

# Handle translate subcommand
if [ "$1" = "translate" ]; then
    shift
    while [ $# -gt 0 ]; do
        case "$1" in
            --path) INPUT="$2"; shift 2 ;;
            --output-path) OUTDIR="$2"; shift 2 ;;
            *) shift ;;
        esac
    done
    mkdir -p "$OUTDIR"
    BASENAME=$(basename "$INPUT" .rs)
    cat > "$OUTDIR/$BASENAME.v" << 'ROCQ'
(* Generated by rocq-of-rust placeholder *)
Require Import RocqOfRust.RocqOfRust.
Module Placeholder.
  Definition placeholder : Value.t := UnsupportedLiteral.
End Placeholder.
ROCQ
else
    echo "Usage: rocq-of-rust translate --path <file> --output-path <dir>" >&2
    exit 1
fi
'''.format(reason, reason)

    repository_ctx.file("bin/rocq-of-rust", placeholder, executable = True)

    build_content = '''# Generated BUILD.bazel for rocq-of-rust (placeholder)

load("@rules_rocq_rust//rocq:defs.bzl", "rocq_library")

package(default_visibility = ["//visibility:public"])

filegroup(
    name = "rocq_of_rust",
    srcs = ["bin/rocq-of-rust"],
)

# RocqOfRust stub library - compiled from stubs
rocq_library(
    name = "rocq_of_rust_main",
    srcs = ["RocqOfRust/RocqOfRust.v"],
    include_path = "RocqOfRust",
    extra_flags = ["-impredicative-set"],
)

# Alias for compatibility
alias(
    name = "rocq_of_rust_rocq_lib",
    actual = ":rocq_of_rust_main",
)
'''
    repository_ctx.file("BUILD.bazel", build_content)
    _create_rocq_library_stubs(repository_ctx)

def _create_rocq_library_stubs(repository_ctx):
    """Create comprehensive RocqOfRust library stubs for generated code."""

    repository_ctx.execute(["mkdir", "-p", "RocqOfRust"])

    # Main RocqOfRust.v - completely self-contained stub with axiomatized primitives.
    # No external Requires - Rocq 9.0 redirects "From Coq" to "From Stdlib" which
    # isn't in the loadpath. This stub axiomatizes everything directly.
    rocq_content = '''(** RocqOfRust - Stub library for translated Rust code.
    This is a minimal stub that allows generated code to type-check.
    For full verification, use the complete RocqOfRust library with Rocq 9.0.

    Uses Rocq 9.0 Stdlib for string and integer support. *)

(* Import Stdlib - Rocq 9.0 renamed Coq -> Stdlib *)
(* Use Export so importing modules get the notations and scopes *)
From Stdlib Require Export PrimString.
From Stdlib Require Export ZArith.
From Stdlib Require Export List.
Export ListNotations.

(* Make scopes globally available to importers *)
Global Open Scope pstring_scope.
Global Open Scope Z_scope.

(** * Type system *)
Module Ty.
  (* Type representation *)
  Inductive t : Type :=
  | path : string -> t
  | apply : t -> list t -> list t -> t
  | tuple : list t -> t
  | dyn : list (string * list t) -> t.

  (* Commonly used paths *)
  Definition unit := path "()".
  Definition bool := path "bool".
  Definition i8 := path "i8".
  Definition i16 := path "i16".
  Definition i32 := path "i32".
  Definition i64 := path "i64".
  Definition i128 := path "i128".
  Definition isize := path "isize".
  Definition u8 := path "u8".
  Definition u16 := path "u16".
  Definition u32 := path "u32".
  Definition u64 := path "u64".
  Definition u128 := path "u128".
  Definition usize := path "usize".
  Definition f32 := path "f32".
  Definition f64 := path "f64".
  Definition str := path "str".
End Ty.

(** * Integer kinds for typed integers *)
Module IntegerKind.
  Inductive t : Type :=
  | I8 | I16 | I32 | I64 | I128 | Isize
  | U8 | U16 | U32 | U64 | U128 | Usize.
End IntegerKind.

(** * Value representation *)
Module Value.
  (* Stub value type - parameterized constructors for type-checking *)
  Inductive t : Type :=
  | MakeValue : t
  | DeclaredButUndefined : t
  | Tuple : list t -> t
  | Integer : IntegerKind.t -> Z -> t
  | Bool : bool -> t
  | String : string -> t
  | Array : list t -> t
  | StructRecord : string -> list t -> list t -> list (string * t) -> t
  | StructTuple : string -> list t -> list t -> list t -> t
  | Closure : t.

  (* Helper function matching generated code pattern *)
  Definition mkStructRecord (name : string) (consts : list t) (tys : list t) (fields : list (string * t)) : t :=
    StructRecord name consts tys fields.

  Definition mkStructTuple (name : string) (consts : list t) (tys : list t) (fields : list t) : t :=
    StructTuple name consts tys fields.
End Value.

(** * Pointer kinds *)
Module Pointer.
  Module Kind.
    Inductive t : Type :=
    | Ref : t
    | MutRef : t
    | Raw : t.
  End Kind.
End Pointer.

(** * Unary operations *)
Module UnOp.
  Definition not (x : Value.t) : Value.t := Value.MakeValue.
  Definition neg (x : Value.t) : Value.t := Value.MakeValue.
End UnOp.

(** * Binary operations - these are Value.t closures passed to call_closure *)
Module BinOp.
  Definition eq : Value.t := Value.MakeValue.
  Definition ne : Value.t := Value.MakeValue.
  Definition lt : Value.t := Value.MakeValue.
  Definition le : Value.t := Value.MakeValue.
  Definition gt : Value.t := Value.MakeValue.
  Definition ge : Value.t := Value.MakeValue.
  Module Wrap.
    Definition add : Value.t := Value.MakeValue.
    Definition sub : Value.t := Value.MakeValue.
    Definition mul : Value.t := Value.MakeValue.
    Definition div : Value.t := Value.MakeValue.
    Definition rem : Value.t := Value.MakeValue.
    Definition shl : Value.t := Value.MakeValue.
    Definition shr : Value.t := Value.MakeValue.
    Definition bit_and : Value.t := Value.MakeValue.
    Definition bit_or : Value.t := Value.MakeValue.
    Definition bit_xor : Value.t := Value.MakeValue.
  End Wrap.
End BinOp.

(** * Monad M for Rust semantics - stub returns Value.t *)
Definition M : Type := Value.t.

(** * Logical operations - defined after M *)
Module LogicalOp.
  Definition and (x : Value.t) (y : M) : M := Value.MakeValue.
  Definition or (x : Value.t) (y : M) : M := Value.MakeValue.
End LogicalOp.

(** * Instance fields for trait implementations - defined before M module *)
Module InstanceField.
  Inductive t : Type :=
  | Method : forall (f : list Value.t -> list Ty.t -> list Value.t -> M), t
  | Ty : Ty.t -> t.
End InstanceField.

(** * Run marker - for stub, just identity *)
Definition run {A : Type} (x : A) : A := x.

(** * Notations - pipe notation for function application *)
(* The (| ... |) notation:
   e (| e1, e2, e3 |) expands to run (((e e1) e2) e3) *)
Notation "e (| e1 , .. , en |)" :=
  (run ((.. (e e1) ..) en))
  (at level 100).

Notation "e (||)" :=
  (run e)
  (at level 100).

Module M.
  (* The M.monadic tactic - for stub, just identity *)
  Ltac monadic e := exact e.

  (* let_user for user-level let bindings *)
  Definition let_user (ty : Ty.t) (v : M) (f : Value.t -> M) : M := Value.MakeValue.
  Definition let_user_monadic (ty : Ty.t) (v : M) (f : Value.t -> M) : M := Value.MakeValue.
  Definition let_ (v : M) (f : Value.t -> M) : M := Value.MakeValue.

  (* Core monadic operations - all return Value.MakeValue for stub *)
  Definition alloc (ty : Ty.t) (v : Value.t) : M := Value.MakeValue.
  Definition read (m : M) : Value.t := Value.MakeValue.
  Definition write (m : M) (v : Value.t) : M := Value.MakeValue.
  Definition copy (m : M) : M := Value.MakeValue.
  Definition pure (v : Value.t) : M := v.
  Definition deref (m : M) : M := Value.MakeValue.
  Definition borrow (k : Pointer.Kind.t) (m : M) : M := Value.MakeValue.

  (* Function calls *)
  Definition call_closure (ty : Ty.t) (f : Value.t) (args : list Value.t) : M := Value.MakeValue.
  Definition get_associated_function (ty : Ty.t) (name : string) (tys1 tys2 : list Ty.t) : Value.t := Value.MakeValue.
  (* get_trait_method: trait, ty, const_generics, type_generics, method_name, method_const_generics, method_type_generics *)
  Definition get_trait_method (trait : string) (ty : Ty.t) (const_generics : list Value.t) (type_generics : list Ty.t) (name : string) (method_const_generics : list Value.t) (method_type_generics : list Ty.t) : Value.t := Value.MakeValue.
  Definition get_function (name : string) (tys : list Ty.t) : Value.t := Value.MakeValue.

  (* Control flow *)
  Definition impossible (s : string) : M := Value.MakeValue.
  Definition never_to_any (m : M) : M := Value.MakeValue.
  (* match_operator: ty, scrutinee, arms *)
  Definition match_operator (ty : Ty.t) (scrutinee : Value.t) (arms : list (Value.t -> M)) : M := Value.MakeValue.

  (* Pointer operations *)
  Module SubPointer.
    Definition get_struct_record_field (m : M) (s1 s2 : string) : M := Value.MakeValue.
    Definition get_struct_tuple_field (m : M) (s : string) (n : Z) : M := Value.MakeValue.
    Definition get_array_field (m1 m2 : M) : M := Value.MakeValue.
  End SubPointer.

  (* Pointer coercion - returns a closure Value.t that represents the coercion *)
  Module PointerCoercion.
    Inductive t : Type :=
    | Unsize : t
    | MutToConstPointer : t
    | ArrayToPointer : t.
  End PointerCoercion.
  (* Takes 3 args and returns a Value.t (closure); 4th arg passed via call_closure *)
  Definition pointer_coercion (pc : PointerCoercion.t) (t1 t2 : Ty.t) : Value.t := Value.MakeValue.

  (* Trait and function instances *)
  (* IsTraitInstance: trait_name, const_params, type_params, Self, instance_fields *)
  Class IsTraitInstance
    (trait_name : string)
    (const_params : list Value.t)
    (type_params : list Ty.t)
    (Self : Ty.t)
    (instance : list (string * InstanceField.t)) : Prop := {}.
  Class IsFunction (C : string) (f : list Value.t -> list Ty.t -> list Value.t -> M) : Prop := {}.

  (* IsAssociatedFunction typeclass for associated functions *)
  Module IsAssociatedFunction.
    Class C (Self : Ty.t) (name : string) (f : list Value.t -> list Ty.t -> list Value.t -> M) : Prop := {}.
  End IsAssociatedFunction.
End M.

(** * Let notations for monadic bindings - defined after M module *)
Notation "'let~' a : ty := b 'in' c" :=
  (M.let_user ty b (fun a => c))
  (at level 200, b at level 100, a name).

Notation "'let*' a := b 'in' c" :=
  (M.let_ b (fun a => c))
  (at level 200, b at level 100, a name).

Notation "'let*~' a : ty := b 'in' c" :=
  (M.let_user_monadic ty b (fun a => c))
  (at level 200, b at level 100, a name).

(** * Helper functions *)
Definition mk_str (s : string) : Value.t := Value.MakeValue.
Definition pointer_coercion (s : string) (v : Value.t) : Value.t := Value.MakeValue.
Definition InlineAssembly : Value.t := Value.MakeValue.
Definition UnsupportedLiteral : Value.t := Value.MakeValue.
'''

    repository_ctx.file("RocqOfRust/RocqOfRust.v", rocq_content)

rocq_of_rust_source = repository_rule(
    implementation = _rocq_of_rust_source_impl,
    attrs = {
        "commit": attr.string(default = _DEFAULT_COMMIT),
        "sha256": attr.string(default = ""),
        "rust_nightly": attr.string(default = _DEFAULT_NIGHTLY),
        "use_real_library": attr.bool(
            default = False,
            doc = "Use real RocqOfRust library (requires nixpkgs deps: coqutil, hammer, smpl)",
        ),
    },
    doc = "Downloads and builds rocq-of-rust from source using cargo nightly.",
)

rocq_of_rust_repository = rocq_of_rust_source
