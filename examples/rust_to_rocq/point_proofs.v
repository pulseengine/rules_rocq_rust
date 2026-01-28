(** * Formal Verification Proofs for point.rs

    This file demonstrates the complete Rust → Rocq → Proof workflow:
    1. point.rs was translated to point.v by rocq-of-rust
    2. point.v was compiled against the RocqOfRust library
    3. This file states and proves properties about the translated code

    The translated code uses a deeply embedded monadic DSL where:
    - M = LowM.t (Value.t + Exception.t)  -- the computation monad
    - pure v = LowM.Pure (inl v)           -- lift a value into M
    - The [monadic] tactic wraps Value.t expressions with [pure] *)

Require Import RocqOfRust.RocqOfRust.
From examples.rust_to_rocq Require Import point.

(** ** Proof 1: origin() produces a pure value with both fields zero

    The Rust function:
      pub fn origin() -> Self { Point { x: 0, y: 0 } }

    Since origin has no arguments and constructs a struct from
    constant literals, the [monadic] tactic wraps the result with
    [pure], producing [LowM.Pure (inl (Value.mkStructRecord ...))]. *)

Theorem origin_returns_zero_point :
  Impl_point_Point.origin [] [] [] =
    M.pure (Value.mkStructRecord "point::Point" [] []
      [("x", Value.Integer IntegerKind.I32 0);
       ("y", Value.Integer IntegerKind.I32 0)]).
Proof.
  reflexivity.
Qed.

(** ** Proof 2: origin() is a pure computation (no side effects)

    We prove that origin returns a [LowM.Pure] value, meaning it
    performs no memory allocations, closure calls, or IO.
    This reflects the Rust semantics: constructing a struct literal
    with constant fields is a pure operation. *)

Theorem origin_is_pure :
  exists v, Impl_point_Point.origin [] [] [] = LowM.Pure v.
Proof.
  eexists.
  reflexivity.
Qed.

(** ** Proof 3: origin() returns a successful (non-exception) value

    The [M] monad uses [Value.t + Exception.t] as its result type.
    A successful computation wraps the value with [inl].
    We prove origin never raises an exception. *)

Theorem origin_succeeds :
  exists v : Value.t,
    Impl_point_Point.origin [] [] [] = LowM.Pure (inl v).
Proof.
  eexists.
  reflexivity.
Qed.

(** ** Proof 4: Wrong argument counts produce M.impossible

    The translated code includes exhaustive pattern matching.
    Calling a function with the wrong argument count falls
    through to the [M.impossible] error case. This ensures
    the Rust function's arity is preserved in the translation. *)

Theorem origin_rejects_extra_args :
  forall v : Value.t,
    Impl_point_Point.origin [] [] [v] =
      M.impossible "wrong number of arguments".
Proof.
  intro v.
  reflexivity.
Qed.

Theorem new_rejects_no_args :
  Impl_point_Point.new [] [] [] =
    M.impossible "wrong number of arguments".
Proof.
  reflexivity.
Qed.

Theorem new_rejects_one_arg :
  forall v : Value.t,
    Impl_point_Point.new [] [] [v] =
      M.impossible "wrong number of arguments".
Proof.
  intro v.
  reflexivity.
Qed.

(** ** Proof 5: The origin struct has the correct type path

    From [origin_returns_zero_point] we know the exact return value.
    We derive that the struct name is "point::Point", matching
    the Rust fully-qualified type path. *)

Corollary origin_struct_name :
  let result := Value.mkStructRecord "point::Point" [] []
    [("x", Value.Integer IntegerKind.I32 0);
     ("y", Value.Integer IntegerKind.I32 0)] in
  Impl_point_Point.origin [] [] [] = M.pure result /\
  result = Value.StructRecord "point::Point" [] []
    [("x", Value.Integer IntegerKind.I32 0);
     ("y", Value.Integer IntegerKind.I32 0)].
Proof.
  split; reflexivity.
Qed.

(** ** Proof 6: origin() returns x=0 and y=0

    We prove that the origin point has both coordinates equal to
    zero by showing the exact field values in the returned struct. *)

Corollary origin_fields_are_zero :
  Impl_point_Point.origin [] [] [] =
    M.pure (Value.StructRecord "point::Point" [] []
      [("x", Value.Integer IntegerKind.I32 0);
       ("y", Value.Integer IntegerKind.I32 0)]).
Proof.
  exact origin_returns_zero_point.
Qed.
