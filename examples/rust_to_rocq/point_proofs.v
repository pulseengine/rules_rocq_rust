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

(* ========================================================================= *)
(** * Section 1: Point::origin() Proofs *)
(* ========================================================================= *)

(** ** origin() produces a pure value with both fields zero *)
Theorem origin_returns_zero_point :
  Impl_point_Point.origin [] [] [] =
    M.pure (Value.mkStructRecord "point::Point" [] []
      [("x", Value.Integer IntegerKind.I32 0);
       ("y", Value.Integer IntegerKind.I32 0)]).
Proof. reflexivity. Qed.

(** ** origin() is a pure computation (no side effects) *)
Theorem origin_is_pure :
  exists v, Impl_point_Point.origin [] [] [] = LowM.Pure v.
Proof. eexists. reflexivity. Qed.

(** ** origin() returns a successful (non-exception) value *)
Theorem origin_succeeds :
  exists v : Value.t,
    Impl_point_Point.origin [] [] [] = LowM.Pure (inl v).
Proof. eexists. reflexivity. Qed.

(* ========================================================================= *)
(** * Section 2: Point::new() Proofs *)
(* ========================================================================= *)

(** ** new() with wrong argument counts produces M.impossible *)
Theorem new_rejects_no_args :
  Impl_point_Point.new [] [] [] =
    M.impossible "wrong number of arguments".
Proof. reflexivity. Qed.

Theorem new_rejects_one_arg :
  forall v : Value.t,
    Impl_point_Point.new [] [] [v] =
      M.impossible "wrong number of arguments".
Proof. intro v. reflexivity. Qed.

Theorem new_rejects_three_args :
  forall a b c : Value.t,
    Impl_point_Point.new [] [] [a; b; c] =
      M.impossible "wrong number of arguments".
Proof. intros. reflexivity. Qed.

(* ========================================================================= *)
(** * Section 3: Point::translate() Proofs *)
(* ========================================================================= *)

(** ** translate() requires exactly 3 arguments (self, dx, dy) *)
Theorem translate_rejects_no_args :
  Impl_point_Point.translate [] [] [] =
    M.impossible "wrong number of arguments".
Proof. reflexivity. Qed.

Theorem translate_rejects_one_arg :
  forall v : Value.t,
    Impl_point_Point.translate [] [] [v] =
      M.impossible "wrong number of arguments".
Proof. intro v. reflexivity. Qed.

Theorem translate_rejects_two_args :
  forall a b : Value.t,
    Impl_point_Point.translate [] [] [a; b] =
      M.impossible "wrong number of arguments".
Proof. intros. reflexivity. Qed.

(* ========================================================================= *)
(** * Section 4: Point::squared_distance() Proofs *)
(* ========================================================================= *)

(** ** squared_distance() requires exactly 1 argument (self) *)
Theorem squared_distance_rejects_no_args :
  Impl_point_Point.squared_distance [] [] [] =
    M.impossible "wrong number of arguments".
Proof. reflexivity. Qed.

Theorem squared_distance_rejects_two_args :
  forall a b : Value.t,
    Impl_point_Point.squared_distance [] [] [a; b] =
      M.impossible "wrong number of arguments".
Proof. intros. reflexivity. Qed.

(* ========================================================================= *)
(** * Section 5: Point::is_origin() Proofs *)
(* ========================================================================= *)

(** ** is_origin() requires exactly 1 argument (self) *)
Theorem is_origin_rejects_no_args :
  Impl_point_Point.is_origin [] [] [] =
    M.impossible "wrong number of arguments".
Proof. reflexivity. Qed.

Theorem is_origin_rejects_two_args :
  forall a b : Value.t,
    Impl_point_Point.is_origin [] [] [a; b] =
      M.impossible "wrong number of arguments".
Proof. intros. reflexivity. Qed.

(* ========================================================================= *)
(** * Section 6: Rectangle Proofs *)
(* ========================================================================= *)

(** ** Rectangle::new() requires exactly 2 arguments *)
Theorem rectangle_new_rejects_no_args :
  Impl_point_Rectangle.new [] [] [] =
    M.impossible "wrong number of arguments".
Proof. reflexivity. Qed.

Theorem rectangle_new_rejects_one_arg :
  forall v : Value.t,
    Impl_point_Rectangle.new [] [] [v] =
      M.impossible "wrong number of arguments".
Proof. intro v. reflexivity. Qed.

Theorem rectangle_new_rejects_three_args :
  forall a b c : Value.t,
    Impl_point_Rectangle.new [] [] [a; b; c] =
      M.impossible "wrong number of arguments".
Proof. intros. reflexivity. Qed.

(** ** Rectangle::width() and height() require exactly 1 argument *)
Theorem rectangle_width_rejects_no_args :
  Impl_point_Rectangle.width [] [] [] =
    M.impossible "wrong number of arguments".
Proof. reflexivity. Qed.

Theorem rectangle_height_rejects_no_args :
  Impl_point_Rectangle.height [] [] [] =
    M.impossible "wrong number of arguments".
Proof. reflexivity. Qed.

(* ========================================================================= *)
(** * Section 7: Type Definitions *)
(* ========================================================================= *)

(** ** Self type for Point implementation is "point::Point" *)
Theorem point_self_type :
  Impl_point_Point.Self = Ty.path "point::Point".
Proof. reflexivity. Qed.

(** ** Self type for Rectangle implementation is "point::Rectangle" *)
Theorem rectangle_self_type :
  Impl_point_Rectangle.Self = Ty.path "point::Rectangle".
Proof. reflexivity. Qed.

(* ========================================================================= *)
(** * Section 8: Derived Trait Implementations *)
(* ========================================================================= *)

(** ** Clone::clone() requires exactly 1 argument *)
Theorem clone_rejects_no_args :
  Impl_core_clone_Clone_for_point_Point.clone [] [] [] =
    M.impossible "wrong number of arguments".
Proof. reflexivity. Qed.

(** ** PartialEq::eq() requires exactly 2 arguments *)
Theorem eq_rejects_no_args :
  Impl_core_cmp_PartialEq_point_Point_for_point_Point.eq [] [] [] =
    M.impossible "wrong number of arguments".
Proof. reflexivity. Qed.

Theorem eq_rejects_one_arg :
  forall v : Value.t,
    Impl_core_cmp_PartialEq_point_Point_for_point_Point.eq [] [] [v] =
      M.impossible "wrong number of arguments".
Proof. intro v. reflexivity. Qed.

(** ** Debug::fmt() requires exactly 2 arguments *)
Theorem debug_fmt_rejects_no_args :
  Impl_core_fmt_Debug_for_point_Point.fmt [] [] [] =
    M.impossible "wrong number of arguments".
Proof. reflexivity. Qed.

Theorem debug_fmt_rejects_one_arg :
  forall v : Value.t,
    Impl_core_fmt_Debug_for_point_Point.fmt [] [] [v] =
      M.impossible "wrong number of arguments".
Proof. intro v. reflexivity. Qed.
