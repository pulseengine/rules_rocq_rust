(** Verification proofs for the Rust code *)

Require Import Arith Bool List.
Require Import CoqOfRust.Prelude CoqOfRust.Types.

(** Import the generated Rust code *)
Require Import RustCode.

(** Additional lemmas and proofs about the Rust code behavior *)

(** Lemma: Point addition is commutative *)
Theorem point_add_comm : forall p1 p2 : RustCode.MyStruct,
  let p1_plus_p2 := RustCode.method_example p1 p2 in
  let p2_plus_p1 := RustCode.method_example p2 p1 in
  p1_plus_p2.(RustCode.field1) = p2_plus_p1.(RustCode.field1) /
  p1_plus_p2.(RustCode.field2) = p2_plus_p1.(RustCode.field2).
Proof.
  intros p1 p2.
  destruct p1, p2.
  simpl in *.
  rewrite Z.add_comm.
  rewrite bool_eqb_eq.
  split; reflexivity.
Qed.

(** Lemma: Adding origin doesn't change a point *)
Theorem point_add_origin : forall p : RustCode.MyStruct,
  let origin := RustCode.my_function 0 false in
  let p_plus_origin := RustCode.method_example p origin in
  p_plus_origin.(RustCode.field1) = p.(RustCode.field1) /
  p_plus_origin.(RustCode.field2) = p.(RustCode.field2).
Proof.
  intros p.
  destruct p.
  simpl.
  rewrite Z.add_0_r.
  rewrite bool_eqb_eq.
  split; reflexivity.
Qed.

(** Lemma: Distance from origin is non-negative *)
Theorem distance_non_negative : forall p : RustCode.MyStruct,
  let dist := RustCode.method_example p in
  dist >= 0.
Proof.
  intros p.
  destruct p.
  simpl.
  apply Z.abs_nonneg.
Qed.

(** Lemma: Origin has zero distance *)
Theorem origin_distance_zero : 
  let origin := RustCode.my_function 0 false in
  let dist := RustCode.method_example origin in
  dist = 0.
Proof.
  simpl.
  rewrite Z.abs_0.
  reflexivity.
Qed.

(** Lemma: Valid points have non-negative coordinates *)
Theorem valid_point_properties : forall p : RustCode.MyStruct,
  RustCode.method_example p = true ->
  p.(RustCode.field1) >= 0 /
  p.(RustCode.field2) = true.
Proof.
  intros p Hvalid.
  destruct p.
  simpl in Hvalid.
  destruct Hvalid.
  split.
  - apply Z.ge_0_le.
  - reflexivity.
Qed.

(** Example: Verify specific point properties *)
Example specific_point_verification :
  let p := RustCode.my_function 5 true in
  let dist := RustCode.method_example p in
  dist = 5.
Proof.
  simpl.
  rewrite Z.abs_N1.
  reflexivity.
Qed.

(** Example: Verify point addition *)
Example point_addition_example :
  let p1 := RustCode.my_function 3 true in
  let p2 := RustCode.my_function 2 false in
  let p3 := RustCode.method_example p1 p2 in
  p3.(RustCode.field1) = 5.
Proof.
  simpl.
  rewrite Z.add_3_2.
  reflexivity.
Qed.