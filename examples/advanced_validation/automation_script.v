(** Proof automation script for advanced validation example *)

Require Import Arith Bool List.
Require Import CoqOfRust.Prelude.

(** Ltac automation tactics for common proof patterns *)

Ltac auto_arith := 
  try solve [intuition; omega];
  try solve [ring];
  try solve [field];
  try solve [lia].

Ltac auto_bool := 
  try solve [tauto];
  try solve [bool_correct].

Ltac auto_equality := 
  try solve [discriminate];
  try solve [injection; intros; subst; auto].

Ltac auto_induction := 
  try solve [induction 1; auto];
  try solve [induction 2; auto];
  try solve [functional induction; auto].

Ltac auto_rewrite := 
  try solve [rewrite <- H; auto];
  try solve [rewrite -> H; auto].

Ltac auto_unfold := 
  try solve [unfold H; auto];
  try solve [unfold H in *; auto].

Ltac auto_apply := 
  try solve [apply H; auto];
  try solve [apply H in X; auto].

Ltac auto_constructor := 
  try solve [constructor; auto];
  try solve [constructor 1; auto];
  try solve [constructor 2; auto].

Ltac auto_destruct := 
  try solve [destruct H; auto];
  try solve [destruct H as [x y]; auto].

Ltac auto_inversion := 
  try solve [inversion H; auto];
  try solve [inversion_clear H; auto].

Ltac auto_simpl := 
  try solve [simpl; auto];
  try solve [simpl in H; auto].

Ltac auto_case := 
  try solve [case H; auto];
  try solve [case_eq H; auto].

Ltac auto_rewrite_pred := 
  try solve [rewrite H; auto];
  try solve [rewrite <- H; auto].

Ltac auto_all := 
  auto_arith || auto_bool || auto_equality || auto_induction || 
  auto_rewrite || auto_unfold || auto_apply || auto_constructor || 
  auto_destruct || auto_inversion || auto_simpl || auto_case || 
  auto_rewrite_pred || auto.

(** Specialized tactics for Rust-like structures *)

Ltac rust_option_auto := 
  try solve [destruct H as [x|]; auto];
  try solve [destruct H as [x|]; auto_all].

Ltac rust_result_auto := 
  try solve [destruct H as [x|e]; auto];
  try solve [destruct H as [x|e]; auto_all].

Ltac rust_vec_auto := 
  try solve [induction H; auto];
  try solve [induction H; auto_all].

Ltac rust_struct_auto := 
  try solve [destruct H; auto];
  try solve [destruct H; auto_all].

(** High-level automation strategy *)

Ltac super_auto := 
  auto_all || 
  rust_option_auto || 
  rust_result_auto || 
  rust_vec_auto || 
  rust_struct_auto || 
  try solve [intros; auto_all].

(** Proof automation hints *)

Hint Resolve auto_arith auto_bool auto_equality auto_induction.
Hint Resolve auto_rewrite auto_unfold auto_apply auto_constructor.
Hint Resolve auto_destruct auto_inversion auto_simpl auto_case.
Hint Resolve rust_option_auto rust_result_auto rust_vec_auto rust_struct_auto.

(** Export automation tactics for use in other files *)

Module AutoTactics.
  Ltac export_auto := super_auto.
  Ltac export_auto_arith := auto_arith.
  Ltac export_auto_bool := auto_bool.
  Ltac export_rust_auto := rust_option_auto || rust_result_auto || rust_vec_auto || rust_struct_auto.
End AutoTactics.

(** Convenience tactics *)

Ltac solve_rust_proof := 
  try super_auto;
  try intros; super_auto;
  try unfold; super_auto;
  try destruct; super_auto;
  try induction; super_auto;
  try apply; super_auto.

(** End of automation script *)