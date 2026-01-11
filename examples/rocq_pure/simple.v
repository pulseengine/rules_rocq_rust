(** Simple Rocq proof example demonstrating basic functionality *)

Require Import Arith.

(** A simple theorem about natural numbers *)
Theorem plus_comm : forall n m : nat, n + m = m + n.
Proof.
  intros n m.
  induction n as [| n' IHn'].
  - (* Base case: n = 0 *) 
    simpl. rewrite <- plus_n_O. reflexivity.
  - (* Inductive case: n = S n' *) 
    simpl. rewrite IHn'. rewrite plus_n_Sm. reflexivity.
Qed.

(** Another simple theorem *) 
Theorem plus_assoc : forall n m p : nat, (n + m) + p = n + (m + p).
Proof.
  intros n m p. 
  induction n as [| n' IHn'].
  - (* Base case: n = 0 *) 
    simpl. rewrite plus_0_r. rewrite plus_0_r. reflexivity.
  - (* Inductive case: n = S n' *) 
    simpl. rewrite <- IHn'. rewrite plus_n_Sm. reflexivity.
Qed.

(** Example of using the theorems *) 
Lemma example_usage : forall a b c : nat, a + (b + c) = c + (a + b).
Proof.
  intros a b c.
  rewrite plus_assoc. 
  rewrite plus_comm with (n := a) (m := b).
  rewrite plus_comm with (n := (a + b)) (m := c).
  reflexivity.
Qed.