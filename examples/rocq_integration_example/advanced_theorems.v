(** Advanced theorems for rocq_integration example *)

Require Import Arith.
Require Import List.
Require Import ZArith.

(** Theorem 3: Property of multiplication *)
Theorem theorem_3: forall n m p : nat, n * (m + p) = n * m + n * p.
Proof.
  intros n m p.
  induction n as [| n' IHn'].
  - rewrite Nat.mul_0_r. rewrite Nat.add_0_r. rewrite Nat.mul_0_r. reflexivity.
  - rewrite Nat.mul_succ_r. rewrite Nat.add_succ_r.
    rewrite IHn'. rewrite Nat.add_associative.
    rewrite Nat.add_comm. reflexivity.
Qed.

(** Theorem 4: Property of list operations *)
Theorem theorem_4: forall (A : Type) (l : list A) (x : A),
  length (x :: l) = S (length l).
Proof.
  intros A l x.
  simpl. reflexivity.
Qed.

(** Proof 3: Proof using theorem_3 *)
Lemma proof_3: forall n m : nat, n * (m + 0) = n * m.
Proof.
  intros n m.
  rewrite theorem_3.
  rewrite Nat.add_0_r.
  rewrite Nat.mul_0_r.
  rewrite Nat.add_0_r.
  reflexivity.
Qed.

(** Proof 4: Complex proof involving multiple theorems *)
Lemma proof_4: forall n m p q : nat,
  (n + m) * (p + q) = n * p + n * q + m * p + m * q.
Proof.
  intros n m p q.
  rewrite theorem_3.
  rewrite Nat.add_comm.
  rewrite theorem_3.
  rewrite Nat.add_associative.
  rewrite Nat.add_comm.
  reflexivity.
Qed.