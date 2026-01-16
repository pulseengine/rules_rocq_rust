(** Basic theorems for rocq_integration example *)

Require Import Arith.
Require Import List.

(** Theorem 1: Simple arithmetic property *)
Theorem theorem_1: forall n m : nat, n + m = m + n.
Proof.
  intros n m.
  induction n as [| n' IHn'].
  - rewrite Nat.add_0_r.
    rewrite Nat.add_0_l.
    reflexivity.
  - rewrite Nat.add_succ_r.
    rewrite <- IHn'.
    rewrite Nat.add_succ_r.
    rewrite Nat.add_associative.
    reflexivity.
Qed.

(** Theorem 2: List length property *)
Theorem theorem_2: forall (A : Type) (l1 l2 : list A),
  length (l1 ++ l2) = length l1 + length l2.
Proof.
  intros A l1.
  induction l1 as [| x l1' IHl1'].
  - simpl. rewrite Nat.add_0_r. reflexivity.
  - simpl. rewrite IHl1'. rewrite Nat.add_succ_r. reflexivity.
Qed.

(** Proof 1: Alternative proof of theorem_1 *)
Lemma proof_1: forall n m : nat, n + m = m + n.
Proof.
  intros n m.
  rewrite Nat.add_comm.
  reflexivity.
Qed.

(** Proof 2: Proof using theorem_1 *)
Lemma proof_2: forall n m p : nat, (n + m) + p = n + (m + p).
Proof.
  intros n m p.
  rewrite Nat.add_associative.
  reflexivity.
Qed.