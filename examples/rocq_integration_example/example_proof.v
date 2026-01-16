(** Example proof for rocq_integration demonstration *)

Require Import Arith.
Require Import List.

(** Example theorem: Commutativity and associativity combined *)
Theorem example_theorem: forall n m p : nat,
  n + (m + p) = (p + m) + n.
Proof.
  intros n m p.
  (** Step 1: Apply associativity *)
  rewrite Nat.add_associative.
  (** Step 2: Apply commutativity to m + p *)
  rewrite Nat.add_comm.
  (** Step 3: Apply associativity again *)
  rewrite Nat.add_associative.
  (** Step 4: Apply commutativity to n + m *)
  rewrite Nat.add_comm.
  (** Step 5: Final simplification *)
  reflexivity.
Qed.

(** Example proof: Using the theorem *)
Lemma example_proof: forall a b c d : nat,
  a + (b + (c + d)) = ((d + c) + b) + a.
Proof.
  intros a b c d.
  (** Apply example_theorem to inner expression *)
  rewrite example_theorem.
  (** Apply associativity *)
  rewrite Nat.add_associative.
  (** Apply commutativity *)
  rewrite Nat.add_comm.
  (** Final simplification *)
  reflexivity.
Qed.