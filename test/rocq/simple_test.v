(** Simple test file to verify Coq syntax *)

(** This file tests that basic Coq syntax is recognized *)

(** A simple theorem *)
Theorem test_theorem : 1 = 1.
Proof.
  reflexivity.
Qed.

(** Another simple theorem *)
Theorem test_theorem2 : forall n:nat, n = n.
Proof.
  intros n. reflexivity.
Qed.