(* Demonstrates the Print Assumptions gate (issue #45, REQ-004): a proof that
   depends on nothing but the kernel -- no Admitted, no project axioms. *)

Theorem plus_n_O_example : forall n : nat, n + 0 = n.
Proof.
  intros n.
  induction n as [| n' IH].
  - reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.
