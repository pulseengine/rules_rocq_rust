(* A named Coq-Interval lemma, audited by rocq_assumptions_test (#66). *)

Require Import Reals.
Require Import Interval.Tactic.

Open Scope R_scope.

Lemma sqrt2_bound : 1.414 <= sqrt 2 <= 1.415.
Proof.
  interval.
Qed.
