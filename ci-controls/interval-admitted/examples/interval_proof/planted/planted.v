(* Planted negative control for #66: a clean interval lemma next to an
   Admitted one. The audit must name planted_admitted and fail, even with the
   full interval trusted base allowed. *)

Require Import Reals.
Require Import Interval.Tactic.

Open Scope R_scope.

Lemma planted_clean : 1.414 <= sqrt 2 <= 1.415.
Proof.
  interval.
Qed.

Lemma planted_admitted : sqrt 2 <= 1.
Admitted.
