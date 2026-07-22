(* Minimal smoke test for the Coq-Interval environment (DD-003, #43).
   Proves this toolchain can actually load and use Interval.Tactic, not just
   fetch the coq-interval package -- FEAT-001's approximation-error layer. *)

Require Import Reals.
Require Import Interval.Tactic.

Goal (1 + 1 <= 3)%R.
Proof.
  interval.
Qed.
