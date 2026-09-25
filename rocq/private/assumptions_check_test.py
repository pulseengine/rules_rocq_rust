#!/usr/bin/env python3
"""Unit tests for assumptions_check.py's parsing logic (issue #45).

Grounded in real `coqc` output, captured empirically before this script was
written:

    Theorem clean_thm : 1 + 1 = 2.
    Proof. reflexivity. Qed.
    Axiom sneaky_axiom : False.
    Theorem dirty_thm : 1 + 1 = 2.
    Proof. destruct sneaky_axiom. Qed.
    Theorem admitted_thm : 2 + 2 = 5.
    Proof. Admitted.
    Print Assumptions clean_thm.
    Print Assumptions dirty_thm.
    Print Assumptions admitted_thm.

produces exactly:

    Closed under the global context
    Axioms:
    sneaky_axiom : False
    Axioms:
    admitted_thm : 2 + 2 = 5

confirming an Admitted proof surfaces as an axiom named after the theorem
itself -- the load-bearing assumption this whole check rests on.
"""
import sys
import unittest

sys.path.insert(0, __file__.rsplit("/", 1)[0])
from assumptions_check import extract_theorem_names, parse_print_assumptions_output  # noqa: E402


REAL_COQC_OUTPUT = (
    "Closed under the global context\n"
    "Axioms:\n"
    "sneaky_axiom : False\n"
    "Axioms:\n"
    "admitted_thm : 2 + 2 = 5\n"
)


class ParsePrintAssumptionsTest(unittest.TestCase):
    def test_real_captured_output(self):
        names = ["clean_thm", "dirty_thm", "admitted_thm"]
        results = parse_print_assumptions_output(REAL_COQC_OUTPUT, names)
        self.assertEqual(results["clean_thm"], (True, []))
        self.assertEqual(results["dirty_thm"], (False, ["sneaky_axiom"]))
        self.assertEqual(results["admitted_thm"], (False, ["admitted_thm"]))

    def test_multiple_axioms_in_one_block(self):
        output = "Axioms:\nfoo : nat\nbar : bool -> Prop\n"
        results = parse_print_assumptions_output(output, ["thm"])
        self.assertEqual(results["thm"], (False, ["foo", "bar"]))

    def test_clean_only(self):
        output = "Closed under the global context\n" * 3
        names = ["a", "b", "c"]
        results = parse_print_assumptions_output(output, names)
        for n in names:
            self.assertEqual(results[n], (True, []))


class ExtractTheoremNamesTest(unittest.TestCase):
    def test_extracts_all_named_forms(self):
        import tempfile
        import os

        src = (
            "Theorem foo : True.\nProof. exact I. Qed.\n\n"
            "Lemma bar : True.\nProof. exact I. Qed.\n\n"
            "Corollary baz : True.\nProof. exact I. Qed.\n\n"
            "(* not a theorem *) Definition quux := 1.\n"
        )
        fd, path = tempfile.mkstemp(suffix=".v")
        try:
            with os.fdopen(fd, "w") as f:
                f.write(src)
            names = extract_theorem_names(path)
        finally:
            os.remove(path)
        self.assertEqual(names, ["foo", "bar", "baz"])


if __name__ == "__main__":
    unittest.main()
