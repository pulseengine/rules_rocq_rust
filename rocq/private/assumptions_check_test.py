#!/usr/bin/env python3
"""Tests for assumptions_check.py (issues #45, #57).

The parser tests use coqc 9.0.1 output captured on 2026-11-13. The
integration tests run the real checker against real coqc on planted sources;
they need `COQC` (path to coqc). Without it they skip, unless
`ASSUMPTIONS_REQUIRE_COQC=1` is set, in which case a missing coqc is a
failure -- CI sets it so the negative control cannot silently skip.
"""
import json
import os
import shutil
import subprocess
import sys
import tempfile
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from assumptions_check import parse_assumptions, parse_search_output  # noqa: E402

CHECKER = os.path.join(HERE, "assumptions_check.py")


class ParseSearchOutputTest(unittest.TestCase):
    def test_captured_output(self):
        # `Search _ inside P.T.` after `Require Import P.T.`, nested module and
        # Local declarations print qualified.
        text = (
            "Inner.inner_bad: False\n"
            "cheat: False\n"
            "T.l1: False\n"
            "ok: True\n"
            "usev: nat -> nat\n"
            "d1: 1 = 2\n"
        )
        self.assertEqual(
            parse_search_output(text),
            ["Inner.inner_bad", "cheat", "T.l1", "ok", "usev", "d1"],
        )

    def test_skips_continuation_lines_and_dedups(self):
        text = "foo: forall n : nat,\n  n = n\nfoo: forall n : nat, n = n\nbar : True\n"
        self.assertEqual(parse_search_output(text), ["foo", "bar"])

    def test_empty(self):
        self.assertEqual(parse_search_output(""), [])


class ParseAssumptionsTest(unittest.TestCase):
    def test_clean(self):
        self.assertEqual(parse_assumptions("Closed under the global context\n"), (True, []))

    def test_admitted_and_axiom(self):
        self.assertEqual(
            parse_assumptions("Axioms:\nsneaky_axiom : False\nadmitted_thm : 2 + 2 = 5\n"),
            (False, ["sneaky_axiom", "admitted_thm"]),
        )

    def test_guard_assumption_is_not_allowlistable_by_name(self):
        clean, entries = parse_assumptions("Axioms:\nU.loop is assumed to be guarded.\n")
        self.assertFalse(clean)
        self.assertEqual(entries, ["[Axioms] U.loop is assumed to be guarded."])

    def test_empty_output_is_a_violation(self):
        clean, entries = parse_assumptions("")
        self.assertFalse(clean)
        self.assertTrue(entries)

    def test_unknown_output_is_a_violation(self):
        clean, entries = parse_assumptions("something unexpected\n")
        self.assertFalse(clean)
        self.assertTrue(entries)


_PLANTED = """\
Example ex1 : False. Admitted.
Definition d1 : 1 = 2. Admitted.
#[local] Lemma l1 : False. Admitted.
Local Theorem t1 : False. Admitted.
Axiom cheat : False.
"""

_CLEAN = """\
Theorem plus_n_O_example : forall n : nat, n + 0 = n.
Proof. intros n. induction n as [| n' IH]. - reflexivity. - simpl. rewrite IH. reflexivity. Qed.
"""

_CLEAN_PLUS_ONE_EXAMPLE = _CLEAN + "Example sneaky : False. Admitted.\n"


class RealCoqcTest(unittest.TestCase):
    def setUp(self):
        self.coqc = os.environ.get("COQC")
        if not self.coqc:
            if os.environ.get("ASSUMPTIONS_REQUIRE_COQC") == "1":
                self.fail("ASSUMPTIONS_REQUIRE_COQC=1 but COQC is not set")
            self.skipTest("COQC not set")
        self.tmp = tempfile.mkdtemp(prefix="assumptions_check_test_")
        os.mkdir(os.path.join(self.tmp, "M"))

    def tearDown(self):
        if hasattr(self, "tmp"):
            shutil.rmtree(self.tmp, ignore_errors=True)

    def check(self, name, source, allowed=()):
        mdir = os.path.join(self.tmp, "M")
        src = os.path.join(mdir, name + ".v")
        with open(src, "w") as f:
            f.write(source)
        subprocess.run([self.coqc, "-q", "-Q", mdir, "P", src], check=True)
        out = os.path.join(self.tmp, name)
        cmd = [
            sys.executable, CHECKER, "--coqc", self.coqc,
            "--qflag", mdir + ":P", "--source", src + ":P",
            "--driver-out", out + "_driver.v",
            "--report-out", out + ".json",
            "--marker-out", out + ".marker",
        ]
        for a in allowed:
            cmd += ["--allowed-axiom", a]
        proc = subprocess.run(cmd, capture_output=True, text=True)
        report = None
        if os.path.exists(out + ".json"):
            with open(out + ".json") as f:
                report = json.load(f)
        return proc, report

    def test_issue57_planted_file_fails(self):
        proc, report = self.check("Planted", _PLANTED)
        self.assertEqual(proc.returncode, 1, proc.stderr)
        self.assertEqual(report["declarations_checked"], 5)
        for name in ["ex1", "d1", "cheat"]:
            self.assertIn(name, proc.stderr)

    def test_clean_theorem_passes(self):
        proc, report = self.check("Clean", _CLEAN)
        self.assertEqual(proc.returncode, 0, proc.stderr)
        self.assertEqual(report["theorems"], {"plus_n_O_example": {"clean": True, "axioms": []}})

    def test_admitted_example_beside_clean_theorem_fails(self):
        proc, _ = self.check("Mixed", _CLEAN_PLUS_ONE_EXAMPLE)
        self.assertEqual(proc.returncode, 1, proc.stderr)
        self.assertIn("sneaky", proc.stderr)

    def test_empty_file_fails(self):
        proc, report = self.check("Empty", "(* nothing *)\n")
        self.assertEqual(proc.returncode, 1, proc.stderr)
        self.assertEqual(report["declarations_checked"], 0)

    def test_allowlist_lets_named_axioms_through(self):
        proc, _ = self.check(
            "Allowed", _PLANTED, allowed=["ex1", "d1", "Allowed.l1", "Allowed.t1", "cheat"]
        )
        self.assertEqual(proc.returncode, 0, proc.stderr)


if __name__ == "__main__":
    unittest.main()
