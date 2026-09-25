#!/usr/bin/env python3
"""Runs `Print Assumptions` on every theorem in a rocq_library target and fails
if anything beyond an explicit allowlist is load-bearing (issue #45).

A proof that is green but rests on an `Admitted` obligation or a project-local
`Axiom` is exactly a vacuous verification -- the guarantee is not enforced on
the path that executes. Coq computes the transitive closure natively:
`Print Assumptions thm.` prints `Closed under the global context` for a clean
theorem, or an `Axioms:` block naming everything it depends on (an `Admitted`
proof shows up as an axiom named after the theorem itself -- verified
empirically, not assumed, before this script was written).

Scope: flat targets only (theorem names resolved as `<logical_prefix>.<basename
of the .v file, minus extension>`), matching every current rocq_library/
gappa_proof/rocq_interval_proof consumer in this repo. A nested multi-file
library (like RocqOfRust/lib/lib.v) is out of scope for now -- extend the
module-path derivation below if one needs this check.
"""
import argparse
import json
import re
import subprocess
import sys

_THEOREM_RE = re.compile(
    r"^\s*(?:Theorem|Lemma|Corollary|Fact|Remark|Proposition)\s+([A-Za-z_][A-Za-z0-9_']*)",
    re.MULTILINE,
)

_CLEAN = "Closed under the global context"


def extract_theorem_names(source_path):
    with open(source_path, "r", errors="ignore") as f:
        text = f.read()
    return _THEOREM_RE.findall(text)


def parse_print_assumptions_output(output, names):
    """Split coqc's stdout into one result per `Print Assumptions <name>.`
    query, in the order issued. Returns {name: (is_clean, [axiom_names])}.
    """
    results = {}
    # Each query's output is either exactly _CLEAN, or "Axioms:\n<name> : <ty>\n"*
    # possibly interleaved with warnings we don't emit (we compile with -q).
    # Split on the two possible block headers, keeping the split effective
    # across repeated invocations.
    chunks = re.split(r"(?=" + re.escape(_CLEAN) + r"|Axioms:)", output)
    chunks = [c for c in chunks if c.strip()]
    idx = 0
    for chunk in chunks:
        if idx >= len(names):
            break
        name = names[idx]
        if chunk.startswith(_CLEAN):
            results[name] = (True, [])
        elif chunk.startswith("Axioms:"):
            axiom_lines = chunk.splitlines()[1:]
            axioms = []
            for line in axiom_lines:
                line = line.strip()
                if not line:
                    continue
                # "name : type" -- take the name, stop at the first top-level ':'.
                axioms.append(line.split(" : ", 1)[0].strip())
            results[name] = (False, axioms)
        else:
            continue
        idx += 1
    return results


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--coqc", required=True)
    ap.add_argument("--qflag", action="append", default=[], help="physical:logical pairs for -Q")
    ap.add_argument("--source", action="append", default=[], help="path:logical_prefix pairs")
    ap.add_argument("--allowed-axiom", action="append", default=[])
    ap.add_argument("--driver-out", required=True)
    ap.add_argument("--report-out", required=True)
    ap.add_argument("--marker-out", required=True)
    args = ap.parse_args()

    allowed = set(args.allowed_axiom)

    all_names = []
    driver_lines = []
    seen_prefixes = set()
    for src_spec in args.source:
        src_path, logical_prefix = src_spec.split(":", 1)
        if logical_prefix not in seen_prefixes:
            seen_prefixes.add(logical_prefix)
        module_basename = src_path.rsplit("/", 1)[-1][: -len(".v")]
        module_path = "{}.{}".format(logical_prefix, module_basename) if logical_prefix else module_basename
        driver_lines.append("Require Import {}.".format(module_path))
        names = extract_theorem_names(src_path)
        all_names.extend(names)

    for name in all_names:
        driver_lines.append("Print Assumptions {}.".format(name))

    with open(args.driver_out, "w") as f:
        f.write("\n".join(driver_lines) + "\n")

    if not all_names:
        # No named theorems found -- nothing to check, but say so rather than
        # silently reporting success on a target this script never measured.
        report = {"target_had_no_named_theorems": True, "theorems": {}}
        with open(args.report_out, "w") as f:
            json.dump(report, f, indent=2)
        with open(args.marker_out, "w") as f:
            f.write("no named theorems found\n")
        return 0

    cmd = [args.coqc, "-q"]
    for qspec in args.qflag:
        physical, logical = qspec.split(":", 1)
        cmd += ["-Q", physical, logical]
    cmd += [args.driver_out]

    proc = subprocess.run(cmd, capture_output=True, text=True)
    # coqc's own kernel check already ran (that's the compile); a non-zero
    # exit here means the DRIVER failed to load the module, not that a proof
    # is vacuous -- a real build problem, not an assumptions finding.
    if proc.returncode != 0:
        sys.stderr.write(proc.stdout)
        sys.stderr.write(proc.stderr)
        sys.stderr.write(
            "\nassumptions_check: driver failed to compile -- this means the "
            "generated Require Import / theorem names didn't resolve, not "
            "that a proof depends on an axiom. Check --qflag / --source.\n"
        )
        return 1

    results = parse_print_assumptions_output(proc.stdout, all_names)

    report = {"target_had_no_named_theorems": False, "theorems": {}}
    violations = []
    for name in all_names:
        is_clean, axioms = results.get(name, (False, ["<Print Assumptions output not parsed>"]))
        report["theorems"][name] = {"clean": is_clean, "axioms": axioms}
        if is_clean:
            continue
        unlisted = [a for a in axioms if a not in allowed]
        if unlisted:
            violations.append((name, unlisted))

    with open(args.report_out, "w") as f:
        json.dump(report, f, indent=2)

    if violations:
        sys.stderr.write("assumptions_check: FAILED -- unlisted axioms/admitted obligations found:\n")
        for name, unlisted in violations:
            sys.stderr.write("  {}: {}\n".format(name, ", ".join(unlisted)))
        sys.stderr.write(
            "\nIf these are intentional, add them to allowed_axioms on the "
            "rocq_assumptions_test target. An Admitted proof shows up here "
            "as an axiom named after the theorem itself.\n"
        )
        return 1

    with open(args.marker_out, "w") as f:
        f.write("{} theorem(s) checked, all clean or explicitly allowed\n".format(len(all_names)))
    return 0


if __name__ == "__main__":
    sys.exit(main())
