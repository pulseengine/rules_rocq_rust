#!/usr/bin/env python3
"""Runs `Print Assumptions` on every declaration in a rocq_library target and
fails if anything beyond an explicit allowlist is load-bearing (issues #45, #57).

A proof that is green but rests on an `Admitted` obligation or a project-local
`Axiom` is exactly a vacuous verification -- the guarantee is not enforced on
the path that executes. Coq computes the transitive closure natively:
`Print Assumptions thm.` prints `Closed under the global context` for a clean
theorem, or an `Axioms:` block naming everything it depends on (an `Admitted`
proof shows up as an axiom named after the theorem itself).

Declarations are enumerated from the COMPILED module, not from the source
text: `Search _ inside <module>.` lists every constant, inductive and
constructor the kernel accepted, including `Example`, `Definition ... Admitted.`,
`#[local]`/`Local` forms, `Program` constants, nested modules and top-level
`Axiom`s. An earlier version matched six source keywords with a regex and
returned 0 when the regex found nothing, so a file of only `Example`/`Axiom`
declarations passed without coqc ever running (#57). An empty enumeration is
now a failure.

Each query's output goes to its own file via `Redirect`, so one query's output
can never be attributed to another declaration.

Scope: flat targets only (module path resolved as `<logical_prefix>.<basename
of the .v file, minus extension>`), matching every current rocq_library/
gappa_proof/rocq_interval_proof consumer in this repo.
"""
import argparse
import json
import os
import re
import subprocess
import sys
import tempfile

_CLEAN = "Closed under the global context"

# A `Search` result line: "<qualid>: <type>". Rocq identifiers may be
# Unicode (`α_bad`), so the name is any run of non-space, non-colon
# characters. Continuation lines of a wrapped type start with whitespace and
# are skipped; any other top-level line is unparsed and fails the check.
_SEARCH_LINE_RE = re.compile(r"^([^\s:]+)\s*:(?:\s|$)")

_PREAMBLE = [
    "Set Printing Width 100000.",
    # Search hides these name patterns by default; an Admitted lemma named
    # Private_foo would otherwise never be checked.
    'Remove Search Blacklist "_subproof" "_subterm" "Private_".',
]


def parse_search_output(text):
    """Parse a `Search` output.

    Returns (names, unparsed): declaration names deduplicated in order, and
    every non-indented, non-empty line that did not parse. The caller fails on
    a non-empty `unparsed` -- a line the parser cannot read is a declaration
    that would otherwise go unchecked.
    """
    names = []
    unparsed = []
    seen = set()
    for line in text.splitlines():
        if not line.strip() or line[0].isspace():
            continue
        m = _SEARCH_LINE_RE.match(line)
        if not m:
            unparsed.append(line)
        elif m.group(1) not in seen:
            seen.add(m.group(1))
            names.append(m.group(1))
    return names, unparsed


def parse_assumptions(text):
    """Parse one `Print Assumptions` output. Returns (is_clean, [entries]).

    Entries under `Axioms:` that look like `name : type` contribute `name`
    (matchable against the allowlist). Any other line -- e.g. `foo is assumed
    to be guarded.`, or a line under another section header -- is kept whole,
    prefixed with its section, so it cannot match an allowlist entry by accident.
    """
    stripped = text.strip()
    if stripped == _CLEAN:
        return True, []
    if not stripped:
        return False, ["<empty Print Assumptions output>"]
    entries = []
    section = None
    for line in text.splitlines():
        if not line.strip() or line[0].isspace():
            continue
        if line.endswith(":") and " : " not in line:
            section = line[:-1]
            continue
        if section == "Axioms" and " : " in line:
            entries.append(line.split(" : ", 1)[0].strip())
        else:
            entries.append("[{}] {}".format(section or "?", line.strip()))
    if not entries:
        entries.append("<unparsed Print Assumptions output: {!r}>".format(stripped[:200]))
    return False, entries


def run_coqc(coqc, qflags, driver_path, outdir):
    cmd = [coqc, "-q", "-output-directory", outdir]
    for qspec in qflags:
        physical, logical = qspec.split(":", 1)
        cmd += ["-Q", physical, logical]
    cmd.append(driver_path)
    return subprocess.run(cmd, capture_output=True, text=True)


def driver_failed(proc, what):
    sys.stderr.write(proc.stdout)
    sys.stderr.write(proc.stderr)
    sys.stderr.write(
        "\nassumptions_check: {} driver failed to compile -- the generated "
        "Require Import / names didn't resolve. This is a build problem, not "
        "an axiom finding. Check --qflag / --source.\n".format(what)
    )
    return 1


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

    modules = []
    for src_spec in args.source:
        src_path, logical_prefix = src_spec.split(":", 1)
        module_basename = os.path.basename(src_path)[: -len(".v")]
        module_path = "{}.{}".format(logical_prefix, module_basename) if logical_prefix else module_basename
        if module_path not in modules:
            modules.append(module_path)

    if not modules:
        sys.stderr.write("assumptions_check: FAILED -- no source modules in deps; nothing would be checked.\n")
        return 1

    requires = ["Require Import {}.".format(m) for m in modules]
    workdir = tempfile.mkdtemp(prefix="assumptions_check_")

    # Pass 1: enumerate declarations from the compiled modules.
    enum_driver = os.path.join(workdir, "enumerate.v")
    with open(enum_driver, "w") as f:
        lines = requires + _PREAMBLE
        for i, m in enumerate(modules):
            lines.append('Redirect "decls_{}" Search _ inside {}.'.format(i, m))
        f.write("\n".join(lines) + "\n")
    proc = run_coqc(args.coqc, args.qflag, enum_driver, workdir)
    if proc.returncode != 0:
        return driver_failed(proc, "enumeration")

    all_names = []
    for i in range(len(modules)):
        out = os.path.join(workdir, "decls_{}.out".format(i))
        if not os.path.exists(out):
            sys.stderr.write("assumptions_check: FAILED -- coqc wrote no Search output for {}.\n".format(modules[i]))
            return 1
        with open(out) as f:
            names, unparsed = parse_search_output(f.read())
        if unparsed:
            sys.stderr.write(
                "assumptions_check: FAILED -- unparsed Search output for {}; "
                "these declarations would go unchecked:\n".format(modules[i])
            )
            for line in unparsed:
                sys.stderr.write("  {}\n".format(line))
            return 1
        for name in names:
            if name not in all_names:
                all_names.append(name)

    if not all_names:
        report = {"declarations_checked": 0, "theorems": {}}
        with open(args.report_out, "w") as f:
            json.dump(report, f, indent=2)
        with open(args.driver_out, "w") as f:
            f.write("\n".join(requires) + "\n")
        sys.stderr.write(
            "assumptions_check: FAILED -- found no declarations in {}. "
            "Refusing to pass a target that was never measured.\n".format(", ".join(modules))
        )
        return 1

    # Pass 2: one Print Assumptions per declaration, each redirected to its
    # own file.
    driver_lines = requires + _PREAMBLE
    for i, name in enumerate(all_names):
        driver_lines.append('Redirect "pa_{}" Print Assumptions {}.'.format(i, name))
    with open(args.driver_out, "w") as f:
        f.write("\n".join(driver_lines) + "\n")
    proc = run_coqc(args.coqc, args.qflag, args.driver_out, workdir)
    if proc.returncode != 0:
        return driver_failed(proc, "Print Assumptions")

    report = {"declarations_checked": len(all_names), "theorems": {}}
    violations = []
    for i, name in enumerate(all_names):
        out = os.path.join(workdir, "pa_{}.out".format(i))
        if os.path.exists(out):
            with open(out) as f:
                is_clean, axioms = parse_assumptions(f.read())
        else:
            is_clean, axioms = False, ["<no Print Assumptions output>"]
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
            "as an axiom named after the declaration itself.\n"
        )
        return 1

    with open(args.marker_out, "w") as f:
        f.write("{} declaration(s) checked, all clean or explicitly allowed\n".format(len(all_names)))
    return 0


if __name__ == "__main__":
    sys.exit(main())
