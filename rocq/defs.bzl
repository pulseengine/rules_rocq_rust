"""Public API for Rocq compilation rules."""

load("//rocq/private:rocq.bzl", _rocq_interval_proof = "rocq_interval_proof", _rocq_library = "rocq_library", _rocq_proof_test = "rocq_proof_test")

rocq_library = _rocq_library
rocq_proof_test = _rocq_proof_test
rocq_interval_proof = _rocq_interval_proof

def gappa_proof(name, src, deps = [], extra_flags = [], visibility = None):
    """Runs `gappa -Bcoq` on a `.gappa` source and kernel-checks the result.

    Gappa establishes a floating-point rounding-error bound outside Rocq and
    emits a Flocq/Rocq proof term as its certificate. Per rivet CC-002, that
    certificate is never trusted on its own: this macro always compiles the
    emitted proof term with `rocq_library`, so the target fails exactly like
    any other Rocq proof if the kernel rejects what Gappa produced.

    Args:
        name: name of the resulting rocq_library target.
        src: the `.gappa` input file.
        deps: rocq_library deps for the generated proof (e.g. other rocq_library
            targets); Flocq and Gappa's own support library are already
            available toolchain-wide and don't need to be listed here.
        extra_flags: extra flags forwarded to coqc, as in rocq_library.
        visibility: visibility for the resulting rocq_library target.
    """
    generated = name + "_generated.v"
    native.genrule(
        name = name + "_gen",
        srcs = [src],
        outs = [generated],
        cmd = "$(location @rocq_gappa_bin//:gappa) -Bcoq $(location %s) > $@" % src,
        tools = ["@rocq_gappa_bin//:gappa"],
    )
    rocq_library(
        name = name,
        srcs = [generated],
        deps = deps,
        extra_flags = extra_flags,
        visibility = visibility,
    )
