#!/usr/bin/env python3
"""Collapse detector for the AUC family: which of these names are one function?

WHY THIS EXISTS
    Four names in this family denoted one bit-identical function, and the
    consequence was not cosmetic: each name carried its own tests, so ONE
    function was validated four times and counted as four. A theorem was then
    stated across two of those names and proved by `rfl` -- `f x = f x` wearing
    two names -- while reading as "AUC is preserved under equal drift".

    Nothing in the corpus's instruments could see that. A range check confirms
    the output is a probability; it cannot notice that two probabilities are the
    same probability by construction. This script is the missing instrument, and
    it takes seconds.

METHOD
    Evaluate every definition of matching arity at random admissible points and
    report any pair whose maximum absolute spread is exactly zero. Bit-identical
    output across a random box is not proof of definitional equality, but it is
    the cheap screen that catches the case before someone writes a theorem on it.

THE TRAP THIS SCRIPT IS BUILT TO AVOID
    `equalVarianceGaussianAUCChart` is `if 1 <= r2 then 1 else
    equalVarianceGaussianAUCFromExplainedR2 r2`. On the interior it IS the other
    function, so a checker sampling only `r2 in [0,1)` reports a collapse that is
    not there and would demand a fix that destroys a deliberate boundary
    extension. The r2 grid below therefore straddles `r2 = 1` on purpose.

    This is the same discipline as putting a witness inside the excepted set: a
    difference that exists only on a boundary is invisible to any sample that
    avoids the boundary.
"""

import itertools
import json
import os
import sys

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
EXTRACT = os.path.abspath(os.path.join(HERE, "..", "..", "extract"))
sys.path.insert(0, EXTRACT)

# The generated tables are untracked by design (see any producer's header in
# validation/extract/). A missing table must stop this script with the command
# rather than let it start on a stale copy from another worktree.
try:
    import lean_defs as L  # noqa: E402
except ImportError as _exc:
    raise SystemExit(
        "auc_collapse_check: cannot import the generated table `lean_defs`.\n"
        "  looked in: %s\n"
        "  reason:    %s\n"
        "  These tables are DELIBERATELY NOT IN GIT -- regenerate them:\n"
        "      python3 validation/empirical/extract/emit.py\n"
        "  (about a minute; writes only inside your worktree)" % (EXTRACT, _exc))

OUT = os.path.join(HERE, "auc_collapse_check_results.json")

RNG = np.random.default_rng(20260803)


def safe(fn, *args):
    try:
        v = float(fn(*args))
        return v if np.isfinite(v) else None
    except Exception:
        return None


# Groups of same-arity AUC definitions, with an admissible sampler for each.
GROUPS = {
    "signal_noise": (
        ["gaussianAUCFromSignalVariance"],
        lambda n: list(zip(RNG.uniform(0.05, 3.0, n), RNG.uniform(0.05, 3.0, n))),
    ),
    "V_A_V_E_fst": (
        ["presentDayGaussianAUC",
         "presentDayEqualVarianceGaussianAUC",
         "targetGaussianAUCFromNeutralAFBenchmark",
         "targetExactGaussianAUCFromNeutralAFBenchmark"],
        lambda n: list(zip(RNG.uniform(0.05, 2.0, n),
                           RNG.uniform(0.05, 2.0, n),
                           RNG.uniform(0.0, 0.6, n))),
    ),
    # Straddles r2 = 1 deliberately: the Chart differs from the base only there.
    "r2": (
        ["equalVarianceGaussianAUCFromExplainedR2",
         "equalVarianceGaussianAUCChart"],
        lambda n: [(x,) for x in np.concatenate(
            [RNG.uniform(0.0, 0.95, n // 2), RNG.uniform(1.0, 1.6, n - n // 2)])],
    ),
    "snr": (
        ["equalVarianceGaussianAUCFromSNR"],
        lambda n: [(x,) for x in RNG.uniform(0.01, 20.0, n)],
    ),
}


def main():
    print("AUC FAMILY COLLAPSE CHECK")
    print("=" * 62)
    results = {}
    collapsed_pairs = []

    for gname, (names, sampler) in GROUPS.items():
        present = [n for n in names if hasattr(L, n)]
        missing = [n for n in names if not hasattr(L, n)]
        pts = sampler(8)
        table = {}
        for n in present:
            fn = getattr(L, n)
            vals = [safe(fn, *p) for p in pts]
            if any(v is None for v in vals):
                continue
            table[n] = np.array(vals, dtype=float)

        print("\n[%s]  %d definitions, %d sample points"
              % (gname, len(table), len(pts)))
        if missing:
            print("   not in the generated mirror (renamed since): %s"
                  % ", ".join(missing))

        for a, b in itertools.combinations(sorted(table), 2):
            spread = float(np.max(np.abs(table[a] - table[b])))
            verdict = "IDENTICAL" if spread == 0.0 else "distinct"
            print("   %-44s vs %-44s  max|d| = %.3e  %s"
                  % (a, b, spread, verdict))
            if spread == 0.0:
                collapsed_pairs.append({"group": gname, "a": a, "b": b})
        results[gname] = {n: list(map(float, v)) for n, v in table.items()}

    print("\n" + "=" * 62)
    if collapsed_pairs:
        print("COLLAPSED PAIRS (one function, two names):")
        for c in collapsed_pairs:
            print("   %s  ==  %s" % (c["a"], c["b"]))
        print("\nEach such pair inflates coverage: both names carry tests, one")
        print("function is validated twice, and a theorem stated across the pair")
        print("is rfl while reading as a claim about AUC.")
    else:
        print("No collapsed pairs found.")

    with open(OUT, "w") as fh:
        json.dump({"collapsed_pairs": collapsed_pairs, "values": results}, fh, indent=2)
    print("\nwrote %s" % OUT)
    return 0


if __name__ == "__main__":
    sys.exit(main())
