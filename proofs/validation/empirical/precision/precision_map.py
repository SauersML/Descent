#!/usr/bin/env python3
"""Precision map: float64 evaluation of corpus closed forms against a 60-digit
reference, with the failing regions pinned so a rewrite cannot reintroduce a
catastrophic cancellation silently.

    python3 proofs/validation/empirical/precision/precision_map.py
    python3 proofs/validation/empirical/precision/precision_map.py --map

Needs `mpmath`, which is why this is NOT in the required set (see the exclusion
buckets at the foot of .github/workflows/prover.yml). It is written to gate
anyway if it ever is wired up: it exits nonzero on a NEW failing formula and on
a pinned failure that becomes clean. It never prints findings and exits 0 --
that is the failure mode the workflow calls out for check_ranges.py.

THE MEASUREMENT, and the trap it took to get right.

Every relative error below compares a float64 evaluation against mpmath at 60
digits with the ARGUMENTS ROUNDED TO FLOAT64 FIRST, then lifted to mpf. Feeding
the reference the un-rounded sweep value evaluates the two formulas at DIFFERENT
POINTS, and near a singularity the input-representation gap swamps the
formula's own conditioning. A first pass without this correction reported
ldWhiteningGain, ldHardEdge, ldPrecisionTrace, hudsonFst and oneMinusRatio as
catastrophically unstable; all five are clean. The tell-tale was the naive form
and a hand-stabilised form reporting the SAME worst error -- an instrument
measuring its own input. Every candidate here therefore carries a stable
competitor where one exists, precisely so that signature stays visible.

WHY THIS IS WORTH PINNING. The corpus's bodies are correct over the reals; a
body and its algebraically stable rewrite are equal as mathematics. What differs
is what a program computing them gets. Two provably equal bodies are not two
equally usable programs, and the equality theorem is exactly what makes the
difference invisible to every other checker in this directory.
"""

import math
import sys
import itertools

try:
    import mpmath as mp
except ImportError:                                          # pragma: no cover
    print("precision_map: mpmath not installed; this instrument is not in the "
          "required set. Install mpmath to run it.")
    sys.exit(0)

mp.mp.dps = 60
TOL = 1e-6


def logspace(lo, hi, n):
    return [mp.mpf(10) ** (lo + (hi - lo) * i / (n - 1)) for i in range(n)]


def sweep(f64, fexact, grid):
    """Return (worst relative error, worst args, n_bad, n_total)."""
    worst, wargs, nbad, ntot = -1.0, None, 0, 0
    for args in grid:
        a64 = [float(x) for x in args]
        try:
            got = f64(*a64)
        except (ZeroDivisionError, ValueError, OverflowError):
            got = float("nan")
        try:
            exact = fexact(*[mp.mpf(x) for x in a64])
        except (ZeroDivisionError, ValueError):
            continue
        if exact == 0:
            continue
        ntot += 1
        if not math.isfinite(got):
            rel = float("inf")
        else:
            rel = float(abs(mp.mpf(got) - exact) / abs(exact))
        if rel > TOL:
            nbad += 1
        if rel > worst:
            worst, wargs = rel, a64
    return worst, wargs, nbad, ntot


# ---------------------------------------------------------------------------
# CANDIDATES.  (name, float64 body, exact body, grid, stable_competitor|None)
# ---------------------------------------------------------------------------

_DECAYS = [1 - x for x in logspace(-14, -1, 14)]
_ANGLES = logspace(-14, 0, 15) + [mp.mpf("0.5"), mp.mpf(1), mp.pi / 2, mp.pi]
_KERNEL_GRID = list(itertools.product(_DECAYS, _ANGLES))

_FST_PAIRS = [(p, p + d)
              for p in [mp.mpf("0.01"), mp.mpf("0.1"), mp.mpf("0.3"),
                        mp.mpf("0.5")]
              for d in logspace(-14, -2, 13)]

_KL_PAIRS = [(p, p + d)
             for p in [mp.mpf("0.001"), mp.mpf("0.1"), mp.mpf("0.5"),
                       mp.mpf("0.9")]
             for d in logspace(-14, -2, 13)]

_LAMTAU = [(x,) for x in logspace(-18, 1, 20)]

_MOMENTS = ([(s ** 2, 3 * s ** 4 * (1 + d))
             for s in [mp.mpf(1), mp.mpf(10), mp.mpf("0.1")]
             for d in logspace(-16, -1, 16)])


def _nei_naive(p1, p2):
    return 1 - (p1 * (1 - p1) + p2 * (1 - p2)) / (2 * ((p1 + p2) / 2)
                                                  * (1 - (p1 + p2) / 2))


def _nei_stable(p1, p2):
    pbar = (p1 + p2) / 2
    return (p1 - p2) ** 2 / (4 * pbar * (1 - pbar))


CANDIDATES = [
    ("Calibrator.neiGst",
     _nei_naive, _nei_naive, _FST_PAIRS,
     ("Calibrator.neiGstFromFrequencies", _nei_stable)),

    ("Calibrator.ldKernelSymbol",
     lambda d, a: (1 - d * d) / (1 - 2 * d * math.cos(a) + d * d),
     lambda d, a: (1 - d ** 2) / (1 - 2 * d * mp.cos(a) + d ** 2),
     _KERNEL_GRID,
     ("ldKernelSymbol_eq_halfAngle",
      lambda d, a: ((1 - d) * (1 + d))
      / ((1 - d) ** 2 + 4 * d * math.sin(a / 2) ** 2))),

    ("Calibrator.bernoulliKLReal",
     lambda p, q: p * math.log(p / q) + (1 - p) * math.log((1 - p) / (1 - q)),
     lambda p, q: p * mp.log(p / q) + (1 - p) * mp.log((1 - p) / (1 - q)),
     _KL_PAIRS, None),

    ("Calibrator.myopiaPrice",
     lambda x: (1 - math.exp(-x)) ** 2,
     lambda x: (1 - mp.e ** (-x)) ** 2,
     _LAMTAU,
     ("expm1 form", lambda x: math.expm1(-x) ** 2)),

    ("Calibrator.fourthCumulantFromMoments",
     lambda m2, m4: m4 - 3 * m2 * m2,
     lambda m2, m4: m4 - 3 * m2 ** 2,
     _MOMENTS, None),

    # Survivors, carried so that a rewrite which BREAKS one is caught.
    ("Calibrator.hudsonFst",
     lambda p1, p2: (p1 - p2) ** 2 / (p1 * (1 - p2) + p2 * (1 - p1)),
     lambda p1, p2: (p1 - p2) ** 2 / (p1 * (1 - p2) + p2 * (1 - p1)),
     _FST_PAIRS, None),

    ("Calibrator.ldWhiteningGain",
     lambda d: (1 + d * d) / (1 - d * d),
     lambda d: (1 + d ** 2) / (1 - d ** 2),
     [(d,) for d in _DECAYS], None),

    ("Calibrator.ldHardEdge",
     lambda d: (1 - d) / (1 + d),
     lambda d: (1 - d) / (1 + d),
     [(d,) for d in _DECAYS], None),
]

# ---------------------------------------------------------------------------
# PINNED FAILING REGIONS.  Measured at commit 0449db90.  A candidate absent
# here must be clean; a candidate present here must still fail, or the pin is
# stale and the entry (and the docstring warning it justifies) should go.
# ---------------------------------------------------------------------------

KNOWN_FAILURES = {
    "Calibrator.neiGst": "1 - H_S/H_T cancels as p1 -> p2; the docstring warning "
                         "on the definition and the DOMAIN note on "
                         "refs.fst_nei_gst both cite this measurement.",
    "Calibrator.ldKernelSymbol": "Poisson divisor rounds to exactly zero near "
                                 "the singularity; ldKernelSymbol_eq_halfAngle "
                                 "is the stable evaluation.",
    "Calibrator.bernoulliKLReal": "cancellation is BETWEEN the two log terms, "
                                  "so log1p does not rescue it; recorded as a "
                                  "domain restriction on the definition.",
    "Calibrator.myopiaPrice": "1 - exp(-lam*tau) at short horizons; expm1 fixes "
                              "it, but Mathlib has no Real.expm1 so the Lean "
                              "body keeps this form and carries the warning.",
    "Calibrator.fourthCumulantFromMoments":
        "irreducible in its own arguments: the cancellation is exactly at the "
        "Gaussian null the cumulant exists to test. The consumer must use k4 "
        "from centered data, not this body.",
}


def main(argv):
    show_map = "--map" in argv
    findings = []
    rows = []
    for name, f64, fexact, grid, competitor in CANDIDATES:
        worst, wargs, nbad, ntot = sweep(f64, fexact, grid)
        fails = worst > TOL
        rows.append((name, worst, nbad, ntot, fails, competitor, grid, fexact))
        if fails and name not in KNOWN_FAILURES:
            findings.append(
                f"NEW PRECISION LOSS: {name} exceeds {TOL:g} relative error in "
                f"{nbad}/{ntot} cells, worst {worst:.3e} at "
                + ", ".join(f"{a:.6g}" for a in (wargs or []))
                + ". Either rewrite the body in a stable algebraic form, or "
                  "restrict its domain in the Lean statement and pin it here "
                  "with the reason.")
        if not fails and name in KNOWN_FAILURES:
            findings.append(
                f"STALE PIN: {name} is pinned as precision-losing but is now "
                f"clean (worst {worst:.3e}). If the body was stabilised, remove "
                f"the pin AND the numerical warning in its docstring, which now "
                f"describes something that is not true.")

    print(f"precision map: {len(CANDIDATES)} formulas, mpmath dps="
          f"{mp.mp.dps}, tolerance {TOL:g}, "
          f"{len(KNOWN_FAILURES)} pinned failing regions.")
    if show_map:
        print(f"\n{'formula':<44}{'worst rel err':>14}{'bad/total':>12}  status")
        for name, worst, nbad, ntot, fails, competitor, grid, fexact in rows:
            status = ("PINNED" if name in KNOWN_FAILURES
                      else ("FAIL" if fails else "clean"))
            print(f"{name:<44}{worst:14.3e}{f'{nbad}/{ntot}':>12}  {status}")
            if competitor is not None:
                cname, cfn = competitor
                cw, _, cbad, ctot = sweep(cfn, fexact, grid)
                print(f"  competitor {cname:<32}{cw:14.3e}"
                      f"{f'{cbad}/{ctot}':>12}  stable form")

    if findings:
        print(f"\n{len(findings)} FINDING(S):\n")
        for f in findings:
            print("  " + f)
        return 1
    print("no new precision loss; every pinned failing region still fails.")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
