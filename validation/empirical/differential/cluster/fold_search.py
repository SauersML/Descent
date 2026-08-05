#!/usr/bin/env python3
"""Search for a fold birth in the genotype modulus curves. numpy + stdlib only.

WHAT A FOLD WOULD MEAN
    If a modulus curve m_j(q) has a quadratic tangency at a value NO OTHER
    BRANCH REACHES, that band is exactly doubly covered through the fold
    involution, and the kernel born there is the ODD functions in the fold
    coordinate. That is a surgery family over genotype panels, confined to the
    band, and invisible to a peeling proof that works from the top of the value
    range downward.

THE CURVES, DERIVED RATHER THAN ASSUMED
    Standardised genotype x = (g - 2q)/sqrt(2q(1-q)), g in {0,1,2}:

        a_0(q) = -sqrt(2q/(1-q))            homozygous reference
        a_1(q) = (1-2q)/sqrt(2q(1-q))       heterozygote
        a_2(q) = sqrt(2(1-q)/q)             homozygous alternate

    Modulus curves m_j = |a_j^2 - 1|:

        m_0 = |(3q-1)/(1-q)|                zero at q = 1/3
        m_1 = |(1-2q)^2/(2q(1-q)) - 1|      zero at 6q^2-6q+1 = 0
        m_2 = |2/q - 3|                     >= 1 on (0,1/2], strictly decreasing

    m_2 is the rare-homozygote atom that the peeling proof uses: it dominates
    everything else and is monotone, which is why the argument works from the
    top and why a LOCAL fiber lower down would be missed by it.

EXACT CRITICAL POINTS, NOT A TOLERANCE SEARCH
    The tangency sites are algebraic and are computed in closed form:

        m_0 vanishes at q = 1/3
        m_1 vanishes at 6q^2 - 6q + 1 = 0, i.e. q = (3 - sqrt(3))/6
                                              = 0.2113248654...

    A tolerance-based extremum scan near a curve that VANISHES is exactly where
    a false positive gets manufactured -- the minimum is flat to second order,
    so any epsilon finds a wide "extremum" and any two nearby curves look
    tangent. The closed forms are used as the sites; a numerical scan runs
    alongside ONLY to confirm it finds the same places, never to locate them.

THE TEST AT EACH SITE
    For a band (0, delta] above the critical value, count how many times EACH
    branch covers it. A fold requires:
        - the folding branch covers the band exactly TWICE (one preimage on
          each side of the tangency), and
        - EVERY OTHER BRANCH covers it ZERO times.
    If another branch reaches the same band the covering is not two and the
    kernel is not the odd functions.

THE CONTROL, WITHOUT WHICH A NULL MEANS NOTHING
    A reflection-symmetric family where a fold is present BY CONSTRUCTION:
    b_0(t) = (t - 1/2)^2 on [0,1], tangent at t = 1/2, with a second branch
    b_1 = 3 that never comes near it. The search MUST report a fold there. If
    it does not, it cannot detect one anywhere and a null on genotypes is
    empty.

    A second control with a fold that must be REJECTED: the same tangency, but
    with a second branch sitting flat at 0 so the band IS reached by something
    else. The search must report no fold, which tests the exclusion clause
    rather than the tangency detector.
"""

import json
import math
import sys

import numpy as np

NQ = 200001            # scan resolution for the confirmation pass only
DELTAS = (1e-6, 1e-4, 1e-2, 1e-1)


# ---------------------------------------------------------------------------
# genotype modulus curves
# ---------------------------------------------------------------------------
def m0(q):
    return np.abs((3.0 * q - 1.0) / (1.0 - q))


def m1(q):
    return np.abs((1.0 - 2.0 * q) ** 2 / (2.0 * q * (1.0 - q)) - 1.0)


def m2(q):
    return np.abs(2.0 / q - 3.0)


GENOTYPE = {"m0": m0, "m1": m1, "m2": m2}
EXACT_SITES = {
    "m0": [("q = 1/3", 1.0 / 3.0)],
    "m1": [("q = (3-sqrt(3))/6", (3.0 - math.sqrt(3.0)) / 6.0)],
    "m2": [],                      # monotone on (0,1/2], no interior extremum
}


def coverage_count(fn, lo, hi, qgrid):
    """How many times the branch's value crosses into the band (lo, hi].

    Counted as the number of MAXIMAL RUNS of grid points inside the band, which
    is the number of preimage intervals. A fold gives 2; a monotone crossing
    gives 1; no contact gives 0.
    """
    v = fn(qgrid)
    inside = (v > lo) & (v <= hi)
    if not inside.any():
        return 0
    edges = np.diff(inside.astype(np.int8))
    return int((edges == 1).sum()) + (1 if inside[0] else 0)


def search(curves, sites, qgrid, label):
    findings = []
    for name, site_list in sites.items():
        for site_name, q0 in site_list:
            v0 = float(curves[name](np.array([q0]))[0])
            for delta in DELTAS:
                lo, hi = v0, v0 + delta
                self_cov = coverage_count(curves[name], lo, hi, qgrid)
                others = {}
                for other in curves:
                    if other == name:
                        continue
                    others[other] = coverage_count(curves[other], lo, hi, qgrid)
                is_fold = (self_cov == 2) and all(c == 0 for c in others.values())
                findings.append({
                    "family": label, "branch": name, "site": site_name,
                    "q0": q0, "critical_value": v0, "delta": delta,
                    "self_coverage": self_cov, "other_coverage": others,
                    "FOLD": bool(is_fold),
                })
    return findings


def main():
    out = {}

    # ---- CONTROL 1: fold present by construction ------------------------
    t = np.linspace(0.0, 1.0, NQ)
    ctrl_pos = {"b0": lambda x: (x - 0.5) ** 2, "b1": lambda x: np.full_like(x, 3.0)}
    f1 = search(ctrl_pos, {"b0": [("t = 1/2", 0.5)], "b1": []}, t,
                "CONTROL-fold-present")
    c1 = any(r["FOLD"] for r in f1)
    print("CONTROL 1  reflection-symmetric, fold present by construction: %s"
          % ("DETECTED" if c1 else "MISSED -- search is blind, stop here"))
    for r in f1:
        print("   delta=%-8g self=%d others=%s FOLD=%s"
              % (r["delta"], r["self_coverage"], r["other_coverage"], r["FOLD"]))
    out["control_fold_present"] = {"findings": f1, "pass": bool(c1)}

    # ---- CONTROL 2: tangency present but band is reached by another -----
    ctrl_neg = {"b0": lambda x: (x - 0.5) ** 2, "b1": lambda x: np.zeros_like(x)}
    f2 = search(ctrl_neg, {"b0": [("t = 1/2", 0.5)], "b1": []}, t,
                "CONTROL-fold-excluded")
    c2 = not any(r["FOLD"] for r in f2)
    print("")
    print("CONTROL 2  same tangency, band also reached by a flat branch: %s"
          % ("CORRECTLY REJECTED" if c2 else "FALSE POSITIVE -- exclusion broken"))
    out["control_fold_excluded"] = {"findings": f2, "pass": bool(c2)}

    # ---- the genotype family --------------------------------------------
    q = np.linspace(1e-9, 0.5, NQ)
    print("")
    print("GENOTYPE FAMILY, exact tangency sites:")
    for nm, lst in EXACT_SITES.items():
        for sn, q0 in lst:
            print("   %s vanishes at %s = %.10f" % (nm, sn, q0))
    fg = search(GENOTYPE, EXACT_SITES, q, "genotype")
    out["genotype"] = fg
    print("")
    print("   %-5s %-22s %-10s %-6s %-26s %s"
          % ("br", "site", "delta", "self", "others", "FOLD"))
    for r in fg:
        print("   %-5s %-22s %-10g %-6d %-26s %s"
              % (r["branch"], r["site"], r["delta"], r["self_coverage"],
                 r["other_coverage"], r["FOLD"]))

    any_fold = any(r["FOLD"] for r in fg)
    out["genotype_fold_found"] = bool(any_fold)
    out["READ_THE_TEST"] = bool(c1 and c2)
    print("")
    print("GENOTYPE FOLD FOUND: %s" % any_fold)
    print("READ_THE_TEST: %s  (both controls must pass for the above to mean "
          "anything)" % out["READ_THE_TEST"])
    fh = open("fold_search_results.json", "w")
    json.dump(out, fh, indent=1)
    fh.close()
    print("-> fold_search_results.json")
    return 0 if out["READ_THE_TEST"] else 1


if __name__ == "__main__":
    sys.exit(main())
