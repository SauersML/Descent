"""Extreme-value / invariant sweep over the Calibrator definitions.

Every definition names a quantity with a known range: an F_ST lives in [0,1], a
probability in [0,1], an R^2 in [0, h^2], a variance in [0, inf), an AUC in
[0,1].  This sweep evaluates each transcribed definition over boundary and
out-of-range-but-representable inputs and reports any violation of the range its
own name asserts.

No simulation: violations found here are outright contradictions, not
approximation error.
"""
from __future__ import annotations

import itertools
import json
import sys

import numpy as np
from scipy import stats

Phi = stats.norm.cdf

VIOL = []


def check(name, source, value, lo, hi, params, note=""):
    bad = False
    if value is None or (isinstance(value, float) and not np.isfinite(value)):
        bad = True
    elif lo is not None and value < lo - 1e-12:
        bad = True
    elif hi is not None and value > hi + 1e-12:
        bad = True
    if bad:
        VIOL.append(dict(name=name, source=source, value=(None if value is None
                          or not np.isfinite(value) else float(value)),
                         lo=lo, hi=hi, params=params, note=note))


def main():
    # ---- singletonProportion: a proportion, must be in [0,1] -------------
    for N0, N1 in itertools.product([100, 1000, 10000], [100, 1000, 10000]):
        v = 1 - np.log(N0) / np.log(N1)
        check("singletonProportion", "DemographicHistory.lean:289", v, 0.0, 1.0,
              dict(N0=N0, N1=N1),
              "population contraction (N1 < N0) gives a negative proportion")

    # ---- expectedR2FromN: an R^2, must be in [0, h2] ---------------------
    for n, h2, M in itertools.product([1e3, 1e5, 1e7], [0.1, 0.5, 0.9], [1e3, 1e4]):
        v = n * h2 / (n * h2 + M)
        check("expectedR2FromN", "EquityAndImplementation.lean:202", v, 0.0, h2,
              dict(n=n, h2=h2, M=M), "R2 cannot exceed the heritability")

    # ---- stabilizingPortability / diversifyingPortability: R^2 >= 0 ------
    for r2_0, fst, s in itertools.product([0.2], [0.1, 0.4, 0.5, 0.6, 0.9], [1.0]):
        v = r2_0 * (1 - 2 * fst) * np.exp(-s * fst)
        check("stabilizingPortability", "PortabilityBounds.lean:223", v, 0.0, None,
              dict(r2_0=r2_0, fst=fst, strength=s), "negative R2 once fst > 0.5")
        v2 = r2_0 * (1 - 2 * fst) * np.exp(-s * fst) ** 2
        check("diversifyingPortability", "PortabilityBounds.lean:246", v2, 0.0,
              None, dict(r2_0=r2_0, fst=fst, lam=s), "negative R2 once fst > 0.5")

    # ---- amInflationFactor: a variance ratio, must be >= 1 ---------------
    for r in [0.0, 0.5, 0.9, 0.99, 1.0, 1.5]:
        v = 1 / (1 - r) if r != 1 else np.inf
        check("amInflationFactor", "StratificationConfounding.lean:138", v, 1.0,
              None, dict(r=r), "spousal correlation r >= 1 gives negative/infinite")

    # ---- amEquilibriumVariance: a variance, must be >= 0 -----------------
    for r, h2 in itertools.product([0.5, 1.0, 1.5], [0.5, 1.0]):
        d = 1 - r * h2
        v = 1.0 / d if d != 0 else np.inf
        check("amEquilibriumVariance", "AssortativeMatingPGS.lean:99", v, 0.0,
              None, dict(r=r, h2=h2), "r*h2 >= 1 gives negative/infinite variance")

    # ---- neiFst / simpleFst: an F_ST, must be in [0,1] -------------------
    for p1, p2 in itertools.product([0.0, 0.01, 0.5, 0.99, 1.0], repeat=2):
        pbar = (p1 + p2) / 2
        den = 4 * pbar * (1 - pbar)
        v = (p1 - p2) ** 2 / den if den != 0 else np.inf
        check("simpleFst", "PopulationGeneticsFoundations.lean:55", v, 0.0, 1.0,
              dict(p1=p1, p2=p2), "monomorphic pooled frequency divides by zero")
    for H_T, H_S in itertools.product([0.0, 0.001, 0.5], [0.0, 0.5, 0.9]):
        v = (H_T - H_S) / H_T if H_T != 0 else np.inf
        check("neiFst", "PopulationGeneticsFoundations.lean:39", v, 0.0, 1.0,
              dict(H_T=H_T, H_S=H_S), "H_S > H_T gives negative F_ST")

    # ---- ldRetentionPerGen: a retention fraction, in [0,1] ---------------
    for r, Ne in itertools.product([0.0, 0.5, 1.0], [0.5, 1.0, 100.0]):
        v = (1 - r) * (1 - 1 / (2 * Ne))
        check("ldRetentionPerGen", "LDDecayTheory.lean:38", v, 0.0, 1.0,
              dict(r=r, Ne=Ne), "Ne < 0.5 gives negative retention")

    # ---- tagR2: an r^2, in [0,1] ----------------------------------------
    for D_sq, vt, vc in itertools.product([0.25], [0.01, 0.25], [0.01, 0.25]):
        v = D_sq / (vt * vc)
        check("tagR2", "LDDecayTheory.lean:103", v, 0.0, 1.0,
              dict(D_sq=D_sq, var_tag=vt, var_causal=vc),
              "no constraint tying D^2 to the variances")

    # ---- approxPower: a probability, in [0,1] ---------------------------
    for ncp in [0.0, 1.0, 100.0]:
        v = 1 - np.exp(-ncp / 2)
        check("approxPower", "PowerAnalysis.lean:74", v, 0.0, 1.0, dict(ncp=ncp))

    # ---- ppv: a probability, in [0,1] -----------------------------------
    for prev, tpr, fpr in itertools.product([0.0, 0.01, 1.0], [0.0, 0.9], [0.0, 0.1]):
        den = prev * tpr + (1 - prev) * fpr
        v = prev * tpr / den if den != 0 else np.inf
        check("ppv", "ClinicalUtilityFairness.lean:699", v, 0.0, 1.0,
              dict(prev=prev, tpr=tpr, fpr=fpr), "zero denominator")

    # ---- numberNeededToScreen: positive and finite -----------------------
    for sens, pi in itertools.product([0.0, 0.5, 1.0], [0.0, 0.001, 0.5]):
        v = 1 / (sens * pi) if sens * pi != 0 else np.inf
        check("numberNeededToScreen", "ClinicalUtilityFairness.lean:951", v, 0.0,
              None, dict(sens=sens, pi=pi), "zero sensitivity or prevalence")

    # ---- neutralAFBenchmarkRatio: a heterozygosity ratio ----------------
    for fs, ft in itertools.product([0.0, 0.5, 0.9, 1.0], repeat=2):
        v = (1 - ft) / (1 - fs) if fs != 1 else np.inf
        check("neutralAFBenchmarkRatio", "PortabilityDrift.lean:2424", v, 0.0,
              None, dict(fstSource=fs, fstTarget=ft), "fstSource = 1 divides by zero")

    # ---- hosmerLemeshowContrib: a chi-square contribution, >= 0 ---------
    for obs, exp_, n in itertools.product([0.0, 0.5], [0.0, 0.5, 1.0], [10.0]):
        den = exp_ * (1 - exp_)
        v = n * (obs - exp_) ** 2 / den if den != 0 else np.inf
        check("hosmerLemeshowContrib", "PGSCalibrationTheory.lean:235", v, 0.0,
              None, dict(observed=obs, expected=exp_, n_group=n),
              "expected at 0 or 1 divides by zero")

    # ---- coalFst / fstFromDrift / islandModelFst: in [0,1] --------------
    for t, Ne in itertools.product([0.0, 1e6], [1e-3, 1e4]):
        check("coalFst", "PopulationGeneticsFoundations.lean:120",
              t / (t + 2 * Ne) if (t + 2 * Ne) != 0 else np.inf, 0.0, 1.0,
              dict(t=t, Ne=Ne))
    for Ne, m in itertools.product([1e4], [0.0, 1.0]):
        check("islandModelFst", "PopulationGeneticsFoundations.lean:636",
              1 / (1 + 4 * Ne * m), 0.0, 1.0, dict(Ne=Ne, m=m))
    for t, Ne in itertools.product([10, 1000], [0.4, 0.5, 1e4]):
        v = 1 - (1 - 1 / (2 * Ne)) ** t
        check("fstFromDrift", "PopulationGeneticsFoundations.lean:283", v, 0.0,
              1.0, dict(t=t, Ne=Ne), "Ne < 0.5 makes the base negative")

    with open(sys.argv[1] if len(sys.argv) > 1 else "extremes.json", "w") as fh:
        json.dump(VIOL, fh)

    print(f"{len(VIOL)} invariant violations\n")
    seen = set()
    for v in VIOL:
        if v["name"] in seen:
            continue
        seen.add(v["name"])
        rng = f"[{v['lo']}, {v['hi']}]"
        print(f"{v['name']}  ({v['source']})")
        print(f"    required {rng}, got {v['value']}  at {v['params']}")
        if v["note"]:
            print(f"    {v['note']}")
    print("\nfull per-parameter list in the json")


if __name__ == "__main__":
    main()
