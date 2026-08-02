"""A property-based harness for the Calibrator definitions.

Instead of a bespoke script per definition, each definition is registered once
as a `Spec`:

    Spec(name, source, fn, domain, rng_lo, rng_hi, oracle=None)

  fn      - the Lean formula, transcribed literally
  domain  - {param: (lo, hi, scale)} sampling box; boundary values are always
            included in addition to random draws
  rng_lo/hi - the range the quantity's NAME requires (an F_ST is in [0,1], an
            R^2 in [0, h2], a variance in [0, inf))
  oracle  - optional ground-truth callable with the same signature; when
            present the harness fuzzes for the worst relative disagreement

Two modes run over every registered spec:

  invariant fuzz - does the formula ever leave its own declared range?
  oracle fuzz    - where does it disagree most with ground truth?

An invariant violation is a LEAD, not a finding: Lean theorems carry hypotheses
that may exclude the offending inputs, and Mathlib defines x/0 = 0, so junk
inputs return plausible numbers rather than erroring.  Each lead must be checked
against the guarding theorem's hypotheses before it is reported.
"""
from __future__ import annotations

import json
import math
import sys
from dataclasses import dataclass, field
from typing import Callable

import numpy as np
from scipy import stats

Phi = stats.norm.cdf
phi = stats.norm.pdf


@dataclass
class Spec:
    name: str
    source: str
    fn: Callable
    domain: dict
    rng_lo: float | None = 0.0
    rng_hi: float | Callable | None = None
    oracle: Callable | None = None
    note: str = ""
    guard: str = ""          # hypotheses the Lean theorems are known to carry
    tags: list = field(default_factory=list)


def sample(domain, rng, n):
    """Random draws plus every boundary corner of the sampling box."""
    keys = list(domain)
    rows = []
    for _ in range(n):
        row = {}
        for k in keys:
            lo, hi, scale = domain[k]
            if scale == "log":
                row[k] = float(np.exp(rng.uniform(np.log(lo), np.log(hi))))
            else:
                row[k] = float(rng.uniform(lo, hi))
        rows.append(row)
    # boundaries: each parameter pinned to lo and hi, others mid
    for k in keys:
        for edge in (0, 1):
            row = {}
            for k2 in keys:
                lo, hi, _ = domain[k2]
                row[k2] = (lo if edge == 0 else hi) if k2 == k else (lo + hi) / 2
            rows.append(row)
    return rows


def run(specs, n_fuzz, seed=0):
    rng = np.random.default_rng(seed)
    leads, oracle_worst = [], []
    for sp in specs:
        worst = None
        for params in sample(sp.domain, rng, n_fuzz):
            try:
                v = sp.fn(**params)
            except ZeroDivisionError:
                v = math.inf
            except Exception:
                continue
            hi = sp.rng_hi(**params) if callable(sp.rng_hi) else sp.rng_hi
            bad = (v is None or not np.isfinite(v)
                   or (sp.rng_lo is not None and v < sp.rng_lo - 1e-9)
                   or (hi is not None and v > hi + 1e-9))
            if bad:
                leads.append(dict(name=sp.name, source=sp.source, params=params,
                                  value=(None if not np.isfinite(v) else float(v)),
                                  lo=sp.rng_lo, hi=hi, guard=sp.guard,
                                  note=sp.note))
            if sp.oracle is not None:
                try:
                    t = sp.oracle(**params)
                except Exception:
                    continue
                if t is None or not np.isfinite(t) or abs(t) < 1e-12:
                    continue
                rel = abs(v - t) / abs(t)
                if worst is None or rel > worst["rel"]:
                    worst = dict(name=sp.name, source=sp.source, params=params,
                                 lean=float(v), truth=float(t), rel=float(rel))
        if worst:
            oracle_worst.append(worst)
    return leads, oracle_worst


# ---------------------------------------------------------------------------
# registry
# ---------------------------------------------------------------------------

def _liab_auc_lean(r2, K):
    return float(Phi(np.sqrt(r2 / (2 * (1 - r2)))))


def _liab_auc_truth(r2, K):
    rho = np.sqrt(r2)
    T = stats.norm.isf(K)
    g = np.linspace(-9, 9, 4001)
    pc = stats.norm.sf((T - rho * g) / np.sqrt(1 - rho**2))
    fcase = phi(g) * pc / K
    fctrl = phi(g) * (1 - pc) / (1 - K)
    F = np.concatenate([[0], np.cumsum((fctrl[1:] + fctrl[:-1]) / 2 * np.diff(g))])
    F /= F[-1]
    return float(np.trapezoid(fcase * F, g))


def _power_lean(ncp, alpha):
    return 1 - np.exp(-ncp / 2)


def _power_truth(ncp, alpha):
    return float(stats.ncx2.sf(stats.chi2.ppf(1 - alpha, 1), 1, ncp))


def _wc_lean(b_over_se, z):
    return b_over_se + 1.0


def _wc_truth(b_over_se, z):
    b = b_over_se
    num = phi(z - b) - phi(z + b)
    den = Phi(b - z) + Phi(-b - z)
    if den <= 0:
        return None
    return b + num / den


def _trunc_lean(b_over_se, z):
    return float(np.exp(-((z - b_over_se) ** 2) / 2) / np.sqrt(2 * np.pi))


def _trunc_truth(b_over_se, z):
    b = b_over_se
    den = Phi(b - z) + Phi(-b - z)
    if den <= 0:
        return None
    return float((phi(z - b) - phi(z + b)) / den)


SPECS = [
    Spec("liabilityAUCFromExplainedR2", "PortabilityDrift.lean:2578",
         _liab_auc_lean, {"r2": (0.001, 0.6, "log"), "K": (0.0005, 0.5, "log")},
         0.5, 1.0, oracle=_liab_auc_truth,
         note="no prevalence argument", tags=["auc"]),
    Spec("approxPower", "PowerAnalysis.lean:74", _power_lean,
         {"ncp": (0.1, 60, "log"), "alpha": (5e-8, 0.05, "log")}, 0.0, 1.0,
         oracle=_power_truth, note="no alpha argument", tags=["power"]),
    Spec("winnersCurseInflation", "PowerAnalysis.lean:389", _wc_lean,
         {"b_over_se": (0.0, 8.0, "lin"), "z": (1.5, 6.0, "lin")}, 0.0, None,
         oracle=_wc_truth, note="no threshold argument", tags=["power"]),
    Spec("truncationBias", "PowerAnalysis.lean:215", _trunc_lean,
         {"b_over_se": (0.0, 8.0, "lin"), "z": (1.5, 6.0, "lin")}, 0.0, None,
         oracle=_trunc_truth, note="numerator-only inverse Mills", tags=["power"]),
    Spec("expectedR2FromN", "EquityAndImplementation.lean:202",
         lambda n, h2, M: n * h2 / (n * h2 + M),
         {"n": (1e2, 1e7, "log"), "h2": (0.01, 0.95, "lin"), "M": (1e2, 1e5, "log")},
         0.0, lambda n, h2, M: h2,
         oracle=lambda n, h2, M: h2 * (n * h2 / (n * h2 + M)),
         note="returns R2/h2, not R2", tags=["pgs"]),
    Spec("singletonProportion", "DemographicHistory.lean:289",
         lambda N0, N1: 1 - np.log(N0) / np.log(N1),
         {"N0": (10, 1e6, "log"), "N1": (10, 1e6, "log")}, 0.0, 1.0,
         note="negative under population contraction", tags=["sfs"]),
    Spec("stabilizingPortability", "PortabilityBounds.lean:223",
         lambda r2_0, fst, strength: r2_0 * (1 - 2 * fst) * np.exp(-strength * fst),
         {"r2_0": (0.01, 0.5, "lin"), "fst": (0.001, 0.9, "log"),
          "strength": (0.1, 50, "log")}, 0.0, None,
         note="negative R2 once fst > 0.5", tags=["portability"]),
    Spec("amInflationFactor", "StratificationConfounding.lean:138",
         lambda r: 1 / (1 - r) if r != 1 else math.inf,
         {"r": (0.0, 0.99, "lin")}, 1.0, None,
         oracle=lambda r: 1 / (1 - r * 0.5),   # truth uses r*h2, h2=0.5 here
         note="no h2 argument; compared at h2=0.5", tags=["am"]),
    Spec("amEquilibriumVariance", "AssortativeMatingPGS.lean:99",
         lambda r, h2: 1 / (1 - r * h2),
         {"r": (0.0, 0.95, "lin"), "h2": (0.01, 0.99, "lin")}, 1.0, None,
         guard="theorems assume r*h2 < 1", tags=["am"]),
    Spec("coalFst", "PopulationGeneticsFoundations.lean:120",
         lambda t, Ne: t / (t + 2 * Ne),
         {"t": (1.0, 1e6, "log"), "Ne": (10.0, 1e6, "log")}, 0.0, 1.0,
         tags=["fst"]),
    Spec("fstFromDrift", "PopulationGeneticsFoundations.lean:283",
         lambda t, Ne: 1 - (1 - 1 / (2 * Ne)) ** t,
         {"t": (1.0, 1e5, "log"), "Ne": (10.0, 1e6, "log")}, 0.0, 1.0,
         oracle=lambda t, Ne: t / (t + 2 * Ne),
         note="documented as split F_ST; compared against the coalescent value",
         tags=["fst"]),
    # r^2 from D: correct only if D is the dosage covariance.  The repo's own
    # admixtureLD / ldAfterGenerations produce HAPLOTYPE D, and composing them
    # with this definition yields r^2/4.  Oracle = the true r^2 for that D.
    Spec("ldCorrelationSq(hapD)", "CovarianceStructure.lean:91",
         lambda D, p_i, p_j: D**2 / ((2 * p_i * (1 - p_i)) * (2 * p_j * (1 - p_j))),
         {"D": (0.001, 0.2, "log"), "p_i": (0.1, 0.9, "lin"),
          "p_j": (0.1, 0.9, "lin")}, 0.0, 1.0,
         oracle=lambda D, p_i, p_j: D**2 / (p_i * (1 - p_i) * p_j * (1 - p_j)),
         note="returns r^2/4 when fed haplotype D", tags=["ld"]),
    # LDSC confounding term: reference is N*a, the definition has N*a/M
    Spec("ldsrExpectedChi2", "CovarianceStructure.lean:308",
         lambda N, h2, M, ell_j, a: N * h2 / M * ell_j + N * a / M + 1,
         {"N": (1e3, 1e6, "log"), "h2": (0.05, 0.8, "lin"),
          "M": (1e3, 1e6, "log"), "ell_j": (1.0, 200.0, "log"),
          "a": (1e-6, 1e-3, "log")}, 1.0, None,
         oracle=lambda N, h2, M, ell_j, a: N * h2 / M * ell_j + N * a + 1,
         note="confounding term divided by M; understates inflation ~M-fold",
         tags=["ldsc"]),
    Spec("bottleneckLDAmplification", "LDDecayTheory.lean:192",
         lambda N_b, t: 1 - (1 - 1 / (2 * N_b)) ** t,
         {"N_b": (10.0, 1e4, "log"), "t": (1.0, 1e4, "log")}, 0.0, 1.0,
         note="no recombination rate; true E[r2] saturates at 1/(1+4Nc)",
         tags=["ld"]),
]


def main():
    n_fuzz = int(sys.argv[1]) if len(sys.argv) > 1 else 4000
    leads, worst = run(SPECS, n_fuzz)

    print(f"registered specs: {len(SPECS)}   fuzz draws per spec: {n_fuzz}\n")
    print("=" * 72)
    print("ORACLE FUZZ: worst relative disagreement found")
    print("=" * 72)
    print(f"{'definition':<32} {'worst rel err':>13}   at")
    for w in sorted(worst, key=lambda z: -z["rel"]):
        ps = " ".join(f"{k}={v:.4g}" for k, v in w["params"].items())
        print(f"{w['name']:<32} {w['rel']*100:12.1f}%   {ps}")
        print(f"{'':<32} lean={w['lean']:.5g} truth={w['truth']:.5g}")

    print()
    print("=" * 72)
    print("INVARIANT LEADS (must be checked against theorem hypotheses)")
    print("=" * 72)
    seen = {}
    for L in leads:
        seen.setdefault(L["name"], L)
    for name, L in seen.items():
        ps = " ".join(f"{k}={v:.4g}" for k, v in L["params"].items())
        n = sum(1 for x in leads if x["name"] == name)
        print(f"{name:<32} {n:5d} violations, e.g. value={L['value']} at {ps}")
        if L["guard"]:
            print(f"{'':<32} GUARDED: {L['guard']}")
        elif L["note"]:
            print(f"{'':<32} {L['note']}")

    with open("harness_out.json", "w") as fh:
        json.dump(dict(leads=leads, oracle_worst=worst), fh)


if __name__ == "__main__":
    main()
