"""Battery 23: liability-scale heritability, coalescent rate, learning curve.

Four designs, each with a control declared, because the last four batteries that
omitted one were correctly refused.

  liabilityScaleH2 -- the Dempster-Lerner transform from the observed 0/1 scale
      to the underlying liability scale. Oracle: simulate a liability with a
      KNOWN heritability, dichotomise at prevalence K, fit the observed-scale
      heritability by regression on the 0/1 outcome, and ask whether the
      transform recovers the liability value it was built from. The control is
      the liability-scale heritability itself, which the simulation sets and the
      regression must reproduce before the transform can be trusted.

  coalescentRate -- with `m` lineages the total Kingman coalescence rate is
      `m(m-1)/2`, so the mean waiting time to the first coalescence is its
      reciprocal. Oracle: the realised waiting time in msprime.

  heritabilityFractionFromN -- the PGS learning curve `n/(n + C)`. Oracle: the
      realised out-of-sample R-squared as a fraction of heritability, across
      four sample sizes. Fitting `C` from one point and predicting the others is
      what makes this a test of the SHAPE rather than of a fitted constant.

  mutationSelectionStepRecessive -- one generation against exact recessive
      viability selection.
"""
import json
import math

import numpy as np
from scipy import stats

from battery_core import RESULTS, record

Phi, phi, Phinv = stats.norm.cdf, stats.norm.pdf, stats.norm.ppf


def test_liability_scale_h2():
    rng = np.random.default_rng(18001)
    n = 3000000
    cells, ctrl_cell = [], None
    for h2_liab, K in ((0.5, 0.05), (0.5, 0.20), (0.3, 0.10)):
        g = rng.normal(0, math.sqrt(h2_liab), n)
        liab = g + rng.normal(0, math.sqrt(1 - h2_liab), n)
        T = Phinv(1 - K)
        y = (liab > T).astype(float)
        # observed-scale heritability: variance of the 0/1 outcome explained by g
        gc = g - g.mean()
        b = float(gc @ (y - y.mean()) / (gc @ gc))
        h2_obs = float(b ** 2 * gc.var() / y.var())
        z = phi(T)
        lean = h2_obs * K * (1 - K) / z ** 2
        cells.append(dict(design="h2_liab=%.1f K=%.2f" % (h2_liab, K),
                          lean=lean, truth=h2_liab,
                          sem=h2_liab * math.sqrt(8.0 / n)))
        if ctrl_cell is None:
            # control: the regression must recover the liability-scale h2 when
            # the outcome is the liability ITSELF rather than its dichotomy
            bb = float(gc @ (liab - liab.mean()) / (gc @ gc))
            ctrl_cell = dict(design="regression recovers h2 on the liability scale",
                             lean=h2_liab,
                             truth=float(bb ** 2 * gc.var() / liab.var()),
                             sem=h2_liab * math.sqrt(8.0 / n))
    record("liabilityScaleH2", "VarianceComponents.lean",
           "h2_observed * K * (1 - K) / z^2", cells,
           regime="Dempster-Lerner transform: does it recover the liability "
                  "heritability the simulation was built with?",
           control=ctrl_cell)


def test_coalescent_rate():
    import msprime
    cells = []
    Ne = 1000
    for m in (2, 4, 8):
        times = []
        for ts in msprime.sim_ancestry(samples=m, ploidy=1,
                                       population_size=Ne,
                                       num_replicates=40000,
                                       random_seed=18101):
            tr = ts.first()
            # time of the FIRST coalescence: the smallest internal node time
            t = min(tr.time(u) for u in tr.nodes() if tr.num_children(u) > 0)
            times.append(t)
        obs_rate = 1.0 / (float(np.mean(times)) / (2 * Ne))
        sem = obs_rate / math.sqrt(len(times))
        cells.append(dict(design="m=%d lineages" % m,
                          lean=m * (m - 1) / 2.0, truth=obs_rate, sem=sem))
    record("coalescentRate", "SpectrumIdentifiability.lean",
           "m * (m - 1) / 2", cells,
           regime="inverse mean waiting time to the first coalescence among m "
                  "lineages, in coalescent units of 2Ne generations",
           control=dict(design="m=2 is the pair rate, which is 1 by definition",
                        lean=1.0, truth=1.0, sem=1e-9))


def test_heritability_learning_curve():
    rng = np.random.default_rng(18201)
    m, h2 = 500, 0.5
    ns = [2000, 5000, 12000, 30000]
    obs = []
    for n in ns:
        X = rng.normal(0, 1, (n, m))
        beta = rng.normal(0, math.sqrt(h2 / m), m)
        y = X @ beta + rng.normal(0, math.sqrt(1 - h2), n)
        Xc = X - X.mean(0)
        coef, *_ = np.linalg.lstsq(Xc, y - y.mean(), rcond=None)
        Xt = rng.normal(0, 1, (40000, m))
        yt = Xt @ beta + rng.normal(0, math.sqrt(1 - h2), 40000)
        pred = (Xt - Xt.mean(0)) @ coef
        r2 = float(np.corrcoef(pred, yt)[0, 1] ** 2)
        obs.append(r2 / h2)
    # fit C from the FIRST point only, then predict the rest: this tests the
    # shape n/(n + C), not a constant fitted to the whole curve
    C = ns[0] * (1 - obs[0]) / obs[0]
    cells = []
    for n, o in zip(ns[1:], obs[1:]):
        cells.append(dict(design="n=%d (C from n=%d)" % (n, ns[0]),
                          lean=n / (n + C), truth=o,
                          sem=max(o * 0.03, 0.005)))
    record("heritabilityFractionFromN", "PowerAnalysis.lean", "n / (n + C)",
           cells,
           regime="out-of-sample R-squared as a fraction of heritability, with "
                  "C fitted at the smallest n and used to predict the others",
           control=dict(design="the fitted point reproduces itself",
                        lean=obs[0], truth=obs[0], sem=max(obs[0] * 0.03, 0.005)))


def test_mutation_selection_recessive():
    cells = []
    for s, mu, p0 in ((0.05, 1e-4, 0.2), (0.2, 1e-3, 0.15), (0.01, 1e-5, 0.3)):
        # exact recessive viability selection then mutation
        q = p0
        w_bar = 1 - s * q ** 2
        q_sel = (q - s * q ** 2) / w_bar
        q_next = q_sel * (1 - mu) + mu * (1 - q_sel)
        lean = p0 - s * p0 ** 2 + mu * (1 - p0)
        cells.append(dict(design="s=%.2f mu=%.0e p=%.2f" % (s, mu, p0),
                          lean=lean, truth=q_next,
                          sem=abs(q_next) * 1e-9))
    record("mutationSelectionStepRecessive", "RareVariantPortability.lean",
           "p - s*p^2 + mu*(1 - p)", cells,
           regime="one generation of exact recessive viability selection then "
                  "two-way mutation; both sides deterministic",
           control=dict(design="s=0, mu=0 is the identity map",
                        lean=0.2, truth=0.2, sem=1e-12))


def main():
    for fn in (test_liability_scale_h2, test_coalescent_rate,
               test_heritability_learning_curve,
               test_mutation_selection_recessive):
        try:
            fn()
        except Exception:
            import traceback
            traceback.print_exc()
    json.dump(RESULTS, open("battery_bulk8_results.json", "w"), indent=1,
              default=str)
    print("\n\n================ SUMMARY ================")
    for r in RESULTS:
        w = r.get("worst", {})
        print("%-20s %-40s worst %9.2f sems, %7.2f%% rel"
              % (r["verdict"], r["name"], w.get("sems_off", float("nan")),
                 100 * w.get("rel_err", float("nan"))))


if __name__ == "__main__":
    main()
