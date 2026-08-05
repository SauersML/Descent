"""Battery 36: the mutation-drift covariance chain, on three measured inputs.

`covarianceDivergenceMutationDrift fst shared_ld = fst + (1-fst)*(1-shared_ld)`,
so `1 - covDiv = (1 - fst) * shared_ld`, and the chain continues

    presentDayPGSVarianceMutationDrift V_A fst s = (1 - covDiv) * V_A
    presentDayR2MutationDrift V_A V_E fst s      = v / (v + V_E)

The crucial difference from `signalRetentionMigrationDrift`, which battery 35
falsified: THIS body takes `shared_ld` as an ARGUMENT. It is not committed to
`M/(1+M)`, the reading battery 34 refuted. So it can be right even though its
migration-parameterised cousin is wrong, and the only way to find out is to feed
it the shared LD that was actually measured.

Three independent observables, all from the same island replicates:

  fst        site-frequency Hudson F_ST (single sites)
  shared_ld  cross-deme correlation of signed LD r (pairs of sites)
  retention  the surviving fraction of the score/genetic-value covariance,
             divided by the estimator's panmictic ceiling

and the claim under test is `retention = (1 - fst) * shared_ld`. None of the
three is computed from either of the others, which is what makes this a test
rather than the algebraic rearrangement it would be if `shared_ld` were
substituted by its formula.

Competitors: `(1 - fst)` alone and `shared_ld` alone -- i.e. dropping either
factor of the product.
"""
import json
import math

import numpy as np

import simlib
from battery_core import RESULTS, record

NE = 1000
SEQ = 5e6
RHO = 1e-8
MU = 1e-8


def r_vector(gm, samples, pairs):
    G = gm[:, samples].astype(float)
    G = G - G.mean(axis=1, keepdims=True)
    nrm = np.sqrt((G ** 2).sum(axis=1))
    out = np.full(len(pairs), np.nan)
    for k, (i, j) in enumerate(pairs):
        if nrm[i] > 0 and nrm[j] > 0:
            out[k] = float(G[i] @ G[j] / (nrm[i] * nrm[j]))
    return out


def one_run(dem, seed, rng, samples):
    import msprime
    # `demography=None` carries no population size, so the panmictic ceiling
    # run needs `population_size` supplied explicitly. Omitting it made every
    # ceiling replicate fail, left `ceil["mean"]` NaN, and propagated NaN into
    # every cell -- which the harness then reported as MATCH at `inf` sems.
    if dem is None:
        ts = msprime.sim_ancestry(samples=samples, population_size=NE,
                                  sequence_length=SEQ, recombination_rate=RHO,
                                  random_seed=seed)
    else:
        ts = msprime.sim_ancestry(samples=samples, demography=dem,
                                  sequence_length=SEQ, recombination_rate=RHO,
                                  random_seed=seed)
    mts = msprime.sim_mutations(ts, rate=MU, random_seed=seed + 5000)
    if mts.num_sites < 200:
        return None
    gm = mts.genotype_matrix()
    if dem is None:
        A, B = np.arange(0, 200), np.arange(200, 400)
    else:
        A, B = mts.samples(population=0), mts.samples(population=1)
    fa, fb = gm[:, A].mean(axis=1), gm[:, B].mean(axis=1)
    keep = np.where((fa > 0.05) & (fa < 0.95) & (fb > 0.05) & (fb < 0.95))[0]
    if keep.size < 120:
        return None
    fst = simlib.hudson_fst(gm[:, A].sum(1).astype(float), len(A),
                            gm[:, B].sum(1).astype(float), len(B))
    sel = keep[:400]
    pairs = [(sel[i], sel[i + 1]) for i in range(0, len(sel) - 1, 2)]
    ra, rb = r_vector(gm, A, pairs), r_vector(gm, B, pairs)
    ok = np.isfinite(ra) & np.isfinite(rb)
    shared = float(np.corrcoef(ra[ok], rb[ok])[0, 1]) if ok.sum() > 30 else np.nan
    causal = keep[rng.choice(keep.size, size=min(80, keep.size), replace=False)]
    beta = rng.normal(0, 1, causal.size)
    XA = gm[np.ix_(causal, A)].astype(float).T
    XB = gm[np.ix_(causal, B)].astype(float).T
    XA, XB = XA - XA.mean(0), XB - XB.mean(0)
    SA = (XA.T @ XA) / (XA.shape[0] - 1)
    SB = (XB.T @ XB) / (XB.shape[0] - 1)
    w = SA @ beta
    den = float(w @ (SA @ beta))
    ret = float(w @ (SB @ beta)) / den if abs(den) > 1e-12 else np.nan
    return fst, shared, ret


def main():
    import msprime
    rng = np.random.default_rng(36001)
    # panmictic ceiling for the retention estimator, and the F_ST control
    cr, cf = [], []
    for r in range(6):
        out = one_run(None, 36777 + r, rng, 200)
        if out:
            cf.append(out[0])
            cr.append(out[2])
    ceil = simlib.summarize(cr)
    cfs = simlib.summarize(cf)
    if not np.isfinite(ceil["mean"]) or ceil["mean"] == 0:
        raise SystemExit("ceiling is NaN/zero -- refusing to report cells that "
                         "would all be NaN and score MATCH at inf sems")
    print("  CEILING panmictic split: retention=%.4f ± %.4f, F_ST=%.4f"
          % (ceil["mean"], ceil["sem"], cfs["mean"]))
    control = dict(design="one population split arbitrarily [F_ST = 0]",
                   lean=0.0, truth=cfs["mean"], sem=max(cfs["sem"], 1e-6))

    cells, c_f, c_s = [], [], []
    for m in (1e-4, 5e-4, 2e-3, 1e-2):
        F, S, R = [], [], []
        for r in range(10):
            dem = msprime.Demography.island_model([NE, NE], migration_rate=m)
            out = one_run(dem, 36101 + r + int(1e6 * m), rng,
                          {"pop_0": 100, "pop_1": 100})
            if out and np.isfinite(out[1]) and np.isfinite(out[2]):
                F.append(out[0]); S.append(out[1]); R.append(out[2])
        sf, ss = simlib.summarize(F), simlib.summarize(S)
        sr = simlib.summarize(R)
        ret = sr["mean"] / ceil["mean"]
        ret_sem = abs(ret) * math.hypot(sr["sem"] / max(abs(sr["mean"]), 1e-12),
                                        ceil["sem"] / max(abs(ceil["mean"]), 1e-12))
        lean = (1 - sf["mean"]) * ss["mean"]
        lab = "4Nm=%.1f" % (4 * NE * m)
        print("  %-10s F=%.4f  sharedLD=%.4f  retention=%.4f ± %.4f | "
              "(1-F)*s=%.4f  (1-F)=%.4f  s=%.4f"
              % (lab, sf["mean"], ss["mean"], ret, ret_sem, lean,
                 1 - sf["mean"], ss["mean"]))
        cells.append(dict(design=lab, lean=lean, truth=ret,
                          sem=max(ret_sem, 1e-6)))
        c_f.append(dict(design=lab, lean=1 - sf["mean"], truth=ret,
                        sem=max(ret_sem, 1e-6)))
        c_s.append(dict(design=lab, lean=ss["mean"], truth=ret,
                        sem=max(ret_sem, 1e-6)))
    reg = ("two-deme island model, Ne = 1000, 5 Mb with recombination; F_ST, "
           "cross-deme LD correlation and score-covariance retention are three "
           "SEPARATE measurements on the same replicates, and the body is fed "
           "the measured shared LD rather than its migration formula -- which "
           "battery_bulk34 refuted. Retention is divided by the estimator's "
           "panmictic ceiling to remove its attenuation")
    record("covarianceDivergenceMutationDrift [1 - covDiv = (1-fst)*shared_ld]",
           "PortabilityDrift.lean", "fst + (1 - fst) * (1 - shared_ld)",
           cells, regime=reg, control=control)
    record("[competing] frequency divergence alone", "PortabilityDrift.lean",
           "1 - fst", c_f, regime=reg, control=control)
    record("[competing] LD sharing alone", "PortabilityDrift.lean",
           "shared_ld", c_s, regime=reg, control=control)
    json.dump(RESULTS, open("battery_bulk36_results.json", "w"), indent=1,
              default=str)
    print("\n================ SUMMARY ================")
    for r in RESULTS:
        w = r.get("worst", {})
        print("%-22s %-52s worst %9.2f sems, %7.2f%% rel"
              % (r["verdict"], r["name"], w.get("sems_off", float("nan")),
                 100 * w.get("rel_err", float("nan"))))


if __name__ == "__main__":
    main()
