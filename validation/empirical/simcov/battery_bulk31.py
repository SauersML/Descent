"""Battery 31: does LD correlation decay EXPONENTIALLY in distance?

`ldCorrelationDecay distance fstGap lambda = exp(-(lambda * fstGap * distance))`
asserts an exponential law in physical distance. Coalescent theory says
otherwise: Sved's relation makes the expected `r^2` between two sites decay as
`1 / (1 + 4 Ne c)` with `c` the recombination fraction, which is HYPERBOLIC in
distance, not exponential. The two differ in shape, so a decay curve measured
across a wide distance range separates them regardless of any free scale.

Both forms are fitted to the SAME measured curve with one free parameter each --
`lambda_eff` for the exponential, `Ne_eff` for the hyperbolic -- so neither is
handicapped, and the comparison is of fit quality across the range rather than
at one point.

IDENTITY RISK, screened first: the oracle is `r^2` computed from a simulated
genotype matrix, binned by physical distance. Neither candidate is evaluated to
produce it, and they disagree with each other, so at most one can match.
"""
import json
import math

import numpy as np
from scipy import optimize

import simlib
from battery_core import RESULTS, record

NE = 1000
SEQ = 5e6
RHO = 1e-8


def measured_decay(bins, reps=8, seed=31001):
    import msprime
    acc = [[] for _ in bins[:-1]]
    for r in range(reps):
        ts = msprime.sim_ancestry(samples=60, population_size=NE,
                                  sequence_length=SEQ,
                                  recombination_rate=RHO,
                                  random_seed=seed + r)
        mts = msprime.sim_mutations(ts, rate=1e-8, random_seed=seed + 900 + r)
        gm = mts.genotype_matrix()
        pos = mts.tables.sites.position
        freq = gm.mean(axis=1)
        keep = (freq > 0.05) & (freq < 0.95)
        gm, pos = gm[keep], pos[keep]
        if gm.shape[0] < 200:
            continue
        idx = np.sort(np.random.default_rng(seed + r).choice(
            gm.shape[0], size=min(1200, gm.shape[0]), replace=False))
        gm, pos = gm[idx], pos[idx]
        G = gm - gm.mean(axis=1, keepdims=True)
        norm = np.sqrt((G ** 2).sum(axis=1))
        for bi in range(len(bins) - 1):
            lo, hi = bins[bi], bins[bi + 1]
            vals = []
            for i in range(0, len(pos), 7):
                d = pos - pos[i]
                sel = np.where((d >= lo) & (d < hi))[0]
                if sel.size == 0:
                    continue
                num = G[sel] @ G[i]
                den = norm[sel] * norm[i]
                ok = den > 0
                if np.any(ok):
                    vals.append(float(np.mean((num[ok] / den[ok]) ** 2)))
            if vals:
                acc[bi].append(float(np.mean(vals)))
    return [simlib.summarize(a) for a in acc]


def main():
    bins = [0, 2e4, 5e4, 1e5, 2e5, 4e5, 8e5, 1.6e6]
    stats = measured_decay(bins)
    mids = np.array([(bins[i] + bins[i + 1]) / 2 for i in range(len(bins) - 1)])
    means = np.array([s["mean"] for s in stats])
    sems = np.array([max(s["sem"], 1e-6) for s in stats])
    ok = np.isfinite(means)
    mids, means, sems = mids[ok], means[ok], sems[ok]
    for d, m, s in zip(mids, means, sems):
        print("  distance %8.0f bp   r2 = %.4f ± %.4f" % (d, m, s))

    def fit(f, p0, bounds):
        sol = optimize.least_squares(
            lambda p: (f(mids, p) - means) / sems, p0, bounds=bounds)
        return sol.x

    # exponential with a free rate and a free amplitude
    pe = fit(lambda d, p: p[0] * np.exp(-p[1] * d), [means[0], 1e-6],
             ([0, 1e-12], [2.0, 1e-2]))
    # hyperbolic (Sved) with a free effective size and a free amplitude
    ph = fit(lambda d, p: p[0] / (1 + 4 * p[1] * RHO * d), [means[0], NE],
             ([0, 1.0], [2.0, 1e7]))
    exp_pred = pe[0] * np.exp(-pe[1] * mids)
    hyp_pred = ph[0] / (1 + 4 * ph[1] * RHO * mids)
    print("  exponential fit: amp %.4f rate %.3g" % (pe[0], pe[1]))
    print("  hyperbolic  fit: amp %.4f Ne_eff %.0f" % (ph[0], ph[1]))

    cells_exp = [dict(design="d=%.0fkb" % (d / 1e3), lean=float(e),
                      truth=float(m), sem=float(s))
                 for d, e, m, s in zip(mids, exp_pred, means, sems)]
    cells_hyp = [dict(design="d=%.0fkb" % (d / 1e3), lean=float(h),
                      truth=float(m), sem=float(s))
                 for d, h, m, s in zip(mids, hyp_pred, means, sems)]
    control = dict(design="Sved 1/(1+4*Ne*c) at the true Ne [classical]",
                   lean=float(means[0] / (1 + 4 * NE * RHO * mids[0])),
                   truth=float(means[0]), sem=float(sems[0]))
    reg = ("single panmictic population Ne = 1000, 5 Mb at recombination 1e-8, "
           "8 replicates; r^2 between common SNP pairs binned by physical "
           "distance over an eightyfold range. Both candidate laws are fitted "
           "to the SAME curve with one free rate and one free amplitude each, "
           "so neither is handicapped by a convention")
    record("ldCorrelationDecay [exponential in distance]",
           "PortabilityDrift.lean", "exp(-(lambda * fstGap * distance))",
           cells_exp, regime=reg, control=control)
    record("[competing] Sved hyperbolic 1/(1 + 4*Ne*c)",
           "PortabilityDrift.lean", "1 / (1 + 4*Ne*c*distance)", cells_hyp,
           regime=reg, control=control)
    json.dump(RESULTS, open("battery_bulk31_results.json", "w"), indent=1,
              default=str)
    print("\n================ SUMMARY ================")
    for r in RESULTS:
        w = r.get("worst", {})
        print("%-22s %-52s worst %9.2f sems, %7.2f%% rel"
              % (r["verdict"], r["name"], w.get("sems_off", float("nan")),
                 100 * w.get("rel_err", float("nan"))))


if __name__ == "__main__":
    main()
