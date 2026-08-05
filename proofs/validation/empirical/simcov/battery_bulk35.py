"""Battery 35: does a transferred PGS retain (1-F)*M/(1+M) of its signal?

`signalRetentionMigrationDrift Ne m = (1 - fstMigrationDriftEquilibrium Ne m)
 * sharedLDFromMigration (scaledMigrationRate Ne m)`, and
`retainedSignalVarianceMigrationDrift V_A Ne m = signalRetentionMigrationDrift
 Ne m * V_A`.

`battery_bulk34.py` has just falsified the second factor's reading -- measured
shared LD is far above `M/(1+M)` once `F_ST` exceeds ~0.2 -- so the product is
expected to be low. This battery tests the PRODUCT directly rather than
inferring it, because a compound claim can be right for compensating reasons.

Oracle: real genotypes from the same two-deme island model. Causal effects are
assigned to segregating sites; a score is built with weights fitted in deme 0
and the observable is the fraction of its deme-0 signal that survives in deme 1
-- `Cov(PGS, g)_target / Cov(PGS, g)_source`, which is what "signal retention"
denotes. Nothing evaluates the body to produce it.

Competitors on the same cells: the retention read as `1 - F` alone (frequency
divergence only, no LD term) and as `M/(1+M)` alone (LD term only).
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


def panmictic_ceiling(rng):
    """The retention this estimator reports for ONE population split in half.

    `w = Sigma_A . beta` reuses the same finite-sample `Sigma_A` that the
    denominator contracts against, so the denominator carries squared estimation
    noise the numerator does not: retention is attenuated below 1 even with no
    differentiation at all. The attenuation depends only on the sample size and
    the site count, both held fixed across cells, so it is a CALIBRATION and is
    divided out rather than being demanded to vanish."""
    import msprime
    cr, cf = [], []
    for r in range(6):
        ts = msprime.sim_ancestry(samples=200, population_size=NE,
                                  sequence_length=SEQ, recombination_rate=RHO,
                                  random_seed=35777 + r)
        mts = msprime.sim_mutations(ts, rate=MU, random_seed=135777 + r)
        gm = mts.genotype_matrix()
        A2, B2 = np.arange(0, 200), np.arange(200, 400)
        fa2, fb2 = gm[:, A2].mean(axis=1), gm[:, B2].mean(axis=1)
        k2 = np.where((fa2 > 0.05) & (fa2 < 0.95)
                      & (fb2 > 0.05) & (fb2 < 0.95))[0]
        if k2.size < 100:
            continue
        cf.append(simlib.hudson_fst(gm[:, A2].sum(1).astype(float), len(A2),
                                    gm[:, B2].sum(1).astype(float), len(B2)))
        c2 = k2[rng.choice(k2.size, size=min(80, k2.size), replace=False)]
        b2 = rng.normal(0, 1, c2.size)
        YA = gm[np.ix_(c2, A2)].astype(float).T
        YB = gm[np.ix_(c2, B2)].astype(float).T
        YA, YB = YA - YA.mean(0), YB - YB.mean(0)
        TA = (YA.T @ YA) / (YA.shape[0] - 1)
        TB = (YB.T @ YB) / (YB.shape[0] - 1)
        w2 = TA @ b2
        d2 = float(w2 @ (TA @ b2))
        n2 = float(w2 @ (TB @ b2))
        if abs(d2) > 1e-12:
            cr.append(n2 / d2)
    return simlib.summarize(cr), simlib.summarize(cf)


def main():
    import msprime
    rng = np.random.default_rng(35001)
    cells, c_f, c_m = [], [], []
    ceil, ceil_fst = panmictic_ceiling(rng)
    print("  CEILING one population split: retention=%.4f ± %.4f, F_ST=%.4f"
          % (ceil["mean"], ceil["sem"], ceil_fst["mean"]))
    # Control on F_ST, where zero really IS the expected value under an
    # arbitrary split -- the retention ceiling is a calibration, not a control.
    control = dict(design="one population split arbitrarily [F_ST = 0]",
                   lean=0.0, truth=ceil_fst["mean"],
                   sem=max(ceil_fst["sem"], 1e-6))
    for m in (1e-4, 5e-4, 2e-3, 1e-2):
        bigM = 4 * NE * m
        ret, fst = [], []
        for r in range(10):
            dem = msprime.Demography.island_model([NE, NE], migration_rate=m)
            ts = msprime.sim_ancestry(
                samples={"pop_0": 100, "pop_1": 100}, demography=dem,
                sequence_length=SEQ, recombination_rate=RHO,
                random_seed=35101 + r + int(1e6 * m))
            mts = msprime.sim_mutations(ts, rate=MU, random_seed=135101 + r)
            if mts.num_sites < 200:
                continue
            gm = mts.genotype_matrix()
            A, B = mts.samples(population=0), mts.samples(population=1)
            fa, fb = gm[:, A].mean(axis=1), gm[:, B].mean(axis=1)
            keep = np.where((fa > 0.05) & (fa < 0.95)
                            & (fb > 0.05) & (fb < 0.95))[0]
            if keep.size < 100:
                continue
            fst.append(simlib.hudson_fst(
                gm[:, A].sum(1).astype(float), len(A),
                gm[:, B].sum(1).astype(float), len(B)))
            causal = keep[rng.choice(keep.size,
                                     size=min(80, keep.size), replace=False)]
            beta = rng.normal(0, 1, causal.size)
            XA = gm[np.ix_(causal, A)].astype(float).T
            XB = gm[np.ix_(causal, B)].astype(float).T
            XA = XA - XA.mean(0)
            XB = XB - XB.mean(0)
            # POPULATION-level weights, not fitted ones. The first version
            # fitted marginal effects in deme 0 from 60 diploids across 80
            # sites; those weights carried deme-0 sampling noise that does not
            # transfer, which depressed retention by a roughly constant amount
            # and left the measurement nearly FLAT across a hundredfold
            # migration sweep. Using the LD projection removes the fitting step
            # entirely: w = Sigma_A . beta is the deme-0 marginal effect vector,
            # and `targetSourceEffectProjection` is separately VALIDATED as
            # exactly that quantity (battery_bulk32).
            nA, nB = XA.shape[0], XB.shape[0]
            SA = (XA.T @ XA) / (nA - 1)
            SB = (XB.T @ XB) / (nB - 1)
            w = SA @ beta
            denom = float(w @ (SA @ beta))
            numer = float(w @ (SB @ beta))
            if abs(denom) > 1e-12:
                ret.append(numer / denom)
        sr, sf = simlib.summarize(ret), simlib.summarize(fst)
        # divide out the estimator's attenuation, measured on the same pipeline
        sr = dict(mean=sr["mean"] / ceil["mean"],
                  sem=abs(sr["mean"] / ceil["mean"]) * math.hypot(
                      sr["sem"] / max(abs(sr["mean"]), 1e-12),
                      ceil["sem"] / max(abs(ceil["mean"]), 1e-12)))
        F = sf["mean"]
        lean = (1 - F) * (bigM / (1 + bigM))
        lab = "m=%.0e (4Nm=%.1f)" % (m, bigM)
        print("  %-22s F_ST=%.4f  retention=%.4f ± %.4f | lean %.4f  "
              "(1-F) %.4f  M/(1+M) %.4f"
              % (lab, F, sr["mean"], sr["sem"], lean, 1 - F,
                 bigM / (1 + bigM)))
        cells.append(dict(design=lab, lean=lean, truth=sr["mean"],
                          sem=max(sr["sem"], 1e-6)))
        c_f.append(dict(design=lab, lean=1 - F, truth=sr["mean"],
                        sem=max(sr["sem"], 1e-6)))
        c_m.append(dict(design=lab, lean=bigM / (1 + bigM), truth=sr["mean"],
                        sem=max(sr["sem"], 1e-6)))
    reg = ("two-deme island model, Ne = 1000, 5 Mb with recombination; 80 causal "
           "sites drawn from those segregating in BOTH demes, score weights the"
           " deme-0 LD PROJECTION, and the observable is the fraction of the deme-0 "
           "score/genetic-value covariance that survives in deme 1, divided by "
           "the same estimator's panmictic ceiling to remove its attenuation")
    record("signalRetentionMigrationDrift", "PortabilityDrift.lean",
           "(1 - F) * M/(1+M)", cells, regime=reg, control=control)
    record("signalRetention [1 - F alone, competing]", "PortabilityDrift.lean",
           "1 - F", c_f, regime=reg, control=control)
    record("signalRetention [M/(1+M) alone, competing]",
           "PortabilityDrift.lean", "M/(1+M)", c_m, regime=reg,
           control=control)
    json.dump(RESULTS, open("battery_bulk35_results.json", "w"), indent=1,
              default=str)
    print("\n================ SUMMARY ================")
    for r in RESULTS:
        w = r.get("worst", {})
        print("%-22s %-52s worst %9.2f sems, %7.2f%% rel"
              % (r["verdict"], r["name"], w.get("sems_off", float("nan")),
                 100 * w.get("rel_err", float("nan"))))


if __name__ == "__main__":
    main()
