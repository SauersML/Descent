"""Battery pd1: the island-model equilibrium F_ST, exact fixed point vs diffusion.

FOUR uncovered PortabilityDrift bodies stand or fall together here, because
three of them forward to the other two:

    ibdRecurrenceFixedPoint Ne rate = (1-rate)^2 / ((1-rate)^2 + 2*Ne*rate*(2-rate))
    fstIslandMultiplicativeEquilibrium Ne m = ibdRecurrenceFixedPoint Ne m
    fstMigrationDriftEquilibrium Ne m = 1 / (1 + 4*Ne*m)              [the rival]
    SplitMigrationModel.fstEqLimitLowMutationManyDemes = 1/(1 + scaledMigrationRate Ne mig)
    SplitMigrationModel.fstMigDriftEq = fstMigrationDriftEquilibrium s.Ne s.mig

THE DESIGN POINT.  The two closed forms differ in `m`, NOT in `4*Ne*m`: hold the
compound parameter fixed and they stay within a percent of each other forever,
which is how three earlier runs (bulk1, bulk20) reached an UNINFORMATIVE MATCH
where both forms passed.  So `m` is swept 50-fold at fixed `4*Ne*m` by SHRINKING
`Ne`, and `4*Ne*m` is swept 4-fold so the rival has a prediction span at all --
a constant prediction scores NO POWER and rejects nothing.

THE SIMULATION.  Explicit Wright-Fisher island model, written here rather than
taken from a coalescent library, because the corpus's recurrence declares a
COMPOSITION CONVENTION -- "the disrupting event acts on the offspring generation
*after* reproduction" -- and the two orderings have fixed points differing by
(1-m)^2, a factor of FOUR at m = 0.5, which is the whole discriminating range.
One generation is

    p_i     <- count_i / (2N)
    pmix_i  <- (1-m) p_i + m * mean_{j != i} p_j        (migration, then)
    count_i <- Binomial(2N, pmix_i)                     (reproduction)

and F_ST is read off `count` post-update, which is the post-migration census the
recurrence is written at.  Drawing 2N gametes from the finite parental deme's own
frequency p_i is what puts the 1/(2N) coalescence in: two draws from a pool of
2N include the self-pair with probability 1/(2N).

THE ESTIMATOR is the identity-probability convention the recurrence denotes, on
DISTINCT pairs, as a ratio of averages over loci:

    J0 = [k(k-1) + (2N-k)(2N-k-1)] / (2N(2N-1))     within a deme
    J1 = mean over ordered pairs i != j of  p_i p_j + (1-p_i)(1-p_j)
    F_ST = mean_loci(J0 - J1) / mean_loci(1 - J1)

Distinct pairs, not `Var(p)/(pbar(1-pbar))`: the with-replacement reading adds
1/(2N) to F_ST, which at N = 2 is 0.25 against a signal of 0.24.  Ratio of
averages, not average of ratios: a per-locus parametric formula against a
mean-of-ratios estimator "falsifies" any correct formula by Jensen.

CONTROLS, both able to fail:
  C1  panmictic pool, d labelled demes all drawing from the global frequency:
      F_ST must be 0.  This is the control that catches the self-pair bias --
      the with-replacement estimator returns 1/(2N) here, not 0.
  C2  ONE population, no migration, two-way mutation at rate mu: the stationary
      allele frequency is Beta(4 N mu, 4 N mu), so Var(p) = 1/(4(2a+1)) with
      a = 4 N mu.  Published, independent of everything island, and it fails if
      the ploidy or the mutation ordering is wrong.
  C3  the formal `control=` handed to verdict.classify: the small-m cell against
      Wright's law with Latter's finite-deme correction, 1/(1 + 4 N m (d/(d-1))^2),
      which is a known result in the regime it was derived for.

argument_source = "model": every argument fed to both closed forms is a
simulation SETUP parameter (N, m as written into the update rule), never an
estimate taken from the replicates the oracle measures.
"""
import json
import math
import os
import sys
from multiprocessing import Pool

import numpy as np

GUARD = "PD1-FRESHNESS-ISLAND-FIXEDPOINT-v3"

D_DEMES = int(os.environ.get("PD1_D", "200"))


# ---------------------------------------------------------------------------
# the simulation
# ---------------------------------------------------------------------------
def island_fst_rep(N, m, d, L, gens, burn, mu, seed, panmictic=False):
    """One independent replicate metapopulation -> one F_ST number."""
    twoN = 2 * N
    rng = np.random.default_rng(seed)
    cnt = rng.binomial(twoN, 0.5, size=(d, L)).astype(np.int64)
    num = 0.0
    den = 0.0
    for g in range(gens):
        p = cnt / twoN
        if panmictic:
            pmix = np.broadcast_to(p.mean(axis=0, keepdims=True), p.shape)
        else:
            tot = p.sum(axis=0, keepdims=True)
            pmix = (1.0 - m) * p + m * (tot - p) / (d - 1)
        if mu > 0.0:
            pmix = pmix * (1.0 - mu) + (1.0 - pmix) * mu
        cnt = rng.binomial(twoN, pmix)
        if g >= burn:
            k = cnt.astype(np.float64)
            j0 = (k * (k - 1.0) + (twoN - k) * (twoN - k - 1.0)) / (twoN * (twoN - 1.0))
            j0m = j0.mean(axis=0)
            q = 1.0 - cnt / twoN
            pp = cnt / twoN
            s1 = pp.sum(axis=0)
            s2 = (pp * pp).sum(axis=0)
            t1 = q.sum(axis=0)
            t2 = (q * q).sum(axis=0)
            j1 = ((s1 * s1 - s2) + (t1 * t1 - t2)) / (d * (d - 1.0))
            num += float((j0m - j1).sum())
            den += float((1.0 - j1).sum())
    return num / den


def beta_var_rep(N, mu, L, gens, burn, seed):
    """One population, two-way mutation, no migration: Var(p) at stationarity."""
    twoN = 2 * N
    rng = np.random.default_rng(seed)
    cnt = rng.binomial(twoN, 0.5, size=L).astype(np.int64)
    acc = []
    for g in range(gens):
        p = cnt / twoN
        pm = p * (1.0 - mu) + (1.0 - p) * mu
        cnt = rng.binomial(twoN, pm)
        if g >= burn:
            pp = cnt / twoN
            # unbiased for Var of the UNDERLYING frequency: the census p IS the
            # underlying frequency here (whole population), so the plain second
            # moment about 1/2 is what the Beta stationary law predicts.
            acc.append(float(np.mean((pp - 0.5) ** 2)))
    return float(np.mean(acc))


# ---------------------------------------------------------------------------
# work units
# ---------------------------------------------------------------------------
def _job(a):
    kind = a[0]
    if kind == "island":
        _, N, m, L, gens, burn, mu, seed, pan = a
        return island_fst_rep(N, m, D_DEMES, L, gens, burn, mu, seed, pan)
    _, N, mu, L, gens, burn, seed = a
    return beta_var_rep(N, mu, L, gens, burn, seed)


REPS = 10

# (N, m, L, gens, burn)  --  4*N*m and the sweep of m at fixed 4*N*m
CELLS = [
    (200, 0.010,   700, 900, 500),   # 4Nm = 8.0
    (50,  0.010,   700, 900, 500),   # 4Nm = 2.0
    (13,  2.0 / 13, 1500, 600, 200), # 4Nm = 8.0, m = 0.1538
    (4,   0.500,  2000, 600, 200),   # 4Nm = 8.0
    (2,   0.250,  2000, 600, 200),   # 4Nm = 2.0
]


def exact(N, m):
    return (1 - m) ** 2 / ((1 - m) ** 2 + 2 * N * m * (2 - m))


def diffusion(N, m):
    return 1.0 / (1.0 + 4 * N * m)


def latter(N, m, d):
    return 1.0 / (1.0 + 4 * N * m * (d / (d - 1.0)) ** 2)


def summarize(vals):
    v = np.array(vals, dtype=float)
    return float(v.mean()), float(v.std(ddof=1) / math.sqrt(len(v)))


def main():
    print("FRESHNESS_GUARD=%s" % GUARD)
    pool = Pool(20)

    jobs = []
    for (N, m, L, gens, burn) in CELLS:
        mu = 0.0025 / N
        for r in range(REPS):
            jobs.append(("island", N, m, L, gens, burn, mu, 90001 + 977 * r + int(1e5 * m) + N, False))
    # C1: panmictic, d labelled demes from the global pool.  N and L taken from
    # the smallest-N cell, which is where a self-pair bias would be largest.
    for r in range(REPS):
        jobs.append(("island", 4, 0.0, 2000, 250, 150, 0.0025 / 4, 41001 + 977 * r, True))
    # C2: Beta(a,a) stationarity, two values of a = 4*N*mu.
    for a in (1.0, 0.25):
        for r in range(REPS):
            jobs.append(("beta", 25, a / (4 * 25), 4000, 1200, 600, 71001 + 977 * r + int(100 * a)))

    out = pool.map(_job, jobs)
    pool.close()
    pool.join()

    k = 0
    cells_exact, cells_diff = [], []
    control = None
    for (N, m, L, gens, burn) in CELLS:
        vals = out[k:k + REPS]
        k += REPS
        mean, sem = summarize(vals)
        design = "Ne=%d m=%.4f (4Nm=%.1f)" % (N, m, 4 * N * m)
        cells_exact.append(dict(design=design, lean=exact(N, m), truth=mean, sem=sem))
        cells_diff.append(dict(design=design, lean=diffusion(N, m), truth=mean, sem=sem))
        if N == 200:
            c3 = (latter(N, m, D_DEMES), mean, sem)

    pan_vals = out[k:k + REPS]
    k += REPS
    pan_mean, pan_sem = summarize(pan_vals)
    # The FORMAL gate is C1, chosen before the run and for a reason: C3 sits at
    # the small-m cell where BOTH candidate forms already agree to a percent, so
    # it gates nothing about the discrimination this design exists to make,
    # while C1 gates the ESTIMATOR, which is the component that has actually
    # broken here (the with-replacement reading returns 1/(2N), not 0).
    control = dict(design="panmictic pool, %d labelled demes, F_ST = 0" % D_DEMES,
                   lean=0.0, truth=pan_mean, sem=pan_sem)

    c2 = []
    for a in (1.0, 0.25):
        vals = out[k:k + REPS]
        k += REPS
        mean, sem = summarize(vals)
        c2.append((a, mean, sem, 1.0 / (4.0 * (2.0 * a + 1.0))))

    print("\nCONTROL C1  panmictic pool, %d labelled demes, expected F_ST = 0" % D_DEMES)
    print("  measured %.6f +/- %.6f   (%.2f sems from zero)"
          % (pan_mean, pan_sem, abs(pan_mean) / pan_sem))
    print("  the with-replacement estimator would read 1/(2N) = %.4f here" % (1.0 / 8.0))
    print("\nCONTROL C2  Beta(a,a) stationary variance, one population, 2-way mutation")
    for (a, mean, sem, pred) in c2:
        print("  a=4Nmu=%.2f   Var(p) predicted %.5f   measured %.5f +/- %.5f   %.2f sems"
              % (a, pred, mean, sem, abs(mean - pred) / sem))

    import verdict
    results = []
    for (nm, src, cells) in (
        ("ibdRecurrenceFixedPoint / fstIslandMultiplicativeEquilibrium",
         "(1-rate)^2 / ((1-rate)^2 + 2*Ne*rate*(2-rate))", cells_exact),
        ("[competing] fstMigrationDriftEquilibrium / fstEqLimitLowMutationManyDemes / fstMigDriftEq",
         "1 / (1 + 4*Ne*m)", cells_diff),
    ):
        v, note, worst = verdict.classify(
            cells, control=control, sem_source="replicates", rel_floor=0.05)
        note = ("; ".join(x for x in (
            note,
            "control C1 panmictic F_ST = %.5f +/- %.5f (%.2f sems from 0)"
            % (pan_mean, pan_sem, abs(pan_mean) / pan_sem),
            "control C2 Beta(a,a) Var(p): " + ", ".join(
                "a=%.2f %.2f sems" % (a, abs(mn - pr) / se) for (a, mn, se, pr) in c2),
            "control C3 Wright/Latter 1/(1+4Nm(d/(d-1))^2) at the small-m cell: "
            "%.5f predicted vs %.5f +/- %.5f measured, %.2f sems"
            % (c3[0], c3[1], c3[2], abs(c3[0] - c3[1]) / c3[2]),
        ) if x))
        regime = ("explicit Wright-Fisher symmetric island model, %d demes, migration then "
                  "reproduction with the census read post-migration (the recurrence's declared "
                  "composition convention); identity-probability F_ST on DISTINCT pairs as a "
                  "ratio of averages over loci; %d independent replicate metapopulations per "
                  "cell, sem across replicates. m is swept 50-fold at fixed 4*Ne*m by shrinking "
                  "Ne, which is what separates the two closed forms; 4*Ne*m is swept 4-fold so "
                  "the rival has a span. rel_floor 0.05 absorbs the O(1/d) finite-deme term."
                  % (D_DEMES, REPS))
        verdict.report(nm, src, cells, v, note, worst, regime=regime)
        preds = [c["lean"] for c in cells]
        results.append(dict(name=nm, file="PortabilityDrift.lean", source=src,
                            note=note, regime=regime, verdict=v, worst=worst,
                            cells=cells, argument_source="model",
                            oracle_independent=True, sem_source="replicates",
                            span=(max(preds) - min(preds)) / max(abs(max(preds)), 1e-12),
                            guard=GUARD))

    results.append(dict(name="[controls]", file="PortabilityDrift.lean",
                        panmictic=dict(mean=pan_mean, sem=pan_sem),
                        beta=[dict(a=a, mean=mn, sem=se, predicted=pr) for (a, mn, se, pr) in c2],
                        guard=GUARD))
    json.dump(results, open("battery_pd1_d%d_results.json" % D_DEMES, "w"), indent=1)
    print("\nFRESHNESS_GUARD=%s DONE" % GUARD)


if __name__ == "__main__":
    main()
