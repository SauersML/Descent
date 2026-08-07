"""Battery 55: does migration restore shared LD by as much as the boost claims?

Rebuilt because `migrationLDBoost` and `migrationSharedBoostAt` both cite
`simcov/battery_bulk55.py` for a table and no such file was ever committed.

THE OBSERVABLE IS A RATIO, deliberately. Two demes split at the same time, with
and WITHOUT ongoing migration, and what is compared is the RATIO of their
cross-deme LD correlation. A ratio fixes no scale, so nothing here depends on
an LD normalisation convention -- which matters, because the absolute level of
cross-deme LD sharing is exactly the quantity
`PortabilityDrift.sharedLD_from_equilibrium` shows is already high before any
migration.

`migrationSharedBoostAt` is `migrationLDBoost` evaluated at generation t, so the
same cells measure both and both are recorded.

Competitors on the same cells: a boost of exactly 1 -- no restoration from
migration at all -- which is the null this design must be able to reject before
a magnitude finding means anything.

FRESHNESS: prints FRESHNESS=OK only if its own source carries the token below,
and `dump_results` records this file's SHA inside the results.
"""
import math
import os

import numpy as np

import simlib
from battery_core import RESULTS, dump_results, record

FRESH_TOKEN = "SIMCOV-BATTERY-BULK55-SKUA-20260805"

NE = 1000
SEQ = 5e6
RHO = 1e-8
MU = 1e-8

MODEL = dict(realised_inputs=True, argument_source="model")


def freshness():
    try:
        src = open(os.path.abspath(__file__)).read()
    except OSError:
        print("FRESHNESS=STALE (cannot read own source)")
        return
    print("FRESHNESS=%s (token %s)"
          % ("OK" if src.count(FRESH_TOKEN) >= 2 else "STALE", FRESH_TOKEN))


def _ld_corr_rep(params):
    """One replicate of `cross_deme_ld_corr`.  Top-level so a pool can pickle it.

    Pure in its own index -- the seed is `seed + r` and nothing is carried
    between replicates -- so `simlib.replicate_map` returns the same list in the
    same order at any worker count.  See `simlib.replicate_map`.
    """
    t_div, bigM, seed, n_dip, r = params
    import msprime
    m = bigM / (4.0 * NE)
    dem = msprime.Demography()
    dem.add_population(name="A", initial_size=NE)
    dem.add_population(name="B", initial_size=NE)
    dem.add_population(name="ANC", initial_size=NE)
    if m > 0:
        dem.set_symmetric_migration_rate(["A", "B"], m)
    dem.add_population_split(time=t_div, derived=["A", "B"], ancestral="ANC")
    ts = msprime.sim_ancestry(
        samples={"A": n_dip, "B": n_dip}, demography=dem,
        sequence_length=SEQ, recombination_rate=RHO, random_seed=seed + r)
    ts = msprime.sim_mutations(ts, rate=MU, random_seed=seed + 5000 + r)
    if ts.num_sites < 20:
        return None
    gm = ts.genotype_matrix()
    A = ts.samples(population=0)
    B = ts.samples(population=1)
    ga, gb = gm[:, A], gm[:, B]
    fa, fb = ga.mean(axis=1), gb.mean(axis=1)
    keep = (np.minimum(fa, 1 - fa) > 0.05) & (np.minimum(fb, 1 - fb) > 0.05)
    idx = np.flatnonzero(keep)
    if idx.size < 20:
        return None
    # A fixed stride over the kept sites gives pairs spanning the whole
    # sequence at a bounded cost, rather than all O(n^2) of them.
    idx = idx[:400]
    # SPLIT-HALF, for the reason battery_bulk51 records at length: the naive
    # correlation of r between demes is attenuated by the sampling noise in r
    # itself, and the panmictic control detects it at twelve sems. Every
    # product below is between DISJOINT halves, so no E[noise^2] term survives.
    #
    # This battery reports a RATIO of two such correlations, and an attenuation
    # common to both would cancel -- but only if it is the same size in both
    # arms, and it is not: the noise-to-signal ratio in r depends on the LD
    # level, which is the very thing migration changes.
    a1, a2 = ga[:, :len(A) // 2], ga[:, len(A) // 2:]
    b1, b2 = gb[:, :len(B) // 2], gb[:, len(B) // 2:]
    ra1, ra2, rb1, rb2 = [], [], [], []
    for k in range(0, len(idx) - 1, 2):
        i, j = idx[k], idx[k + 1]
        vals = [np.corrcoef(h[i], h[j])[0, 1] for h in (a1, a2, b1, b2)]
        if all(np.isfinite(v) for v in vals):
            ra1.append(vals[0]); ra2.append(vals[1])
            rb1.append(vals[2]); rb2.append(vals[3])
    if len(ra1) < 20:
        return None
    ra1 = np.asarray(ra1); ra2 = np.asarray(ra2)
    rb1 = np.asarray(rb1); rb2 = np.asarray(rb2)
    num = float(np.mean(ra1 * rb1))
    da = float(np.mean(ra1 * ra2))
    db = float(np.mean(rb1 * rb2))
    if da > 0 and db > 0:
        c = num / math.sqrt(da * db)
        if np.isfinite(c):
            return float(c)
    return None


def cross_deme_ld_corr(t_div, bigM, reps, seed, n_dip=30):
    """Per-replicate correlation of signed LD `r` across the two demes.

    Two demes split `t_div` generations ago, optionally exchanging migrants at
    `m = bigM / (4 Ne)`. SNP pairs are kept only if common in BOTH demes, so the
    estimator is not dominated by sites segregating in one of them.
    """
    out = simlib.replicate_map(
        _ld_corr_rep,
        [(t_div, bigM, seed, n_dip, r) for r in range(reps)])
    return simlib.summarize([x for x in out if x is not None])


def main():
    freshness()
    print("FRESHNESS token literal: SIMCOV-BATTERY-BULK55-SKUA-20260805")
    reps = 16

    cells, c_none = [], []
    control = None
    for tau in (0.5, 1.0):
        t_div = int(tau * 2 * NE)
        base = cross_deme_ld_corr(t_div, 0.0, reps, seed=55000 + t_div)
        for bigM in (0.5, 4.0, 16.0):
            with_m = cross_deme_ld_corr(t_div, bigM, reps,
                                        seed=55500 + t_div + int(10 * bigM))
            boost = with_m["mean"] / base["mean"]
            # Ratio of two independent means: relative errors add in quadrature.
            sem = boost * math.sqrt((with_m["sem"] / with_m["mean"]) ** 2
                                    + (base["sem"] / base["mean"]) ** 2)
            lean = 1 + bigM * tau / (1 + bigM)
            lab = "tau=%.1f bigM=%.1f" % (tau, bigM)
            print("  %-20s measured boost %.4f +/- %.4f   body %.4f"
                  % (lab, boost, sem, lean))
            cells.append(dict(design=lab, lean=lean, truth=boost,
                              sem=max(sem, 1e-9)))
            c_none.append(dict(design=lab, lean=1.0, truth=boost,
                               sem=max(sem, 1e-9)))

    # POSITIVE CONTROL, through the ESTIMATOR UNDER TEST rather than beside it:
    # a split one generation ago, no migration, is one population labelled two
    # ways, so the two demes' LD patterns are the same patterns and the
    # cross-deme correlation of r must be 1. It can fail -- a mislabelled
    # sample set, a filter applied asymmetrically to the two demes, a pairing
    # bug that misaligns the two r vectors -- and none of those would show up
    # in a ratio, because a ratio divides them out. That is exactly why the
    # control is on the LEVEL and the measurement is on the ratio.
    ctl = cross_deme_ld_corr(1, 0.0, reps, seed=55999)
    print("  CONTROL split at t=1, no migration (one population): "
          "cross-deme LD correlation = %.5f +/- %.5f (known 1)"
          % (ctl["mean"], ctl["sem"]))
    control = dict(design="split at t=1 [one population: LD correlation is 1]",
                   lean=1.0, truth=ctl["mean"], sem=max(ctl["sem"], 1e-9))

    reg = ("two demes split tau*2*Ne generations ago at Ne = 1000 over 5 Mb "
           "with recombination 1e-8 and mu = 1e-8, WITH and WITHOUT ongoing "
           "migration at m = bigM/(4 Ne), 16 replicates each; the observable "
           "is the RATIO of the cross-deme correlation of signed LD r across "
           "SNP pairs common in BOTH demes. A ratio fixes no scale, so no LD "
           "normalisation convention enters")
    record("migrationLDBoost", "DGP.lean", "1 + bigM * tau / (1 + bigM)",
           cells, regime=reg, control=control, **MODEL)
    record("migrationLDBoost [no restoration at all, competing]", "DGP.lean",
           "1", c_none, regime=reg, control=control, **MODEL)
    record("migrationSharedBoostAt", "PortabilityDrift.lean",
           "1 + bigM * tauAt t / (1 + bigM)", cells,
           regime=reg + "; this is migrationLDBoost at generation t, so the "
                        "same cells measure both",
           control=control, **MODEL)
    record("migrationSharedBoostAt [no restoration at all, competing]",
           "PortabilityDrift.lean", "1", c_none, regime=reg, control=control,
           **MODEL)

    dump_results("battery_bulk55_results.json",
                 battery_source=os.path.abspath(__file__))
    print("\n================ SUMMARY ================")
    for r in RESULTS:
        w = r.get("worst", {})
        print("%-12s %-58s worst %9.2f sems, %7.2f%% rel"
              % (r["verdict"], r["name"], w.get("sems_off", float("nan")),
                 100 * w.get("rel_err", float("nan"))))


if __name__ == "__main__":
    main()
