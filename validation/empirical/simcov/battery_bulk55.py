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

    # THE DESIGN SWEEPS `tau` EIGHTFOLD, and that is the change.
    #
    # The previous run held `tau` to 0.5 and 1.0 -- a factor of two -- and
    # reported the body FALSIFIED on magnitude. Magnitude was the wrong reading
    # of its own numbers: at each `bigM` the measured EXCESS was the same at
    # both depths to within a sem, while the body says the excess is
    # PROPORTIONAL to `tau` and must therefore double. A factor of two in the
    # swept parameter is not enough to separate "too large by a constant" from
    # "does not depend on tau at all", and those call for different repairs --
    # one rescales a constant, the other deletes an argument.
    #
    # So `tau` runs 0.25 to 2.0 here. If the excess is still flat across an
    # eightfold change in divergence depth, no constant repairs the body.
    taus = (0.25, 0.5, 1.0, 2.0)
    bigMs = (0.5, 4.0, 16.0)
    obs = []
    for tau in taus:
        t_div = int(tau * 2 * NE)
        base = cross_deme_ld_corr(t_div, 0.0, reps, seed=55000 + t_div)
        for bigM in bigMs:
            with_m = cross_deme_ld_corr(t_div, bigM, reps,
                                        seed=55500 + t_div + int(10 * bigM))
            boost = with_m["mean"] / base["mean"]
            # Ratio of two independent means: relative errors add in quadrature.
            sem = boost * math.sqrt((with_m["sem"] / with_m["mean"]) ** 2
                                    + (base["sem"] / base["mean"]) ** 2)
            lab = "tau=%.2f bigM=%.1f" % (tau, bigM)
            print("  %-22s measured boost %.4f +/- %.4f   body %.4f"
                  % (lab, boost, sem, 1 + bigM * tau / (1 + bigM)))
            obs.append((tau, bigM, lab, boost, max(sem, 1e-9)))

    # ONE FREE PARAMETER EACH, and the corpus body gets none.
    #
    # The question is no longer whether the body's amplitude is right -- it
    # plainly is not -- but whether its SHAPE is. So both rivals are fitted, by
    # weighted least squares on these very cells, and the body is not. A rival
    # fitted to the curve it is tested against is the strongest form the
    # comparison can take: if the tau-BEARING shape still loses to the tau-FREE
    # one with an amplitude chosen in its favour, no choice of constant repairs
    # the tau factor, and the argument has to go rather than be rescaled.
    def fit(basis):
        num = sum(basis(t, M) * (b - 1.0) / s ** 2 for t, M, _, b, s in obs)
        den = sum(basis(t, M) ** 2 / s ** 2 for t, M, _, b, s in obs)
        return num / den if den > 0 else 0.0

    tau_basis = lambda t, M: M * t / (1 + M)
    flat_basis = lambda t, M: M / (1 + M)
    a_tau = fit(tau_basis)
    a_flat = fit(flat_basis)
    print("  fitted amplitudes: tau-bearing a=%.4f, tau-free a=%.4f"
          % (a_tau, a_flat))

    cells, c_none, c_fit_tau, c_flat = [], [], [], []
    for tau, bigM, lab, boost, sem in obs:
        cell = lambda v: dict(design=lab, lean=v, truth=boost, sem=sem)
        cells.append(cell(1 + bigM * tau / (1 + bigM)))
        c_none.append(cell(1.0))
        c_fit_tau.append(cell(1 + a_tau * tau_basis(tau, bigM)))
        c_flat.append(cell(1 + a_flat * flat_basis(tau, bigM)))

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
           "migration at m = bigM/(4 Ne), %d replicates each; tau sweeps 0.25 "
           "to 2.0, EIGHTFOLD, which is what separates an amplitude error from "
           "a dependence that is not there. The observable is the RATIO of the "
           "cross-deme correlation of signed LD r across SNP pairs common in "
           "BOTH demes. A ratio fixes no scale, so no LD normalisation "
           "convention enters" % reps)
    fitted = ("; this rival is FITTED by weighted least squares on these very "
              "cells, and the corpus body is not, so it is being given every "
              "advantage the comparison can give it")
    record("migrationLDBoost", "DGP.lean", "1 + bigM * tau / (1 + bigM)",
           cells, regime=reg, control=control, **MODEL)
    record("migrationLDBoost [no restoration at all, competing]", "DGP.lean",
           "1", c_none, regime=reg, control=control, **MODEL)
    record("migrationLDBoost [tau-bearing shape, free amplitude, competing]",
           "DGP.lean", "1 + a * bigM * tau / (1 + bigM), a fitted",
           c_fit_tau, regime=reg + fitted, control=control,
           note="the body's own shape with its magnitude repaired: this is the "
                "best any rescaling of the constant can do, and it is carried "
                "so that a magnitude reading of this design can be excluded "
                "rather than assumed away",
           **MODEL)
    record("migrationLDBoost [tau-free, free amplitude, competing]",
           "DGP.lean", "1 + a * bigM / (1 + bigM), a fitted", c_flat,
           regime=reg + fitted, control=control,
           note="the same one free parameter, spent on an amplitude instead of "
                "on a tau. If this beats the row above across an eightfold tau "
                "sweep then the divergence depth does not enter the boost, and "
                "the repair deletes the argument rather than rescaling it",
           **MODEL)
    record("migrationSharedBoostAt", "PortabilityDrift.lean",
           "1 + bigM * tauAt t / (1 + bigM)", cells,
           regime=reg + "; this is migrationLDBoost at generation t, so the "
                        "same cells measure both",
           control=control, **MODEL)
    record("migrationSharedBoostAt [no restoration at all, competing]",
           "PortabilityDrift.lean", "1", c_none, regime=reg, control=control,
           **MODEL)
    record("migrationSharedBoostAt [tau-free, free amplitude, competing]",
           "PortabilityDrift.lean", "1 + a * bigM / (1 + bigM), a fitted",
           c_flat, regime=reg + fitted, control=control,
           note="same rival, same cells: whatever the tau sweep says about "
                "migrationLDBoost it says about this one, because they are the "
                "same expression read at a generation",
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
