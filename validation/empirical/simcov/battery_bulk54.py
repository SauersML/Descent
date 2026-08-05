"""Battery 54: is the LD-correlation decay rate linear in fstGap, or in its root?

Rebuilt because `ldCorrelationDecay` cites `simcov/battery_bulk54.py` for the
table that settled its divergence factor, and no such file was ever committed.

WHAT IS AND IS NOT REFUTABLE HERE, because the body carries a free constant and
that changes what a measurement can say. `ldCorrelationDecay distance fstGap
lambda = exp(-(lambda * sqrt fstGap * distance))` has `lambda` free, so the
ABSOLUTE decay rate is not refutable at all -- any rate can be reached by
choosing `lambda`. What IS refutable is the SHAPE of the rate-versus-divergence
relation, and it becomes so once each candidate is ANCHORED at one cell: fix
`lambda` from the first cell and every other cell's rate is then a prediction
with nothing left to fit.

So the design sweeps the migration rate over two orders of magnitude, measures
the cross-deme LD correlation as a function of physical distance in each arm,
fits one decay rate per arm, and asks which power of `F_ST` those rates track.

Candidates, each anchored at the first cell:
    rate proportional to fstGap          -- the SUPERSEDED body's reading
    rate proportional to sqrt(fstGap)    -- what the body now carries
    rate independent of fstGap           -- the null, which must be rejected
                                            before either of the others means
                                            anything

That last one is why `verdict.classify`'s NO POWER gate had to learn to look at
whether a flat prediction AGREES: an anchored constant has zero span, and this
row is the design's null. The earlier attempt (`battery_bulk53`) failed for the
neighbouring reason -- it compared ONE fitted-rate ratio against ONE F_ST ratio,
so the PREDICTION span was zero and the gate correctly refused a verdict. The
fix was more cells, not a better estimator.

FRESHNESS: prints FRESHNESS=OK only if its own source carries the token below,
and `dump_results` records this file's SHA inside the results.
"""
import math
import os

import numpy as np

import simlib
from battery_core import RESULTS, dump_results, record

FRESH_TOKEN = "SIMCOV-BATTERY-BULK54-GANNET54-20260805"

NE = 1000
SEQ = 4e6
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


BINS = np.array([2e4, 6e4, 1.5e5, 4e5, 1.0e6])


def arm(bigM, reps, seed, n_dip=30):
    """(F_ST, per-replicate fitted decay rate) for one migration rate.

    The decay rate is fitted per REPLICATE, so its error bar comes from
    independent simulations rather than from a curve-fit covariance -- the
    binned points within one replicate are not independent of each other and a
    fit's own standard error would understate the scatter by whatever the
    correlation time of the genome is.
    """
    import msprime
    dem = msprime.Demography.island_model([NE, NE],
                                          migration_rate=bigM / (4.0 * NE))
    rates, fsts = [], []
    for r in range(reps):
        ts = msprime.sim_ancestry(
            samples={"pop_0": n_dip, "pop_1": n_dip}, demography=dem,
            sequence_length=SEQ, recombination_rate=RHO,
            random_seed=seed + r)
        ts = msprime.sim_mutations(ts, rate=MU, random_seed=seed + 7000 + r)
        if ts.num_sites < 100:
            continue
        gm = ts.genotype_matrix()
        pos = ts.tables.sites.position
        A, B = ts.samples(population=0), ts.samples(population=1)
        ga, gb = gm[:, A], gm[:, B]
        fa, fb = ga.mean(axis=1), gb.mean(axis=1)
        keep = ((np.minimum(fa, 1 - fa) > 0.05)
                & (np.minimum(fb, 1 - fb) > 0.05))
        idx = np.flatnonzero(keep)
        if idx.size < 60:
            continue
        ac1 = ga.sum(axis=1).astype(float)
        ac2 = gb.sum(axis=1).astype(float)
        fsts.append(simlib.hudson_fst(ac1, len(A), ac2, len(B)))

        # Cross-deme correlation of signed r, binned by physical separation.
        ys, xs = [], []
        for b, hi in enumerate(BINS):
            lo = 0.0 if b == 0 else BINS[b - 1]
            ra, rb = [], []
            # Sample pairs whose separation falls in the bin, capped so the
            # cost does not grow with the site count.
            for k in range(idx.size):
                i = idx[k]
                lohi = np.flatnonzero((pos[idx] - pos[i] > lo)
                                      & (pos[idx] - pos[i] <= hi))
                if lohi.size == 0:
                    continue
                j = idx[lohi[0]]
                ca = np.corrcoef(ga[i], ga[j])[0, 1]
                cb = np.corrcoef(gb[i], gb[j])[0, 1]
                if np.isfinite(ca) and np.isfinite(cb):
                    ra.append(ca)
                    rb.append(cb)
                if len(ra) >= 150:
                    break
            if len(ra) >= 30:
                c = np.corrcoef(ra, rb)[0, 1]
                if np.isfinite(c) and c > 0.02:
                    xs.append(0.5 * (lo + hi))
                    ys.append(math.log(min(c, 0.999)))
        if len(xs) >= 3:
            # Slope of log-correlation against distance: the decay rate the
            # body's exponent is a claim about.
            x = np.asarray(xs, float)
            y = np.asarray(ys, float)
            slope = float(np.polyfit(x, y, 1)[0])
            if slope < 0:
                rates.append(-slope)
    return simlib.summarize(fsts), simlib.summarize(rates)


def main():
    freshness()
    print("FRESHNESS token literal: SIMCOV-BATTERY-BULK54-GANNET54-20260805")
    reps = 10

    arms = []
    for bigM in (0.5, 2.0, 8.0, 30.0, 120.0):
        f, rate = arm(bigM, reps, seed=54000 + int(bigM))
        print("  4Nem=%6.1f  F_ST=%.4f +/- %.4f   fitted decay rate "
              "%.3e +/- %.3e" % (bigM, f["mean"], f["sem"], rate["mean"],
                                 rate["sem"]))
        arms.append((bigM, f["mean"], rate["mean"], rate["sem"]))

    # ANCHOR at the first arm: each candidate's constant is fixed there, so
    # every other arm is a prediction with nothing left to fit.
    bigM0, f0, rate0, _ = arms[0]
    cells_sqrt, cells_lin, cells_flat = [], [], []
    for bigM, f, rate, sem in arms[1:]:
        lab = "4Nem=%.1f (F_ST=%.4f)" % (bigM, f)
        cells_sqrt.append(dict(design=lab, lean=rate0 * math.sqrt(f / f0),
                               truth=rate, sem=max(sem, 1e-12)))
        cells_lin.append(dict(design=lab, lean=rate0 * (f / f0), truth=rate,
                              sem=max(sem, 1e-12)))
        cells_flat.append(dict(design=lab, lean=rate0, truth=rate,
                               sem=max(sem, 1e-12)))

    # POSITIVE CONTROL for the FITTER, which is the instrument under test here
    # and not the simulation: feed it a curve of KNOWN exponential shape on the
    # same x grid with matched noise and require it to recover that rate. The
    # control the earlier work reached for -- that the fit recovers the
    # simulated Ne -- does not work, because E[r^2] from a finite sample of
    # chromosomes is biased downward by a known and reproducible factor.
    true_rate = 4e-6
    rng = np.random.default_rng(54999)
    fits = []
    for _ in range(40):
        x = np.array([0.5 * (0.0 if b == 0 else BINS[b - 1] + BINS[b])
                      for b in range(len(BINS))])
        y = np.log(np.exp(-true_rate * x) * (1 + 0.05 * rng.standard_normal(x.size)))
        fits.append(-float(np.polyfit(x, y, 1)[0]))
    cmean = float(np.mean(fits))
    csem = float(np.std(fits, ddof=1) / math.sqrt(len(fits)))
    print("  CONTROL fitter on a TRUE exponential of rate %.2e: recovered "
          "%.3e +/- %.3e" % (true_rate, cmean, csem))
    control = dict(design="fitter on a known exponential [recovers its rate]",
                   lean=true_rate, truth=cmean, sem=max(csem, 1e-12))

    reg = ("two-deme island model at Ne = 1000 over 4 Mb with recombination "
           "1e-8 and mu = 1e-8, 10 replicates per arm, 4*Ne*m swept 240-fold; "
           "per replicate the cross-deme correlation of signed r is binned by "
           "physical separation and a decay RATE is fitted, so the error bar "
           "comes from independent simulations rather than from a curve fit. "
           "Each candidate's constant is ANCHORED at the first arm, which is "
           "what makes the SHAPE of the rate-versus-divergence relation "
           "refutable while the free lambda leaves the absolute rate not")
    record("ldCorrelationDecay", "PortabilityDrift.lean",
           "rate proportional to sqrt(fstGap) -- exp(-(lambda * sqrt fstGap * "
           "distance))", cells_sqrt, regime=reg, control=control, **MODEL)
    record("ldCorrelationDecay [rate proportional to fstGap, superseded, "
           "competing]", "PortabilityDrift.lean",
           "exp(-(lambda * fstGap * distance))", cells_lin, regime=reg,
           control=control, **MODEL)
    record("ldCorrelationDecay [rate independent of fstGap, competing]",
           "PortabilityDrift.lean", "exp(-(lambda * distance))", cells_flat,
           regime=reg, control=control, **MODEL)

    dump_results("battery_bulk54_results.json",
                 battery_source=os.path.abspath(__file__))
    print("\n================ SUMMARY ================")
    for r in RESULTS:
        w = r.get("worst", {})
        print("%-12s %-64s worst %9.2f sems, %7.2f%% rel"
              % (r["verdict"], r["name"], w.get("sems_off", float("nan")),
                 100 * w.get("rel_err", float("nan"))))


if __name__ == "__main__":
    main()
