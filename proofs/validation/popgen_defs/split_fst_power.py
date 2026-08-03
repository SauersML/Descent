"""Settle CHECK 1: is `coalFst = t/(t+2Ne)` consistent with msprime, or not?

The single-replicate run showed errors of +97.0%, -15.7%, -14.9%, -12.6% with
ALTERNATING SIGN, which reads like Monte Carlo noise -- and "probably noise" is
exactly the reasoning that leaves a real discrepancy unexamined.  So this
measures the error bars instead of assuming them.

NOTHING ABOUT THE MODEL IS CHANGED.  Same demography, same MU = RHO = 1e-8,
same 2 Mb, same 40+40 diploid samples, same Hudson ratio-of-averages estimator.
ONLY the replicate count and the GRID change.  Tuning the simulation until the
discrepancy shrinks is the failure this whole effort exists to prevent; adding
replicates and cells until the UNCERTAINTY shrinks is the opposite move and
leaves the estimand alone.

WHY ONE REPLICATE WAS NEVER GOING TO SETTLE IT: at Ne=1000, RHO=1e-8 and
L=2 Mb the expected number of recombination events is 4*Ne*RHO*L = 80, so a
replicate contains on the order of eighty independent genealogies.  An F_ST of
0.02 estimated from eighty trees has a standard error comparable to its own
value.

AND WHY FOUR CELLS WERE NEVER GOING TO SETTLE IT EITHER.  `coalFst` is a claim
about a CURVE, t/(t+2Ne) over the whole (t, Ne) plane, and four points cannot
distinguish a curve from a different curve that happens to pass near four
points.  Both axes are now swept log-spaced, because t/(2Ne) is the quantity
that matters and it spans three orders of magnitude across the grid: the
default sweep is 11 split times crossed with 6 population sizes, which puts the
scaled time t/(2Ne) between about 6e-4 and 26 and lets a reader see the shape
of the curve rather than four dots.

POOLING IS RATIO-OF-AVERAGES, NOT AVERAGE-OF-RATIOS.  Hudson's estimator is a
ratio of sums over sites; averaging per-replicate ratios is biased at small
F_ST, which is precisely where the +97% cell sits.  Numerator and denominator
are summed across every replicate and divided once.  The delete-one jackknife
over replicates gives the standard error of that pooled ratio.

Every replicate's own numerator and denominator are written to the results
file, not only the pooled ratio.  The jackknife can then be recomputed by a
reader, and -- the reason it matters here -- a cell whose pooled ratio is
carried by one outlying replicate is visible as such instead of averaging into
a clean-looking number.
"""
from __future__ import annotations

import argparse
import os
import sys
import time
from concurrent.futures import ProcessPoolExecutor

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

for _v in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS",
           "NUMEXPR_NUM_THREADS", "VECLIB_MAXIMUM_THREADS"):
    os.environ.setdefault(_v, "1")

import numpy as np  # noqa: E402

import simprov  # noqa: E402

MU = 1e-8
RHO = 1e-8
SEQ = 2e6
NDIP = 40                      # per deme, as in check_defs.py

# Default grid.  Log-spaced on both axes because t/(2Ne) is the argument of the
# law and it spans three decades here.  The four cells this file used to test --
# (1000, 50), (1000, 100), (1000, 1000), (5000, 4000) -- all lie on or beside
# this grid, so the old numbers remain comparable.
DEFAULT_NE = [500, 1000, 2000, 5000, 10000, 20000]
DEFAULT_T = simprov.int_log_grid(25, 25600, 11)
DEFAULT_REPS = 200
DEFAULT_SEED = 100000


def one(args):
    """Return (numerator_sum, denominator_sum, n_sites) for one replicate."""
    import msprime
    Ne, t, seed = args
    dem = msprime.Demography()
    dem.add_population(name="A", initial_size=Ne)
    dem.add_population(name="B", initial_size=Ne)
    dem.add_population(name="ANC", initial_size=Ne)
    dem.add_population_split(time=t, derived=["A", "B"], ancestral="ANC")
    ts = msprime.sim_ancestry(samples={"A": NDIP, "B": NDIP}, demography=dem,
                              sequence_length=SEQ, recombination_rate=RHO,
                              random_seed=seed)
    ts = msprime.sim_mutations(ts, rate=MU, random_seed=seed + 1)
    G = ts.genotype_matrix()
    if G.shape[0] == 0:
        return 0.0, 0.0, 0
    a = 2 * NDIP
    c1 = G[:, :a].sum(axis=1).astype(float)
    c2 = G[:, a:2 * a].sum(axis=1).astype(float)
    p1, p2 = c1 / a, c2 / a
    num = (p1 - p2) ** 2 - p1 * (1 - p1) / (a - 1) - p2 * (1 - p2) / (a - 1)
    den = p1 * (1 - p2) + p2 * (1 - p1)
    ok = den > 0
    return float(num[ok].sum()), float(den[ok].sum()), int(ok.sum())


def jackknife_se(nums, dens):
    """Delete-one jackknife SE of the pooled ratio sum(num)/sum(den)."""
    nums, dens = np.asarray(nums), np.asarray(dens)
    N = len(nums)
    if N < 2:
        return float("nan")
    sn, sd = nums.sum(), dens.sum()
    dd = sd - dens
    good = dd != 0
    jk = (sn - nums[good]) / dd[good]
    k = len(jk)
    if k < 2:
        return float("nan")
    return float(np.sqrt((k - 1) / k * ((jk - jk.mean()) ** 2).sum()))


def main(argv=None):
    ap = argparse.ArgumentParser(
        description="Sweep coalFst = t/(t+2Ne) against msprime.")
    ap.add_argument("--ne", type=simprov.parse_ints, default=DEFAULT_NE,
                    help="effective population sizes, comma separated")
    ap.add_argument("--split-times", type=simprov.parse_ints, default=DEFAULT_T,
                    help="split times in generations, comma separated")
    simprov.add_sweep_args(ap, DEFAULT_REPS, "split_fst_power.json",
                           DEFAULT_SEED)
    args = ap.parse_args(argv)

    cells_spec = [(Ne, t) for Ne in args.ne for t in args.split_times]
    jobs = [(Ne, t, args.seed + 7919 * r + 13 * Ne + t)
            for (Ne, t) in cells_spec for r in range(args.reps)]
    print("%d cells x %d replicates = %d simulations on %d workers"
          % (len(cells_spec), args.reps, len(jobs), args.jobs), flush=True)

    t0 = time.time()
    with ProcessPoolExecutor(max_workers=args.jobs) as ex:
        results = list(ex.map(one, jobs, chunksize=1))
    print("simulation wall time %.1f s" % (time.time() - t0), flush=True)

    records, cells = [], []
    for ci, (Ne, t) in enumerate(cells_spec):
        blk = results[ci * args.reps:(ci + 1) * args.reps]
        nums = np.array([b[0] for b in blk])
        dens = np.array([b[1] for b in blk])
        for r, (n, d, ns) in enumerate(blk):
            records.append(dict(Ne=Ne, t=t, rep=r, seed=jobs[ci * args.reps + r][2],
                                num=n, den=d, n_sites=ns,
                                fst_rep=(n / d) if d > 0 else None))
        lean = t / (t + 2.0 * Ne)
        if dens.sum() <= 0:
            cells.append(dict(Ne=Ne, t=t, reps=args.reps, sim=None, se=None,
                              coalFst=lean, deviation=None, z=None,
                              rel_err_pct=None, n_sites=simprov.summarize(
                                  [b[2] for b in blk])))
            continue
        pooled = float(nums.sum() / dens.sum())
        se = jackknife_se(nums, dens)
        dev = pooled - lean
        z = dev / se if se > 0 else float("nan")
        cells.append(dict(
            Ne=Ne, t=t, reps=args.reps, scaled_time=t / (2.0 * Ne),
            sim=pooled, se=se, coalFst=lean, deviation=dev, z=z,
            rel_err_pct=100.0 * dev / lean if lean > 0 else None,
            # Per-replicate ratios are biased at small F_ST, so they are NOT the
            # headline estimate; they are reported so the scatter is visible.
            per_rep_ratio=simprov.summarize(
                [(n / d) if d > 0 else float("nan") for n, d, _ in blk]),
            n_sites=simprov.summarize([b[2] for b in blk])))
        print("Ne=%-6d t=%-6d sim=%.5f +/- %.5f   coalFst=%.5f   "
              "dev=%+.5f  z=%+.2f  rel=%+.1f%%"
              % (Ne, t, pooled, se, lean, dev, z,
                 100.0 * dev / lean if lean > 0 else float("nan")), flush=True)

    zs = [abs(c["z"]) for c in cells
          if c["z"] is not None and np.isfinite(c["z"])]
    worst = max(zs) if zs else float("nan")
    print("")
    print("replicates per cell: %d" % args.reps)
    print("cells: %d" % len(cells))
    print("largest |z|: %.2f" % worst)
    # A sweep this wide will show a few |z| > 3 by chance alone, so the verdict
    # is stated against the count expected under the null, not against a single
    # threshold that a large grid is guaranteed to cross.
    exceed = sum(1 for z in zs if z > 3)
    expected = 0.0027 * len(zs)
    print("cells beyond 3 SE: %d of %d (expected under the null: %.1f)"
          % (exceed, len(zs), expected))
    if exceed <= max(1, 3 * expected):
        print("VERDICT: the excursions past 3 SE are no more numerous than")
        print("chance predicts across a grid this size. The single-replicate")
        print("errors were Monte Carlo noise; the formula is consistent with")
        print("msprime over the swept region.")
    else:
        print("VERDICT: more cells deviate past 3 SE than chance predicts.")
        print("This is NOT noise -- either coalFst is not the F_ST msprime")
        print("measures here, or the split model differs from the formula's.")
        print("Reporting rather than tuning.")

    p = simprov.write(args.output, "popgen_defs/split_fst_power.py",
                      dict(Ne=args.ne, split_times=args.split_times,
                           MU=MU, RHO=RHO, SEQ=SEQ, NDIP=NDIP),
                      args.seed, args.reps, cells, records)
    print("-> %s (%d cells, %d replicate records)"
          % (p, len(cells), len(records)))


if __name__ == "__main__":
    main()
