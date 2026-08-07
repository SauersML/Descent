"""Battery 51: the LD-correlation migration ansatz, against a simulation.

Rebuilt because `ldCorrelationMigrationAnsatz` cites `simcov/battery_bulk51.py`
for a table and no such file was ever committed.

The declaration's own docstring says, in as many words, that the shape is a
STIPULATION and that nothing derives it -- "no source is cited, nothing derives
this shape from a migration process". This battery is the comparison that
paragraph says nobody had made.

The observable is the cross-deme correlation of signed LD `r` across SNP pairs
common in BOTH demes -- the quantity the body names -- with `4*Ne*m` swept a
hundredfold. The UNSQUARED `M/(1+M)` rides along, so a failure cannot be
dismissed as one power too many.

Control: one panmictic population split into two arbitrary halves, through the
SAME estimator and the SAME filters, must give an LD correlation of 1 and an
F_ST indistinguishable from zero. A control on the LEVEL is what this design
needs, because every failure mode of the pairing and filtering shows up there
and nowhere in the sweep.

FRESHNESS: prints FRESHNESS=OK only if its own source carries the token below,
and `dump_results` records this file's SHA inside the results.
"""
import math
import os

import numpy as np

import simlib
from battery_core import RESULTS, dump_results, record

FRESH_TOKEN = "SIMCOV-BATTERY-BULK51-FULMAR-20260805"

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


def _ld_fst_rep(params):
    """One replicate of `ld_corr_and_fst`.  Top-level so a pool can pickle it.

    Pure in its own index -- the seed is `seed + r` and nothing is carried
    between replicates -- so `simlib.replicate_map` returns the same list in the
    same order at any worker count.  See `simlib.replicate_map`.
    """
    bigM, seed, n_dip, panmictic, r = params
    import msprime
    if panmictic:
        ts = msprime.sim_ancestry(
            samples=2 * n_dip, population_size=NE, sequence_length=SEQ,
            recombination_rate=RHO, random_seed=seed + r)
    else:
        dem = msprime.Demography.island_model(
            [NE, NE], migration_rate=bigM / (4.0 * NE))
        ts = msprime.sim_ancestry(
            samples={"pop_0": n_dip, "pop_1": n_dip}, demography=dem,
            sequence_length=SEQ, recombination_rate=RHO,
            random_seed=seed + r)
    ts = msprime.sim_mutations(ts, rate=MU, random_seed=seed + 9000 + r)
    if ts.num_sites < 40:
        return None
    gm = ts.genotype_matrix()
    if panmictic:
        all_s = ts.samples()
        A, B = all_s[:2 * n_dip], all_s[2 * n_dip:]
    else:
        A, B = ts.samples(population=0), ts.samples(population=1)
    ga, gb = gm[:, A], gm[:, B]
    fa, fb = ga.mean(axis=1), gb.mean(axis=1)
    keep = ((np.minimum(fa, 1 - fa) > 0.05)
            & (np.minimum(fb, 1 - fb) > 0.05))
    idx = np.flatnonzero(keep)[:600]
    if idx.size < 40:
        return None
    # SPLIT-HALF, because the naive correlation of r between demes is
    # ATTENUATED and the control caught it: one panmictic population split
    # in two gave 0.9914 +/- 0.0007 where the answer is 1, twelve sems out.
    # Nothing was wrong with the simulation -- r estimated from a finite
    # sample carries noise, and a correlation between two noisy estimates
    # is pulled toward zero by exactly the noise-to-signal ratio.
    #
    # The repair is to build every product from DISJOINT halves, so no
    # E[noise^2] term survives: the numerator pairs deme A's first half
    # with deme B's first half (independent samples of independent demes),
    # and each denominator pairs a deme's two halves with each other.
    a1, a2 = ga[:, :len(A) // 2], ga[:, len(A) // 2:]
    b1, b2 = gb[:, :len(B) // 2], gb[:, len(B) // 2:]
    ra1, ra2, rb1, rb2 = [], [], [], []
    for k in range(0, idx.size - 1, 2):
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
    corr = None
    if da > 0 and db > 0:
        c = num / math.sqrt(da * db)
        if np.isfinite(c):
            corr = float(c)
    ac1 = ga.sum(axis=1).astype(float)
    ac2 = gb.sum(axis=1).astype(float)
    return (corr, simlib.hudson_fst(ac1, len(A), ac2, len(B)))


def ld_corr_and_fst(bigM, reps, seed, n_dip=30, panmictic=False):
    """(cross-deme LD correlation, Hudson F_ST) per replicate.

    With `panmictic=True` a single population is simulated and its samples are
    split into two arbitrary halves, which is the control: the same estimator
    and the same filters, on data where the answer is known.
    """
    out = simlib.replicate_map(
        _ld_fst_rep,
        [(bigM, seed, n_dip, panmictic, r) for r in range(reps)])
    corrs = [x[0] for x in out if x is not None and x[0] is not None]
    fsts = [x[1] for x in out if x is not None]
    return simlib.summarize(corrs), simlib.summarize(fsts)


def main():
    freshness()
    print("FRESHNESS token literal: SIMCOV-BATTERY-BULK51-FULMAR-20260805")
    reps = 20

    # A THOUSANDFOLD SWEEP, AND A SUCCESSOR THAT IS ALLOWED TO WIN.
    #
    # The previous run swept `4*Ne*m` a hundredfold and rejected both the ansatz
    # and its unsquared form. That is a complete finding about those two bodies
    # and no finding at all about what the quantity IS, and a withdrawal that
    # names no replacement leaves every consumer with the refuted number,
    # because it is the only one written down.
    #
    # So the sweep widens to a thousandfold and the design carries CANDIDATE
    # successors, fitted by weighted least squares on these very cells. Fitting
    # a rival to the curve it is tested against is the strongest form of a shape
    # claim: the ansatz gets no free parameter, the candidates get one or two,
    # and if a candidate still fails then no choice of constant rescues that
    # shape either -- which is the difference between "we have not found the
    # law" and "this family cannot contain it".
    #
    # The candidates are chosen from what the measurements already say. The
    # correlation is near ONE at the lowest migration and rises slowly, so the
    # object is a small DEFICIT that decays in M, not a share that grows from
    # zero: any body of the form f(M) -> 0 as M -> 0 is excluded before it is
    # fitted, and both refuted forms are of exactly that shape.
    bigMs = (0.1, 0.4, 1.0, 2.0, 8.0, 20.0, 40.0, 100.0)
    obs = []
    for bigM in bigMs:
        corr, fst = ld_corr_and_fst(bigM, reps, seed=51000 + int(10 * bigM))
        lab = "4Nem=%.1f" % bigM
        print("  %-12s measured LD corr %.5f +/- %.5f   ansatz %.5f   "
              "M/(1+M) %.5f   (F_ST %.4f)"
              % (lab, corr["mean"], corr["sem"], bigM ** 2 / (1 + bigM) ** 2,
                 bigM / (1 + bigM), fst["mean"]))
        obs.append((bigM, lab, corr["mean"], max(corr["sem"], 1e-9)))

    # The deficit `1 - corr` on a log-log grid: a straight line there is a power
    # law, and its slope is the exponent no amount of rescaling can supply.
    xs = [math.log(M) for M, _, c, _ in obs]
    ys = [math.log(max(1.0 - c, 1e-12)) for _, _, c, _ in obs]
    n = len(xs)
    mx, my = sum(xs) / n, sum(ys) / n
    sxx = sum((x - mx) ** 2 for x in xs)
    sxy = sum((x - mx) * (y - my) for x, y in zip(xs, ys))
    slope = sxy / sxx if sxx > 0 else 0.0
    logc = my - slope * mx
    b_free, c_free = -slope, math.exp(logc)
    print("  fitted deficit power law: 1 - corr = %.5f * M^(-%.4f)"
          % (c_free, b_free))

    def fit_amp(expo):
        """Weighted least-squares amplitude for `1 - corr = c * M^(-expo)`."""
        num = sum((M ** -expo) * (1.0 - t) / s ** 2 for M, _, t, s in obs)
        den = sum((M ** -expo) ** 2 / s ** 2 for M, _, t, s in obs)
        return num / den if den > 0 else 0.0

    c_half = fit_amp(0.5)
    print("  fitted amplitude at the pinned square-root exponent: c=%.5f"
          % c_half)

    cells, c_unsquared, c_pow, c_sqrt = [], [], [], []
    for bigM, lab, truth, sem in obs:
        cell = lambda v: dict(design=lab, lean=v, truth=truth, sem=sem)
        cells.append(cell(bigM ** 2 / (1 + bigM) ** 2))
        c_unsquared.append(cell(bigM / (1 + bigM)))
        c_pow.append(cell(1.0 - c_free * bigM ** (-b_free)))
        c_sqrt.append(cell(1.0 - c_half / math.sqrt(bigM)))

    ccorr, cfst = ld_corr_and_fst(0.0, reps, seed=51900, panmictic=True)
    print("  CONTROL panmictic, split into two arbitrary halves: LD corr "
          "%.5f +/- %.5f (known 1), F_ST %.5f +/- %.5f (known 0)"
          % (ccorr["mean"], ccorr["sem"], cfst["mean"], cfst["sem"]))
    control = dict(
        design="panmictic split into halves [LD correlation is 1]",
        lean=1.0, truth=ccorr["mean"], sem=max(ccorr["sem"], 1e-9))

    reg = ("two-deme island model at Ne = 1000 over 5 Mb with recombination "
           "1e-8 and mu = 1e-8, 20 replicates; the observable is the "
           "cross-deme correlation of signed LD r across SNP pairs common in "
           "BOTH demes -- the quantity this body names -- with 4*Ne*m swept a "
           "THOUSANDFOLD, 0.1 to 100. The control runs one panmictic "
           "population through the "
           "same estimator and the same filters")
    fitted = ("; this candidate is FITTED by weighted least squares on these "
              "very cells and the ansatz is not, so the comparison is being "
              "made on the ansatz's worst terms -- which is what makes a "
              "candidate's failure a statement about its SHAPE")
    record("ldCorrelationMigrationAnsatz", "PopulationGeneticsFoundations.lean",
           "M^2 / (1 + M)^2", cells, regime=reg, control=control, **MODEL)
    record("ldCorrelationMigrationAnsatz [unsquared M/(1+M), competing]",
           "PopulationGeneticsFoundations.lean", "M / (1 + M)", c_unsquared,
           regime=reg, control=control, **MODEL)
    record("ldCorrelationMigrationAnsatz "
           "[CANDIDATE: unit minus a free power law, competing]",
           "PopulationGeneticsFoundations.lean",
           "1 - c * M^(-b), both c and b fitted", c_pow,
           regime=reg + fitted,
           note="the shape the measurements point at rather than the shape the "
                "ansatz assumed: what migration moves is a DEFICIT that decays "
                "in M, not a share that grows from zero. Two free parameters "
                "against eight cells spanning a thousandfold in M",
           **MODEL)
    record("ldCorrelationMigrationAnsatz "
           "[CANDIDATE: unit minus c/sqrt(M), competing]",
           "PopulationGeneticsFoundations.lean",
           "1 - c / sqrt(M), c fitted and the exponent PINNED at one half",
           c_sqrt, regime=reg + fitted,
           note="the same family with the exponent held fixed instead of "
                "fitted, so it spends ONE parameter where the row above spends "
                "two. If it survives the same cells, the exponent is not a "
                "fitted quantity but a half, and the deficit is a diffusive "
                "one -- which is a claim a mechanism could be asked for",
           **MODEL)

    dump_results("battery_bulk51_results.json",
                 battery_source=os.path.abspath(__file__))
    print("\n================ SUMMARY ================")
    for r in RESULTS:
        w = r.get("worst", {})
        print("%-12s %-58s worst %9.2f sems, %7.2f%% rel"
              % (r["verdict"], r["name"], w.get("sems_off", float("nan")),
                 100 * w.get("rel_err", float("nan"))))


if __name__ == "__main__":
    main()
