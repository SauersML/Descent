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


def ld_corr_and_fst(bigM, reps, seed, n_dip=30, panmictic=False):
    """(cross-deme LD correlation, Hudson F_ST) per replicate.

    With `panmictic=True` a single population is simulated and its samples are
    split into two arbitrary halves, which is the control: the same estimator
    and the same filters, on data where the answer is known.
    """
    import msprime
    corrs, fsts = [], []
    for r in range(reps):
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
            continue
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
            continue
        ra, rb = [], []
        for k in range(0, idx.size - 1, 2):
            i, j = idx[k], idx[k + 1]
            ca = np.corrcoef(ga[i], ga[j])[0, 1]
            cb = np.corrcoef(gb[i], gb[j])[0, 1]
            if np.isfinite(ca) and np.isfinite(cb):
                ra.append(ca)
                rb.append(cb)
        if len(ra) < 20:
            continue
        c = np.corrcoef(ra, rb)[0, 1]
        if np.isfinite(c):
            corrs.append(float(c))
        ac1 = ga.sum(axis=1).astype(float)
        ac2 = gb.sum(axis=1).astype(float)
        fsts.append(simlib.hudson_fst(ac1, len(A), ac2, len(B)))
    return simlib.summarize(corrs), simlib.summarize(fsts)


def main():
    freshness()
    print("FRESHNESS token literal: SIMCOV-BATTERY-BULK51-FULMAR-20260805")
    reps = 12

    cells, c_unsquared = [], []
    for bigM in (0.4, 2.0, 8.0, 40.0):
        corr, fst = ld_corr_and_fst(bigM, reps, seed=51000 + int(10 * bigM))
        lean = bigM ** 2 / (1 + bigM) ** 2
        unsq = bigM / (1 + bigM)
        lab = "4Nem=%.1f" % bigM
        print("  %-12s measured LD corr %.5f +/- %.5f   ansatz %.5f   "
              "M/(1+M) %.5f   (F_ST %.4f)"
              % (lab, corr["mean"], corr["sem"], lean, unsq, fst["mean"]))
        cells.append(dict(design=lab, lean=lean, truth=corr["mean"],
                          sem=max(corr["sem"], 1e-9)))
        c_unsquared.append(dict(design=lab, lean=unsq, truth=corr["mean"],
                                sem=max(corr["sem"], 1e-9)))

    ccorr, cfst = ld_corr_and_fst(0.0, reps, seed=51900, panmictic=True)
    print("  CONTROL panmictic, split into two arbitrary halves: LD corr "
          "%.5f +/- %.5f (known 1), F_ST %.5f +/- %.5f (known 0)"
          % (ccorr["mean"], ccorr["sem"], cfst["mean"], cfst["sem"]))
    control = dict(
        design="panmictic split into halves [LD correlation is 1]",
        lean=1.0, truth=ccorr["mean"], sem=max(ccorr["sem"], 1e-9))

    reg = ("two-deme island model at Ne = 1000 over 5 Mb with recombination "
           "1e-8 and mu = 1e-8, 12 replicates; the observable is the "
           "cross-deme correlation of signed LD r across SNP pairs common in "
           "BOTH demes -- the quantity this body names -- with 4*Ne*m swept a "
           "hundredfold. The control runs one panmictic population through the "
           "same estimator and the same filters")
    record("ldCorrelationMigrationAnsatz", "PopulationGeneticsFoundations.lean",
           "M^2 / (1 + M)^2", cells, regime=reg, control=control, **MODEL)
    record("ldCorrelationMigrationAnsatz [unsquared M/(1+M), competing]",
           "PopulationGeneticsFoundations.lean", "M / (1 + M)", c_unsquared,
           regime=reg, control=control, **MODEL)

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
