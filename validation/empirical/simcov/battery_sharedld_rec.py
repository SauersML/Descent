"""Battery sharedld_rec: the shared-LD fraction against migration and recombination.

Rebuilt because `sharedLD_from_equilibrium` cites `simcov/battery_sharedld_rec.py`
for the table behind its CONDITIONALLY VALID marker, and no such file was ever
committed.

WHAT THE BODY IS A CLAIM ABOUT, and why the argument list is itself the finding.
`m / (m + c)` names a race between the migration that reunites two lineages and
the recombination that separates the two sites whose disequilibrium is being
shared. `F_ST` is a property of ONE site and shared LD of a PAIR, so no shape in
`F_ST` alone can be admissible -- and `Ne` is absent for the same reason: it sets
how much LD there is, not how much of it is shared. The design puts both of
those to the test by varying `Ne` THREEFOLD AT FIXED `m`, where an `Ne`-free
body must not move, and by sweeping `c/m` across two orders of magnitude at
fixed `F_ST`, where an `F_ST`-only body cannot move.

THE ESTIMATOR IS A SECOND-MOMENT RATIO, not a correlation of `r`. The declaration
says so -- "a fraction of the disequilibrium SECOND MOMENT, sigma_B/sigma_W, not
a correlation of r" -- and the two are different numbers.

EVERY PRODUCT IS TAKEN BETWEEN DISJOINT SAMPLE HALVES. That is what removes
sampling noise from both the numerator and the denominator: E[D_hat_1 * D_hat_2]
over independent halves has no E[noise^2] term, so the ratio is not attenuated.
The old correlation estimator returned 0.9945 on the panmictic control where the
answer is 1, and that 0.55% shortfall WAS the attenuation. With the split-half
denominator the control can fail for a reason other than its own bias, which is
the only way a control earns its place.

Competitors on the same cells, and each is killed by a different axis:
    1 - F_ST                     moves with Ne, not with c -- backwards
    M / (1 + M)                  same
    1 / (1 + 4*Ne*c)             the WITHIN-deme Sved shape: moves with c but
                                 not with m
    2*m / (2*m + c)              the shape that tracks the measurement past
                                 c ~ m/2, carried so the region where this body
                                 reads low is visible in the record. NOT a
                                 candidate for adoption: it is this race with
                                 the destruction rate halved by hand, and a
                                 fitted factor of two named as a law is what
                                 this corpus refuses.

FRESHNESS: prints FRESHNESS=OK only if its own source carries the token below,
and `dump_results` records this file's SHA inside the results.
"""
import math
import os

import numpy as np

import simlib
from battery_core import RESULTS, dump_results, record

FRESH_TOKEN = "SIMCOV-BATTERY-SHAREDLD-REC-PETREL-20260805"

SEQ = 6e6
RHO = 1e-8
MU = 1e-8

# `argument_source="model"` with `c` REALIZED from the separations of the pairs
# actually drawn, which is what the declaration's own docstring asks for: the
# nominal bin centre and the mean realised separation differ, and at these error
# bars the difference is not negligible.
MODEL = dict(realised_inputs=True, argument_source="model")


def freshness():
    try:
        src = open(os.path.abspath(__file__)).read()
    except OSError:
        print("FRESHNESS=STALE (cannot read own source)")
        return
    print("FRESHNESS=%s (token %s)"
          % ("OK" if src.count(FRESH_TOKEN) >= 2 else "STALE", FRESH_TOKEN))


def split_half_D(g_half1, g_half2, i, j):
    """E[D_1 * D_2] over two DISJOINT halves of the same sample.

    D is the standard two-locus disequilibrium p_AB - p_A p_B. Multiplying the
    estimate from one half by the estimate from the other gives an unbiased
    second moment with no E[noise^2] term, which is the whole point: the naive
    E[D_hat^2] carries the sampling variance of D_hat and attenuates every ratio
    built from it.
    """
    def D(g):
        a, b = g[i], g[j]
        return float((a * b).mean() - a.mean() * b.mean())
    return D(g_half1) * D(g_half2)


def cell(ne, m, reps, seed, bins, n_dip=40, panmictic=False):
    """(realised c, sigma_B/sigma_W) per distance bin.

    `sigma_W` is the within-deme second moment and `sigma_B` the between-deme
    one, both built from split-half products so neither is attenuated.
    """
    import msprime
    # PER-REPLICATE accumulators. The sem must come from independent
    # SIMULATIONS, not from blocks of pairs within one: pairs drawn from the
    # same genome share its whole coalescent history, so a within-replicate
    # block sem understates the scatter by whatever the correlation length is.
    # It did: the panmictic control came back 0.9560 +/- 0.0100, four sems from
    # a known 1, and VOIDed every verdict in the battery. The bar was the
    # defect, not the estimator.
    per_rep = {b: [] for b in range(len(bins))}
    acc = {b: {"num": [], "den": [], "sep": []} for b in range(len(bins))}
    for r in range(reps):
        if panmictic:
            dem = msprime.Demography()
            dem.add_population(name="P", initial_size=ne)
            ts = msprime.sim_ancestry(
                samples={"P": 2 * n_dip}, demography=dem, sequence_length=SEQ,
                recombination_rate=RHO, random_seed=seed + r)
        else:
            dem = msprime.Demography.island_model([ne, ne], migration_rate=m)
            ts = msprime.sim_ancestry(
                samples={"pop_0": n_dip, "pop_1": n_dip}, demography=dem,
                sequence_length=SEQ, recombination_rate=RHO,
                random_seed=seed + r)
        ts = msprime.sim_mutations(ts, rate=MU, random_seed=seed + 3000 + r)
        if ts.num_sites < 100:
            continue
        gm = ts.genotype_matrix().astype(float)
        pos = ts.tables.sites.position
        if panmictic:
            s = ts.samples()
            A, B = s[:2 * n_dip], s[2 * n_dip:]
        else:
            A, B = ts.samples(population=0), ts.samples(population=1)
        ga, gb = gm[:, A], gm[:, B]
        fa, fb = ga.mean(axis=1), gb.mean(axis=1)
        # PER-DEME frequency filter. The declaration's docstring names the
        # ascertainment systematic this choice carries (a pooled filter moves
        # the measured ratio by ~12%), so the choice is stated rather than
        # buried.
        keep = ((np.minimum(fa, 1 - fa) > 0.05)
                & (np.minimum(fb, 1 - fb) > 0.05))
        idx = np.flatnonzero(keep)
        if idx.size < 60:
            continue
        ha1, ha2 = ga[:, :len(A) // 2], ga[:, len(A) // 2:]
        hb1, hb2 = gb[:, :len(B) // 2], gb[:, len(B) // 2:]
        for b, (lo, hi) in enumerate(bins):
            n_used = 0
            rep_num, rep_den = [], []
            for k in range(idx.size):
                i = idx[k]
                cand = np.flatnonzero((pos[idx] - pos[i] > lo)
                                      & (pos[idx] - pos[i] <= hi))
                if cand.size == 0:
                    continue
                j = idx[cand[0]]
                # WITHIN: both halves from the same deme. BETWEEN: one half
                # from each deme, so the product is of two disequilibria that
                # share only what migration has made common.
                w = 0.5 * (split_half_D(ha1, ha2, i, j)
                           + split_half_D(hb1, hb2, i, j))
                bt = split_half_D(ha1, hb2, i, j)
                acc[b]["num"].append(bt)
                acc[b]["den"].append(w)
                acc[b]["sep"].append(float(pos[j] - pos[i]))
                rep_num.append(bt)
                rep_den.append(w)
                n_used += 1
                if n_used >= 120:
                    break
            if len(rep_den) >= 20 and float(np.mean(rep_den)) > 0:
                per_rep[b].append(float(np.mean(rep_num) / np.mean(rep_den)))
    out = []
    for b in range(len(bins)):
        den = np.asarray(acc[b]["den"], float)
        num = np.asarray(acc[b]["num"], float)
        sep = np.asarray(acc[b]["sep"], float)
        if den.size < 30 or den.mean() <= 0:
            out.append(None)
            continue
        # Ratio of averages, not average of ratios: the per-pair denominator
        # passes through zero and the per-pair ratio explodes there.
        ratio = float(num.mean() / den.mean())
        reps_here = per_rep[b]
        sem = (float(np.std(reps_here, ddof=1) / math.sqrt(len(reps_here)))
               if len(reps_here) > 2 else float("nan"))
        out.append(dict(ratio=ratio, sem=sem, c=float(sep.mean()) * RHO))
    return out


def main():
    freshness()
    print("FRESHNESS token literal: SIMCOV-BATTERY-SHAREDLD-REC-PETREL-20260805")
    reps = 6
    # Bins chosen so c/m spans from well inside the body's regime to well past
    # it at the migration rates below.
    bins = [(2e3, 1.5e4), (3e4, 9e4), (1.5e5, 4e5)]

    cells, c_fst, c_bigM, c_sved, c_halved = [], [], [], [], []
    for ne, m in ((2000, 4.0e-3), (1000, 1.0e-3), (2000, 1.0e-3),
                  (4000, 1.0e-3)):
        rows = cell(ne, m, reps, seed=61000 + ne + int(1e6 * m), bins=bins)
        bigM = 4.0 * ne * m
        fst = 1.0 / (1.0 + 4.0 * ne * m)
        for row in rows:
            if row is None or not (row["sem"] == row["sem"]):
                continue
            c = row["c"]
            lab = "Ne=%d m=%.1e c/m=%.2f" % (ne, m, c / m)
            lean = m / (m + c)
            print("  %-30s measured %.4f +/- %.4f   body %.4f   1-F %.4f   "
                  "M/(1+M) %.4f   Sved %.4f   2m/(2m+c) %.4f"
                  % (lab, row["ratio"], row["sem"], lean, 1 - fst,
                     bigM / (1 + bigM), 1.0 / (1 + 4 * ne * c),
                     2 * m / (2 * m + c)))
            common = dict(design=lab, truth=row["ratio"],
                          sem=max(row["sem"], 1e-9))
            cells.append(dict(lean=lean, **common))
            c_fst.append(dict(lean=1 - fst, **common))
            c_bigM.append(dict(lean=bigM / (1 + bigM), **common))
            c_sved.append(dict(lean=1.0 / (1 + 4 * ne * c), **common))
            c_halved.append(dict(lean=2 * m / (2 * m + c), **common))

    # POSITIVE CONTROL: one panmictic population split arbitrarily in two, run
    # through the SAME estimator. The two "demes" are the same population, so
    # the between-half second moment IS the within-half one and the ratio must
    # be 1 at every distance.
    ctl = cell(2000, 0.0, reps, seed=61999, bins=bins, panmictic=True)
    ok = [r for r in ctl if r and r["sem"] == r["sem"]]
    cmean = float(np.mean([r["ratio"] for r in ok]))
    csem = float(np.mean([r["sem"] for r in ok])) / math.sqrt(max(len(ok), 1))
    print("  CONTROL panmictic split in two: sigma_B/sigma_W = %.4f +/- %.4f "
          "(known 1)" % (cmean, csem))
    control = dict(design="panmictic split in two [ratio is 1 at every "
                          "distance]", lean=1.0, truth=cmean,
                   sem=max(csem, 1e-9))

    reg = ("two-deme island model over 6 Mb at recombination 1e-8 and "
           "mu = 1e-8, 6 replicates per cell; the observable is "
           "sigma_B/sigma_W, a ratio of disequilibrium SECOND MOMENTS with "
           "every product taken between DISJOINT sample halves so no sampling "
           "noise enters either the numerator or the denominator. Ne is varied "
           "FOURFOLD at fixed m, where an Ne-free body must not move, and c/m "
           "is swept across two orders of magnitude at fixed F_ST, where an "
           "F_ST-only body cannot move. c is the REALISED mean separation of "
           "the pairs actually drawn, times the recombination rate")
    record("sharedLD_from_equilibrium", "PortabilityDrift.lean", "m / (m + c)",
           cells, regime=reg, control=control, **MODEL)
    record("sharedLD_from_equilibrium [1 - fstMigrationDriftEquilibrium, "
           "competing]", "PortabilityDrift.lean", "1 - 1/(1 + 4*Ne*m)", c_fst,
           regime=reg, control=control, **MODEL)
    record("sharedLD_from_equilibrium [M/(1+M), competing]",
           "PortabilityDrift.lean", "bigM / (1 + bigM)", c_bigM, regime=reg,
           control=control, **MODEL)
    record("sharedLD_from_equilibrium [within-deme Sved 1/(1+4*Ne*c), "
           "competing]", "PortabilityDrift.lean", "1 / (1 + 4*Ne*c)", c_sved,
           regime=reg, control=control, **MODEL)
    record("sharedLD_from_equilibrium [2*m/(2*m + c), competing]",
           "PortabilityDrift.lean", "2*m / (2*m + c)", c_halved, regime=reg,
           control=control, **MODEL)

    dump_results("battery_sharedld_rec_results.json",
                 battery_source=os.path.abspath(__file__))
    print("\n================ SUMMARY ================")
    for r in RESULTS:
        w = r.get("worst", {})
        print("%-12s %-64s worst %9.2f sems, %7.2f%% rel"
              % (r["verdict"], r["name"], w.get("sems_off", float("nan")),
                 100 * w.get("rel_err", float("nan"))))


if __name__ == "__main__":
    main()
