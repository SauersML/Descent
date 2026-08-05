"""Battery ibd01: Rousset's isolation-by-distance law, and which N it takes.

THE CLAIM.  `AssortativeMatingPGS.ibdFst d N sigma_sq = d / (4*N*sigma_sq + d)`,
whose docstring states the convention this battery tests: `N` is a population
DENSITY -- individuals per unit of the same length in which `d` and `sigma_sq`
are measured -- and the body is Rousset's `F/(1-F) = d/(4*N*sigma^2)`
rearranged.  The migration rate is deliberately ABSENT, because dispersal enters
through `sigma_sq`.  The docstring's own dimensional argument rules out the
deme-size reading; it says in as many words that this is a consistency argument
and not a measurement.  This is the measurement.

CONVENTIONS, declared before any number is read.
  * DEME SPACING IS ONE.  Distances are counted in demes, so a density in
    "individuals per unit length" and a deme census size are the SAME NUMBER
    here, and the two readings are separated by what multiplies them, not by a
    change of units.  That is the point of the design: it puts the two readings
    on one axis where only one of them can fit.
  * `sigma_sq` is the AXIAL MEAN SQUARED PARENT-OFFSPRING DISPLACEMENT per
    generation.  With `stepping_stone_model(migration_rate=m/2)` each deme sends
    `m/2` to each neighbour, so `sigma_sq = 2*(m/2)*1^2 = m` exactly.
  * `F` is HUDSON's F_ST as a ratio of averages, the corpus's declared estimator,
    computed by `simlib.hudson_fst`.  Not Nei's G_ST, which is about half of it
    at low differentiation and would move every cell by a factor.

THE COMPETITOR, and it is the one that matters.  The corpus's other
stepping-stone body, `DemographicHistory.demoSteppingStoneFst =
d / (d + 4*Ne*m*sigma_sq)`, reads `Ne` as a deme size and carries the migration
rate as well.  With `sigma_sq = m` the two denominators differ by a factor of
`m` -- a factor of twenty to fifty at these parameters -- so a single simulation
decides between them and no calibration constant can reconcile the loser.

THE CONVENTION-FREE ARM.  Rousset's law is linear in distance on the `F/(1-F)`
scale, with slope `1/(4*N*sigma_sq)`.  The slope is recorded as its own row, so
the finding does not rest on the absolute level at any one distance.

CONTROL: Strobeck's result that in a conservative symmetric migration model the
mean WITHIN-deme coalescence time is `2*N_total` regardless of the migration
rate, so within-deme nucleotide diversity is `4*N_total*mu` with `N_total` the
whole metapopulation.  It is measured on the same tree sequences, it is
independent of every body under test, and it fails if the demography or the
mutation rate is not what this battery thinks it is.

FRESHNESS: prints FRESHNESS=OK only if its own source carries the token below.
"""
import math
import os

import numpy as np

import simlib
from battery_core import RESULTS, dump_results, record

FRESH_TOKEN = "SIMCOV-BATTERY-IBD01-DUNLIN-20260804"


def freshness():
    try:
        src = open(os.path.abspath(__file__)).read()
    except Exception:
        print("FRESHNESS=STALE (cannot read own source)")
        return
    print("FRESHNESS=%s (token %s)"
          % ("OK" if src.count(FRESH_TOKEN) >= 2 else "STALE", FRESH_TOKEN))


def one_rep(n_demes, Ne, m, n_dip, seq_len, mu, seed, sampled):
    import msprime
    dem = msprime.Demography.stepping_stone_model(
        [Ne] * n_demes, migration_rate=m / 2.0, boundaries=True)
    ts = msprime.sim_ancestry(
        samples={"pop_%d" % i: n_dip for i in sampled}, demography=dem,
        sequence_length=seq_len, recombination_rate=1e-8, random_seed=seed)
    ts = msprime.sim_mutations(ts, rate=mu, random_seed=seed + 7919)
    gm = ts.genotype_matrix()
    ac, nn, pi_w = {}, {}, []
    for i in sampled:
        s = ts.samples(population=i)
        ac[i] = gm[:, s].sum(1).astype(float)
        nn[i] = len(s)
        p = ac[i] / nn[i]
        het = 2 * p * (1 - p) * nn[i] / (nn[i] - 1.0)
        pi_w.append(float(het.sum() / seq_len))
    return ac, nn, float(np.mean(pi_w))


def main():
    freshness()
    print("FRESHNESS token literal: SIMCOV-BATTERY-IBD01-DUNLIN-20260804")

    n_demes, n_dip, seq_len, mu = 20, 20, 2e6, 1e-8
    sampled = [2, 3, 5, 7, 9, 12, 16]
    reps = 10
    dists = (1, 2, 4, 7, 10)

    body, rival, slope_cells, slope_rival = [], [], [], []
    control = None
    for Ne, m in ((200, 0.05), (200, 0.02), (400, 0.05)):
        per_rep = {d: [] for d in dists}
        pis = []
        for r in range(reps):
            ac, nn, pi_w = one_rep(n_demes, Ne, m, n_dip, seq_len, mu,
                                   seed=1000 * r + Ne + int(1000 * m), sampled=sampled)
            pis.append(pi_w)
            for d in dists:
                vals = [simlib.hudson_fst(ac[a], nn[a], ac[b], nn[b])
                        for a in sampled for b in sampled if b - a == d]
                if vals:
                    per_rep[d].append(float(np.mean(vals)))
        sigma_sq = m                      # axial mean squared displacement
        for d in dists:
            v = np.array(per_rep[d])
            truth = float(v.mean())
            sem = float(v.std(ddof=1) / math.sqrt(len(v)))
            lab = "Ne=%d m=%.2f d=%d" % (Ne, m, d)
            lean = d / (4.0 * Ne * sigma_sq + d)
            other = d / (d + 4.0 * Ne * m * sigma_sq)
            print("  %-22s density-reading %.5f  deme-size-with-m %.5f  "
                  "Hudson F_ST %.5f ± %.5f" % (lab, lean, other, truth, sem))
            body.append(dict(design=lab, lean=lean, truth=truth, sem=sem))
            rival.append(dict(design=lab, lean=other, truth=truth, sem=sem))
        # convention-free arm: the slope of F/(1-F) against distance
        xs = np.array(dists, dtype=float)
        ys = np.array([np.mean(per_rep[d]) / (1 - np.mean(per_rep[d]))
                       for d in dists])
        per_rep_slope = []
        for r in range(reps):
            yr = np.array([per_rep[d][r] / (1 - per_rep[d][r]) for d in dists])
            per_rep_slope.append(float((xs * yr).sum() / (xs * xs).sum()))
        s_hat = float(np.mean(per_rep_slope))
        s_sem = float(np.std(per_rep_slope, ddof=1) / math.sqrt(reps))
        lab = "Ne=%d m=%.2f slope of F/(1-F) vs d" % (Ne, m)
        print("  %-22s density 1/(4*N*sigma_sq) %.5f  deme-size-with-m %.5f  "
              "fitted %.5f ± %.5f"
              % (lab, 1.0 / (4 * Ne * sigma_sq), 1.0 / (4 * Ne * m * sigma_sq),
                 s_hat, s_sem))
        slope_cells.append(dict(design=lab, lean=1.0 / (4 * Ne * sigma_sq),
                                truth=s_hat, sem=s_sem))
        slope_rival.append(dict(design=lab, lean=1.0 / (4 * Ne * m * sigma_sq),
                                truth=s_hat, sem=s_sem))
        if control is None:
            # Strobeck: within-deme pi = 4 * N_total * mu, migration-free
            control = dict(design="within-deme pi = 4*N_total*mu (Strobeck), "
                                  "Ne=%d m=%.2f" % (Ne, m),
                           lean=4.0 * n_demes * Ne * mu,
                           truth=float(np.mean(pis)),
                           sem=float(np.std(pis, ddof=1) / math.sqrt(reps)))
            print("  CONTROL %s: predicted %.6f measured %.6f ± %.6f"
                  % (control["design"], control["lean"], control["truth"],
                     control["sem"]))

    reg = ("1D stepping stone, 20 demes with reflecting boundaries, deme "
           "spacing 1, migration m/2 to each neighbour so sigma_sq = m; "
           "20 diploids sampled from seven demes, 2 Mb at mu = 1e-8 with "
           "recombination, 10 independent replicates. F is Hudson's F_ST as a "
           "ratio of averages, averaged over all sampled pairs at the given "
           "lattice distance; the error bar is across replicate simulations")
    # `realised_inputs=True` and the reason it is not a fudge: every input here
    # is an EXACT model constant, not a sample estimate. The lattice distance is
    # an integer, the deme census size is the number of individuals the model was
    # given, and `sigma_sq = m` is the second moment of the migration kernel
    # itself rather than a realised displacement -- the coalescent samples no
    # dispersal event whose variance could differ from it. There is no
    # nominal/realised gap to be the size of a finding, and the rejected reading
    # misses by a factor of ten to forty rather than by O(1/sqrt(m)).
    MODEL = dict(regime=reg, control=control, realised_inputs=True,
                 argument_source="model")

    record("ibdFst", "AssortativeMatingPGS.lean",
           "d / (4 * N * sigma_sq + d), N a density", body, **MODEL)
    record("ibdFst [deme-size reading carrying m, competing]",
           "AssortativeMatingPGS.lean", "d / (d + 4*Ne*m*sigma_sq)", rival,
           **MODEL)
    record("ibdFst [slope of F/(1-F) against distance]",
           "AssortativeMatingPGS.lean", "1 / (4 * N * sigma_sq)", slope_cells,
           **MODEL)
    record("ibdFst [slope, deme-size reading carrying m, competing]",
           "AssortativeMatingPGS.lean", "1 / (4*Ne*m*sigma_sq)", slope_rival,
           **MODEL)

    dump_results("battery_ibd01_results.json")
    print("\n================ SUMMARY ================")
    for rec in RESULTS:
        w = rec.get("worst", {}) or {}
        print("%-24s %-58s worst %9.2f sems, %8.2f%% rel"
              % (rec["verdict"], rec["name"][:58], w.get("sems_off", float("nan")),
                 100 * w.get("rel_err", float("nan"))))


if __name__ == "__main__":
    main()
