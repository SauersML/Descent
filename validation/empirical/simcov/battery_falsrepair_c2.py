"""Battery falsrepair-C2: the many-deme limit at d = 20, with recombination.

FRESHNESS guard string: FALSREPAIR_C2_GUARD_20260804

group_c used simlib.island_fst, which sets recombination_rate = 0.  One
genealogy per replicate makes the error bars honest but wide, and the cell at
4*Ne*m = 4 came out ~20% low in BOTH that run and the older battery_verify run.
Either that is two draws of the same noise or it is real curvature.  This run
adds recombination so each replicate averages over many genealogies, doubles the
replicates, and fills in the sweep, so the cell either moves back or stays.

NAMING.  The row transcribing the body in PopulationGeneticsFoundations.lean is
recorded BARE; only rivals carry a bracket tag.  `ledger.split_name` reads
`<decl> -- <candidate>` as a tagged row, so a battery whose every row is tagged
has no CORPUS row and its corpus verdict never enters the ledger at all.

`realised_inputs=True`: `4*Ne*m` and `4*Ne*mu` are the exact constants the
demography was built from, not estimates off the same replicates the oracle
measures, so there is no nominal/realised gap for a finding to be confused with.
Undeclared, the two-deme rejection this design turns on is downgraded to a LEAD,
and a downgraded rejection leaves the corpus row looking uncompeted.
"""
import json
import math
import os

import numpy as np

import simlib
from battery_core import RESULTS, dump_results, record

MODEL = dict(realised_inputs=True)

GUARD = "FALSREPAIR_C2_GUARD_20260804"
NE, MU, D = 1000, 1e-8, 20


def island_fst_rec(Ne, m, n_demes, reps, seed, seq_len=2e6, rho=1e-8,
                   n_dip=50):
    import msprime
    dem = msprime.Demography.island_model([Ne] * n_demes,
                                          migration_rate=m / (n_demes - 1))
    hud = []
    for r in range(reps):
        ts = msprime.sim_ancestry(
            samples={"pop_0": n_dip, "pop_1": n_dip}, demography=dem,
            sequence_length=seq_len, recombination_rate=rho,
            random_seed=seed + r)
        ts = msprime.sim_mutations(ts, rate=MU, random_seed=seed + 30000 + r)
        if ts.num_sites == 0:
            continue
        gm = ts.genotype_matrix()
        a, b = ts.samples(population=0), ts.samples(population=1)
        ac1 = gm[:, a].sum(axis=1).astype(float)
        ac2 = gm[:, b].sum(axis=1).astype(float)
        hud.append(simlib.hudson_fst(ac1, len(a), ac2, len(b)))
    return simlib.summarize(hud)


def main():
    print("FRESHNESS=OK %s" % GUARD)
    cands = {
        "body [1/(1 + 4*Ne*m + 4*Ne*mu)], the many-deme limit":
            lambda M: 1.0 / (1 + M + 4 * NE * MU),
        "finite-deme form at d=20 [correction 20/19]":
            lambda M: 1.0 / (1 + M * D / (D - 1.0) + 4 * NE * MU),
        "two-deme form [1/(1 + 2*4*Ne*m)], competing":
            lambda M: 1.0 / (1 + 2 * M + 4 * NE * MU),
    }
    cells = {k: [] for k in cands}
    for M in (1.0, 2.0, 4.0, 8.0, 16.0):
        s = island_fst_rec(NE, M / (4.0 * NE), D, 48, 66000 + int(10 * M))
        print("  4Nem=%5.1f  F_ST=%.5f +/- %.5f   " % (M, s["mean"], s["sem"])
              + "  ".join("%.5f" % fn(M) for fn in cands.values()))
        for k, fn in cands.items():
            cells[k].append(dict(design="d=20 4Nem=%.1f" % M, lean=fn(M),
                                 truth=s["mean"], sem=max(s["sem"], 1e-6)))
    c2 = island_fst_rec(NE, 4.0 / (4.0 * NE), 2, 48, 67000)
    print("  CONTROL d=2 4Nem=4: F_ST=%.5f +/- %.5f (two-deme 0.11111, "
          "limit 0.20000)" % (c2["mean"], c2["sem"]))
    control = dict(design="d=2 4Nem=4 [two-deme form 1/(1+2*4Ne*m)]",
                   lean=1.0 / 9.0, truth=c2["mean"], sem=max(c2["sem"], 1e-6))
    reg = ("msprime symmetric island model, 20 demes of Ne = 1000, total "
           "emigration m spread over the 19 other demes, mu = 1e-8, 2 Mb at "
           "recombination 1e-8 so each replicate averages many genealogies, "
           "Hudson F_ST between demes 0 and 1, 48 replicates, 4*Ne*m swept "
           "sixteenfold")
    CORPUS = "body [1/(1 + 4*Ne*m + 4*Ne*mu)], the many-deme limit"
    for k, c in cells.items():
        record("fstMigrationMutationEquilibriumManyDemes" if k == CORPUS
               else "fstMigrationMutationEquilibriumManyDemes [%s]" % k,
               "PopulationGeneticsFoundations.lean", k, c, regime=reg,
               control=control, **MODEL)
    dump_results("battery_falsrepair_c2_results.json",
                 battery_source=os.path.abspath(__file__))
    print("\n================ SUMMARY ================")
    for r in RESULTS:
        print("%-10s %-62s worst %.2f sems, %.1f%% rel"
              % (r["verdict"], r["name"], r["worst"]["sems_off"],
                 100 * r["worst"]["rel_err"]))


if __name__ == "__main__":
    main()
