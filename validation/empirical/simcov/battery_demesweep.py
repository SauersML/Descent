"""Battery DEMESWEEP: the deme dependence of `Core.PopGenParameters.fstEquilibrium`.

FRESHNESS guard string: DEMESWEEP_GUARD_20260806

THE DESIGN THIS CORPUS SAYS IT IS OWED.  `Core/Parameters.lean`'s
`fstEquilibrium` carries `Empirical status: MIXED`, and the second half of that
marker is the reason this file exists:

    The `nDemes = 2` member is VALIDATED; the deme dependence of the general
    body is UNTESTED.  Every cell of every battery below was run at two demes,
    so what has been measured is the two-deme specialisation, and the `d/(d-1)`
    factor has never been swept against THIS body.

It is not a formality.  `battery_falsrepair_c2.py` FALSIFIES the many-deme limit
at `d = 20` at 3.92 sems where the finite-deme form matches at 2.47, so the
correction is measurable and moves the answer -- but that run tests
`PopGen.fstMigrationMutationEquilibriumManyDemes`, whose signature is `(Ne, m,
mu)` and which cannot express a deme count at all.  The body on trial here is the
one the deployed metric reads:

    fstEquilibrium p = 1 / (1 + 4 Ne m * d/(d-1) + 4 Ne mu)

and `d` is a field of the record rather than a constant of the law.

WHAT SEPARATES THE CANDIDATES.  `d/(d-1)` is 2.000, 1.250, 1.053 and 1.020 at
`d` = 2, 5, 20, 50 -- a factor of two across the sweep, most of it between the
first two cells.  So:

  * the many-deme limit (correction dropped) agrees at large `d` and is wrong by
    a factor of two at `d = 2`;
  * the two-deme form (correction frozen at 2) agrees at `d = 2` and is wrong by
    the same factor at `d = 50`;
  * the squared correction agrees with the body at large `d` and separates from
    it at small `d`.

No single-`d` design can tell any of these apart from the corpus body, which is
precisely why three previous runs at `d = 2` left this UNTESTED.  A sweep in `d`
at fixed `4 Ne m` puts the FUNCTIONAL FORM of the correction on trial rather than
its value at one point, and the second block sweeps `4 Ne m` at two deme counts
so that a candidate cannot pass by absorbing the correction into the rate.

THE `d = 2` CELL IS A POSITIVE CONTROL AND IS TIED TO THE EXISTING LEDGER.  At
`d = 2` the corpus body reduces to `1/(1 + theta + 2M)` -- that is
`fstEquilibrium_eq_scaled_two_demes` in the Lean, and it is the member
`battery_falsrepair.py` group_a and `battery_bulk38b.py` measured at 1.10 and
1.03 sems.  If this design's `d = 2` cell disagrees with those, the disagreement
is in the DESIGN and not in the body, and the sweep says nothing until that is
resolved.  That is what the control field carries.

NAMING.  The row transcribing the corpus body is recorded BARE and every rival
carries a bracket tag, because `ledger.split_name` reads `<decl> -- <candidate>`
as a tagged row and a battery whose every row is tagged contributes no corpus
verdict at all.

`realised_inputs=True`: `4*Ne*m`, `4*Ne*mu` and `d` are the exact constants the
demography was built from, not estimates taken off the same replicates the
oracle measures, so there is no nominal/realised gap for a finding to be
confused with.  Undeclared, a rejection here is downgraded to a LEAD.

MIGRATION CONVENTION, and it must match `falsrepair_c2` or the two runs are not
comparable.  `msprime.Demography.island_model` takes a PER-PAIR rate, so a total
emigration `m` spread over the `d - 1` other demes is `migration_rate = m/(d-1)`.
That is the convention `islandDemeCorrection` is written for: a deme receives
lineages from `d - 1` sources, which is where `d/(d-1)` comes from.  Passing `m`
itself would build the correction into the simulation and this battery would then
measure its own parameterisation.
"""
import os

import simlib
from battery_core import RESULTS, dump_results, record

MODEL = dict(realised_inputs=True)

GUARD = "DEMESWEEP_GUARD_20260806"
NE, MU = 1000, 1e-8
THETA = 4.0 * NE * MU
SEQ_LEN, RHO, N_DIP, REPS = 2e6, 1e-8, 50, 48

DEMES = (2, 5, 20, 50)


def island_fst_rec(Ne, m, n_demes, reps, seed, seq_len=SEQ_LEN, rho=RHO,
                   n_dip=N_DIP):
    """Hudson `F_ST` between demes 0 and 1 of a symmetric island model.

    Recombination is ON.  `simlib.island_fst` sets it to zero, which gives one
    genealogy per replicate and an error bar too wide to separate the candidates
    -- that is exactly what `falsrepair` group_c bought and what `falsrepair_c2`
    had to redo.  2 Mb at 1e-8 makes each replicate an average over many
    independent trees.
    """
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


# The candidates, each a function of the scaled migration rate `M = 4*Ne*m` and
# the deme count `d`.  The corpus body is first and is the only one recorded
# bare.
CANDIDATES = {
    "body [1/(1 + 4*Ne*m*d/(d-1) + 4*Ne*mu)], the deme-corrected island form":
        lambda M, d: 1.0 / (1 + M * d / (d - 1.0) + THETA),
    "many-deme limit [correction dropped]":
        lambda M, d: 1.0 / (1 + M + THETA),
    "two-deme form [correction frozen at 2]":
        lambda M, d: 1.0 / (1 + 2 * M + THETA),
    "squared correction [(d/(d-1))^2]":
        lambda M, d: 1.0 / (1 + M * (d / (d - 1.0)) ** 2 + THETA),
}
CORPUS = "body [1/(1 + 4*Ne*m*d/(d-1) + 4*Ne*mu)], the deme-corrected island form"


def main():
    print("FRESHNESS=OK %s" % GUARD)
    cells = {k: [] for k in CANDIDATES}

    # BLOCK 1: sweep the deme count at fixed scaled migration.  This is the
    # block that puts the FORM of the correction on trial: 4*Ne*m is held at 4
    # so nothing about the rate moves, and d/(d-1) runs over a factor of two.
    print("  block 1: d swept at 4Nem=4.0   (d/(d-1) runs 2.000 -> 1.020)")
    M = 4.0
    for d in DEMES:
        s = island_fst_rec(NE, M / (4.0 * NE), d, REPS, 81000 + 100 * d)
        print("    d=%2d  corr=%.3f  F_ST=%.5f +/- %.5f   " %
              (d, d / (d - 1.0), s["mean"], s["sem"])
              + "  ".join("%.5f" % fn(M, d) for fn in CANDIDATES.values()))
        for k, fn in CANDIDATES.items():
            cells[k].append(dict(design="d=%d 4Nem=%.1f" % (d, M),
                                 lean=fn(M, d), truth=s["mean"],
                                 sem=max(s["sem"], 1e-6)))

    # BLOCK 2: sweep the scaled migration at two deme counts.  Without this a
    # candidate could pass block 1 by absorbing the correction into the rate;
    # here the rate moves sixteenfold at each of two lattice sizes, so the
    # correction and the rate are separately on trial.
    print("  block 2: 4Nem swept at d=2 and d=20")
    for d in (2, 20):
        for M in (1.0, 4.0, 16.0):
            s = island_fst_rec(NE, M / (4.0 * NE), d, REPS,
                               82000 + 1000 * d + int(10 * M))
            print("    d=%2d 4Nem=%5.1f  F_ST=%.5f +/- %.5f   " %
                  (d, M, s["mean"], s["sem"])
                  + "  ".join("%.5f" % fn(M, d) for fn in CANDIDATES.values()))
            for k, fn in CANDIDATES.items():
                cells[k].append(dict(design="d=%d 4Nem=%.1f" % (d, M),
                                     lean=fn(M, d), truth=s["mean"],
                                     sem=max(s["sem"], 1e-6)))

    # CONTROL.  The d = 2 cell at 4*Ne*m = 4 against 1/(1 + theta + 2M), which
    # is what `fstEquilibrium_eq_scaled_two_demes` proves the corpus body
    # reduces to there and what falsrepair group_a and bulk38b measured at 1.10
    # and 1.03 sems.  A design whose two-deme cell disagrees with the runs that
    # already validated that member is a design with a problem, and the sweep
    # says nothing until that is settled.
    c2 = island_fst_rec(NE, 4.0 / (4.0 * NE), 2, REPS, 83000)
    print("  CONTROL d=2 4Nem=4 against 1/(1+theta+2M)=%.5f: F_ST=%.5f +/- %.5f"
          % (1.0 / (1 + 8.0 + THETA), c2["mean"], c2["sem"]))
    control = dict(design="d=2 4Nem=4 [1/(1 + theta + 2M), the VALIDATED member]",
                   lean=1.0 / (1 + 8.0 + THETA), truth=c2["mean"],
                   sem=max(c2["sem"], 1e-6))

    reg = ("msprime symmetric island model, Ne = 1000 per deme, mu = 1e-8, "
           "total emigration m spread over the d-1 other demes so "
           "migration_rate = m/(d-1), 2 Mb at recombination 1e-8 so each "
           "replicate averages many genealogies, Hudson F_ST between demes 0 "
           "and 1, 48 replicates per cell. d swept 2/5/20/50 at 4*Ne*m = 4, "
           "and 4*Ne*m swept sixteenfold at d = 2 and d = 20. REGIME: "
           "equilibrium under migration, mutation and drift; this is NOT the "
           "clean-split transient, which is fstAtGeneration")

    for k, c in cells.items():
        record("fstEquilibrium" if k == CORPUS else "fstEquilibrium [%s]" % k,
               "Parameters.lean", k, c, regime=reg, control=control, **MODEL)

    dump_results("battery_demesweep_results.json",
                 battery_source=os.path.abspath(__file__))
    print("\n================ SUMMARY ================")
    for r in RESULTS:
        print("%-10s %-70s worst %.2f sems, %.1f%% rel"
              % (r["verdict"], r["name"], r["worst"]["sems_off"],
                 100 * r["worst"]["rel_err"]))


if __name__ == "__main__":
    main()
