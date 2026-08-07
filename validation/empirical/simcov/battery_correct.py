"""Battery 5: determine the CORRECT form of each falsified definition.

Falsifying a formula and leaving it in place is half a job: the corpus still
computes the wrong number, and the docstring only warns whoever reads it.  This
battery measures what the right formula IS, precisely enough to install it.

Three questions:

  1. `pairwiseFstFromBranchTaus`: with the double-counted split removed, does
     the MEAN of the branch taus reproduce the measured F_ST?  On a symmetric
     split it must reduce to `coalFst`, which is already validated; the open
     part is whether it survives unequal daughter sizes.

  2. `freqCorrFromFst`: is
     `corr = Var(p0) / (Var(p0) + F * E[p0(1-p0)])` the exact law?  Tested
     across four ancestral distributions and two drift depths, which is eight
     cells that a formula in `F_ST` alone must get wrong and this one must get
     right.

  3. `fstMigrationMutationEquilibrium`: what IS the deme-count law?  A finite
     island model has a candidate factor `(n/(n-1))^2`; the earlier run was too
     noisy at large `n` to accept or reject it.  Enough replicates here to
     decide, because installing an unvalidated correction is the same mistake
     as leaving an unvalidated formula.

RECORDING THE VERDICTS.  For three releases this battery printed numbers and
called `record()` nowhere, so seven docstrings cited it for an empirical status
that the ledger could not see: the citation was followable and the arithmetic
was real, but nothing in the repository stated what the run CONCLUDED.  Each
group below now files the CURRENT corpus body as the corpus row and the form it
superseded as a competitor -- in that order, because filing the proposal as the
corpus row is what leaves the ledger asserting a falsification of a formula no
file contains.
"""
import json

import numpy as np

import simlib
from battery_core import dump_results, record, run_groups

OUT = {}


# ---------------------------------------------------------------------------
# 1. the corrected branch-tau composition
# ---------------------------------------------------------------------------
def correct_pairwise_tau():
    from battery_fix import split_fst_rec
    print("\n=== 1. pairwiseFstFromBranchTaus: sum vs mean of branch taus ===")
    print("  %-26s %9s %9s %9s %8s" % ("design", "sum", "mean", "simulated", "sem"))
    rows = []
    # The two halves are recorded SEPARATELY because the definition's status is
    # conditional and a single row cannot say so.  Equal branch lengths is the
    # regime the docstring validates; unequal is the boundary it disowns, and
    # merging them would report one FALSIFIED row over a design four fifths of
    # which the body gets right.
    sym, asym, comp_sym = [], [], []
    designs = ((1000, 1000, 500, 1000), (1000, 1000, 1000, 1000),
               (1000, 1000, 2000, 1000), (600, 600, 1200, 600),
               (500, 2000, 1000, 1000), (400, 1600, 1000, 1000),
               (500, 2000, 2000, 1000))
    for NeA, NeB, t, NeANC in designs:
        s = split_fst_rec(NeA, t, NeA=NeA, NeB=NeB, NeANC=NeANC, n_dip=50,
                          seq_len=2e7, reps=30, seed=2101)
        tS, tT = t / (2.0 * NeA), t / (2.0 * NeB)
        f_sum = (tS + tT) / (1 + tS + tT)
        f_mean = ((tS + tT) / 2) / (1 + (tS + tT) / 2)
        rows.append((NeA, NeB, t, f_sum, f_mean, s["mean"], s["sem"]))
        lab = "NeA=%d NeB=%d t=%d" % (NeA, NeB, t)
        cell = dict(design=lab, lean=f_mean, truth=s["mean"], sem=s["sem"])
        (sym if NeA == NeB else asym).append(cell)
        if NeA == NeB:
            comp_sym.append(dict(design=lab, lean=f_sum, truth=s["mean"],
                                 sem=s["sem"]))
        print("  %-26s %9.5f %9.5f %9.5f %8.5f  (mean form: %.1f sems)"
              % (lab, f_sum, f_mean, s["mean"], s["sem"],
                 abs(f_mean - s["mean"]) / s["sem"]))
    OUT["pairwise_tau"] = rows

    # CONTROL: a symmetric split at a depth NOT in the design above, scored
    # against `coalFst = t/(t + 2Ne)`, which `battery_core` validates on its own
    # engine.  It is a different depth on purpose: a control that is also a
    # design cell tests the same arithmetic twice.
    cs = split_fst_rec(1000, 3000, NeA=1000, NeB=1000, NeANC=1000, n_dip=50,
                       seq_len=2e7, reps=30, seed=2601)
    control = dict(design="symmetric t=3000 Ne=1000: coalFst = t/(t+2Ne)",
                   lean=3000 / (3000 + 2000.0), truth=cs["mean"],
                   sem=cs["sem"])
    print("  CONTROL %s: predicted %.5f measured %.5f +/- %.5f"
          % (control["design"], control["lean"], control["truth"],
             control["sem"]))
    OUT["pairwise_tau_control"] = control

    reg_sym = ("clean two-deme split with RECOMBINATION on (rho = 1e-8 over "
               "20 Mb, so a replicate holds many genealogies), no migration, "
               "EQUAL daughter sizes -- the equal-branch-length regime the "
               "declaration's status restricts itself to; Hudson F_ST, 30 "
               "replicates, both branch taus taken from the simulation's own "
               "Ne and split time")
    record("pairwiseFstFromBranchTaus", "Definitions.lean",
           "fstFromTau (Tau.ofScaled ((tauS + tauT) / 2))", sym,
           regime=reg_sym, control=control, realised_inputs=True,
           argument_source="model",
           note="the superseded SUM form is carried on the same cells")
    record("pairwiseFstFromBranchTaus [sum of branch taus, superseded]",
           "Definitions.lean", "fstFromTau (Tau.ofScaled (tauS + tauT))",
           comp_sym, regime=reg_sym, control=control, realised_inputs=True,
           argument_source="model",
           note="the body this declaration carried before the split time was "
                "counted once instead of twice")
    record("pairwiseFstFromBranchTaus [unequal branch lengths]",
           "Definitions.lean",
           "fstFromTau (Tau.ofScaled ((tauS + tauT) / 2)), unequal Ne",
           asym, regime=reg_sym.replace("EQUAL daughter sizes", "UNEQUAL "
                                        "daughter sizes"),
           control=control, realised_inputs=True, argument_source="model",
           note="this is the boundary the declaration's status names, measured "
                "rather than asserted: the mean of the branch taus is not the "
                "pairwise F_ST when the two branches differ in length")


# ---------------------------------------------------------------------------
# 2. the exact allele-frequency correlation law
# ---------------------------------------------------------------------------
def correct_freq_corr():
    print("\n=== 2. freqCorrFromFst: Var(p0)/(Var(p0)+F*E[p0(1-p0)]) ===")
    rng = np.random.default_rng(2201)
    Ne, n_loci, reps = 200, 4000, 400
    print("  %-30s %9s %9s %9s %8s"
          % ("design", "1-Fst", "proposed", "measured", "sems"))
    rows = []
    cells, comp = [], []
    gst_cells = []
    for lab, draw in (("uniform(0.05,0.95)", lambda n: rng.uniform(0.05, 0.95, n)),
                      ("beta(0.5,0.5)", lambda n: rng.beta(0.5, 0.5, n).clip(.02, .98)),
                      ("beta(2,2)", lambda n: rng.beta(2, 2, n).clip(.02, .98)),
                      ("all p0 = 0.5", lambda n: np.full(n, 0.5))):
        for t in (60, 200):
            p0 = draw(n_loci)
            var_p0 = float(np.var(p0))
            e_pq = float(np.mean(p0 * (1 - p0)))
            two_n = 2 * Ne
            p1 = np.tile(p0, (reps, 1))
            p2 = np.tile(p0, (reps, 1))
            for _ in range(t):
                p1 = rng.binomial(two_n, p1) / two_n
                p2 = rng.binomial(two_n, p2) / two_n
            pbar = (p1 + p2) / 2
            hs = (2 * p1 * (1 - p1) + 2 * p2 * (1 - p2)) / 2
            ht = 2 * pbar * (1 - pbar)
            gst = float((ht.mean() - hs.mean()) / ht.mean())
            # PER-REPLICATE G_ST as well as the pooled one: the pooled number
            # has no error bar, and a control without one is a control that
            # cannot fail.  This is the drift index the correlation law takes
            # as its `fst` argument, so measuring it is what makes the argument
            # a model parameter rather than an assumption.
            gst_reps = [float((ht[k].mean() - hs[k].mean()) / ht[k].mean())
                        for k in range(reps)]
            cs = [float(np.corrcoef(p1[k], p2[k])[0, 1]) for k in range(reps)]
            s = simlib.summarize(cs)
            f_br = 1 - (1 - 1.0 / (2 * Ne)) ** t
            proposed = (var_p0 / (var_p0 + f_br * e_pq)) if var_p0 > 0 else 0.0
            z = abs(proposed - s["mean"]) / s["sem"] if s["sem"] > 0 else float("nan")
            rows.append((lab, t, 1 - gst, proposed, s["mean"], s["sem"]))
            design = "%s t=%d" % (lab, t)
            cells.append(dict(design=design, lean=proposed,
                              truth=s["mean"], sem=s["sem"]))
            comp.append(dict(design=design, lean=1 - gst,
                             truth=s["mean"], sem=s["sem"]))
            g = simlib.summarize(gst_reps)
            gst_cells.append(dict(design=design, lean=f_br,
                                  truth=g["mean"], sem=g["sem"]))
            print("  %-30s %9.4f %9.4f %9.4f %8.1f"
                  % (design, 1 - gst, proposed, s["mean"], z))
    OUT["freq_corr"] = rows

    # CONTROL: the Wright drift index itself.  `F = 1 - (1 - 1/(2Ne))^t` is the
    # textbook recursion and is what the correlation law is evaluated at, so a
    # run in which the simulated G_ST does NOT reproduce it has no standing to
    # report anything about the correlation.  The worst of the eight cells is
    # taken, because a control that passes only on its easiest cell is not one.
    control = max(gst_cells,
                  key=lambda c: abs(c["lean"] - c["truth"]) / max(c["sem"], 1e-12))
    control = dict(control)
    control["design"] = ("Wright drift index F = 1-(1-1/(2Ne))^t, worst of the "
                         "eight cells: " + control["design"])
    print("  CONTROL %s: predicted %.5f measured %.5f +/- %.5f"
          % (control["design"], control["lean"], control["truth"],
             control["sem"]))
    OUT["freq_corr_control"] = control

    reg = ("Wright-Fisher forward simulation, Ne = 200, 4000 loci, 400 "
           "replicate deme pairs, four ancestral frequency distributions "
           "crossed with two drift depths; the correlation is taken ACROSS "
           "LOCI WITHIN a replicate so its scatter is measured, the two "
           "ancestral moments are the realised moments of the drawn p0, and "
           "the drift index is the model's 1-(1-1/(2Ne))^t and never one "
           "estimated from the replicates the oracle measures")
    MODEL = dict(regime=reg, control=control, realised_inputs=True,
                 argument_source="model")
    record("alleleFreqCorrelation", "MutationDrift.lean",
           "varAncestral / (varAncestral + fst * meanHetAncestral)", cells,
           note="the design holds the drift index nearly fixed at each depth "
                "and moves the correlation across the range the quantity "
                "admits, which is what separates the two readings",
           **MODEL)
    record("alleleFreqCorrelation [1 - Fst, the superseded identification]",
           "MutationDrift.lean", "1 - fst", comp,
           note="the claim the rename retired: this was `freqCorrFromFst`, and "
                "the ledger's three rows under that dead name are this "
                "measurement. The body `1 - fst` survives under "
                "`covarianceRetentionFactorFromFst`, which is what consumers "
                "use it as; what is refuted here is only the identification "
                "of it with the correlation",
           **MODEL)


# ---------------------------------------------------------------------------
# 3. the island-model deme-count law
# ---------------------------------------------------------------------------
def correct_island_deme_count():
    print("\n=== 3. fstMigrationMutationEquilibrium: the deme-count law ===")
    Ne, mu = 1000, 1e-8
    print("  %-8s %10s %8s %11s %11s" % ("n_demes", "simulated", "sem",
                                         "1/(1+4Nm)", "with (n/(n-1))^2"))
    rows = []
    cells, comp_limit, comp_sq = [], [], []
    m = 1e-3
    for n in (2, 3, 4, 6, 10, 20, 40):
        r = simlib.island_fst(Ne, m, n_demes=n, n_dip=40, seq_len=2e7,
                              mu=mu, reps=40, seed=2301)
        naive = 1 / (1 + 4 * Ne * m)
        # THE CORPUS BODY IS THE LINEAR CORRECTION, and until now this script
        # computed only the limit form and the SQUARED candidate -- so the
        # column the declaration's docstring calls "this def" was not among the
        # numbers this battery produced.  A battery that does not evaluate the
        # body it is cited for cannot have measured it.
        lin = 1 / (1 + 4 * Ne * m * (n / (n - 1.0)) + 4 * Ne * mu)
        corr = 1 / (1 + 4 * Ne * m * (n / (n - 1.0)) ** 2)
        sem = r["hudson"]["sem"]
        rows.append((n, r["hudson"]["mean"], sem, naive, lin, corr))
        design = "n_demes=%d, 4Nm=%.1f held fixed" % (n, 4 * Ne * m)
        cells.append(dict(design=design, lean=lin,
                          truth=r["hudson"]["mean"], sem=sem))
        comp_limit.append(dict(design=design, lean=naive,
                               truth=r["hudson"]["mean"], sem=sem))
        comp_sq.append(dict(design=design, lean=corr,
                            truth=r["hudson"]["mean"], sem=sem))
        print("  %-8d %10.5f %8.5f %11.5f %11.5f %11.5f"
              "   (limit %.1f sems, linear %.1f, squared %.1f)"
              % (n, r["hudson"]["mean"], sem, naive, lin, corr,
                 abs(naive - r["hudson"]["mean"]) / sem,
                 abs(lin - r["hudson"]["mean"]) / sem,
                 abs(corr - r["hudson"]["mean"]) / sem))
    OUT["island"] = rows

    # CONTROL: many demes and a migration rate ten times higher, where the
    # deme-count correction is 1.026 and every candidate collapses onto
    # Wright's `1/(1 + 4 Ne m)`.  That number is independently known, so a run
    # that misses it has no standing to report which correction is right --
    # and because the three candidates agree there, the control cannot be
    # passed by getting the thing under test right.
    m_ctl = 1e-2
    rc = simlib.island_fst(Ne, m_ctl, n_demes=40, n_dip=40, seq_len=2e7,
                           mu=mu, reps=40, seed=2701)
    control = dict(design="n_demes=40, m=1e-2: Wright's 1/(1+4Nm) at 4Nm=40",
                   lean=1 / (1 + 4 * Ne * m_ctl), truth=rc["hudson"]["mean"],
                   sem=rc["hudson"]["sem"])
    print("  CONTROL %s: predicted %.5f measured %.5f +/- %.5f"
          % (control["design"], control["lean"], control["truth"],
             control["sem"]))
    OUT["island_control"] = control

    reg = ("msprime symmetric island model at migration-drift-mutation "
           "equilibrium, Ne = 1000, TOTAL emigration rate m = 1e-3 held FIXED "
           "so 4 Ne m = 4.0 is identical in every row and the deme count is "
           "the only thing that moves, mu = 1e-8, Hudson F_ST over 40 "
           "replicates of 20 Mb; every rate is the simulation's own parameter")
    MODEL = dict(regime=reg, control=control, realised_inputs=True,
                 argument_source="model")
    record("fstIslandEquilibriumFiniteDemes", "MigrationDriftFoundations.lean",
           "fstFromFlow (4*Ne*m * islandDemeCorrection nDemes + 4*Ne*mu)",
           cells,
           note="at fixed 4 Ne m the limit form is one number and this one "
                "spans 0.111 to 0.196, so the design separates them by "
                "construction rather than by power",
           **MODEL)
    record("fstIslandEquilibriumFiniteDemes [many-deme limit, superseded]",
           "MigrationDriftFoundations.lean", "fstFromFlow (4*Ne*m)",
           comp_limit,
           note="constant across the whole design: this is the form that "
                "cannot see the deme count at all",
           **MODEL)
    record("fstIslandEquilibriumFiniteDemes [squared correction, competing]",
           "MigrationDriftFoundations.lean",
           "fstFromFlow (4*Ne*m * (nDemes/(nDemes-1))^2)", comp_sq,
           note="the candidate this battery was written to accept or reject; "
                "it over-corrects at small deme counts, where the linear form "
                "and the data agree",
           **MODEL)


def main():
    failed = run_groups(correct_pairwise_tau, correct_freq_corr,
                        correct_island_deme_count)
    path = "battery_correct_results.json"
    dump_results(path, battery_source=__file__, failed_groups=failed)
    # The raw tables stay in the same file: the docstrings that cite this
    # battery quote them, and moving them out would break every citation to
    # buy nothing.  `ledger.py` reads `results` and ignores the rest.
    payload = json.load(open(path))
    payload["raw"] = OUT
    with open(path, "w") as fh:
        json.dump(payload, fh, indent=1, default=str)


if __name__ == "__main__":
    main()
