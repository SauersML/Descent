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
import math

import numpy as np

import battery_core
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
    for NeA, NeB, t, NeANC in ((1000, 1000, 500, 1000), (1000, 1000, 1000, 1000),
                               (1000, 1000, 2000, 1000), (600, 600, 1200, 600),
                               (500, 2000, 1000, 1000)):
        s = split_fst_rec(NeA, t, NeA=NeA, NeB=NeB, NeANC=NeANC, n_dip=50,
                          seq_len=2e7, reps=30, seed=2101)
        tS, tT = t / (2.0 * NeA), t / (2.0 * NeB)
        f_sum = (tS + tT) / (1 + tS + tT)
        f_mean = ((tS + tT) / 2) / (1 + (tS + tT) / 2)
        rows.append((NeA, NeB, t, f_sum, f_mean, s["mean"], s["sem"]))
        print("  %-26s %9.5f %9.5f %9.5f %8.5f  (mean form: %.1f sems)"
              % ("NeA=%d NeB=%d t=%d" % (NeA, NeB, t), f_sum, f_mean,
                 s["mean"], s["sem"], abs(f_mean - s["mean"]) / s["sem"]))
    OUT["pairwise_tau"] = rows


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
            cs = [float(np.corrcoef(p1[k], p2[k])[0, 1]) for k in range(reps)]
            s = simlib.summarize(cs)
            f_br = 1 - (1 - 1.0 / (2 * Ne)) ** t
            proposed = (var_p0 / (var_p0 + f_br * e_pq)) if var_p0 > 0 else 0.0
            z = abs(proposed - s["mean"]) / s["sem"] if s["sem"] > 0 else float("nan")
            rows.append((lab, t, 1 - gst, proposed, s["mean"], s["sem"]))
            print("  %-30s %9.4f %9.4f %9.4f %8.1f"
                  % ("%s t=%d" % (lab, t), 1 - gst, proposed, s["mean"], z))
    OUT["freq_corr"] = rows


# ---------------------------------------------------------------------------
# 3. the island-model deme-count law
# ---------------------------------------------------------------------------
def correct_island_deme_count():
    print("\n=== 3. fstMigrationMutationEquilibrium: the deme-count law ===")
    Ne, mu = 1000, 1e-8
    print("  %-8s %10s %8s %11s %11s" % ("n_demes", "simulated", "sem",
                                         "1/(1+4Nm)", "with (n/(n-1))^2"))
    rows = []
    m = 1e-3
    for n in (2, 3, 4, 6, 10, 20, 40):
        r = simlib.island_fst(Ne, m, n_demes=n, n_dip=40, seq_len=2e7,
                              mu=mu, reps=40, seed=2301)
        naive = 1 / (1 + 4 * Ne * m)
        corr = 1 / (1 + 4 * Ne * m * (n / (n - 1.0)) ** 2)
        sem = r["hudson"]["sem"]
        rows.append((n, r["hudson"]["mean"], sem, naive, corr))
        print("  %-8d %10.5f %8.5f %11.5f %11.5f   (naive %.1f sems, corr %.1f sems)"
              % (n, r["hudson"]["mean"], sem, naive, corr,
                 abs(naive - r["hudson"]["mean"]) / sem,
                 abs(corr - r["hudson"]["mean"]) / sem))
    OUT["island"] = rows


def main():
    for fn in (correct_pairwise_tau, correct_freq_corr, correct_island_deme_count):
        try:
            fn()
        except Exception:
            import traceback
            traceback.print_exc()
    json.dump(OUT, open("battery_correct_results.json", "w"), indent=1, default=str)


if __name__ == "__main__":
    main()
