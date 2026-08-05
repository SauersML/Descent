"""Battery 23: coalescent timescale, haplotype homozygosity, multi-trait N_eff.

Three bodies chosen because each has a NEARBY WRONG FORM that a simulation can
separate, and each is cheap enough to run in seconds:

  A. `coalescentTimeScale = ploidy * Ne`. The mean pairwise coalescence time in
     a diploid population of size `Ne` is `2 Ne` generations, not `4 Ne` -- the
     `4 Ne` that appears everywhere else in this corpus is the scaled MUTATION
     rate `theta = 4 Ne mu`, a different quantity that happens to share the
     shape. Both are carried. Measured in branch mode, where the mean pairwise
     coalescence time is read directly off the trees and no mutations are
     needed.

  B. `haplotypeHomozygosity = sum freq_i ^ 2`. The oracle does not evaluate the
     sum: it draws two haplotypes at random and counts how often they MATCH.
     That the match probability equals the sum of squared frequencies is the
     content, and counting matches is an independent route to it.

  C. `multiTraitEffectiveSampleSize = n1 + rg^2 * n2`. Two genetically
     correlated traits; the effective sample size is defined by what it does to
     the estimator's variance, so the oracle measures `Var(beta_hat)` for the
     optimally combined two-trait estimator across replicates and inverts
     `Var = sigma^2 / N_eff`. The competing readings `n1 + rg * n2` (no square)
     and `n1 + n2` (perfect borrowing) are carried on the same cells, and `rg`
     is swept so they separate by more than twofold.
"""
import json
import math

import numpy as np

import simlib
from battery_core import RESULTS, record


def group_a():
    import msprime

    cells_two, cells_four = [], []
    control = None
    for Ne in (500, 1000, 2000, 5000):
        vals = []
        for r in range(40):
            ts = msprime.sim_ancestry(
                samples=1, population_size=Ne, sequence_length=2e6,
                recombination_rate=1e-8, random_seed=23001 + r)
            # branch-mode diversity of a sample of 2 is 2 * E[T2]
            vals.append(float(ts.diversity(mode="branch")) / 2.0)
        s = simlib.summarize(vals)
        lab = "Ne=%d" % Ne
        print("  %-10s E[T2] = %.1f ± %.1f   (2Ne = %d, 4Ne = %d)"
              % (lab, s["mean"], s["sem"], 2 * Ne, 4 * Ne))
        cells_two.append(dict(design=lab, lean=2.0 * Ne, truth=s["mean"],
                              sem=s["sem"]))
        cells_four.append(dict(design=lab, lean=4.0 * Ne, truth=s["mean"],
                               sem=s["sem"]))
        if Ne == 1000:
            # control: the same trees give heterozygosity 4*Ne*mu/(1+4*Ne*mu)
            # under mutation -- but simpler and fully independent here, the
            # coefficient of variation of T2 for a sample of two is 1, because
            # T2 is exponential. Measured, not assumed.
            cv = float(np.std(vals, ddof=1) / np.mean(vals)) * math.sqrt(40)
            control = dict(design=lab + " [CV of T2 = 1, T2 exponential]",
                           lean=1.0, truth=cv,
                           sem=1.0 / math.sqrt(2 * (40 - 1)))
    reg = ("single panmictic diploid population, sample of two chromosomes, "
           "2 Mb with recombination so each replicate averages many independent "
           "genealogies; the observable is the mean pairwise coalescence time "
           "in generations, read in branch mode -- no mutation model, so no "
           "mutation-rate convention enters")
    record("coalescentTimeScale", "Conventions.lean", "ploidy * Ne = 2 * Ne",
           cells_two, regime=reg, control=control)
    record("coalescentTimeScale [4*Ne reading, competing]", "Conventions.lean",
           "4 * Ne", cells_four, regime=reg, control=control,
           note="the 4*Ne that appears throughout this corpus is the scaled "
                "mutation rate theta = 4*Ne*mu, a different quantity")


def group_b():
    rng = np.random.default_rng(23002)
    cells = []
    control = None
    for label, freq in (("uniform 4", np.array([0.25] * 4)),
                        ("skewed 4", np.array([0.7, 0.2, 0.07, 0.03])),
                        ("uniform 10", np.array([0.1] * 10)),
                        ("dominant 3", np.array([0.9, 0.07, 0.03]))):
        n = 4000000
        a = rng.choice(len(freq), size=n, p=freq)
        b = rng.choice(len(freq), size=n, p=freq)
        match = float(np.mean(a == b))
        sem = math.sqrt(match * (1 - match) / n)
        lean = float(np.sum(freq ** 2))
        print("  %-12s match rate = %.6f ± %.6f  (lean %.6f)"
              % (label, match, sem, lean))
        cells.append(dict(design=label, lean=lean, truth=match, sem=sem))
        if label == "uniform 4":
            # control: the realised marginal frequency of the first haplotype
            # reproduces its input, an independent fact about the sampler
            control = dict(design=label + " [realised freq of allele 0]",
                           lean=float(freq[0]),
                           truth=float(np.mean(a == 0)),
                           sem=math.sqrt(freq[0] * (1 - freq[0]) / n))
    record("haplotypeHomozygosity", "HaplotypeTheory.lean", "sum freq_i ^ 2",
           cells,
           regime="the observable is the probability that two INDEPENDENTLY "
                  "drawn haplotypes are identical, counted over 4e6 pairs; the "
                  "sum of squared frequencies is never evaluated to produce the "
                  "oracle",
           control=control)


def group_c():
    rng = np.random.default_rng(23003)
    cells_sq, cells_lin, cells_sum = [], [], []
    control = None
    reps = 4000
    for n1, n2, rg in ((2000, 8000, 0.9), (2000, 8000, 0.5),
                       (4000, 4000, 0.7), (2000, 8000, 0.2)):
        beta1 = 0.1
        beta2 = rg * beta1
        est = []
        for _ in range(reps):
            # per-study marginal estimates of each trait's effect at one locus,
            # standardized genotypes so Var(beta_hat_k) = 1/n_k
            b1 = beta1 + rng.normal(0, 1 / math.sqrt(n1))
            b2 = beta2 + rng.normal(0, 1 / math.sqrt(n2))
            # the optimal linear combination for estimating beta1, using trait 2
            # only through the genetic correlation: weight by inverse variance
            # after rescaling trait 2's estimate by rg
            w1 = n1
            w2 = n2 * rg ** 2
            est.append((w1 * b1 + w2 * (b2 / rg if rg != 0 else 0.0))
                       / (w1 + w2))
        est = np.asarray(est)
        var = float(est.var(ddof=1))
        n_eff = 1.0 / var
        # sem on N_eff from the sem on the variance
        sem = n_eff * math.sqrt(2.0 / (reps - 1))
        lab = "n1=%d n2=%d rg=%.1f" % (n1, n2, rg)
        print("  %-24s N_eff = %.0f ± %.0f | sq %.0f  lin %.0f  sum %.0f"
              % (lab, n_eff, sem, n1 + rg ** 2 * n2, n1 + rg * n2, n1 + n2))
        cells_sq.append(dict(design=lab, lean=n1 + rg ** 2 * n2, truth=n_eff,
                             sem=sem))
        cells_lin.append(dict(design=lab, lean=n1 + rg * n2, truth=n_eff,
                              sem=sem))
        cells_sum.append(dict(design=lab, lean=float(n1 + n2), truth=n_eff,
                              sem=sem))
        if rg == 0.9 and n1 == 2000:
            # control: trait 1 alone must give N_eff = n1, measured through the
            # same estimator with the trait-2 weight set to zero
            solo = np.asarray([beta1 + rng.normal(0, 1 / math.sqrt(n1))
                               for _ in range(reps)])
            control = dict(design=lab + " [trait 1 alone, N_eff = n1]",
                           lean=float(n1), truth=1.0 / float(solo.var(ddof=1)),
                           sem=n1 * math.sqrt(2.0 / (reps - 1)))
    reg = ("two genetically correlated traits measured on independent samples, "
           "one locus, standardized genotypes so a study of size n estimates "
           "the effect with variance 1/n; the observable is the realised "
           "variance of the optimally combined estimator over 4000 replicates, "
           "inverted through Var = 1/N_eff. rg is swept 0.2 to 0.9, over which "
           "the three candidate forms separate by more than twofold")
    record("multiTraitEffectiveSampleSize", "GeneticArchitectureDiscovery.lean",
           "n1 + rg ^ 2 * n2", cells_sq, regime=reg, control=control)
    record("multiTraitEffectiveSampleSize [n1 + rg*n2, competing]",
           "GeneticArchitectureDiscovery.lean", "n1 + rg * n2", cells_lin,
           regime=reg, control=control)
    record("multiTraitEffectiveSampleSize [n1 + n2, competing]",
           "GeneticArchitectureDiscovery.lean", "n1 + n2", cells_sum,
           regime=reg, control=control)


def main():
    for fn in (group_b, group_c, group_a):
        print("\n===== %s =====" % fn.__name__)
        try:
            fn()
        except Exception as e:
            print("*** %s RAISED %r" % (fn.__name__, e))
            import traceback
            traceback.print_exc()
    json.dump(RESULTS, open("battery_bulk23_results.json", "w"), indent=1,
              default=str)
    print("\n================ SUMMARY ================")
    for r in RESULTS:
        w = r.get("worst", {})
        print("%-22s %-52s worst %9.2f sems, %7.2f%% rel"
              % (r["verdict"], r["name"], w.get("sems_off", float("nan")),
                 100 * w.get("rel_err", float("nan"))))


if __name__ == "__main__":
    main()
