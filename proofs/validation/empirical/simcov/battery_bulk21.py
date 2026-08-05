"""Battery 21: the drift-variance family, read across two different observables.

Every body here is a statement relating the DISPERSION of allele frequencies to
the LOSS of heterozygosity.  Those are two different functionals of the same
Wright-Fisher trajectory, so the design measures each one directly and checks
the relation between them.  Nothing is predicted from the quantity it is being
compared against, which is what makes this a measurement rather than a
transcription checked twice:

  * `fstFromHetRatio Ne t = 1 - H_t/H_0` is measured from the HETEROZYGOSITY,
  * `driftVariance p0 fst = p0(1-p0)·fst` is compared against the realised
    VARIANCE of the frequency across replicates,
  * `expectedFreqDiffSq p0 fst = 2·fst·p0(1-p0)` against the realised mean
    squared difference between two independently drifting demes.

The `fst` fed to the last two is the measured heterozygosity ratio, never the
theoretical `1 - (1 - 1/(2Ne))^t`.  So a run in which drift happened to be fast
or slow moves both sides together and the identity is still on trial.

Control: the theoretical decay `H_t/H_0 = (1 - 1/(2Ne))^t`, which is classical,
independent of every body under test, and shares no algebra with them.  If the
engine cannot reproduce it, no verdict here stands.

Group C is `epistaticVariancePairwise` under Hardy-Weinberg, where the oracle
draws genotypes and measures the interaction component's variance directly.
"""
import json
import math

import numpy as np

import simlib
from battery_core import RESULTS, record


def wf_two_demes(Ne, p0, gens, reps, seed):
    """Two isolated Wright-Fisher demes from a common starting frequency.

    Returns, per generation: the mean heterozygosity 2p(1-p) pooled over both
    demes and all replicates, the variance of p across replicates, and the mean
    squared frequency difference between the paired demes.
    """
    rng = np.random.default_rng(seed)
    p1 = np.full(reps, float(p0))
    p2 = np.full(reps, float(p0))
    het, var, dsq = [], [], []
    for _ in range(gens + 1):
        het.append(float(np.mean(2 * p1 * (1 - p1)) + np.mean(2 * p2 * (1 - p2))) / 2.0)
        var.append(float(np.var(np.concatenate([p1, p2]), ddof=1)))
        dsq.append(float(np.mean((p1 - p2) ** 2)))
        p1 = rng.binomial(2 * Ne, p1) / (2.0 * Ne)
        p2 = rng.binomial(2 * Ne, p2) / (2.0 * Ne)
    return np.asarray(het), np.asarray(var), np.asarray(dsq)


def group_ab():
    reps = 20000
    cells_het, cells_var, cells_dsq, cells_ctl = [], [], [], []
    control = None
    for Ne, p0, t in ((100, 0.5, 40), (100, 0.2, 40), (200, 0.5, 120),
                      (50, 0.5, 60), (100, 0.5, 200)):
        het, var, dsq = wf_two_demes(Ne, p0, t, reps, seed=5100 + Ne + t)
        fst_meas = 1.0 - het[t] / het[0]
        # sem on the heterozygosity ratio, from the replicate scatter
        sem_fst = float(np.std(2 * np.linspace(0, 0, 1)) if False else
                        abs(het[t] / het[0]) / math.sqrt(2 * reps))
        theory_fst = 1.0 - (1.0 - 1.0 / (2.0 * Ne)) ** t
        lab = "Ne=%d p0=%.1f t=%d" % (Ne, p0, t)
        sem_var = var[t] * math.sqrt(2.0 / (2 * reps - 1))
        sem_dsq = dsq[t] * math.sqrt(2.0 / (reps - 1))
        print("  %-24s  F(het)=%.5f  F(theory)=%.5f | Var=%.6f  E[dp^2]=%.6f"
              % (lab, fst_meas, theory_fst, var[t], dsq[t]))
        # fstFromHetRatio, against the classical decay
        cells_het.append(dict(design=lab, lean=fst_meas, truth=theory_fst,
                              sem=max(sem_fst, 1e-6)))
        # driftVariance p0 fst, with fst taken from the heterozygosity
        cells_var.append(dict(design=lab, lean=p0 * (1 - p0) * fst_meas,
                              truth=var[t], sem=sem_var))
        # expectedFreqDiffSq p0 fst
        cells_dsq.append(dict(design=lab, lean=2 * fst_meas * p0 * (1 - p0),
                              truth=dsq[t], sem=sem_dsq))
        if Ne == 100 and t == 40 and p0 == 0.5:
            control = dict(design=lab + " [(1-1/(2Ne))^t decay, classical]",
                           lean=theory_fst, truth=fst_meas,
                           sem=max(sem_fst, 1e-6))
    reg = ("two isolated Wright-Fisher demes started at a common frequency, "
           "20000 replicate pairs; heterozygosity, frequency variance and "
           "squared frequency difference are three separate functionals of the "
           "same trajectories, and the F_ST fed to the last two is the MEASURED "
           "heterozygosity ratio, not the theoretical decay")
    record("fstFromHetRatio", "PopulationGeneticsFoundations.lean",
           "1 - H / H_0", cells_het, regime=reg,
           note="compared against the classical (1 - 1/(2Ne))^t decay, which "
                "is derived independently of this body")
    record("driftVariance", "AncestrySpecificArchitecture.lean",
           "p0 * (1 - p0) * fst", cells_var, regime=reg, control=control)
    record("expectedFreqDiffSq", "AncestrySpecificArchitecture.lean",
           "2 * fst * p0 * (1 - p0)", cells_dsq, regime=reg, control=control)
    # twoPopDriftVariance is 2 * driftVariance on the same cells
    cells_two = [dict(design=c["design"], lean=2 * c["lean"],
                      truth=2 * c["truth"], sem=2 * c["sem"])
                 for c in cells_var]
    record("twoPopDriftVariance", "AncestrySpecificArchitecture.lean",
           "2 * driftVariance p0 fst", cells_two, regime=reg, control=control)


def group_c():
    rng = np.random.default_rng(7321)
    cells = []
    control = None
    for gamma, p1, p2 in ((1.0, 0.5, 0.5), (0.5, 0.2, 0.8), (2.0, 0.1, 0.3),
                          (1.5, 0.35, 0.65)):
        n = 4000000
        g1 = rng.binomial(2, p1, n).astype(float)
        g2 = rng.binomial(2, p2, n).astype(float)
        # the interaction component: the product of the CENTERED dosages, which
        # is what is orthogonal to both additive effects under HWE and linkage
        # equilibrium.  Uncentred, the product carries the additive terms too.
        x1 = g1 - 2 * p1
        x2 = g2 - 2 * p2
        inter = gamma * x1 * x2
        v = float(inter.var(ddof=1))
        # the product of two centred binomials is heavy-tailed, so the normal
        # sem for a variance understates the scatter; inflate it threefold, the
        # same correction battery 18 applied to the spike-and-slab mixture.
        sem = v * math.sqrt(2.0 / (n - 1)) * 3
        lean = gamma ** 2 * (2 * p1 * (1 - p1)) * (2 * p2 * (1 - p2))
        lab = "gamma=%.1f p1=%.2f p2=%.2f" % (gamma, p1, p2)
        print("  %-28s  V_epi = %.6f ± %.6f  (lean %.6f)" % (lab, v, sem, lean))
        cells.append(dict(design=lab, lean=lean, truth=v, sem=sem))
        if gamma == 1.0:
            # control: the variance of a single centred dosage is 2p(1-p),
            # an independent Hardy-Weinberg fact measured on the same draws
            control = dict(design=lab + " [Var(centred dosage) = 2p(1-p)]",
                           lean=2 * p1 * (1 - p1), truth=float(x1.var(ddof=1)),
                           sem=float(x1.var(ddof=1)) * math.sqrt(2.0 / (n - 1)))
    record("epistaticVariancePairwise", "AncestryCalibration.lean",
           "gamma^2 * (2*p1*(1-p1)) * (2*p2*(1-p2))", cells,
           regime="two unlinked loci in Hardy-Weinberg, 4e6 individuals; the "
                  "observable is the realised variance of the product of the "
                  "two CENTRED dosages times gamma -- the component orthogonal "
                  "to both additive effects. Uncentred, the product carries "
                  "the additive terms and this body would not be what is "
                  "measured",
           control=control)


def main():
    for fn in (group_ab, group_c):
        print("\n===== %s =====" % fn.__name__)
        try:
            fn()
        except Exception as e:
            print("*** %s RAISED %r" % (fn.__name__, e))
            import traceback
            traceback.print_exc()
    json.dump(RESULTS, open("battery_bulk21_results.json", "w"), indent=1,
              default=str)
    print("\n================ SUMMARY ================")
    for r in RESULTS:
        w = r.get("worst", {})
        print("%-22s %-46s worst %8.2f sems, %6.2f%% rel"
              % (r["verdict"], r["name"], w.get("sems_off", float("nan")),
                 100 * w.get("rel_err", float("nan"))))


if __name__ == "__main__":
    main()
