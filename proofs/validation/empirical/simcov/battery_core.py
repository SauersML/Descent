"""Battery 1: core population-genetic definitions against a simulated oracle.

Each entry transcribes the Lean body LITERALLY (the transcription is quoted in
`source` so a reader can diff it against the file), evaluates it across a design
that makes the prediction MOVE, and compares against `simlib`'s ground truth in
units of the simulation's own standard error.

Verdict rule, applied uniformly:
  MATCH      -- every cell within 3 sems
  FALSIFIED  -- some cell off by more than 3 sems AND more than 2 percent
  NO POWER   -- the prediction spans less than 5 percent across the design, so
                the design could not have rejected a wrong functional form
The middle clause matters: with enough replicates everything is significantly
wrong, and a 0.1 percent bias at 8 sems is a report about the estimator, not
about the definition.
"""
import json
import math
import sys

import numpy as np

import simlib

RESULTS = []


def record(name, lean_file, source, cells, note="", regime=""):
    """`cells` is a list of dicts: design, lean value, truth mean, truth sem."""
    preds = [c["lean"] for c in cells]
    span = (max(preds) - min(preds)) / max(abs(max(preds)), 1e-12)
    worst = None
    for c in cells:
        sem = c["sem"] if c["sem"] and c["sem"] > 0 else float("nan")
        z = abs(c["lean"] - c["truth"]) / sem if sem == sem and sem > 0 else float("inf")
        rel = abs(c["lean"] - c["truth"]) / max(abs(c["truth"]), 1e-12)
        c["sems_off"], c["rel_err"] = z, rel
        if worst is None or z > worst["sems_off"]:
            worst = c
    if span < 0.05:
        verdict = "NO POWER"
    elif worst["sems_off"] > 3 and worst["rel_err"] > 0.02:
        verdict = "FALSIFIED"
    else:
        verdict = "MATCH"
    RESULTS.append(dict(name=name, file=lean_file, source=source, note=note,
                        regime=regime, span=span, verdict=verdict,
                        worst=worst, cells=cells))
    print("\n%-38s %s   (span %.0f%%)" % (name, verdict, 100 * span))
    print("  lean: %s" % source)
    print("  %-34s %10s %10s %8s %8s" % ("design", "lean", "sim", "sem", "sems"))
    for c in cells:
        print("  %-34s %10.5f %10.5f %8.5f %8.2f"
              % (c["design"], c["lean"], c["truth"], c["sem"], c["sems_off"]))


# ---------------------------------------------------------------------------
# A.  coalFst  --  PopulationGeneticsFoundations.lean:195
# ---------------------------------------------------------------------------
def test_coalFst():
    lean = lambda t, Ne: t / (t + 2 * Ne)
    Ne = 1000
    cells = []
    for t in (200, 500, 1000, 2000, 4000):
        r = simlib.split_fst(Ne, t, n_dip=40, seq_len=4e6, reps=16, seed=11)
        cells.append(dict(design="t=%d Ne=%d" % (t, Ne), lean=lean(t, Ne),
                          truth=r["hudson"]["mean"], sem=r["hudson"]["sem"]))
    record("coalFst", "PopulationGeneticsFoundations.lean",
           "t / (t + 2 * Ne)", cells,
           regime="clean split, no migration, Hudson estimator")


# ---------------------------------------------------------------------------
# B.  neiGst / hudsonFst as parametric limits  --  Conventions.lean
#     Both are stated on TRUE frequencies, so the oracle is the estimator
#     applied to simulated frequencies with sampling noise removed.
# ---------------------------------------------------------------------------
def test_nei_vs_hudson():
    def nei(p1, p2):
        pbar = (p1 + p2) / 2
        return 1 - (p1 * (1 - p1) + p2 * (1 - p2)) / (2 * pbar * (1 - pbar))

    def hud(p1, p2):
        return (p1 - p2) ** 2 / (p1 * (1 - p2) + p2 * (1 - p1))

    rng = np.random.default_rng(4)
    cells = []
    for lo, hi, lab in ((0.4, 0.6, "p near 1/2"), (0.05, 0.95, "p wide"),
                        (0.01, 0.2, "p rare")):
        p1 = rng.uniform(lo, hi, 40000)
        p2 = rng.uniform(lo, hi, 40000)
        # ratio-of-averages, the convention both are written for
        n_nei = np.mean(2 * ((p1 + p2) / 2) * (1 - (p1 + p2) / 2)
                        - (p1 * (1 - p1) + p2 * (1 - p2)))
        d_nei = np.mean(2 * ((p1 + p2) / 2) * (1 - (p1 + p2) / 2))
        cells.append(dict(design="neiGst, " + lab,
                          lean=float(np.mean([nei(a, b) for a, b in
                                              zip(p1[:4000], p2[:4000])])),
                          truth=float(n_nei / d_nei), sem=float(n_nei / d_nei) * 0.01))
    record("neiGst (per-site vs ratio-of-averages)", "Conventions.lean",
           "1 - (p1(1-p1)+p2(1-p2)) / (ploidy * pbar * (1-pbar))", cells,
           note="tests whether the per-site formula composes to the "
                "ratio-of-averages F_ST it is used as")


# ---------------------------------------------------------------------------
# C.  fstMigrationMutationEquilibrium  --  PopulationGeneticsFoundations:1205
# ---------------------------------------------------------------------------
def test_fst_migration():
    lean = lambda Ne, m, mu: 1 / (1 + 4 * Ne * m + 4 * Ne * mu)
    Ne, mu = 1000, 1e-8
    for n_demes, tag in ((20, "20 demes"), (2, "2 demes")):
        cells = []
        for m in (1e-4, 3e-4, 1e-3, 3e-3):
            r = simlib.island_fst(Ne, m, n_demes=n_demes, n_dip=40,
                                  seq_len=4e6, mu=mu, reps=16, seed=21)
            cells.append(dict(design="%s m=%.0e (4Nm=%.1f)" % (tag, m, 4 * Ne * m),
                              lean=lean(Ne, m, mu),
                              truth=r["hudson"]["mean"], sem=r["hudson"]["sem"]))
        record("fstMigrationMutationEquilibrium [%s]" % tag,
               "PopulationGeneticsFoundations.lean",
               "1 / (1 + 4*Ne*m + 4*Ne*mu)", cells,
               regime="symmetric island model, %s" % tag)


# ---------------------------------------------------------------------------
# D.  alleleFreqAfterMigration  --  PopulationGeneticsFoundations:1429
# ---------------------------------------------------------------------------
def test_allele_freq_migration():
    lean = lambda p0, pc, m, t: pc + (p0 - pc) * (1 - m) ** t
    cells = []
    for m in (0.01, 0.05, 0.2):
        for t in (5, 40):
            p0, pc = 0.9, 0.1
            p = p0
            for _ in range(t):          # explicit continent-island iteration
                p = (1 - m) * p + m * pc
            cells.append(dict(design="m=%.2f t=%d" % (m, t),
                              lean=lean(p0, pc, m, t), truth=p, sem=1e-12))
    record("alleleFreqAfterMigration", "PopulationGeneticsFoundations.lean",
           "p_c + (p0 - p_c) * (1 - m)^t", cells,
           regime="deterministic continent-island recursion")


# ---------------------------------------------------------------------------
# E.  cumulativeDrift  --  DemographicHistory.lean:780
# ---------------------------------------------------------------------------
def test_cumulative_drift():
    lean = lambda sched: sum(1.0 / (2 * N) for N in sched)
    cells = []
    for sched, lab in (([500] * 20, "N=500 x20"),
                       ([200] * 50, "N=200 x50"),
                       ([50] * 60, "N=50 x60 (deep)"),
                       ([1000] * 10 + [30] * 10 + [1000] * 10, "bottleneck")):
        h = simlib.wf_drift_het(sched, reps=300, n_loci=400, seed=33)
        truth = 1 - h[-1] / h[0]          # realised inbreeding 1 - H_t/H_0
        cells.append(dict(design=lab, lean=lean(sched), truth=float(truth),
                          sem=float(truth) * 0.01))
    record("cumulativeDrift", "DemographicHistory.lean",
           "sum_i 1 / (2 * Ne_i)", cells,
           regime="read as the realised inbreeding 1 - H_t/H_0")


# ---------------------------------------------------------------------------
# F.  hweGenotypeVariance  --  Conventions.lean:93
# ---------------------------------------------------------------------------
def test_hwe_variance():
    rng = np.random.default_rng(9)
    cells = []
    for p in (0.05, 0.25, 0.5):
        g = rng.binomial(2, p, 400000)
        cells.append(dict(design="p=%.2f" % p, lean=2 * p * (1 - p),
                          truth=float(g.var()), sem=float(g.var()) * 0.005))
    record("hweGenotypeVariance", "Conventions.lean", "ploidy * p * (1 - p)",
           cells, regime="dosage 0/1/2 under Hardy-Weinberg")


# ---------------------------------------------------------------------------
# G.  admixtureLD / admixedAlleleFreq  --  LDDecayTheory:237, DemographicHistory:568
# ---------------------------------------------------------------------------
def test_admixture():
    rng = np.random.default_rng(12)
    cellsD, cellsP = [], []
    for alpha in (0.2, 0.5, 0.8):
        for (pA1, pB1, pA2, pB2) in [(0.8, 0.2, 0.7, 0.1)]:
            n = 400000
            src = rng.random(n) < alpha
            l1 = np.where(src, rng.random(n) < pA1, rng.random(n) < pB1)
            l2 = np.where(src, rng.random(n) < pA2, rng.random(n) < pB2)
            D = float(np.mean(l1 * l2) - np.mean(l1) * np.mean(l2))
            lean_D = alpha * (1 - alpha) * (pA1 - pB1) * (pA2 - pB2)
            cellsD.append(dict(design="alpha=%.1f" % alpha, lean=lean_D,
                               truth=D, sem=abs(D) * 0.01))
            lean_p = alpha * pA1 + (1 - alpha) * pB1
            cellsP.append(dict(design="alpha=%.1f" % alpha, lean=lean_p,
                               truth=float(np.mean(l1)),
                               sem=float(np.std(l1)) / math.sqrt(n)))
    record("admixtureLD", "LDDecayTheory.lean",
           "alpha * (1 - alpha) * dp1 * dp2", cellsD,
           regime="one-pulse admixture, generation 0, gametic D")
    record("admixedAlleleFreq", "DemographicHistory.lean",
           "alpha * p_A + (1 - alpha) * p_B", cellsP)


# ---------------------------------------------------------------------------
# H.  driftLDRetention  --  LDDecayTheory.lean:388
#     The claim is a per-generation retention factor on the LD measure.  It
#     carries a drift term, so it can only be read on the SECOND moment.
# ---------------------------------------------------------------------------
def test_drift_ld_retention():
    lean = lambda Ne, c: (1 - c) ** 2 * (1 - 1 / (2 * Ne))
    cells = []
    for Ne, c in ((100, 0.0), (100, 0.02), (100, 0.05), (500, 0.02)):
        tl = simlib.wf_two_locus(Ne=Ne, c=c, gens=12, reps=4000, seed=41)
        d2 = tl["D2"]
        # geometric mean of the per-generation ratio over the run
        ratios = d2[1:] / d2[:-1]
        truth = float(np.exp(np.mean(np.log(ratios))))
        sem = float(np.std(np.log(ratios)) / math.sqrt(len(ratios))) * truth
        cells.append(dict(design="Ne=%d c=%.2f" % (Ne, c), lean=lean(Ne, c),
                          truth=truth, sem=sem))
    record("driftLDRetention", "LDDecayTheory.lean",
           "(1 - c)^2 * (1 - 1/(2*Ne))", cells,
           regime="per-generation retention of E[D^2] under WF drift")


# ---------------------------------------------------------------------------
# I.  steppingStoneFstQuadratic vs the validated demoSteppingStoneFst
# ---------------------------------------------------------------------------
def test_stepping_stone():
    import msprime
    n_demes, Ne = 12, 500
    cells_q, cells_l = [], []
    for m in (0.005, 0.02, 0.05):
        dem = msprime.Demography.stepping_stone_model(
            [Ne] * n_demes, migration_rate=m / 2.0, boundaries=True)
        hud = []
        for r in range(12):
            ts = msprime.sim_ancestry(
                samples={"pop_0": 40, "pop_3": 40}, demography=dem,
                sequence_length=4e6, random_seed=51 + r)
            ts = msprime.sim_mutations(ts, rate=1e-8, random_seed=151 + r)
            if ts.num_sites == 0:
                continue
            gm = ts.genotype_matrix()
            a, b = ts.samples(population=0), ts.samples(population=3)
            hud.append(simlib.hudson_fst(gm[:, a].sum(1).astype(float), len(a),
                                         gm[:, b].sum(1).astype(float), len(b)))
        s = simlib.summarize(hud)
        d, sigma_sq = 3.0, m      # mean squared displacement per generation
        cells_q.append(dict(design="m=%.3f d=3" % m,
                            lean=d / (d + 4 * Ne * sigma_sq ** 2 * m ** 2),
                            truth=s["mean"], sem=s["sem"]))
        cells_l.append(dict(design="m=%.3f d=3" % m,
                            lean=d / (d + 4 * Ne * m * sigma_sq),
                            truth=s["mean"], sem=s["sem"]))
    record("steppingStoneFstQuadratic", "DemographicHistory.lean",
           "d / (d + 4*Ne*sigma_sq^2*m^2)", cells_q,
           regime="1D stepping stone, 12 demes, distance 3")
    record("demoSteppingStoneFst [already VALIDATED, re-checked]",
           "DemographicHistory.lean", "d / (d + 4*Ne*m*sigma_sq)", cells_l,
           regime="same design, the sibling form")


def main():
    for fn in (test_coalFst, test_nei_vs_hudson, test_fst_migration,
               test_allele_freq_migration, test_cumulative_drift,
               test_hwe_variance, test_admixture, test_drift_ld_retention,
               test_stepping_stone):
        try:
            fn()
        except Exception as e:
            print("\n*** %s RAISED %r" % (fn.__name__, e))
            import traceback
            traceback.print_exc()
    json.dump(RESULTS, open("battery_core_results.json", "w"), indent=1)
    print("\n\n================ SUMMARY ================")
    for r in RESULTS:
        print("%-12s %-46s worst %6.1f sems, %5.1f%% rel"
              % (r["verdict"], r["name"], r["worst"]["sems_off"],
                 100 * r["worst"]["rel_err"]))


if __name__ == "__main__":
    main()
