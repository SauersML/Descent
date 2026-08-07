"""Battery 3: instrument fixes, then the tests that depended on them.

Four corrections, each to the TEST rather than to the corpus:

 1. RECOMBINATION.  Batteries 1-2 simulated with `recombination_rate = 0`, so
    every site in a replicate sat on ONE genealogy: a 20 Mb sequence carried no
    more independent information about F_ST than a single site.  The error bars
    were honest (they were taken across replicates) but enormous, and two runs
    of the SAME demography differed by 2.4 sems (0.300 vs 0.370).  With
    recombination on, each replicate contains many independent genealogies and
    F_ST tightens by roughly the square root of that count.  No F_ST verdict
    from batteries 1-2 that rested on a coalescent error bar survives without
    being recomputed here.

 2. hetMutationFloor divided by the number of SEGREGATING sites.  Conditioning
    on a site being polymorphic inflates heterozygosity by exactly the factor
    that vanishes as theta grows -- which is precisely the pattern the run
    showed (11.6 sems off at theta = 0.04, 0.2 sems at theta = 1.2).  The
    denominator is the whole sequence.

 3. Var_Delta_Mu was fed Nei's G_ST between the two demes, which for a pure
    split equals HALF the per-branch drift F and a QUARTER of the corpus's own
    pairwise F_ST (`pairwiseFstFromBranches fstS fstT`).  That is a factor of
    four, and it is the entire discrepancy.  Re-run against the corpus
    convention, and both conventions reported side by side.

 4. freqCorrFromFst is tested across several ancestral frequency distributions,
    because `corr(p1, p2) = Var(p0) / (Var(p0) + F E[p0(1-p0)])` depends on the
    ancestral spread and is NOT a function of F_ST alone.  Whether `1 - Fst`
    holds is therefore a property of the distribution, and reporting one number
    from one arbitrary choice would be reporting the choice.
"""
import json
import math

import numpy as np

import simlib
from battery_core import RESULTS, record


def _split_fst_rec_rep(params):
    """One recombining-split replicate.  Top-level so a pool can pickle it.

    The seed is `seed + r` and nothing carries between replicates, so fanning
    these out across processes returns the same numbers in the same order --
    see `simlib.replicate_map`.
    """
    NeA, NeB, NeANC, t, n_dip, seq_len, mu, rho, seed, r = params
    import msprime
    dem = msprime.Demography()
    dem.add_population(name="A", initial_size=NeA)
    dem.add_population(name="B", initial_size=NeB)
    dem.add_population(name="ANC", initial_size=NeANC)
    dem.add_population_split(time=t, derived=["A", "B"], ancestral="ANC")
    ts = msprime.sim_ancestry(samples={"A": n_dip, "B": n_dip},
                              demography=dem, sequence_length=seq_len,
                              recombination_rate=rho, random_seed=seed + r)
    ts = msprime.sim_mutations(ts, rate=mu, random_seed=seed + 7000 + r)
    if ts.num_sites == 0:
        return None
    gm = ts.genotype_matrix()
    a, b = ts.samples(population=0), ts.samples(population=1)
    return simlib.hudson_fst(gm[:, a].sum(1).astype(float), len(a),
                             gm[:, b].sum(1).astype(float), len(b))


def split_fst_rec(Ne, t, NeA=None, NeB=None, NeANC=None, n_dip=50,
                  seq_len=2e7, mu=1e-8, rho=1e-8, reps=25, seed=1,
                  workers=None):
    """Clean split with RECOMBINATION on, so a replicate holds many genealogies."""
    NeA = NeA or Ne
    NeB = NeB or Ne
    NeANC = NeANC or Ne
    out = simlib.replicate_map(
        _split_fst_rec_rep,
        [(NeA, NeB, NeANC, t, n_dip, seq_len, mu, rho, seed, r)
         for r in range(reps)],
        workers=workers)
    return simlib.summarize([x for x in out if x is not None])


# ---------------------------------------------------------------------------
# 1. coalFst and pairwiseFstFromBranchTaus, both with a usable error bar
# ---------------------------------------------------------------------------
def test_fst_composition():
    """coalFst vs pairwiseFstFromBranchTaus on the SAME simulated designs.

    These two corpus definitions are both meant to give the F_ST of a clean
    split.  On a symmetric split they disagree by construction -- `t/(t+2Ne)`
    against `2tau/(1+2tau)` -- so at most one of them can be the measured
    quantity, and the simulation says which.
    """
    coal = lambda t, Ne: t / (t + 2 * Ne)
    pair = lambda tS, tT: (tS + tT) / (1 + tS + tT)
    cells_c, cells_p = [], []
    for NeA, NeB, t in ((1000, 1000, 500), (1000, 1000, 1000),
                        (1000, 1000, 2000), (500, 2000, 1000)):
        s = split_fst_rec(1000, t, NeA=NeA, NeB=NeB, NeANC=1000,
                          n_dip=50, seq_len=2e7, reps=25, seed=801)
        tauS, tauT = t / (2.0 * NeA), t / (2.0 * NeB)
        lab = "NeA=%d NeB=%d t=%d" % (NeA, NeB, t)
        # coalFst is written for a symmetric split; use the harmonic-mean Ne
        Ne_eff = 2.0 / (1.0 / NeA + 1.0 / NeB)
        cells_c.append(dict(design=lab, lean=coal(t, Ne_eff),
                            truth=s["mean"], sem=s["sem"]))
        cells_p.append(dict(design=lab, lean=pair(tauS, tauT),
                            truth=s["mean"], sem=s["sem"]))
    record("coalFst / fstFromGenerations [recombining]",
           "PopulationGeneticsFoundations.lean", "t / (t + 2*Ne)", cells_c,
           regime="clean split, recombining, Hudson ratio-of-averages")
    record("pairwiseFstFromBranchTaus [recombining]", "PortabilityDrift.lean",
           "(tauS + tauT) / (1 + tauS + tauT)", cells_p,
           regime="same runs, same estimator, the sibling composition")


# ---------------------------------------------------------------------------
# 2. hetMutationFloor with the right denominator
# ---------------------------------------------------------------------------
def test_het_mutation_floor_fixed():
    import msprime
    cells = []
    Ne = 1000
    for mu in (1e-5, 3e-5, 1e-4, 3e-4):
        L = 20000
        hets = []
        for r in range(15):
            ts = msprime.sim_ancestry(samples=60, population_size=Ne,
                                      sequence_length=L, recombination_rate=1e-8,
                                      random_seed=901 + r)
            ts = msprime.sim_mutations(ts, rate=mu,
                                       model=msprime.InfiniteAlleles(),
                                       random_seed=1901 + r)
            gm = ts.genotype_matrix()
            tot = 0.0
            for row in gm:
                _, cnt = np.unique(row, return_counts=True)
                f = cnt / cnt.sum()
                tot += 1 - float((f ** 2).sum())
            # DENOMINATOR IS THE WHOLE SEQUENCE: monomorphic sites have het 0
            hets.append(tot / L)
        s = simlib.summarize(hets)
        theta = 4 * Ne * mu
        cells.append(dict(design="theta=%.2f" % theta, lean=theta / (1 + theta),
                          truth=s["mean"], sem=s["sem"]))
    record("hetMutationFloor [fixed denominator]", "PortabilityDrift.lean",
           "4*Ne*mu / (1 + 4*Ne*mu)", cells,
           regime="infinite-alleles heterozygosity per site, all sites")


# ---------------------------------------------------------------------------
# 3. Var_Delta_Mu under the corpus's own pairwise-F_ST convention
# ---------------------------------------------------------------------------
def test_var_delta_mu_conventions():
    from battery_pgs import pgs_split_drift
    cells_corpus, cells_gst = [], []
    Ne = 200
    for t in (20, 60, 150, 300):
        r = pgs_split_drift(Ne, t, n_loci=400, reps=2000, seed=101 + t)
        obs = float(np.var(r["delta"], ddof=1))
        sem = obs * math.sqrt(2.0 / (len(r["delta"]) - 1))
        f_branch = 1 - (1 - 1.0 / (2 * Ne)) ** t
        # the corpus's own composition of two branches into a pairwise F_ST
        f_pair = 1 - (1 - f_branch) ** 2
        cells_corpus.append(dict(design="t=%d (F_pair=%.3f)" % (t, f_pair),
                                 lean=2 * f_pair * r["V_A"], truth=obs, sem=sem))
        cells_gst.append(dict(design="t=%d (G_ST=%.3f)" % (t, r["fst_realised"]),
                              lean=2 * r["fst_realised"] * r["V_A"],
                              truth=obs, sem=sem))
    record("Var_Delta_Mu [corpus pairwise F_ST convention]",
           "PortabilityDrift.lean", "2 * fst * V_A", cells_corpus,
           regime="fst read as pairwiseFstFromBranches(fstS, fstT)")
    record("Var_Delta_Mu [Nei G_ST convention]", "PortabilityDrift.lean",
           "2 * fst * V_A", cells_gst,
           regime="fst read as the Nei G_ST measured between the two demes")


# ---------------------------------------------------------------------------
# 4. freqCorrFromFst across ancestral frequency distributions
# ---------------------------------------------------------------------------
def test_freq_corr_distributions():
    """Is corr(p1,p2) = 1 - Fst, or is it a property of the ancestral spread?"""
    rng = np.random.default_rng(31)
    Ne, n_loci, reps = 200, 3000, 300
    print("\nfreqCorrFromFst: corr(p1,p2) against 1 - Fst, by ancestral distribution")
    print("  %-22s %8s %10s %10s %10s" % ("ancestral p0", "F_br", "1 - G_ST",
                                          "corr(p1,p2)", "gap"))
    rows = []
    for lab, draw in (("uniform(0.05,0.95)", lambda n: rng.uniform(0.05, 0.95, n)),
                      ("neutral SFS ~1/p", lambda n: np.clip(
                          np.exp(rng.uniform(np.log(0.02), np.log(0.98), n)), 0.02, 0.98)),
                      ("beta(0.5,0.5)", lambda n: rng.beta(0.5, 0.5, n).clip(0.02, 0.98)),
                      ("all p0 = 0.5", lambda n: np.full(n, 0.5))):
        for t in (60, 200):
            p0 = draw(n_loci)
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
            corr = float(np.corrcoef(p1.ravel(), p2.ravel())[0, 1])
            f_br = 1 - (1 - 1.0 / (2 * Ne)) ** t
            rows.append((lab, t, f_br, 1 - gst, corr))
            print("  %-22s %8.3f %10.4f %10.4f %+9.1f%%"
                  % ("%s t=%d" % (lab, t), f_br, 1 - gst, corr,
                     100 * (corr - (1 - gst)) / (1 - gst)))
    print("  The prediction `1 - Fst` moves with the ancestral distribution at")
    print("  FIXED Fst, so it cannot be a function of Fst alone.")
    RESULTS.append(dict(name="freqCorrFromFst (distribution sensitivity)",
                        file="PortabilityDrift.lean", source="1 - fst",
                        verdict="CONVENTION/REGIME DEPENDENT", rows=rows,
                        note="corr(p1,p2) = Var(p0)/(Var(p0)+F E[p0(1-p0)]); "
                             "equals 1-F only when Var(p0) and E[p0(1-p0)] "
                             "stand in a particular ratio",
                        worst=dict(sems_off=float("nan"), rel_err=float("nan"))))


def main():
    for fn in (test_fst_composition, test_het_mutation_floor_fixed,
               test_var_delta_mu_conventions, test_freq_corr_distributions):
        try:
            fn()
        except Exception:
            import traceback
            traceback.print_exc()
    json.dump(RESULTS, open("battery_fix_results.json", "w"), indent=1, default=str)


if __name__ == "__main__":
    main()
