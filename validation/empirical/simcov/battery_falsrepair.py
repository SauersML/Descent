"""Battery falsrepair: settle four FALSIFIED markers with measurements.

FRESHNESS guard string: FALSREPAIR_GUARD_20260804_A

Group A  fstEquilibrium.  battery_bulk38 falsified `1/(1 + theta + bigM)` and
         concluded "no simple composition survives".  The structured-coalescent
         solution for a pair of lineages in a d-deme island model with mutation
         is  F_ST = 1 / (1 + theta + bigM * d/(d-1)),  i.e. ADDITIVE after all,
         with the migration term carrying the deme-count correction the corpus
         already measured and installed as `islandDemeCorrection`.  At d = 2
         that is `1/(1 + theta + 2*bigM)`.  Same design, same estimator, new
         seeds; the old body and two other compositions ride along.

Group B  closedPopulation / neutralDriftFactor / heterozygosityLossDerived.
         All three were falsified at demographic equilibrium, which is OUTSIDE
         the closed-population no-mutation regime each one declares.  Measure
         them INSIDE it: forward Wright-Fisher, no mutation.  Competing
         retentions (1-1/(4Ne))^t and (1-1/Ne)^t ride along.

Group C  fstMigrationMutationEquilibriumManyDemes.  Falsified at two demes,
         which its name excludes.  Measure at TWENTY demes, sweeping 4*Ne*m so
         the prediction spans a factor of eight.  The two-deme form rides along
         and must be rejected.

Group D  calibratedBrierFromVariances.  Falsified under a liability threshold.
         Measure in the regime the body is written for: p a calibrated
         probability with mean pi and variance r2*pi*(1-pi) on the OBSERVED
         scale.  The liability-scale form rides along and must be rejected.

NAMING, and why it had to change.  Every row here used to be recorded as
`<decl> -- <candidate>`, which `ledger.split_name` reads as a TAGGED row.  A
battery in which no row is bare has no CORPUS row at all: `ledger.build` then
files all four candidates as competitors against nothing, `against` is `None`,
and the corpus body's own verdict never enters the ledger.  The row that
transcribes the body in the Lean file is now named BARE and only the rivals
carry tags.

`realised_inputs=True`, and why it is not a fudge: in every group the prediction
is evaluated at EXACT MODEL CONSTANTS -- `theta` and `bigM` are what the
demography was built from, `Ne` and `t` are an integer and a loop counter, and
`pi`/`r2` in group D are the parameters the calibrated probabilities were drawn
with.  None is estimated from the same replicates the oracle measures, so there
is no nominal/realised gap of size O(1/sqrt(m)) for a finding to be confused
with.  Undeclared, every disagreement this battery finds -- including the
competitor REJECTIONS the whole design turns on -- is downgraded to LEAD, and a
downgraded rejection leaves the corpus MATCH looking uncompeted.
"""
import json
import math
import os
import sys

import numpy as np

import simlib
from battery_core import RESULTS, dump_results, record

GUARD = "FALSREPAIR_GUARD_20260804_A"

# See the module docstring. Passed to every `record` call in this file.
MODEL = dict(realised_inputs=True)

# ---------------------------------------------------------------------------
# Group A -- fstEquilibrium, the bulk38 design at new seeds
# ---------------------------------------------------------------------------
NE_A = 500


def identities(theta, bigM, reps=60, seed=91001):
    """Per-replicate (F_within, F_between, F_ST) under infinite alleles.

    Copied from battery_bulk38.identities so the DESIGN is the one that
    falsified the body, not a new one that happens to agree.  The only changes
    are the seed base, the replicate count, and that the per-replicate F_ST is
    returned so its sem comes from replicates rather than from a ratio of two
    separately averaged numbers.
    """
    import msprime
    mu = theta / (4.0 * NE_A)
    m = bigM / (4.0 * NE_A)
    dem = msprime.Demography.island_model([NE_A, NE_A], migration_rate=m)
    W, B, F = [], [], []
    for r in range(reps):
        ts = msprime.sim_ancestry(samples={"pop_0": 25, "pop_1": 25},
                                  demography=dem, sequence_length=1,
                                  random_seed=seed + r)
        mts = msprime.sim_mutations(ts, rate=mu,
                                    model=msprime.InfiniteAlleles(),
                                    random_seed=seed + 7000 + r)
        st = None
        for v in mts.variants():
            st = np.asarray(v.genotypes)
            break
        if st is None:
            W.append(1.0); B.append(1.0); F.append(0.0)
            continue
        A = st[mts.samples(population=0)]
        Bg = st[mts.samples(population=1)]
        between = float(np.mean(A[:, None] == Bg[None, :]))
        wa = float((np.sum(A[:, None] == A[None, :]) - A.size)
                   / max(A.size * (A.size - 1), 1))
        wb = float((np.sum(Bg[:, None] == Bg[None, :]) - Bg.size)
                   / max(Bg.size * (Bg.size - 1), 1))
        w = (wa + wb) / 2.0
        W.append(w); B.append(between)
        F.append((w - between) / (1.0 - between) if between < 1.0 else 0.0)
    return simlib.summarize(W), simlib.summarize(B), simlib.summarize(F)


def group_a():
    print("\n===== GROUP A  fstEquilibrium  (%s)" % GUARD)
    # The four bulk38 cells, plus two that push bigM further so the deme
    # correction (a factor on bigM alone) is separated from the old body by
    # more than it is at bigM = 1.
    grid = [(1.0, 1.0), (2.0, 0.5), (0.5, 2.0), (3.0, 3.0),
            (1.0, 4.0), (0.5, 6.0)]
    # The FIRST key is the corpus body as it now stands in DGP.lean
    # (`1 / (1 + p.theta + 2 * p.bigM)`); it is recorded BARE so the ledger
    # files it as the corpus row. The rest are rivals and carry tags.
    CORPUS_A = "corrected [1/(1+theta+2*bigM)], islandDemeCorrection 2 on migration"
    cands = {
        CORPUS_A:
            lambda th, M: 1.0 / (1 + th + 2 * M),
        "superseded body [1/(1+theta+bigM)]":
            lambda th, M: 1.0 / (1 + th + M),
        "multiplicative [1/((1+theta)(1+bigM))], competing":
            lambda th, M: 1.0 / ((1 + th) * (1 + M)),
        "squared correction [1/(1+theta+4*bigM)], competing":
            lambda th, M: 1.0 / (1 + th + 4 * M),
    }
    cells = {k: [] for k in cands}
    for th, M in grid:
        w, b, f = identities(th, M, seed=91000 + int(100 * (th + 10 * M)))
        lab = "theta=%.1f bigM=%.1f" % (th, M)
        print("  %s  F_ST=%.4f +/- %.4f   " % (lab, f["mean"], f["sem"])
              + "  ".join("%s=%.4f" % (k.split(" ")[0], fn(th, M))
                          for k, fn in cands.items()))
        for k, fn in cands.items():
            cells[k].append(dict(design=lab, lean=fn(th, M), truth=f["mean"],
                                 sem=max(f["sem"], 1e-6)))
    # Control, exactly bulk38's: at bigM = 200 the demes are one population of
    # size 2*Ne, so within-deme identity is panmictic at the metapopulation
    # rate 2*theta.
    cw, cb, cf = identities(1.0, 200.0, seed=91900)
    expect = 1.0 / (1 + 2 * 1.0)
    print("  CONTROL bigM=200: F_within=%.5f +/- %.5f  (1/(1+2*theta)=%.5f)"
          % (cw["mean"], cw["sem"], expect))
    control = dict(design="high migration [F_within = 1/(1+2*theta)]",
                   lean=expect, truth=cw["mean"], sem=max(cw["sem"], 1e-6))
    reg = ("two-deme island model at Ne = 500 under msprime's INFINITE ALLELES "
           "model, sequence_length = 1; the observable is the per-replicate "
           "F_ST = (F_within - F_between)/(1 - F_between) from identity by "
           "state, 60 replicates.  This is battery_bulk38's design at new "
           "seeds with two extra migration cells")
    for k, c in cells.items():
        name = ("EvolutionaryParameters.fstEquilibrium" if k == CORPUS_A
                else "EvolutionaryParameters.fstEquilibrium [%s]" % k)
        record(name, "DGP.lean", k, c, regime=reg, control=control, **MODEL)


# ---------------------------------------------------------------------------
# Group B -- the closed-population regime, measured inside itself
# ---------------------------------------------------------------------------
def group_b():
    print("\n===== GROUP B  closed population, no mutation  (%s)" % GUARD)
    Ne = 1000
    times = [200, 1000, 4000]
    reps = 24
    n_loci = 400
    # per-replicate retention so the sem comes from replicates
    rng = np.random.default_rng(20260804)
    ret = {t: [] for t in times}
    for r in range(reps):
        p = np.full(n_loci, 0.5)
        h0 = float((2 * p * (1 - p)).mean())
        two_n = 2 * Ne
        for g in range(1, max(times) + 1):
            p = rng.binomial(two_n, p) / two_n
            if g in ret:
                ret[g].append(float((2 * p * (1 - p)).mean()) / h0)
    cands = {
        "body [(1 - 1/(2*Ne))^t]": lambda t: (1 - 1.0 / (2 * Ne)) ** t,
        "competing [(1 - 1/(4*Ne))^t]": lambda t: (1 - 1.0 / (4 * Ne)) ** t,
        "competing [(1 - 1/Ne)^t]": lambda t: (1 - 1.0 / Ne) ** t,
    }
    cells = {k: [] for k in cands}
    for t in times:
        s = simlib.summarize(ret[t])
        print("  t=%5d  retention=%.4f +/- %.4f   " % (t, s["mean"], s["sem"])
              + "  ".join("%.4f" % fn(t) for fn in cands.values()))
        for k, fn in cands.items():
            cells[k].append(dict(design="Ne=1000 t=%d" % t, lean=fn(t),
                                 truth=s["mean"], sem=max(s["sem"], 1e-6)))
    # Control: at t = 0 the retention is 1 by construction; a real control is
    # a SECOND population size, where the same body must track a different
    # curve.  Ne = 100, t = 200 gives 0.368 where Ne = 1000 gives 0.905.
    ret2 = []
    for r in range(reps):
        p = np.full(n_loci, 0.5)
        h0 = float((2 * p * (1 - p)).mean())
        for g in range(200):
            p = rng.binomial(200, p) / 200
        ret2.append(float((2 * p * (1 - p)).mean()) / h0)
    s2 = simlib.summarize(ret2)
    exp2 = (1 - 1.0 / 200.0) ** 200
    print("  CONTROL Ne=100 t=200: retention=%.4f +/- %.4f (body=%.4f)"
          % (s2["mean"], s2["sem"], exp2))
    control = dict(design="Ne=100 t=200 [second population size]", lean=exp2,
                   truth=s2["mean"], sem=max(s2["sem"], 1e-6))
    reg = ("forward Wright-Fisher, 400 independent biallelic loci at p0 = 0.5, "
           "NO mutation and no migration -- the closed-population regime these "
           "bodies declare -- 24 replicates, retention H_t/H_0 measured per "
           "replicate")
    # THREE declarations, three sets of rows -- not one row naming all three.
    # `ledger.split_name` takes everything up to the first space or bracket as
    # the declaration, so `"closedPopulation / neutralDriftFactor / ..."` was
    # filed entirely under `closedPopulation` and the other two got no record
    # at all while their docstrings cited this battery.
    BODY_B = "body [(1 - 1/(2*Ne))^t]"
    for decl, lean_file, src in (
            ("DriftRegime.closedPopulation", "DriftRegime.lean",
             "(1 - 1 / (2 * Ne))^t * H0"),
            ("neutralDriftFactor", "PhenomeWidePortability.lean",
             "(1 - 1 / (2 * Ne))^t")):
        for k, c in cells.items():
            record(decl if k == BODY_B else "%s [%s]" % (decl, k),
                   lean_file, src if k == BODY_B else k, c,
                   regime=reg, control=control, **MODEL)

    # `heterozygosityLossDerived` is `1 - retention`, so it needs its own cells:
    # the same replicates read as a LOSS. Recording it against the retention
    # cells would have been transcribing a body the file does not contain.
    loss_control = dict(control, lean=1 - control["lean"],
                        truth=1 - control["truth"])
    loss_cells = {k: [dict(cell, lean=1 - cell["lean"],
                           truth=1 - cell["truth"]) for cell in c]
                  for k, c in cells.items()}
    for k, c in loss_cells.items():
        record("heterozygosityLossDerived" if k == BODY_B
               else "heterozygosityLossDerived [%s]" % k,
               "PopulationGeneticsFoundations.lean",
               "1 - (1 - 1 / (2 * Ne))^t" if k == BODY_B else "1 - " + k, c,
               regime=reg + "; read as the LOSS 1 - H_t/H_0",
               control=loss_control, **MODEL)


# ---------------------------------------------------------------------------
# Group C -- the many-deme limit, measured at many demes
# ---------------------------------------------------------------------------
def group_c():
    print("\n===== GROUP C  many-deme limit at d = 20  (%s)" % GUARD)
    Ne, mu, d = 1000, 1e-8, 20
    cands = {
        "body [1/(1 + 4*Ne*m + 4*Ne*mu)], the many-deme limit":
            lambda M: 1.0 / (1 + M + 4 * Ne * mu),
        "two-deme form [1/(1 + 2*4*Ne*m + 4*Ne*mu)], competing":
            lambda M: 1.0 / (1 + 2 * M + 4 * Ne * mu),
        "finite-deme form at d=20 [correction 20/19]":
            lambda M: 1.0 / (1 + M * d / (d - 1.0) + 4 * Ne * mu),
    }
    cells = {k: [] for k in cands}
    for M in (1.0, 4.0, 16.0):
        m = M / (4.0 * Ne)
        r = simlib.island_fst(Ne, m, n_demes=d, n_dip=50, seq_len=1e6, mu=mu,
                              reps=24, seed=77000 + int(M))
        s = r["hudson"]
        print("  4Nem=%5.1f  F_ST=%.5f +/- %.5f   " % (M, s["mean"], s["sem"])
              + "  ".join("%.5f" % fn(M) for fn in cands.values()))
        for k, fn in cands.items():
            cells[k].append(dict(design="d=20 4Nem=%.1f" % M, lean=fn(M),
                                 truth=s["mean"], sem=max(s["sem"], 1e-6)))
    # Control: two demes at the same 4*Ne*m, where the deme correction is 2 and
    # the many-deme body is known to fail.  If the engine reproduces the
    # two-deme value, the d = 20 agreement is not an engine artefact.
    M = 4.0
    r2 = simlib.island_fst(Ne, M / (4.0 * Ne), n_demes=2, n_dip=50,
                           seq_len=1e6, mu=mu, reps=24, seed=78000)
    exp2 = 1.0 / (1 + 2 * M)
    print("  CONTROL d=2 4Nem=4: F_ST=%.5f +/- %.5f (two-deme form=%.5f, "
          "many-deme body=%.5f)"
          % (r2["hudson"]["mean"], r2["hudson"]["sem"], exp2, 1.0 / (1 + M)))
    control = dict(design="d=2 4Nem=4 [two-deme form 1/(1+2*4Ne*m)]",
                   lean=exp2, truth=r2["hudson"]["mean"],
                   sem=max(r2["hudson"]["sem"], 1e-6))
    reg = ("msprime symmetric island model, TWENTY demes of Ne = 1000, total "
           "emigration rate m spread over the 19 other demes, mu = 1e-8, 1 Mb, "
           "Hudson F_ST between demes 0 and 1, 24 replicates.  4*Ne*m is swept "
           "sixteenfold so the prediction spans 0.5 to 0.059")
    # The first key transcribes the body in PopulationGeneticsFoundations.lean
    # (`1 / (1 + 4*Ne*m + 4*Ne*mu)`) and is recorded BARE; the rest are rivals.
    CORPUS_C = "body [1/(1 + 4*Ne*m + 4*Ne*mu)], the many-deme limit"
    for k, c in cells.items():
        record("fstMigrationMutationEquilibriumManyDemes" if k == CORPUS_C
               else "fstMigrationMutationEquilibriumManyDemes [%s]" % k,
               "PopulationGeneticsFoundations.lean", k, c, regime=reg,
               control=control, **MODEL)


# ---------------------------------------------------------------------------
# Group D -- the calibrated Brier body in its own regime
# ---------------------------------------------------------------------------
def group_d():
    print("\n===== GROUP D  calibrated Brier, observed scale  (%s)" % GUARD)
    from scipy.stats import multivariate_normal, norm
    rng = np.random.default_rng(5150)
    N = 800000
    cells_body, cells_liab, cells_sq = [], [], []
    for pi, vS, vR in [(0.50, 1.0, 1.0), (0.20, 1.0, 3.0),
                       (0.10, 2.0, 1.0), (0.35, 0.5, 2.0)]:
        r2 = vS / (vS + vR)
        var = r2 * pi * (1 - pi)
        # Beta with mean pi and variance var: the calibrated probability is a
        # random variable on the OBSERVED scale, which is the regime the body
        # is exact in.  Nothing here evaluates the body.
        k = pi * (1 - pi) / var - 1.0
        a, b = pi * k, (1 - pi) * k
        p = rng.beta(a, b, size=N)
        y = (rng.random(N) < p).astype(float)
        brier = (y - p) ** 2
        s = simlib.summarize(list(brier[:200000].reshape(20, -1).mean(axis=1)))
        body = pi * (1 - pi) * (1 - r2)
        # the liability-threshold form, which is what the falsification says
        # the body must be replaced by when vSignal/vResidual are liability
        # variances -- carried here so it can be REJECTED on the observed scale
        z = norm.ppf(pi)
        liab = pi - float(multivariate_normal(mean=[0, 0],
                          cov=[[1, r2], [r2, 1]]).cdf([z, z]))
        sq = pi * (1 - pi) * (1 - r2) ** 2
        lab = "pi=%.2f r2=%.3f" % (pi, r2)
        print("  %s  realised=%.6f +/- %.6f  body=%.6f  liability=%.6f  "
              "sq=%.6f" % (lab, s["mean"], s["sem"], body, liab, sq))
        cells_body.append(dict(design=lab, lean=body, truth=s["mean"],
                               sem=max(s["sem"], 1e-6)))
        cells_liab.append(dict(design=lab, lean=liab, truth=s["mean"],
                               sem=max(s["sem"], 1e-6)))
        cells_sq.append(dict(design=lab, lean=sq, truth=s["mean"],
                             sem=max(s["sem"], 1e-6)))
    # Control: r2 = 0, where the calibrated predictor knows only the prevalence
    # and the Brier score must be pi*(1-pi) exactly.
    pi = 0.30
    y = (rng.random(N) < pi).astype(float)
    br = (y - pi) ** 2
    sc = simlib.summarize(list(br[:200000].reshape(20, -1).mean(axis=1)))
    print("  CONTROL r2=0 pi=0.30: realised=%.6f +/- %.6f (pi*(1-pi)=%.6f)"
          % (sc["mean"], sc["sem"], pi * (1 - pi)))
    control = dict(design="r2=0 [Brier = pi*(1-pi)]", lean=pi * (1 - pi),
                   truth=sc["mean"], sem=max(sc["sem"], 1e-6))
    reg = ("calibrated probability drawn Beta(mean pi, variance r2*pi*(1-pi)) "
           "on the OBSERVED scale, outcome Bernoulli(p), realised mean squared "
           "error over 8e5 draws, sem from 20 blocks of 1e4.  This is the "
           "additive-noise regime; the liability-threshold design that "
           "falsified the body is a different regime")
    record("calibratedBrierFromVariances", "DGP.lean",
           "pi*(1-pi)*(1 - vSignal/(vSignal+vResidual))", cells_body,
           regime=reg, control=control, **MODEL)
    record("calibratedBrierFromVariances [liability form, competing]",
           "DGP.lean", "pi - Phi2(z, z; r2)", cells_liab, regime=reg,
           control=control, **MODEL)
    record("calibratedBrierFromVariances [squared factor, competing]",
           "DGP.lean", "pi*(1-pi)*(1 - r2)^2", cells_sq, regime=reg,
           control=control, **MODEL)


if __name__ == "__main__":
    # FRESHNESS: the token is a literal in this file and nowhere else, so a log
    # carrying it is evidence about WHICH source produced the numbers. It is
    # printed unconditionally only because `dump_results` now also records this
    # file's SHA inside the results, which is the signal a file copy cannot
    # flip; the token is the fallback for readers of the log alone.
    print("FRESHNESS=OK %s" % GUARD)
    which = sys.argv[1] if len(sys.argv) > 1 else "abcd"
    if "a" in which: group_a()
    if "b" in which: group_b()
    if "c" in which: group_c()
    if "d" in which: group_d()
    dump_results("battery_falsrepair_results.json",
                 battery_source=os.path.abspath(__file__))
    print("\n================ SUMMARY ================")
    for r in RESULTS:
        print("%-8s %-90s worst %s" % (r["verdict"], r["name"], r["worst"]))
