"""Popgen/selection battery: every cell carries a competitor and a declared
argument_source.  Guard string PGSEL_V1 exists only in this source.

Cells
  A  driftLDCreationRate            msprime DTWF pairwise coalescence (cross-engine)
  B  bottleneckExcessLD             numpy 2-locus IBD Wright-Fisher with a bottleneck
  C  freeRecombinationStep          deterministic 2-locus gamete recursion + finite-N WF
  D  selectionPortabilityTimescale  deterministic viability-selection recursion
"""
import json, math, sys
import numpy as np

GUARD = "PGSEL_V1"
rows = []


def rec(**kw):
    kw["guard"] = GUARD
    rows.append(kw)


# --------------------------------------------------------------- cell A
# Corpus: driftLDCreationRate Ne = 1/(2 Ne)  (== driftRatePerGen == alleleFreqDivergenceRate).
# Reading under test: a per-generation DRIFT rate, i.e. the per-generation
# probability that two distinct gene copies coalesce, whose reciprocal is the
# mean pairwise coalescence time.
# argument_source: msprime's DiscreteTimeWrightFisher model.  Independent code
# path, independent API, and NOT the recursion the corpus body was derived from.
def cell_A():
    import msprime
    out = []
    for N in (10, 25, 60):
        ts_iter = msprime.sim_ancestry(
            samples=1, ploidy=2, population_size=N,
            model="dtwf", sequence_length=1, discrete_genome=True,
            random_seed=20260804, num_replicates=40000)
        t = np.fromiter((ts.first().time(ts.first().root) for ts in ts_iter),
                        dtype=float, count=40000)
        mean, sem = t.mean(), t.std(ddof=1) / math.sqrt(len(t))
        # rate estimated two ways; the geometric-tail slope is convention-free.
        rate_hat = 1.0 / mean
        rate_sem = sem / mean**2
        cands = {
            "corpus  1/(2Ne)": 1.0 / (2 * N),
            "COMP    1/(4Ne)": 1.0 / (4 * N),
            "COMP    1/Ne": 1.0 / N,
            "PLANTED 1.4/(2Ne)": 1.4 / (2 * N),
        }
        out.append(dict(N=N, mean_tmrca=mean, sem=sem, rate_hat=rate_hat,
                        rate_sem=rate_sem,
                        sems={k: (v - rate_hat) / rate_sem for k, v in cands.items()},
                        pred=cands))
    rec(cell="A", target="driftLDCreationRate",
        argument_source="msprime DiscreteTimeWrightFisher pairwise coalescence time",
        detail=out)


# --------------------------------------------------------------- cell B
# Corpus: bottleneckExcessLD Ne_b Ne_s c t_b
#          = driftLDTrajectory Ne_b c (driftLDEquilibrium Ne_s c) t_b
#            - driftLDEquilibrium Ne_s c
# Simulated: 2N labelled gametes; each offspring gamete picks a parent
# INDIVIDUAL, then with prob c takes its two loci from the individual's two
# gametes, else both from one.  Q = P(two distinct gametes carry the same
# founder label at BOTH loci).
# argument_source: a labelled-ancestry individual-based simulation.  The corpus
# recursion is a theorem about this model, so agreement on the CLEAN cells
# confirms the algebra; the discrimination that carries information is the
# rejection of the deleted predecessor formula, which is a DIFFERENT function of
# the same model and is rejected by the same cells.
def q_stat(lab):
    n = len(lab)
    _, cnt = np.unique(lab, return_counts=True)
    return (cnt * (cnt - 1)).sum() / (n * (n - 1))


def wf_two_locus(N, c, gens, lab, rng, counter):
    """Joint two-locus haplotype identity.  A gamete carries one id for the
    INTACT two-locus haplotype; a recombinant offspring gets a brand-new id
    because its two loci no longer descend together.  Q = P(two distinct
    gametes share an id).  Without the fresh id on recombination the ids fix
    and Q goes to 1 -- the identity-by-descent-with-no-reset trap."""
    twoN = 2 * N
    for _ in range(gens):
        par_ind = rng.integers(0, N, size=twoN)
        which = rng.integers(0, 2, size=twoN)
        src = 2 * par_ind + which
        new = lab[src].copy()
        recomb = rng.random(twoN) < c
        k = int(recomb.sum())
        if k:
            new[recomb] = counter[0] + np.arange(k)
            counter[0] += k
        lab = new
    return lab


def drift_ld_step(Ne, c, Q):
    return (1 - c) ** 2 * (1 / (2 * Ne) + (1 - 1 / (2 * Ne)) * Q)


def drift_ld_eq(Ne, c):
    return (1 - c) ** 2 * (1 / (2 * Ne)) / (1 - (1 - c) ** 2 * (1 - 1 / (2 * Ne)))


def cell_B():
    rng = np.random.default_rng(4041)
    out = []
    for (Ns, Nb, c, tb) in ((50, 10, 0.02, 8), (50, 5, 0.05, 5), (80, 20, 0.01, 12)):
        reps = 800
        burn = 600
        acc, pres = [], []
        counter = [10 ** 6]
        for r in range(reps):
            lab = np.arange(2 * Ns)
            counter[0] = 10 ** 6
            lab = wf_two_locus(Ns, c, burn, lab, rng, counter)
            q_pre = q_stat(lab)
            lab = wf_two_locus(Nb, c, tb, lab[:2 * Nb], rng, counter)
            pres.append(q_pre)
            acc.append(q_stat(lab) - q_pre)
        acc = np.array(acc); pres = np.array(pres)
        m, s = acc.mean(), acc.std(ddof=1) / math.sqrt(reps)
        Qs = drift_ld_eq(Ns, c)
        Q = Qs
        for _ in range(tb):
            Q = drift_ld_step(Nb, c, Q)
        corpus = Q - Qs
        pred_old = (1 - (1 - 1 / (2 * Nb)) ** tb) - (1 - (1 - 1 / (2 * Ns)) ** tb)
        Q2 = Qs
        for _ in range(tb):
            Q2 = (1 / (2 * Nb) + (1 - 1 / (2 * Nb)) * Q2)   # no (1-c)^2 factor
        cands = {"corpus": corpus, "COMP deleted-predecessor": pred_old,
                 "COMP no-recombination-factor": Q2 - Qs,
                 "PLANTED 1.4x corpus": 1.4 * corpus}
        pm, ps = pres.mean(), pres.std(ddof=1) / math.sqrt(reps)
        out.append(dict(Ns=Ns, Nb=Nb, c=c, tb=tb, measured=m, sem=s,
                        pred=cands, sems={k: (v - m) / s for k, v in cands.items()},
                        positive_control_preBottleneckQ=dict(
                            measured=pm, sem=ps, driftLDEquilibrium=Qs,
                            sems=(Qs - pm) / ps)))
    rec(cell="B", target="bottleneckExcessLD",
        argument_source="labelled-ancestry individual-based two-locus WF; competitor "
                        "discrimination against the deleted predecessor formula",
        detail=out)


# --------------------------------------------------------------- cell C
# Corpus: freeRecombinationStep replaces the joint genotype law by the PRODUCT of
# the per-locus marginals in ONE generation.  Two-locus gamete recursion says
# D' = (1-r) D, so with free recombination r = 1/2 one generation leaves D/2.
# argument_source: the standard deterministic two-locus gamete recursion under
# random mating -- a different derivation from the corpus's product-law fiat --
# plus a finite-N WF check that the deterministic answer is not an artefact.
def cell_C():
    out = []
    for D0 in (0.10, 0.20, -0.15):
        pA, pB = 0.5, 0.5
        h = np.array([pA * pB + D0, pA * (1 - pB) - D0,
                      (1 - pA) * pB - D0, (1 - pA) * (1 - pB) + D0])
        assert (h > 0).all()
        for r in (0.5, 0.25):
            D = h[0] * h[3] - h[1] * h[2]
            Dn = (1 - r) * D
            out.append(dict(D0=D0, r=r, D_after_one_gen=Dn,
                            corpus_claim_D_after_one_gen=0.0,
                            ratio_to_D0=Dn / D0))
    # finite-N check: does the product law hold after ONE generation at r=1/2?
    rng = np.random.default_rng(77)
    N, reps = 4000, 400
    D0 = 0.20
    p = np.array([0.25 + D0, 0.25 - D0, 0.25 - D0, 0.25 + D0])
    Ds = []
    for _ in range(reps):
        g = rng.multinomial(2 * N, p) / (2 * N)
        # one generation of random mating with recombination fraction r=1/2
        D = g[0] * g[3] - g[1] * g[2]
        pa = g[0] + g[1]
        pb = g[0] + g[2]
        newp = np.array([pa * pb, pa * (1 - pb), (1 - pa) * pb, (1 - pa) * (1 - pb)])
        newp = newp + 0.5 * D * np.array([1, -1, -1, 1]) * 1.0  # D' = (1-r)D = D/2
        g2 = rng.multinomial(2 * N, newp / newp.sum()) / (2 * N)
        Ds.append(g2[0] * g2[3] - g2[1] * g2[2])
    Ds = np.array(Ds)
    rec(cell="C", target="freeRecombinationStep",
        argument_source="deterministic two-locus gamete recursion D' = (1-r) D, "
                        "independent of the corpus's product-law definition",
        deterministic=out,
        finite_N=dict(N=N, reps=reps, D0=D0, mean_D_after_one_gen=Ds.mean(),
                      sem=Ds.std(ddof=1) / math.sqrt(reps),
                      corpus_claim=0.0, expected_half=0.5 * D0))


# --------------------------------------------------------------- cell D
# Corpus: selectionPortabilityTimescale s = 1/(2 s), documented as "the
# characteristic timescale for portability decay is 1/(2s) generations".
# Measured: the e-folding time of the deterministic viability-selection
# trajectory for a rare allele, p' = p(1+s)/(1+s p).
# argument_source: the deterministic selection recursion; no free parameter.
def cell_D():
    out = []
    for s in (0.001, 0.005, 0.02):
        p = 1e-6
        t = 0
        while p < 1e-6 * math.e:
            p = p * (1 + s) / (1 + s * p)
            t += 1
        # refine with the continuous solution
        efold = math.log(math.e) / math.log(1 + s)
        cands = {"corpus 1/(2s)": 1 / (2 * s), "COMP 1/s": 1 / s,
                 "COMP 2/s": 2 / s, "PLANTED 1.4/(2s)": 1.4 / (2 * s)}
        out.append(dict(s=s, efold_gens_measured=efold, efold_gens_integer=t,
                        pred=cands,
                        ratio={k: v / efold for k, v in cands.items()}))
    rec(cell="D", target="selectionPortabilityTimescale",
        argument_source="deterministic viability-selection recursion e-folding time",
        detail=out)


if __name__ == "__main__":
    which = sys.argv[1] if len(sys.argv) > 1 else "ABCD"
    if "A" in which: cell_A()
    if "B" in which: cell_B()
    if "C" in which: cell_C()
    if "D" in which: cell_D()
    print("FRESHNESS=OK", GUARD)
    print(json.dumps(rows, indent=1, default=float))
