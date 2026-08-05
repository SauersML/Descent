"""Check Descent population-genetics *definitions* against simulation.

Every theorem in `Descent` is machine-checked, and there are no
`sorry`s -- so a wrong result can only enter through a definition whose name
claims a population-genetic meaning that its formula does not have.  This
harness transcribes each Lean definition literally (the Lean source is quoted in
each docstring) and compares it against a simulation of the quantity the name
refers to.

Ground truth is msprime for coalescent quantities and an exact vectorized
Wright-Fisher forward simulation for the two-locus LD quantities.

HOW TO RUN IT.  There is exactly one interpreter on this cluster that works:

    /projects/standard/hsiehph/sauer354/popgen_venv/bin/python check_defs.py all out.json
    /projects/standard/hsiehph/sauer354/popgen_venv/bin/python report.py out.json

Built with `/usr/bin/python3.12 -m venv`, then `pip install numpy msprime`
(numpy 2.5.1, msprime 1.4.2).  It lives on /projects/standard, not in a
RAM-backed directory, so it survives.  The three obvious alternatives are all
dead ends, and this note exists so the next person does not rediscover them:

    /usr/bin/python3.12                      has no numpy
    system python3                           numpy 1.19.5, but Python 3.6.8
    module load python3/3.10.9_anaconda...   numpy 1.23.5, but the install is
                                             broken: `ImportError: numpy._core
                                             .multiarray failed to import`

THE DESIGN PROPERTY THAT MATTERS.  Each check simulates THE QUANTITY THE NAME
ASSERTS, never the quantity the body computes.  A check written from the body
agrees with the body by construction and passes green no matter what the name
claims -- which is precisely how a name is able to drift away from its formula
without anything noticing.  `founderFst` is the specimen: a check comparing it
against simulated heterozygosity loss agrees with it perfectly, while the name
says F_ST and the measurable F_ST is a different number entirely.  So
`check_founder_fst` below compares it against BOTH and reports both directions.
"""
from __future__ import annotations

import json
import os
import sys
from concurrent.futures import ProcessPoolExecutor

for _v in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS",
           "NUMEXPR_NUM_THREADS", "VECLIB_MAXIMUM_THREADS"):
    os.environ[_v] = "1"

import numpy as np  # noqa: E402

MU = 1e-8
RHO = 1e-8


# --------------------------------------------------------------------------
# Lean definitions, transcribed literally
# --------------------------------------------------------------------------

def lean_coalFst(t, Ne):
    """PopulationGeneticsFoundations.lean:120  `t / (t + 2 * Ne)`"""
    return t / (t + 2 * Ne)


def lean_fstFromDrift(t, Ne):
    """PopulationGeneticsFoundations.lean:283  `1 - (1 - 1 / (2 * Ne)) ^ t`"""
    return 1 - (1 - 1 / (2 * Ne)) ** t


def lean_islandModelFst(Ne, m):
    """PopulationGeneticsFoundations.lean:636  `1 / (1 + 4 * Ne * m)`"""
    return 1 / (1 + 4 * Ne * m)


def lean_singletonProportion(N0, N1):
    """DemographicHistory.lean:289  `1 - Real.log N₀ / Real.log N₁`"""
    return 1 - np.log(N0) / np.log(N1)


def lean_admixedFst(alpha, fst_AB):
    """DemographicHistory.lean:173  `(1 - α) ^ 2 * fst_AB`"""
    return (1 - alpha) ** 2 * fst_AB


def lean_ldRetentionPerGen(r, Ne):
    """LDDecayTheory.lean:38  `(1 - r) * (1 - 1 / (2 * Ne))`"""
    return (1 - r) * (1 - 1 / (2 * Ne))


def lean_ldAfterGenerations(D0, r, Ne, t):
    """LDDecayTheory.lean:67  `D₀ * (ldRetentionPerGen r Ne) ^ t`"""
    return D0 * lean_ldRetentionPerGen(r, Ne) ** t


def lean_ldHalfLife(r, Ne):
    """LDDecayTheory.lean:906  `Real.log 2 / (-Real.log (ldRetentionPerGen r Ne))`

    WAS TRANSCRIBED AS `2 * Ne * Real.log 2`, taking one argument.  That is the
    drift-only half-life; the corpus now divides by the log of the FULL
    per-generation retention, which includes recombination, and takes `r` as
    well.  The transcription was never exercised by a check, so the arity change
    did not even raise -- it simply sat here being wrong.  That is the failure
    mode a transcription registry is meant to end; see TRANSCRIBED_FROM.
    """
    return np.log(2) / (-np.log(lean_ldRetentionPerGen(r, Ne)))


def lean_neiGstFromFrequencies(p1, p2):
    """PopulationGeneticsFoundations.lean:87
    `let p_bar := (p1 + p2) / 2; (p1 - p2)^2 / (4 * p_bar * (1 - p_bar))`"""
    pbar = (p1 + p2) / 2
    return (p1 - p2) ** 2 / (4 * pbar * (1 - pbar))


def lean_hudsonFst(p1, p2):
    """Conventions.lean:246
    `(p1 - p2)^2 / (p1 * (1 - p2) + p2 * (1 - p1))`"""
    return (p1 - p2) ** 2 / (p1 * (1 - p2) + p2 * (1 - p1))


def lean_founderFst(k, t):
    """DemographicHistory.lean:598  `1 - (1 - 1 / (2 * k)) ^ t`

    THE NAME SAYS F_ST.  This formula is the accumulated inbreeding / expected
    heterozygosity loss inside ONE population of size k after t generations.
    `check_founder_fst` simulates both quantities and reports both distances.
    """
    return 1 - (1 - 1 / (2 * k)) ** t


def lean_expectedHeterozygosity(theta):
    """PopulationGeneticsFoundations.lean:127  `theta / (1 + theta)`"""
    return theta / (1 + theta)


# Every hand transcription above, paired with the fully-qualified Lean name it
# claims to transcribe.  `verify_transcriptions.py` reads this and compares each
# one against the body the extractor pulled out of the Lean, so a transcription
# that goes stale -- or names a definition that has been renamed out of the
# corpus -- is caught mechanically instead of quietly comparing simulation
# against a formula the development no longer contains.
TRANSCRIBED_FROM = {
    "lean_coalFst": "Descent.coalFst",
    "lean_admixedFst": "Descent.admixedFst",
    "lean_ldRetentionPerGen": "Descent.ldRetentionPerGen",
    "lean_ldAfterGenerations": "Descent.ldAfterGenerations",
    "lean_ldHalfLife": "Descent.ldHalfLife",
    "lean_neiGstFromFrequencies": "Descent.neiGstFromFrequencies",
    "lean_hudsonFst": "Descent.hudsonFst",
    "lean_founderFst": "Descent.founderFst",
    "lean_expectedHeterozygosity": "Descent.expectedHeterozygosity",
}

# Transcriptions that named a definition the corpus NO LONGER CONTAINS.  They
# are recorded rather than deleted: each one is a check that silently stopped
# testing anything, and the list is the evidence for why TRANSCRIBED_FROM has to
# be verified rather than trusted.
RETIRED_TRANSCRIPTIONS = {
    "lean_fstFromDrift": "Descent.fstFromDrift -- ABSENT from the corpus",
    "lean_islandModelFst": "Descent.islandModelFst -- ABSENT from the corpus",
    "lean_singletonProportion": "Descent.singletonProportion -- ABSENT",
}

# Definitions the coordinator asked for that have NO check here yet, recorded
# explicitly so the comparison set cannot shrink silently again.
GAPS = {
    "Descent.steppingStoneFst": "min 1 (fst_neighbor * (1 + alpha*(d-1))) -- a "
        "phenomenological interpolation, not a coalescent quantity; needs a "
        "stepping-stone lattice simulation to have any ground truth at all",
    "Descent.ohtaKimuraSigmaDSq": "needs two-locus sigma_d^2 under drift-"
        "recombination equilibrium; the WF engine below tracks E[D] and E[D^2] "
        "but not the ratio E[D^2]/E[p(1-p)q(1-q)]",
    "Descent.driftLDEquilibrium": "same engine gap as ohtaKimuraSigmaDSq",
    "Descent.cumulativeDrift": "sum over a per-generation Ne vector; needs a "
        "variable-size WF run, which the current engine does not take",
}


# --------------------------------------------------------------------------
# helpers
# --------------------------------------------------------------------------

def hudson_fst(c1, c2, n1, n2):
    p1 = c1 / n1
    p2 = c2 / n2
    num = (p1 - p2) ** 2 - p1 * (1 - p1) / (n1 - 1) - p2 * (1 - p2) / (n2 - 1)
    den = p1 * (1 - p2) + p2 * (1 - p1)
    ok = den > 0
    return float(num[ok].sum() / den[ok].sum())


def fst_from_ts(ts, n_hap_per_deme):
    G = ts.genotype_matrix()
    if G.shape[0] == 0:
        return np.nan
    a = n_hap_per_deme
    c1 = G[:, :a].sum(axis=1).astype(float)
    c2 = G[:, a:2 * a].sum(axis=1).astype(float)
    return hudson_fst(c1, c2, a, a)


# --------------------------------------------------------------------------
# check 1: split Fst  ->  coalFst vs fstFromDrift
# --------------------------------------------------------------------------

def check_split_fst(args):
    import msprime
    Ne, t, seed = args
    dem = msprime.Demography()
    dem.add_population(name="A", initial_size=Ne)
    dem.add_population(name="B", initial_size=Ne)
    dem.add_population(name="ANC", initial_size=Ne)
    dem.add_population_split(time=t, derived=["A", "B"], ancestral="ANC")
    ts = msprime.sim_ancestry(samples={"A": 40, "B": 40}, demography=dem,
                              sequence_length=2e6, recombination_rate=RHO,
                              random_seed=seed)
    ts = msprime.sim_mutations(ts, rate=MU, random_seed=seed + 1)
    return dict(check="split_fst", Ne=Ne, t=t, sim=fst_from_ts(ts, 80),
                lean_coalFst=lean_coalFst(t, Ne),
                lean_fstFromDrift=lean_fstFromDrift(t, Ne))


# --------------------------------------------------------------------------
# check 2: island-model equilibrium Fst  ->  islandModelFst
# --------------------------------------------------------------------------

def check_island_fst(args):
    import msprime
    Ne, m, ndemes, seed = args
    dem = msprime.Demography.island_model([Ne] * ndemes, migration_rate=m)
    samples = {f"pop_{i}": (40 if i < 2 else 0) for i in range(ndemes)}
    ts = msprime.sim_ancestry(samples=samples, demography=dem,
                              sequence_length=2e6, recombination_rate=RHO,
                              random_seed=seed)
    ts = msprime.sim_mutations(ts, rate=MU, random_seed=seed + 1)
    return dict(check="island_fst", Ne=Ne, m=m, ndemes=ndemes, Nm=Ne * m,
                sim=fst_from_ts(ts, 80), lean=lean_islandModelFst(Ne, m))


# --------------------------------------------------------------------------
# check 3: singleton proportion under expansion  ->  singletonProportion
# --------------------------------------------------------------------------

def check_singletons(args):
    import msprime
    N0, N1, T_growth, nsamp, seed = args
    # population of present size N1 that grew exponentially from N0 over T_growth
    growth = 0.0 if N1 == N0 else np.log(N1 / N0) / T_growth
    dem = msprime.Demography()
    dem.add_population(name="P", initial_size=N1, growth_rate=growth)
    dem.add_population_parameters_change(time=T_growth, population="P",
                                         initial_size=N0, growth_rate=0)
    ts = msprime.sim_ancestry(samples={"P": nsamp}, demography=dem,
                             sequence_length=5e6, recombination_rate=RHO,
                             random_seed=seed)
    ts = msprime.sim_mutations(ts, rate=MU, random_seed=seed + 1)
    G = ts.genotype_matrix()
    ac = G.sum(axis=1)
    n_hap = 2 * nsamp
    seg = (ac > 0) & (ac < n_hap)
    singleton = (ac == 1) | (ac == n_hap - 1)
    harmonic = float(np.sum(1.0 / np.arange(1, n_hap)))
    return dict(check="singletons", N0=N0, N1=N1, nsamp=nsamp,
                sim=float(singleton[seg].sum() / seg.sum()),
                lean=lean_singletonProportion(N0, N1),
                neutral_constant_size=1.0 / harmonic)


# --------------------------------------------------------------------------
# check 4: two-locus LD decay  ->  ldRetentionPerGen / ldAfterGenerations
#
# Exact vectorized Wright-Fisher: R independent replicate populations, each
# 2N gametes over 4 haplotypes, recombination then multinomial resampling.
# --------------------------------------------------------------------------

def check_ld_decay(args):
    N, r, gens, reps, seed = args
    rng = np.random.default_rng(seed)
    # start every replicate at maximum LD: haplotypes AB and ab at 1/2 each
    x = np.zeros((reps, 4))
    x[:, 0] = 0.5   # AB
    x[:, 3] = 0.5   # ab
    D0 = 0.25
    twoN = 2 * N
    traj_D, traj_D2 = [], []
    for _ in range(gens):
        D = x[:, 0] * x[:, 3] - x[:, 1] * x[:, 2]
        traj_D.append(D.mean())
        traj_D2.append((D ** 2).mean())
        # recombination acts on the gamete pool
        y = x.copy()
        y[:, 0] -= r * D
        y[:, 3] -= r * D
        y[:, 1] += r * D
        y[:, 2] += r * D
        y = np.clip(y, 0, None)
        y /= y.sum(axis=1, keepdims=True)
        # drift: multinomial resampling of 2N gametes
        counts = np.empty_like(y)
        for i in range(reps):
            counts[i] = rng.multinomial(twoN, y[i])
        x = counts / twoN
    out = []
    for t in (1, 5, 10, 20, 50, 100):
        if t >= gens:
            continue
        out.append(dict(
            check="ld_decay", N=N, r=r, t=t,
            sim_ED_ratio=float(traj_D[t] / D0),
            sim_ED2_ratio=float(traj_D2[t] / D0 ** 2),
            lean_ldAfterGenerations_ratio=float(
                lean_ldAfterGenerations(D0, r, N, t) / D0),
            pure_recombination=float((1 - r) ** t),
        ))
    return out


# --------------------------------------------------------------------------
# check 5: founderFst  ->  simulate BOTH quantities the name could mean
# --------------------------------------------------------------------------

def check_founder_fst(args):
    """`founderFst k t` against the two quantities its name and body suggest.

    WRITTEN FROM THE NAME.  A founder population of k diploids is drawn from a
    large source population and drifts for t generations.  Two things can be
    measured, and the corpus formula is compared against BOTH:

      truth_hetloss : 1 - H_t / H_0 inside the founded population.  This is
                      what the BODY computes.
      truth_fst     : Hudson F_ST between the founded population and the
                      unbottlenecked source.  This is what the NAME says.

    Reporting only the first is what let the name drift: it agrees to three
    decimals and the check goes green while the name is wrong.
    """
    k, t, nloci, seed = args
    rng = np.random.default_rng(seed)
    p0 = rng.uniform(0.05, 0.95, size=nloci)      # source allele frequencies
    twok = 2 * k
    p = p0.copy()
    for _ in range(t):
        p = rng.binomial(twok, p) / twok          # WF drift in the founded pop
    H0 = 2 * p0 * (1 - p0)
    Ht = 2 * p * (1 - p)
    truth_hetloss = float(1 - Ht.mean() / H0.mean())
    # Hudson F_ST between founded (p) and source (p0), the ratio-of-averages
    # estimator, which is the one the corpus's own hudsonFst matches.
    num = (p - p0) ** 2
    den = p * (1 - p0) + p0 * (1 - p)
    ok = den > 0
    truth_fst = float(num[ok].sum() / den[ok].sum())
    lean = float(lean_founderFst(k, t))
    return dict(check="founder_fst", k=k, t=t,
                lean_founderFst=lean,
                truth_hetloss=truth_hetloss,
                truth_fst=truth_fst,
                err_vs_hetloss=lean - truth_hetloss,
                err_vs_fst=lean - truth_fst)


# --------------------------------------------------------------------------
# check 6: hudsonFst vs neiGst  ->  the conversion identity, as a regression
# --------------------------------------------------------------------------

def check_hudson_vs_neigst(args):
    """`hudsonFst = 2*G/(1+G)` where `G = neiGstFromFrequencies`.

    This is an exact algebraic identity, not an approximation:
        4*p_bar*(1-p_bar) + (p1-p2)^2 = 2*(p1*(1-p2) + p2*(1-p1)),
    so 2G/(1+G) collapses to Hudson's ratio term by term.

    It is wired in as a REGRESSION.  These two definitions have been renamed
    across each other before -- `hudsonFst` once carried Nei's G_ST, and the
    corpus recorded the correction in a docstring rather than in a check.  A
    docstring cannot fail.  This can: if a future rename swaps them back, the
    identity breaks and this row goes red.
    """
    p1, p2, seed = args
    G = float(lean_neiGstFromFrequencies(p1, p2))
    H = float(lean_hudsonFst(p1, p2))
    pred = 2 * G / (1 + G)
    return dict(check="hudson_vs_neigst", p1=p1, p2=p2,
                neiGst=G, hudsonFst=H, from_identity=pred,
                abs_err=abs(H - pred),
                rel_err=abs(H - pred) / max(abs(H), 1e-300))


# --------------------------------------------------------------------------

def main():
    which = sys.argv[1] if len(sys.argv) > 1 else "all"
    jobs = []

    if which in ("all", "split"):
        for Ne in (1000, 5000):
            for t in (50, 100, 250, 500, 1000, 2000, 4000):
                for rep in range(2):
                    jobs.append((check_split_fst, (Ne, t, 7 + 13 * rep + t)))

    if which in ("all", "island"):
        for ndemes in (2, 5, 20):
            for Nm in (0.25, 1.0, 4.0):
                Ne = 1000
                for rep in range(2):
                    jobs.append((check_island_fst,
                                 (Ne, Nm / Ne, ndemes, 101 + 17 * rep + int(Nm * 10))))

    if which in ("all", "singletons"):
        for (N0, N1) in ((1000, 1000), (1000, 10000), (1000, 100000), (1000, 1000000)):
            for nsamp in (50, 200):
                jobs.append((check_singletons, (N0, N1, 500, nsamp, 55 + nsamp)))

    if which in ("all", "ld"):
        for N in (500, 2000):
            for r in (0.0, 0.001, 0.01):
                jobs.append((check_ld_decay, (N, r, 101, 4000, 900 + N + int(r * 1e4))))

    if which in ("all", "founder"):
        for k in (20, 50, 200, 1000):
            for t in (5, 20, 50, 100):
                jobs.append((check_founder_fst, (k, t, 20000, 4242 + k + t)))

    if which in ("all", "identity"):
        for p1 in (0.05, 0.2, 0.5, 0.8):
            for p2 in (0.1, 0.3, 0.6, 0.9):
                if p1 != p2:
                    jobs.append((check_hudson_vs_neigst, (p1, p2, 0)))

    with ProcessPoolExecutor(max_workers=int(os.environ.get("NPROC", "24"))) as ex:
        futs = [ex.submit(fn, a) for fn, a in jobs]
        out = []
        for f in futs:
            r = f.result()
            out.extend(r) if isinstance(r, list) else out.append(r)

    with open(sys.argv[2] if len(sys.argv) > 2 else "defs.json", "w") as fh:
        json.dump(out, fh)
    print(f"wrote {len(out)} records")


if __name__ == "__main__":
    main()
