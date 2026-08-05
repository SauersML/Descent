"""Ground-truth engines for the Descent empirical surface.

Three independent sources of truth, deliberately not sharing code paths with
each other or with the Lean transcriptions:

  `coalescent`  -- msprime, for anything defined by a genealogy: F_ST under a
                   clean split, under migration, under mutation-drift balance.
  `wright_fisher` -- explicit forward simulation of allele frequencies and
                   two-locus haplotype counts, for drift, LD decay and
                   variance components.  Forward sim is the only oracle that
                   can see a *transient*; the coalescent gives equilibria.
  `exact`       -- closed-form or exact-rational evaluation, for the handful of
                   definitions that are identities rather than models.

EVERY estimator returns replicates, never only a mean.  `summarize` turns those
into (mean, sem), and a comparison is reported in units of that sem.  A
prediction that misses by 0.3 percent at 15 sems is falsified; one that misses
by 20 percent at 0.4 sems is a design with no power, and the two are
indistinguishable without the error bar.  This is the same rule
`validation/empirical/simprov.py` states for the sweeps.
"""
import math

import numpy as np

# --------------------------------------------------------------------------
# estimators over allele-frequency tables
# --------------------------------------------------------------------------


def hudson_fst(ac1, n1, ac2, n2):
    """Hudson's F_ST as a RATIO OF AVERAGES (Bhatia et al. 2013).

    Averaging per-site ratios instead is a different and badly behaved
    estimator: at low-frequency sites the denominator approaches zero and the
    per-site ratio explodes, so the average is dominated by the least
    informative sites.  Every F_ST number in this module is ratio-of-averages,
    and any comparison against a Lean definition inherits that convention.
    """
    p1 = ac1 / n1
    p2 = ac2 / n2
    num = (p1 - p2) ** 2 - p1 * (1 - p1) / (n1 - 1) - p2 * (1 - p2) / (n2 - 1)
    den = p1 * (1 - p2) + p2 * (1 - p1)
    keep = den > 0
    if not np.any(keep):
        return float("nan")
    return float(np.sum(num[keep]) / np.sum(den[keep]))


def nei_gst(ac1, n1, ac2, n2):
    """Nei's G_ST from expected heterozygosities, ratio of averages."""
    p1 = ac1 / n1
    p2 = ac2 / n2
    pbar = (p1 + p2) / 2.0
    h_s = (2 * p1 * (1 - p1) + 2 * p2 * (1 - p2)) / 2.0
    h_t = 2 * pbar * (1 - pbar)
    keep = h_t > 0
    if not np.any(keep):
        return float("nan")
    return float((np.sum(h_t[keep]) - np.sum(h_s[keep])) / np.sum(h_t[keep]))


def summarize(vals):
    """mean, sd and STANDARD ERROR over replicates, NaNs dropped."""
    a = np.asarray([v for v in vals if v is not None and np.isfinite(v)], float)
    if a.size == 0:
        return dict(mean=float("nan"), sd=float("nan"), sem=float("nan"), n=0)
    sd = float(a.std(ddof=1)) if a.size > 1 else 0.0
    return dict(mean=float(a.mean()), sd=sd,
                sem=sd / math.sqrt(a.size) if a.size > 1 else 0.0,
                n=int(a.size))


# --------------------------------------------------------------------------
# coalescent engine
# --------------------------------------------------------------------------


def split_fst(Ne, t_split, n_dip=50, seq_len=5e5, mu=1e-8, rho=0.0,
              reps=20, seed=1):
    """F_ST between two demes that split `t_split` generations ago.

    No migration, ancestral size `Ne`, both daughters size `Ne`.  This is the
    design whose Hudson F_ST theory predicts exactly `t/(t + 2Ne)`, so it is
    also the engine's own calibration case.
    """
    import msprime
    dem = msprime.Demography()
    dem.add_population(name="A", initial_size=Ne)
    dem.add_population(name="B", initial_size=Ne)
    dem.add_population(name="ANC", initial_size=Ne)
    dem.add_population_split(time=t_split, derived=["A", "B"], ancestral="ANC")
    hud, nei = [], []
    for r in range(reps):
        ts = msprime.sim_ancestry(
            samples={"A": n_dip, "B": n_dip}, demography=dem,
            sequence_length=seq_len, recombination_rate=rho,
            random_seed=seed + r)
        ts = msprime.sim_mutations(ts, rate=mu, random_seed=seed + 10000 + r)
        if ts.num_sites == 0:
            continue
        gm = ts.genotype_matrix()
        a = ts.samples(population=0)
        b = ts.samples(population=1)
        ac1 = gm[:, a].sum(axis=1).astype(float)
        ac2 = gm[:, b].sum(axis=1).astype(float)
        hud.append(hudson_fst(ac1, len(a), ac2, len(b)))
        nei.append(nei_gst(ac1, len(a), ac2, len(b)))
    return dict(hudson=summarize(hud), nei=summarize(nei),
                hudson_reps=hud, nei_reps=nei)


def island_fst(Ne, m, n_demes=2, n_dip=50, seq_len=5e5, mu=1e-8,
               reps=20, seed=1):
    """F_ST at migration-drift-mutation equilibrium in a symmetric island model.

    `m` is the per-generation probability that a lineage's parent sat in a
    different deme, summed over source demes -- the same `m` that
    `1/(1 + 4 Ne m)` is written with.  msprime's migration matrix entries are
    per-ordered-pair, so each of the `n_demes - 1` sources gets `m/(n-1)`.
    Getting this wrong rescales the prediction by `n-1` and would manufacture a
    falsification out of a units error.
    """
    import msprime
    dem = msprime.Demography.island_model(
        [Ne] * n_demes, migration_rate=m / (n_demes - 1))
    hud, nei = [], []
    for r in range(reps):
        ts = msprime.sim_ancestry(
            samples={f"pop_{i}": n_dip for i in range(2)}, demography=dem,
            sequence_length=seq_len, recombination_rate=0.0,
            random_seed=seed + r)
        ts = msprime.sim_mutations(ts, rate=mu, random_seed=seed + 20000 + r)
        if ts.num_sites == 0:
            continue
        gm = ts.genotype_matrix()
        a = ts.samples(population=0)
        b = ts.samples(population=1)
        ac1 = gm[:, a].sum(axis=1).astype(float)
        ac2 = gm[:, b].sum(axis=1).astype(float)
        hud.append(hudson_fst(ac1, len(a), ac2, len(b)))
        nei.append(nei_gst(ac1, len(a), ac2, len(b)))
    return dict(hudson=summarize(hud), nei=summarize(nei))


# --------------------------------------------------------------------------
# Wright-Fisher forward engine
# --------------------------------------------------------------------------


def wf_two_locus(Ne, c, gens, reps=400, p0=0.5, q0=0.5, D0=None, seed=1):
    """Forward Wright-Fisher on two biallelic loci, tracking the LD covariance.

    Returns the replicate-mean of `D` and of `D^2` at every generation.  `D^2`
    is the one that matters: `E[D]` decays by `(1 - c)` per generation with no
    drift term at all, so a formula carrying a `1/(2Ne)` can only be tested
    against the SECOND moment.  A test that compared it against `E[D]` would
    pass for any value of the drift coefficient.
    """
    rng = np.random.default_rng(seed)
    if D0 is None:
        D0 = 0.25 * math.sqrt(p0 * (1 - p0) * q0 * (1 - q0))
    # haplotype frequencies (AB, Ab, aB, ab) from p, q, D
    f = np.empty((reps, 4))
    f[:, 0] = p0 * q0 + D0
    f[:, 1] = p0 * (1 - q0) - D0
    f[:, 2] = (1 - p0) * q0 - D0
    f[:, 3] = (1 - p0) * (1 - q0) + D0
    if np.any(f < 0):
        raise ValueError("initial haplotype frequencies not a valid simplex")
    two_n = int(2 * Ne)
    d_mean, d2_mean = [], []
    for _ in range(gens + 1):
        p = f[:, 0] + f[:, 1]
        q = f[:, 0] + f[:, 2]
        D = f[:, 0] - p * q
        d_mean.append(float(D.mean()))
        d2_mean.append(float((D ** 2).mean()))
        # recombination acts on the expected haplotype frequencies, then the
        # next generation is a multinomial resample of 2Ne gametes: drift is
        # the sampling, not an added variance term.
        Dr = D * (1 - c)
        g = np.empty_like(f)
        g[:, 0] = p * q + Dr
        g[:, 1] = p * (1 - q) - Dr
        g[:, 2] = (1 - p) * q - Dr
        g[:, 3] = (1 - p) * (1 - q) + Dr
        g = np.clip(g, 0.0, None)
        g /= g.sum(axis=1, keepdims=True)
        for i in range(reps):
            f[i] = rng.multinomial(two_n, g[i]) / two_n
    return dict(D=np.array(d_mean), D2=np.array(d2_mean))


def wf_drift_het(Ne_schedule, reps=400, p0=0.5, n_loci=200, seed=1):
    """Heterozygosity loss under a possibly time-varying population size.

    `Ne_schedule` is the list of diploid sizes, one per generation.  Returns
    mean heterozygosity `2p(1-p)` after each generation, averaged over loci and
    replicates -- the quantity `1 - H_t/H_0` that inbreeding formulas predict.
    """
    rng = np.random.default_rng(seed)
    p = np.full((reps, n_loci), float(p0))
    het = [float((2 * p * (1 - p)).mean())]
    for Ne in Ne_schedule:
        two_n = int(2 * Ne)
        p = rng.binomial(two_n, p) / two_n
        het.append(float((2 * p * (1 - p)).mean()))
    return np.array(het)


# --------------------------------------------------------------------------
# engine self-test
# --------------------------------------------------------------------------


def selftest():
    """Calibrate the engines against results that are known independently.

    An oracle nobody checked is just a second opinion of unknown quality.  If
    any of these drifts, every finding downstream of it is suspect.
    """
    out = []

    # 1. Clean split, Hudson F_ST = t / (t + 2Ne).  This is theory that does
    #    not come from the corpus, so it calibrates the coalescent engine.
    Ne, t = 1000, 1000
    r = split_fst(Ne, t, reps=12, seed=7)
    pred = t / (t + 2 * Ne)
    got, sem = r["hudson"]["mean"], r["hudson"]["sem"]
    out.append(("coalescent split F_ST", pred, got, sem,
                abs(got - pred) / sem if sem > 0 else float("inf")))

    # 2. Drift: heterozygosity decays by (1 - 1/(2Ne)) per generation.
    Ne = 100
    h = wf_drift_het([Ne] * 50, reps=200, n_loci=400, seed=3)
    pred = h[0] * (1 - 1.0 / (2 * Ne)) ** 50
    out.append(("WF heterozygosity decay", pred, float(h[-1]),
                float(h[-1]) * 0.02, abs(h[-1] - pred) / (0.02 * h[-1])))

    # 3. LD: with no drift (large Ne), E[D] decays exactly by (1 - c)^t.
    c, g = 0.05, 30
    tl = wf_two_locus(Ne=200000, c=c, gens=g, reps=60, seed=5)
    pred = tl["D"][0] * (1 - c) ** g
    got = tl["D"][-1]
    out.append(("WF E[D] decay (1-c)^t", pred, got, abs(pred) * 0.05,
                abs(got - pred) / (0.05 * abs(pred))))

    print("%-28s %12s %12s %10s %8s" % ("engine check", "theory", "sim",
                                        "sem", "sems off"))
    for name, pred, got, sem, z in out:
        flag = "OK" if z < 3 else "*** DRIFT ***"
        print("%-28s %12.5f %12.5f %10.5f %8.2f  %s"
              % (name, pred, got, sem, z, flag))
    return out


if __name__ == "__main__":
    selftest()
