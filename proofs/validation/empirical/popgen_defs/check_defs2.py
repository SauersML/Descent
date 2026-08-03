"""Round 2 of the Calibrator definition checks.

Fixes two flawed round-1 designs and adds three definitions:

  * island model -- round 1 set msprime's *pairwise* migration rate, so total
    immigration scaled with deme count and the deme-count trend was an artifact
    of the harness.  Here the total immigration rate per deme is held fixed.
  * split Fst -- round 1 used site statistics (2 replicates, one region), which
    is dominated by genealogical noise.  Here we use tskit branch-mode
    divergence, which is the expectation over mutations given the genealogy.
  * assortative mating equilibrium variance (forward Wright-Fisher).
  * admixedFst, expectedSegmentLength (msprime admixture pulse).
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


def lean_admixedFst(alpha, fst_AB):
    """DemographicHistory.lean:173  `(1 - α) ^ 2 * fst_AB`"""
    return (1 - alpha) ** 2 * fst_AB


def lean_expectedSegmentLength(g, r_total):
    """HaplotypeTheory.lean:505  `1 / (g * r_total)`"""
    return 1 / (g * r_total)


def lean_amEquilibriumVariance(V_A, r, h2):
    """AssortativeMatingPGS.lean:99  `V_A / (1 - r * h2)`"""
    return V_A / (1 - r * h2)


# --------------------------------------------------------------------------
# branch-mode Hudson Fst: 1 - mean(pi_within) / d_xy
# --------------------------------------------------------------------------

def branch_fst(ts, ss):
    dxy = ts.divergence(sample_sets=ss, indexes=[(0, 1)], mode="branch")[0]
    pi = ts.diversity(sample_sets=ss, mode="branch")
    return float(1 - (pi[0] + pi[1]) / 2 / dxy)


def check_split_fst(args):
    import msprime
    Ne, t, seed = args
    dem = msprime.Demography()
    dem.add_population(name="A", initial_size=Ne)
    dem.add_population(name="B", initial_size=Ne)
    dem.add_population(name="ANC", initial_size=Ne)
    dem.add_population_split(time=t, derived=["A", "B"], ancestral="ANC")
    ts = msprime.sim_ancestry(samples={"A": 30, "B": 30}, demography=dem,
                              sequence_length=2e7, recombination_rate=RHO,
                              random_seed=seed)
    ss = [list(range(60)), list(range(60, 120))]
    return dict(check="split_fst", Ne=Ne, t=t, sim=branch_fst(ts, ss),
                lean_coalFst=lean_coalFst(t, Ne),
                lean_fstFromDrift=lean_fstFromDrift(t, Ne))


def check_island_fst(args):
    """Total immigration rate per deme is held at m_total, independent of d."""
    import msprime
    Ne, m_total, ndemes, seed = args
    pairwise = m_total / (ndemes - 1)
    dem = msprime.Demography.island_model([Ne] * ndemes, migration_rate=pairwise)
    samples = {f"pop_{i}": (30 if i < 2 else 0) for i in range(ndemes)}
    ts = msprime.sim_ancestry(samples=samples, demography=dem,
                              sequence_length=2e7, recombination_rate=RHO,
                              random_seed=seed)
    ss = [list(range(60)), list(range(60, 120))]
    d = ndemes
    return dict(check="island_fst", Ne=Ne, m_total=m_total, ndemes=d,
                Nm=Ne * m_total, sim=branch_fst(ts, ss),
                lean=lean_islandModelFst(Ne, m_total),
                finite_deme_theory=1 / (1 + 4 * Ne * m_total * (d / (d - 1)) ** 2))


def check_admixture(args):
    """Admixture pulse: alpha from A, 1-alpha from B, g generations ago."""
    import msprime
    Ne, split_t, alpha, g, seed = args
    dem = msprime.Demography()
    dem.add_population(name="A", initial_size=Ne)
    dem.add_population(name="B", initial_size=Ne)
    dem.add_population(name="ADM", initial_size=Ne)
    dem.add_population(name="ANC", initial_size=Ne)
    dem.add_admixture(time=g, derived="ADM", ancestral=["A", "B"],
                      proportions=[alpha, 1 - alpha])
    dem.add_population_split(time=split_t, derived=["A", "B"], ancestral="ANC")
    ts = msprime.sim_ancestry(samples={"A": 30, "B": 30, "ADM": 30},
                              demography=dem, sequence_length=2e7,
                              recombination_rate=RHO, random_seed=seed)
    A = list(range(60))
    B = list(range(60, 120))
    ADM = list(range(120, 180))
    return dict(check="admixture", Ne=Ne, split_t=split_t, alpha=alpha, g=g,
                fst_AB=branch_fst(ts, [A, B]),
                fst_ADM_A=branch_fst(ts, [ADM, A]),
                lean_admixedFst_vs_A=lean_admixedFst(alpha, branch_fst(ts, [A, B])))


def check_assortative_mating(args):
    """Forward WF with primary phenotypic assortment; measure equilibrium V_A."""
    N, L, r_target, h2, gens, seed = args
    rng = np.random.default_rng(seed)
    # unlinked biallelic loci at frequency 1/2, unit effect sizes
    g = rng.binomial(2, 0.5, size=(2 * N, L)).astype(np.float64)
    A0 = g.sum(axis=1)
    V_A0 = float(A0.var())
    V_E = V_A0 * (1 - h2) / h2

    traj = []
    realized_r = []
    for _ in range(gens):
        A = g.sum(axis=1)
        P = A + rng.normal(0, np.sqrt(V_E), size=g.shape[0])
        males = np.arange(0, N)
        females = np.arange(N, 2 * N)
        # pair by rank under a Gaussian copula so that corr(P_m, P_f) ~= r
        z = rng.multivariate_normal([0, 0], [[1, r_target], [r_target, 1]], size=N)
        om = males[np.argsort(P[males])][np.argsort(np.argsort(z[:, 0]))]
        of = females[np.argsort(P[females])][np.argsort(np.argsort(z[:, 1]))]
        realized_r.append(float(np.corrcoef(P[om], P[of])[0, 1]))
        traj.append(float(A.var()))
        # each parent transmits one allele per locus (free recombination)
        pick = np.repeat(np.arange(N), 2)  # two offspring per couple
        dad, mom = om[pick], of[pick]
        child = (rng.random((2 * N, L)) < g[dad] / 2).astype(np.float64)
        child += (rng.random((2 * N, L)) < g[mom] / 2)
        g = child

    V_eq = float(np.mean(traj[-5:]))
    r_hat = float(np.mean(realized_r[-5:]))
    return dict(check="assortative_mating", N=N, L=L, r_target=r_target,
                r_realized=r_hat, h2=h2, V_A0=V_A0, V_eq=V_eq,
                ratio_obs=V_eq / V_A0,
                lean_ratio=lean_amEquilibriumVariance(1.0, r_hat, h2),
                traj=traj[::5])


def main():
    which = sys.argv[1] if len(sys.argv) > 1 else "all"
    jobs = []

    if which in ("all", "split"):
        for Ne in (1000, 5000):
            for t in (100, 250, 500, 1000, 2000, 4000):
                jobs.append((check_split_fst, (Ne, t, 7 + t)))

    if which in ("all", "island"):
        for ndemes in (2, 5, 20, 50):
            for Nm in (0.25, 1.0, 4.0):
                jobs.append((check_island_fst, (1000, Nm / 1000, ndemes,
                                                101 + ndemes + int(Nm * 10))))

    if which in ("all", "admix"):
        for alpha in (0.2, 0.5, 0.8):
            for g in (10, 100):
                jobs.append((check_admixture, (1000, 4000, alpha, g,
                                               303 + int(alpha * 10) + g)))

    if which in ("all", "am"):
        for r in (0.1, 0.2, 0.4):
            for h2 in (0.3, 0.6):
                jobs.append((check_assortative_mating,
                             (3000, 300, r, h2, 40, 11 + int(r * 100) + int(h2 * 10))))

    with ProcessPoolExecutor(max_workers=int(os.environ.get("NPROC", "24"))) as ex:
        futs = [ex.submit(fn, a) for fn, a in jobs]
        out = [f.result() for f in futs]

    with open(sys.argv[2] if len(sys.argv) > 2 else "defs2.json", "w") as fh:
        json.dump(out, fh)
    print(f"wrote {len(out)} records")


if __name__ == "__main__":
    main()
