"""Round 4a: high-power reruns of the three round-2 checks that were noisy.

  * assortative mating -- separate `amEquilibriumVariance` (1/(1-r*h2)) from
    `amInflationFactor` (1/(1-r)); these are two definitions in the same
    development that both claim to be the AM variance inflation.
  * admixedFst at realistic F_ST (round 2 used F_ST ~ 0.65, where any
    linearization is expected to break) with replication.
  * split F_ST with replication: coalFst vs fstFromDrift.
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


def lean_amEquilibriumVariance(V_A, r, h2):
    """AssortativeMatingPGS.lean:99  `V_A / (1 - r * h2)`"""
    return V_A / (1 - r * h2)


def lean_amInflationFactor(r):
    """StratificationConfounding.lean:138  `1 / (1 - r)`"""
    return 1 / (1 - r)


def lean_admixedFst(alpha, fst_AB):
    """DemographicHistory.lean:173  `(1 - α) ^ 2 * fst_AB`"""
    return (1 - alpha) ** 2 * fst_AB


def lean_coalFst(t, Ne):
    """PopulationGeneticsFoundations.lean:120  `t / (t + 2 * Ne)`"""
    return t / (t + 2 * Ne)


def lean_fstFromDrift(t, Ne):
    """PopulationGeneticsFoundations.lean:283  `1 - (1 - 1 / (2 * Ne)) ^ t`"""
    return 1 - (1 - 1 / (2 * Ne)) ** t


def branch_fst(ts, ss):
    dxy = ts.divergence(sample_sets=ss, indexes=[(0, 1)], mode="branch")[0]
    pi = ts.diversity(sample_sets=ss, mode="branch")
    return float(1 - (pi[0] + pi[1]) / 2 / dxy)


# --------------------------------------------------------------------------

def am_rep(args):
    """Forward WF, primary phenotypic assortment, run long and averaged."""
    N, L, r_target, h2, gens, seed = args
    rng = np.random.default_rng(seed)
    g = rng.binomial(2, 0.5, size=(2 * N, L)).astype(np.float64)
    V_A0 = float(g.sum(axis=1).var())
    V_E = V_A0 * (1 - h2) / h2

    vars_, rs = [], []
    for t in range(gens):
        A = g.sum(axis=1)
        P = A + rng.normal(0, np.sqrt(V_E), size=g.shape[0])
        males = np.arange(0, N)
        females = np.arange(N, 2 * N)
        z = rng.multivariate_normal([0, 0], [[1, r_target], [r_target, 1]], size=N)
        om = males[np.argsort(P[males])][np.argsort(np.argsort(z[:, 0]))]
        of = females[np.argsort(P[females])][np.argsort(np.argsort(z[:, 1]))]
        if t >= gens // 2:                       # average over the second half
            vars_.append(float(A.var()))
            rs.append(float(np.corrcoef(P[om], P[of])[0, 1]))
        pick = np.repeat(np.arange(N), 2)
        child = (rng.random((2 * N, L)) < g[om[pick]] / 2).astype(np.float64)
        child += (rng.random((2 * N, L)) < g[of[pick]] / 2)
        g = child

    V_eq = float(np.mean(vars_))
    r_hat = float(np.mean(rs))
    h2_eq = V_eq / (V_eq + V_E)
    return dict(check="am", N=N, L=L, r_target=r_target, r_realized=r_hat,
                h2_base=h2, h2_eq=h2_eq, V_A0=V_A0, V_eq=V_eq,
                ratio_obs=V_eq / V_A0,
                lean_amEquilibrium_base_h2=lean_amEquilibriumVariance(1.0, r_hat, h2),
                lean_amEquilibrium_eq_h2=lean_amEquilibriumVariance(1.0, r_hat, h2_eq),
                lean_amInflationFactor=lean_amInflationFactor(r_hat))


def admix_rep(args):
    import msprime
    Ne, split_t, alpha, g, seed = args
    dem = msprime.Demography()
    for name in ("A", "B", "ADM", "ANC"):
        dem.add_population(name=name, initial_size=Ne)
    dem.add_admixture(time=g, derived="ADM", ancestral=["A", "B"],
                      proportions=[alpha, 1 - alpha])
    dem.add_population_split(time=split_t, derived=["A", "B"], ancestral="ANC")
    ts = msprime.sim_ancestry(samples={"A": 25, "B": 25, "ADM": 25},
                              demography=dem, sequence_length=5e6,
                              recombination_rate=RHO, random_seed=seed)
    A, B, ADM = list(range(50)), list(range(50, 100)), list(range(100, 150))
    fst_AB = branch_fst(ts, [A, B])
    return dict(check="admix", Ne=Ne, split_t=split_t, alpha=alpha, g=g,
                fst_AB=fst_AB, fst_ADM_A=branch_fst(ts, [ADM, A]),
                lean=lean_admixedFst(alpha, fst_AB))


def split_rep(args):
    import msprime
    Ne, t, seed = args
    dem = msprime.Demography()
    for name in ("A", "B", "ANC"):
        dem.add_population(name=name, initial_size=Ne)
    dem.add_population_split(time=t, derived=["A", "B"], ancestral="ANC")
    ts = msprime.sim_ancestry(samples={"A": 25, "B": 25}, demography=dem,
                              sequence_length=5e6, recombination_rate=RHO,
                              random_seed=seed)
    return dict(check="split", Ne=Ne, t=t,
                sim=branch_fst(ts, [list(range(50)), list(range(50, 100))]),
                lean_coalFst=lean_coalFst(t, Ne),
                lean_fstFromDrift=lean_fstFromDrift(t, Ne))


def main():
    jobs = []
    for r in (0.1, 0.2, 0.3, 0.4, 0.5):
        for h2 in (0.2, 0.5, 0.8):
            for rep in range(2):
                jobs.append((am_rep, (5000, 400, r, h2, 80, 11 + rep * 977
                                      + int(r * 100) + int(h2 * 10))))
    for split_t in (100, 300, 1000):          # F_ST ~ 0.05, 0.13, 0.33
        for alpha in (0.2, 0.5, 0.8):
            for rep in range(4):
                jobs.append((admix_rep, (1000, split_t, alpha, 20,
                                         5 + rep * 131 + split_t + int(alpha * 10))))
    for Ne in (1000, 5000):
        for t in (100, 250, 500, 1000, 2000, 4000):
            for rep in range(6):
                jobs.append((split_rep, (Ne, t, 3 + rep * 313 + t + Ne)))

    with ProcessPoolExecutor(max_workers=int(os.environ.get("NPROC", "24"))) as ex:
        out = [f.result() for f in [ex.submit(fn, a) for fn, a in jobs]]
    with open(sys.argv[1] if len(sys.argv) > 1 else "r4a.json", "w") as fh:
        json.dump(out, fh)
    print(f"wrote {len(out)} records")


if __name__ == "__main__":
    main()
