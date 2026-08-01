"""Check Calibrator population-genetics *definitions* against simulation.

Every theorem in `proofs/Calibrator` is machine-checked, and there are no
`sorry`s -- so a wrong result can only enter through a definition whose name
claims a population-genetic meaning that its formula does not have.  This
harness transcribes each Lean definition literally (the Lean source is quoted in
each docstring) and compares it against a simulation of the quantity the name
refers to.

Ground truth is msprime for coalescent quantities and an exact vectorized
Wright-Fisher forward simulation for the two-locus LD quantities.
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


def lean_ldHalfLife(Ne):
    """LDDecayTheory.lean:423  `2 * Ne * Real.log 2`"""
    return 2 * Ne * np.log(2)


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
