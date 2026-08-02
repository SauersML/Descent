"""PopulationGeneticsFoundations battery: mutation-drift and migration formulas.

  :100  expectedHeterozygosity theta        = theta / (1 + theta)
  :1184 hetEquilibrium Ne mu                = 4 Ne mu / (1 + 4 Ne mu)
  :463  fstMutationDriftEquilibrium theta   = 1 / (1 + theta)
  :409  heterozygosityLossFromDrift Ne t    = 1 - (1 - 1/(2Ne))^t
  :982  effectiveMigration m12 m21          = (m12 + m21) / 2
  :1015 ldCorrelationFromMigration M        = M^2 / (1 + M)^2
  :219  continentIslandStepSelectionFirst   (added in response to finding #16)
  :226  continentIslandStepMigrationFirst

The mutation-drift quantities need an INFINITE-ALLELES simulator, which the
coalescent and the two-locus code cannot provide: each mutation must create a
brand-new allele so that homozygosity is measurable.  This implements one
directly -- 2N gene copies resampled each generation, each mutating to a novel
allele with probability mu.
"""
from __future__ import annotations

import json
import os
import sys
from concurrent.futures import ProcessPoolExecutor

for _v in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS"):
    os.environ[_v] = "1"

import numpy as np  # noqa: E402


def infinite_alleles(args):
    """Wright-Fisher with infinite alleles.

    Runs MANY INDEPENDENT replicate populations rather than one long chain: at
    these mutation rates the autocorrelation time is ~2N generations, so a
    single 40k-generation run yields only ~20 effectively independent samples
    and the estimate is dominated by sampling noise.
    """
    N, mu, gens, burn, seed = args
    rng = np.random.default_rng(seed)
    twoN = 2 * N
    reps = 400
    # reps independent populations evolved in parallel as rows
    alleles = np.zeros((reps, twoN), dtype=np.int64)
    next_id = 1
    hs = []
    for g in range(gens):
        idx = rng.integers(0, twoN, size=(reps, twoN))
        alleles = np.take_along_axis(alleles, idx, axis=1)
        nmut = rng.binomial(twoN * reps, mu)
        if nmut:
            flat = rng.choice(twoN * reps, size=nmut, replace=False)
            alleles.reshape(-1)[flat] = np.arange(next_id, next_id + nmut)
            next_id += nmut
        if g >= burn and g % 50 == 0:
            # homozygosity per replicate, then averaged across replicates
            for r in range(reps):
                _, c = np.unique(alleles[r], return_counts=True)
                p = c / twoN
                hs.append(1.0 - float((p ** 2).sum()))
    H = float(np.mean(hs))
    se = float(np.std(hs) / np.sqrt(len(hs)))
    theta = 4 * N * mu
    return dict(check="infinite_alleles", N=N, mu=mu, theta=theta,
                H_obs=H, H_se=se, n_samples=len(hs),
                lean_expectedHeterozygosity=theta / (1 + theta),
                lean_fstMutationDrift=1 / (1 + theta),
                F_obs=1 - H)


def drift_only(args):
    """heterozygosityLossFromDrift: closed population, NO mutation."""
    N, t, reps, seed = args
    rng = np.random.default_rng(seed)
    p = np.full(reps, 0.5)
    H0 = float(np.mean(2 * p * (1 - p)))
    for _ in range(t):
        p = rng.binomial(2 * N, p) / (2 * N)
    H = float(np.mean(2 * p * (1 - p)))
    return dict(check="drift_only", N=N, t=t, obs=1 - H / H0,
                lean=1 - (1 - 1 / (2 * N)) ** t)


def continent_island(args):
    """Both step orderings, run to equilibrium; exact deterministic recursion."""
    s, m, sel_first, seed = args
    p = 0.5
    for _ in range(500000):
        prev = p
        if sel_first:
            p = p * (1 + s) / (1 + s * p)
            p = (1 - m) * p
        else:
            p = (1 - m) * p
            p = p * (1 + s) / (1 + s * p)
        if abs(p - prev) < 1e-15:
            break
        if p < 1e-15:
            p = 0.0
            break
    return dict(check="continent_island", s=s, m=m, sel_first=sel_first,
                equilibrium=float(p), classical=max(0.0, 1 - m / s),
                old_lean_s_over_s_plus_m=s / (s + m))


def main():
    jobs = []
    for N, mu in [(500, 1e-4), (500, 5e-4), (1000, 1e-4), (1000, 5e-4)]:
        jobs.append((infinite_alleles, (N, mu, 4000, 2000, 7 + N + int(mu * 1e6))))
    for N, t in [(100, 50), (500, 200), (1000, 500)]:
        jobs.append((drift_only, (N, t, 40000, 11 + N + t)))
    for s, m in [(0.1, 0.02), (0.1, 0.08), (0.2, 0.05)]:
        for sf in (True, False):
            jobs.append((continent_island, (s, m, sf, 1)))

    with ProcessPoolExecutor(max_workers=int(os.environ.get("NPROC", "16"))) as ex:
        out = [f.result() for f in [ex.submit(fn, a) for fn, a in jobs]]
    with open(sys.argv[1] if len(sys.argv) > 1 else "pgf.json", "w") as fh:
        json.dump(out, fh)

    print("=== expectedHeterozygosity = theta/(1+theta), infinite alleles ===")
    print(f"{'N':>6} {'mu':>9} {'theta':>7} {'H obs':>9} {'lean H':>9} {'err%':>7} "
          f"{'F obs':>9} {'lean 1/(1+th)':>14} {'err%':>7}")
    for r in [x for x in out if x["check"] == "infinite_alleles"]:
        lh = r["lean_expectedHeterozygosity"]
        lf = r["lean_fstMutationDrift"]
        print(f"{r['N']:6d} {r['mu']:9.1e} {r['theta']:7.2f} {r['H_obs']:9.4f} "
              f"+-{r['H_se']:.4f} {lh:9.4f} {100*(lh-r['H_obs'])/r['H_obs']:7.1f} "
              f"{r['F_obs']:9.4f} {lf:9.4f} {100*(lf-r['F_obs'])/r['F_obs']:7.1f}")

    print("\n=== heterozygosityLossFromDrift (closed population, no mutation) ===")
    print(f"{'N':>6} {'t':>6} {'obs':>9} {'lean':>9} {'err%':>7}")
    for r in [x for x in out if x["check"] == "drift_only"]:
        print(f"{r['N']:6d} {r['t']:6d} {r['obs']:9.4f} {r['lean']:9.4f} "
              f"{100*(r['lean']-r['obs'])/r['obs']:7.1f}")

    print("\n=== continent-island equilibrium, both step orderings ===")
    print(f"{'s':>6} {'m':>6} {'order':>10} {'equilibrium':>12} {'1-m/s':>8} "
          f"{'s/(s+m)':>9}")
    for r in [x for x in out if x["check"] == "continent_island"]:
        order = "sel-first" if r["sel_first"] else "mig-first"
        print(f"{r['s']:6.2f} {r['m']:6.2f} {order:>10} {r['equilibrium']:12.5f} "
              f"{r['classical']:8.4f} {r['old_lean_s_over_s_plus_m']:9.4f}")


if __name__ == "__main__":
    main()
