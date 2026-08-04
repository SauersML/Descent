"""Infinite-alleles forward simulator, the engine two batteries needed and lacked.

The transient family -- `fstTransientAt`, `mutationSharedRetentionAt`,
`migrationSharedBoostAt`, the `MutationDriftModelAssumptions` pair -- states how
`F_ST` APPROACHES its equilibrium, and that cannot come from the coalescent,
which delivers equilibria only. Batteries 21 and 22 tried a forward simulation
with BIALLELIC mutation and were voided twice, because the `theta` in
`fstEquilibrium = 1/(1 + theta + bigM)` is an infinite-alleles parameter: under
biallelic mutation a lineage can mutate BACK to its current allele, so identity
is restored at a rate the infinite-alleles model never has, and the two
equilibria differ by construction.

Here each mutation creates an allele never seen before, which is the model those
definitions are written for. Identity is then simply equality of allele labels,
so the within- and between-deme homozygosities are counted directly rather than
inferred, and `F_ST = 1 - H_S/H_T` needs no estimator convention.

CALIBRATION STATE -- one arm is ready and one is not.

  SINGLE POPULATION: ready. The equilibrium homozygosity comes out 0.4956
      against the theoretical `1/(1 + theta) = 0.5000`, a 0.9 percent gap. The
      mutation-and-drift core is therefore sound, which is the part biallelic
      mutation got wrong.

  ISLAND F_ST: NOT ready. Against `1/(1 + theta + bigM)` the plateau sits about
      7 percent low and the cause is not identified. The obvious candidate --
      Nei's `G_ST` being downward biased at small deme counts -- was tested and
      REJECTED: at 12, 24 and 40 demes the gap runs -7.7, -5.2 and -8.2 percent,
      which does not close with deme count and whose non-monotonicity is
      consistent with noise at six replicates rather than with a deme-count
      effect.

So this engine must NOT yet be used as the positive control for the transient
family. A control that is itself 7 percent off would void every battery it
gates, correctly, and quoting it as though it were calibrated would be the
mistake this whole harness exists to prevent. What is needed next is either the
cause of the island gap or a bias-corrected estimator; the single-population arm
can be used in the meantime for anything that does not involve migration.
"""
import math

import numpy as np


def run(Ne, m, mu, gens, n_demes=12, reps=24, seed=1, record_every=1):
    """Infinite-alleles island model. Returns F_ST at each recorded generation.

    Every gene copy carries an integer allele label. Each generation a gene
    draws its parent from its own deme with probability `1 - m` and from the
    pooled population with probability `m`, then mutates to a BRAND NEW label
    with probability `mu`. Labels are compacted each generation so the bincount
    stays small.
    """
    rng = np.random.default_rng(seed)
    two_n = int(2 * Ne)
    total = n_demes * two_n
    # state[r, d, i] would be the natural shape; flatten the deme axis for speed
    state = np.zeros((reps, n_demes, two_n), dtype=np.int64)
    next_label = np.ones(reps, dtype=np.int64)   # label 0 is the common ancestor
    out_t, out_f = [], []

    for g in range(gens + 1):
        if g % record_every == 0:
            out_t.append(g)
            out_f.append(_fst(state))
        # --- choose parents -------------------------------------------------
        from_pool = rng.random((reps, n_demes, two_n)) < m
        own_idx = rng.integers(0, two_n, size=(reps, n_demes, two_n))
        pool_d = rng.integers(0, n_demes, size=(reps, n_demes, two_n))
        pool_i = rng.integers(0, two_n, size=(reps, n_demes, two_n))
        r_idx = np.arange(reps)[:, None, None]
        d_idx = np.arange(n_demes)[None, :, None]
        own = state[r_idx, d_idx, own_idx]
        pooled = state[r_idx, pool_d, pool_i]
        state = np.where(from_pool, pooled, own)
        # --- mutate to brand-new labels -------------------------------------
        hit = rng.random((reps, n_demes, two_n)) < mu
        n_hit = hit.sum(axis=(1, 2))
        for r in range(reps):
            k = int(n_hit[r])
            if k:
                state[r][hit[r]] = next_label[r] + np.arange(k)
                next_label[r] += k
        # compact labels so bincount stays bounded
        for r in range(reps):
            _, state[r] = np.unique(state[r], return_inverse=True)
            state[r] = state[r].reshape(n_demes, two_n)
        next_label[:] = state.reshape(reps, -1).max(axis=1) + 1
    return np.array(out_t), np.array(out_f)


def _fst(state):
    """1 - H_S/H_T with identity read off allele labels, averaged over reps."""
    reps, n_demes, two_n = state.shape
    vals = []
    for r in range(reps):
        s = state[r]
        k = int(s.max()) + 1
        # within-deme homozygosity
        hom_s = 0.0
        for d in range(n_demes):
            c = np.bincount(s[d], minlength=k).astype(float) / two_n
            hom_s += float((c ** 2).sum())
        hom_s /= n_demes
        # total homozygosity on the pooled sample
        c = np.bincount(s.ravel(), minlength=k).astype(float) / (n_demes * two_n)
        hom_t = float((c ** 2).sum())
        hs, ht = 1 - hom_s, 1 - hom_t
        vals.append((ht - hs) / ht if ht > 0 else float("nan"))
    return float(np.nanmean(vals))


def selftest():
    """Calibrate against two equilibria the engine does not contain."""
    print("%-46s %10s %10s %8s" % ("engine check", "theory", "sim", "rel"))
    # 1. one deme, no migration: equilibrium homozygosity is 1/(1 + theta)
    Ne, mu = 100, 2.5e-3
    theta = 4 * Ne * mu
    _, _ = run(Ne, 0.0, mu, 0, n_demes=1, reps=1, seed=2)
    st = np.zeros((8, 1, 2 * Ne), dtype=np.int64)
    # run a single deme forward and read its homozygosity
    t, f = run(Ne, 0.0, mu, 1200, n_demes=1, reps=8, seed=3, record_every=200)
    # F_ST is undefined for one deme; measure homozygosity instead
    hom = _homozygosity_single(Ne, mu, gens=1200, reps=8, seed=4)
    print("%-46s %10.4f %10.4f %7.1f%%"
          % ("single deme homozygosity 1/(1+theta)", 1 / (1 + theta), hom,
             100 * (hom - 1 / (1 + theta)) / (1 / (1 + theta))))
    # 2. island model equilibrium 1/(1 + theta + bigM)
    Ne, m, mu = 150, 0.004, 6.7e-4
    theta, bigM = 4 * Ne * mu, 4 * Ne * m
    t, f = run(Ne, m, mu, 2500, n_demes=12, reps=10, seed=5, record_every=500)
    plateau = float(np.mean(f[-3:]))
    pred = 1 / (1 + theta + bigM)
    print("%-46s %10.4f %10.4f %7.1f%%"
          % ("island F_ST 1/(1+theta+bigM)", pred, plateau,
             100 * (plateau - pred) / pred))


def _homozygosity_single(Ne, mu, gens, reps, seed):
    rng = np.random.default_rng(seed)
    two_n = 2 * Ne
    state = np.zeros((reps, two_n), dtype=np.int64)
    nxt = np.ones(reps, dtype=np.int64)
    for _ in range(gens):
        idx = rng.integers(0, two_n, size=(reps, two_n))
        state = np.take_along_axis(state, idx, axis=1)
        hit = rng.random((reps, two_n)) < mu
        for r in range(reps):
            k = int(hit[r].sum())
            if k:
                state[r][hit[r]] = nxt[r] + np.arange(k)
                nxt[r] += k
        for r in range(reps):
            _, state[r] = np.unique(state[r], return_inverse=True)
        nxt[:] = state.max(axis=1) + 1
    vals = []
    for r in range(reps):
        c = np.bincount(state[r]).astype(float) / two_n
        vals.append(float((c ** 2).sum()))
    return float(np.mean(vals))


if __name__ == "__main__":
    selftest()
