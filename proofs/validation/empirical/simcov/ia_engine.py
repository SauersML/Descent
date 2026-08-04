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

  ISLAND F_ST: nearly ready, with a stated 4 percent systematic. Against
      `1/(1 + theta + bigM)` at `theta` near 1, where heterozygosity is about
      one half and the estimator is in a usable regime, the plateau sits 4.1,
      4.2 and 3.3 percent low at `m` = 0.002, 0.005 and 0.010. A consistent
      small offset across a factor of five in migration.

      TWO EARLIER DIAGNOSES OF THIS ARM WERE WRONG AND ARE RETRACTED.

      The first said "about 7 percent, cause unidentified". The second, reached
      by setting `mu` to 2e-5 so that the prediction would reduce to the
      drift-migration equilibrium, reported 38 percent and concluded the engine
      migrated 1.8 times too fast. Both were artefacts of the regime, not
      properties of the engine.

      At `mu` = 2e-5 the equilibrium heterozygosity is `theta/(1 + theta)` with
      `theta` = 0.006, so `H` is about six parts in a thousand. The within-deme
      homozygosity estimator `sum (c/n)^2` carries a bias of order `1/(2 Ne)` =
      0.0033, which is more than HALF of `H_T` itself. Every `F_ST` computed
      there is dominated by that bias. The test built to be decisive was run
      where its own estimator does not work, and the sharper-sounding diagnosis
      it produced was worth less than the vaguer one it replaced.

      That is the fourth design error in this thread and the most instructive:
      a limit taken to simplify a comparison can destroy the statistic being
      compared. Check that the estimator survives the limit before trusting
      what it says there.

USING IT. The single-population arm is calibrated at 0.9 percent and is ready.
The island arm carries a known 4 percent systematic, so it may serve as a
positive control only where 4 percent is comfortably inside the tolerance, and
never at a three-sem gate with tight error bars -- there it would void batteries
for its own offset. Closing that last 4 percent, most likely with unbiased
homozygosity estimators `sum c(c-1) / (n(n-1))`, is what remains before the
transient family can be measured against it.
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
