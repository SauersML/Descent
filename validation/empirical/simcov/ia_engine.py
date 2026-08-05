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

  ISLAND F_ST: a consistent 5 percent offset against the corpus formula, cause
      NOT identified, and THREE hypotheses tested and rejected. The offset is
      -4.8, -5.5 and -5.5 percent at `m` = 0.002, 0.005 and 0.010 with `theta`
      near 1, so it is flat across a factor of five in migration.

      Rejected 1 -- small-deme-count `G_ST` bias. The gap does not close with
      deme count: -7.7, -5.2, -8.2 percent at 12, 24 and 40 demes.

      Rejected 2 -- the mutation term. A test at `mu` = 2e-5 appeared to show a
      38 percent gap and was itself invalid: at `theta` = 0.006 the equilibrium
      heterozygosity is six parts in a thousand and the homozygosity bias
      `1/(2 Ne)` is more than half of `H_T`. The statistic does not survive that
      limit. Measured where `H` is about one half, the gap is the 5 percent
      above.

      Rejected 3 -- plug-in homozygosity bias. `sum (c/n)^2` overestimates
      homozygosity by about `1/n` and enters `H_S` and `H_T` at different sample
      sizes, so it does not cancel in the ratio. Replacing it with the unbiased
      `sum c(c-1)/(n(n-1))` -- which is used below, being correct regardless --
      moved the gap from -4.1/-4.2/-3.3 to -4.8/-5.5/-5.5. It did not close it
      and slightly widened it, so this is not the cause either.

      WHAT REMAINS. The offset is flat in `m`, which argues against anything
      scaling with migration, and it survives an unbiased estimator, which
      argues against sampling. The two live possibilities are a residual in this
      engine's generation cycle -- migration and reproduction are one draw here,
      not the two composed events of the island model -- and the corpus formula
      itself, which composes `theta` and `bigM` ADDITIVELY in
      `1/(1 + theta + bigM)`. Distinguishing those needs an island oracle
      independent of both, which this branch does not have: the coalescent one
      is mutation-free and so cannot test the composition.

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


def _unbiased_hom(counts, n):
    """Unbiased estimator of `sum p_i^2`: `sum c(c-1) / (n(n-1))`.

    The plug-in `sum (c/n)^2` overestimates homozygosity by about `1/n`, and
    that bias is NOT harmless here because it enters `H_S` and `H_T` at
    different sample sizes -- `2 Ne` within a deme against `n_demes * 2 Ne`
    pooled -- so it does not cancel in the ratio. With `H` near one half and
    `2 Ne` = 300 the within-deme bias is a third of a percent of `H`, and the
    island arm sat 4 percent low with it in place.
    """
    if n < 2:
        return float("nan")
    return float((counts * (counts - 1)).sum()) / (n * (n - 1))


def _fst(state):
    """1 - H_S/H_T with identity read off allele labels, averaged over reps."""
    reps, n_demes, two_n = state.shape
    vals = []
    for r in range(reps):
        s = state[r]
        k = int(s.max()) + 1
        hom_s = 0.0
        for d in range(n_demes):
            c = np.bincount(s[d], minlength=k).astype(float)
            hom_s += _unbiased_hom(c, two_n)
        hom_s /= n_demes
        c = np.bincount(s.ravel(), minlength=k).astype(float)
        hom_t = _unbiased_hom(c, n_demes * two_n)
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
