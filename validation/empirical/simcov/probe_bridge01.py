"""The population-to-cohort bridge, sized on a spectrum with NO MAF FLOOR.

WHY THIS EXISTS. The gap between the POPULATION-level polymorphism probability and
the SAMPLE-level one was measured before and reported as negligible -- under one
sem by n = 1000 haplotypes. Every one of those measurements was on spectra
truncated at MAF >= 0.01 or 0.05. The pipeline the chain is meant to describe has
no MAF filter at all: a variant enters the candidate pool by being polymorphic in
the discovery cohort, which reaches singletons. The gap is largest at low
frequency, so the earlier evidence and the operative regime do not overlap on the
axis that decides the question. This measures it where it lives.

WHAT IS COMPARED, and both sides are the same two validated laws evaluated, not
simulated.

  SAMPLE side: `1 - p_mono(p0, n, tau)`, the coalescent duality validated in
  battery_fix36 -- P(sample of n monomorphic | ancestral frequency p0, coalescent
  time tau) = sum_k P(N_tau = k | n) (p0^k + (1-p0)^k), with the block-counting
  pmf by uniformization.

  POPULATION side: `stillSegregatingProb(Ne, p0, t)`, Kimura's diffusion solution,
  which is the n -> infinity limit of the same object. So the gap is a genuine
  n-dependence of one law, not a comparison across two conventions, and it is
  non-negative by construction: a fixed population makes every sample monomorphic.

THE MECHANISM THE SWEEP IS DESIGNED TO EXPOSE. A sample of n haplotypes has
O(2/tau) ancestral blocks once tau exceeds ~2/n, because the initial collapse from
n lineages takes coalescent time about 2/n. At the depths here 2/tau is 24, 8 and
3. If that is what governs the sample-level object, then beyond a few hundred
haplotypes the answer stops depending on n and the bridge is a formality -- and
the n sweep is what shows it rather than assuming it. n is therefore swept
FORTYFOLD, and the saturation point is the finding.

NO VERDICT IS EMITTED. This sizes an effect; it does not score a body, and it
records no cells. Reporting it as a MATCH would be claiming a test it is not.
"""
import math
import sys

import numpy as np

NE = 1500.0
TWO_NE = 2.0 * NE
T_GRID = (250, 750, 2000)
N_GRID = (100, 500, 1000, 2000, 4000)
COHORT = 4000              # 2000 diploids, the discovery cohort under discussion
M_LOCI = 40000
BINS = (1.0 / TWO_NE, 3.0 / TWO_NE, 10.0 / TWO_NE, 0.01, 0.05, 0.2, 0.5)


# ---------------------------------------------------------------------------
# The two laws, transcribed from the batteries that validated them.
# ---------------------------------------------------------------------------
def block_counting_pmf(n, tau):
    """P(N_tau = k | N_0 = n) by uniformization -- battery_fix36's routine.

    The Poisson weight underflows to zero for the first `m - 40 sqrt(m)` terms at
    these rates, so the loop is started at the first representable term and the
    state vector is advanced to it without accumulating. That is a speed change
    only: the terms skipped contribute exactly 0.0 in the original.
    """
    if n == 1:
        return np.array([1.0])
    lam = np.array([k * (k - 1) / 2.0 for k in range(1, n + 1)])
    Lam = lam[-1]
    stay, down = 1.0 - lam / Lam, lam / Lam
    v = np.zeros(n)
    v[n - 1] = 1.0
    out = np.zeros(n)
    m = Lam * tau
    jmax = int(m + 10 * math.sqrt(m) + 50)
    logw = -m
    for j in range(jmax + 1):
        if logw > -745.0:
            out += math.exp(logw) * v
        nxt = v * stay
        nxt[:-1] += v[1:] * down[1:]
        v = nxt
        logw += math.log(m) - math.log(j + 1)
    return out / out.sum()


def p_mono(p, pmf):
    """P(sample monomorphic | ancestral frequency p), given the block pmf."""
    i = np.arange(1, len(pmf) + 1)
    keep = pmf > 1e-18            # k with no mass cannot matter and p^k underflows
    i, P = i[keep], pmf[keep]
    return np.power.outer(p, i) @ P + np.power.outer(1.0 - p, i) @ P


def gegenbauer_32(kmax, z):
    c = np.empty((kmax + 1, z.size))
    c[0] = 1.0
    if kmax >= 1:
        c[1] = 3.0 * z
    for k in range(1, kmax):
        c[k + 1] = (2.0 * (k + 1.5) * z * c[k] - (k + 2.0) * c[k - 1]) / (k + 1.0)
    return c


def still_segregating_prob(ne, p, t, n_terms=400):
    """Kimura's diffusion solution -- battery_clean02's routine, verbatim."""
    if t == 0:
        return np.ones_like(p)
    z = 1.0 - 2.0 * p
    c = gegenbauer_32(n_terms, z)
    tot = np.zeros_like(p)
    for n in range(1, n_terms + 1, 2):
        lam = n * (n + 1.0) / (4.0 * ne)
        e = math.exp(-lam * t)
        if e < 1e-18:
            break
        tot += (4.0 * (2 * n + 1) / (n * (n + 1.0))) * c[n - 1] * e
    return p * (1.0 - p) * tot


def main():
    rng = np.random.default_rng(4300111)
    lo, hi = 1.0 / TWO_NE, 1.0 - 1.0 / TWO_NE
    # 1/p on [1/(2Ne), 1 - 1/(2Ne)] -- NO MAF FLOOR, reaching population singletons
    p0 = np.exp(rng.random(M_LOCI) * (math.log(hi) - math.log(lo)) + math.log(lo))
    w = 2.0 * p0 * (1.0 - p0)          # the signal weighting the chain composes with
    print("spectrum: 1/p on [%.6g, %.6g], %d loci, NO MAF floor; Ne=%g"
          % (lo, hi, M_LOCI, NE))
    print("lowest bin holds %d loci below 3/(2Ne)=%.6g, carrying %.4f%% of the "
          "signal weight"
          % (int((p0 < 3 / TWO_NE).sum()), 3 / TWO_NE,
             100 * w[p0 < 3 / TWO_NE].sum() / w.sum()))

    edges = list(BINS) + [0.5]
    for t in T_GRID:
        tau = t / TWO_NE
        pop_seg = still_segregating_prob(NE, p0, t)
        print("\n=== t=%d generations, tau=%.4f, 2/tau=%.1f expected blocks ==="
              % (t, tau, 2.0 / tau))
        samp = {}
        for n in N_GRID:
            pmf = block_counting_pmf(n, tau)
            k = np.arange(1, len(pmf) + 1)
            ebar = float(k @ pmf)
            samp[n] = 1.0 - p_mono(p0, pmf)
            gap = pop_seg - samp[n]
            print("  n=%5d  E[N_tau]=%7.2f | signal-weighted: pop %.6f  "
                  "sample %.6f  gap %.3e" %
                  (n, ebar, float(w @ pop_seg / w.sum()),
                   float(w @ samp[n] / w.sum()), float(w @ gap / w.sum())))
        print("  --- binned by ancestral frequency, at the cohort n=%d, "
              "UNWEIGHTED means ---" % COHORT)
        print("  %-22s %7s %10s %10s %10s" %
              ("bin", "loci", "pop", "sample", "gap"))
        s = samp[COHORT]
        for a, b in zip([0.0] + edges[:-1], edges):
            sel = (p0 >= a) & (p0 < b)
            if not sel.any():
                continue
            print("  [%8.6f,%8.6f) %7d %10.6f %10.6f %10.3e"
                  % (a, b, int(sel.sum()), float(pop_seg[sel].mean()),
                     float(s[sel].mean()), float((pop_seg - s)[sel].mean())))


if __name__ == "__main__":
    main()
