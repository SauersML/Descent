"""Cell G: CovarianceStructure.admixtureLDMagnitude

  D_admix = alpha*(1-alpha) * (p_A - p_B)^2 * (1-r)^g

A single admixture pulse: an admixed population formed as `alpha` from source A
and `1-alpha` from source B, each parental population in linkage equilibrium at
its own allele frequencies, then `g` generations of random mating with
recombination fraction `r`.

Measured with a finite-N individual-based two-locus simulation -- gametes, not a
frequency recursion -- so the decay is realised by actual recombination events
and drift is present.  The body is the equal-frequency-difference case
`q_A = p_A`, `q_B = p_B` of `admixture_ld_at_gen_eq`, so the cells are run at
that specialization.

Competitors on the same cells:
  * `alpha^2` in place of `alpha*(1-alpha)` -- the admixture-fraction slip
  * `exp(-r*g)` in place of `(1-r)^g` -- the continuous-time approximation
  * no decay factor at all
  * PLANTED: the corpus body inflated 40 percent

Guard PGSEL_G1.
"""
import json, math, sys
import numpy as np

GUARD = "PGSEL_G1"


def simulate(alpha, pA, pB, r, g, N, reps, rng):
    """Returns mean D at generation g over `reps` replicate admixed populations."""
    out = []
    twoN = 2 * N
    for _ in range(reps):
        # form the admixed pool: each gamete is drawn from A with prob alpha,
        # and within a source the two loci are independent (linkage equilibrium)
        src = rng.random(twoN) < alpha
        p = np.where(src, pA, pB)
        locA = (rng.random(twoN) < p).astype(np.int8)
        locB = (rng.random(twoN) < p).astype(np.int8)
        for _ in range(g):
            # random mating: each offspring gamete comes from one parent
            # individual's two gametes, recombining between the loci with prob r
            par = rng.integers(0, N, size=twoN)
            which = rng.integers(0, 2, size=twoN)
            g1 = 2 * par + which
            g2 = 2 * par + (1 - which)
            rec = rng.random(twoN) < r
            a = locA[g1]
            b = np.where(rec, locB[g2], locB[g1])
            locA, locB = a, b
        pa, pb = locA.mean(), locB.mean()
        out.append(((locA * locB).mean()) - pa * pb)
    a = np.array(out)
    return a.mean(), a.std(ddof=1) / math.sqrt(reps)


def cell_G(reps=400):
    rng = np.random.default_rng(3113)
    rows = []
    for (alpha, pA, pB, r, g) in ((0.30, 0.80, 0.20, 0.05, 4),
                                  (0.50, 0.90, 0.10, 0.10, 3),
                                  (0.20, 0.70, 0.30, 0.02, 8)):
        N = 3000
        m, se = simulate(alpha, pA, pB, r, g, N, reps, rng)
        d0 = (pA - pB) ** 2
        cands = {
            "corpus": alpha * (1 - alpha) * d0 * (1 - r) ** g,
            "COMP alpha^2": alpha ** 2 * d0 * (1 - r) ** g,
            "COMP exp(-rg)": alpha * (1 - alpha) * d0 * math.exp(-r * g),
            "COMP no decay": alpha * (1 - alpha) * d0,
            "PLANTED 1.4x": 1.4 * alpha * (1 - alpha) * d0 * (1 - r) ** g,
        }
        rows.append(dict(alpha=alpha, pA=pA, pB=pB, r=r, g=g, N=N, reps=reps,
                         measured=m, sem=se, pred=cands,
                         sems={k: (v - m) / se for k, v in cands.items()}))
    return rows


if __name__ == "__main__":
    r = cell_G(int(sys.argv[1]) if len(sys.argv) > 1 else 400)
    print("FRESHNESS=OK", GUARD)
    print(json.dumps(dict(cell="G", target="admixtureLDMagnitude", guard=GUARD,
                          argument_source="finite-N individual-based two-locus gamete "
                                          "simulation of a single admixture pulse; decay "
                                          "realised by recombination events, not by "
                                          "iterating the closed form",
                          detail=r), indent=1, default=float))
