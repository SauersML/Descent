"""Can a SAMPLE-level fixation object disagree with the population-level one on
clean02's Phi cells?

The corpus body predicts the weighted fraction of signal on variants still
segregating IN THE SOURCE POPULATION.  The proposed rival replaces that with the
probability the variant is still polymorphic IN A SAMPLE of n chromosomes drawn
from the source.  Sample-monomorphic contains population-fixed, so the rival is
never larger; the question is by how much, at the n this design actually has.

Reported for each cell: the body, the sample-level object at four sample sizes,
and the gap in units of the sem clean02 recorded for that cell.

WHAT THIS LICENSES AND WHAT IT DOES NOT. The answer is that at clean02's own
cohort the substitution CANNOT FAIL: the gap is below the printing precision at
n = 80000 chromosomes, 0.03 to 0.42 sems at n = 4000 -- the entire source
population -- and reaches one sem only around n = 1000. So a rival built from a
sample-conditioned law would be an identity control on these cells, and the
honest sentence for a head is that the population/sample distinction is below the
resolution of this design by four orders of magnitude, NOT that it was checked
and agreed. The structural reason is that a segregating frequency in a 2Ne = 4000
population is at least 1/4000, so P(sample monomorphic) is at most
(1 - 1/4000)^n, which is 2e-9 at n = 80000.

It does NOT license the reverse claim that the two objects are interchangeable in
general. At an n where the gap has power -- a few hundred chromosomes -- it is no
longer this design's cohort, and the question becomes a GWAS-ascertainment one
about a different oracle. The companion measurement `probe_bridge01.py` sizes
that regime properly, on a spectrum with no MAF floor.

`p_s` is drifted forward with the same Wright-Fisher step clean02 uses, and the
sample-level column is the EXPECTATION given `p_s` rather than a drawn cohort:
`1 - p^n - (1-p)^n`. That is the right object for comparing two laws and it
carries no cohort-sampling variance, so it bounds the mean and not the spread.
"""
import math

import numpy as np

NE_S = 2000.0
M = 10000
BLOCKS = 6
T_GRID = (100, 250, 500, 800, 1100)
SPECTRA = {"[0.01,0.99]": (0.01, 0.99), "[0.05,0.95]": (0.05, 0.95)}
N_CHR = (200, 1000, 4000, 80000)
# the sems clean02 recorded on its fourteen Phi cells
SEM = {(100, "[0.01,0.99]"): 0.000526, (250, "[0.01,0.99]"): 0.001582,
       (500, "[0.01,0.99]"): 0.002159, (800, "[0.01,0.99]"): 0.004623,
       (1100, "[0.01,0.99]"): 0.004564, (100, "[0.05,0.95]"): 0.000191,
       (250, "[0.05,0.95]"): 0.000565, (500, "[0.05,0.95]"): 0.002358,
       (800, "[0.05,0.95]"): 0.002894, (1100, "[0.05,0.95]"): 0.004353}


def anc(m, rng, lo_hi):
    lo, hi = math.log(lo_hi[0]), math.log(lo_hi[1])
    return np.exp(rng.random(m) * (hi - lo) + lo)


def drift(p, ne, t, rng):
    two_n = int(round(2 * ne))
    for _ in range(t):
        p = rng.binomial(two_n, p) / two_n
    return p


print("%-12s %5s %10s %10s %10s %10s %10s"
      % ("spectrum", "t", "poly_S", "n=200", "n=1000", "n=4000", "n=80000"))
for lab, lo_hi in SPECTRA.items():
    for t in T_GRID:
        pop, samp = [], {n: [] for n in N_CHR}
        for b in range(BLOCKS):
            rng = np.random.default_rng(90000 + 100 * b + t)
            p0 = anc(M, rng, lo_hi)
            beta = rng.standard_normal(M) / math.sqrt(M)
            w = beta ** 2 * 2 * p0 * (1 - p0)
            p_s = drift(p0, NE_S, t, rng)
            tot = float(np.sum(w))
            pop.append(float(np.sum(w * ((p_s > 0) & (p_s < 1))) / tot))
            for n in N_CHR:
                q = 1.0 - p_s ** n - (1.0 - p_s) ** n
                samp[n].append(float(np.sum(w * q) / tot))
        s = SEM[(t, lab)]
        row = "%-12s %5d %10.6f" % (lab, t, np.mean(pop))
        for n in N_CHR:
            row += " %10.6f" % np.mean(samp[n])
        print(row)
        gaps = " ".join("%.2f" % (abs(np.mean(pop) - np.mean(samp[n])) / s)
                        for n in N_CHR)
        print("%-12s %5s %10s  gap in clean02 sems: %s" % ("", "", "", gaps))
