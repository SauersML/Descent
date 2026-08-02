#!/usr/bin/env python3
"""HEAVY 2 -- is `driftLDEquilibrium` the probability of gametic identity, or E[r^2]?

DECIDES: `LDDecayTheory.driftLDEquilibrium` (LDDecayTheory.lean:300) and, with
it, `driftLDStep`, `driftLDRetention`, `driftLDTrajectory`, and every downstream
use of "LD at drift-recombination equilibrium".

The analytic tier already established (exactly, no sampling) that the closed
form IS the exact fixed point of its own step function, and that this fixed
point differs from Ohta & Kimura's sigma_d^2 by +120% at rho = 4Nc = 0 falling
to +2% at rho = 100.  What it CANNOT establish is which of the two the corpus
should be using, because Ohta-Kimura is itself a diffusion approximation.  Only
simulation decides that.

WHAT TO SIMULATE
    Neutral Wright-Fisher, constant diploid size Ne, two loci at recombination
    fraction c, run to stationarity under recurrent mutation, replicated.
    Coalescent (msprime) with a short segment is the cheap route; a forward
    Wright-Fisher on explicit two-locus haplotype counts is the honest one and
    is what this script does, because the quantity is a ratio of expectations
    over the stationary distribution and the coalescent parameterises it only
    indirectly.

WHAT TO MEASURE
    sigma_d^2 = E[D^2] / E[p(1-p) q(1-q)], averaged over replicates and over
    generations after burn-in.  Report E[r^2] separately: it is NOT the same
    statistic and conflating them is a live risk here.

WHAT EACH CANDIDATE PREDICTS
    Lean driftLDEquilibrium : (1-c)^2/(2Ne) / (1 - (1-c)^2(1-1/2Ne))
    Sved                    : 1/(1 + 4 Ne c)
    Ohta & Kimura           : (10 + rho)/((2 + rho)(11 + rho)),  rho = 4 Ne c

THE CAN-FAIL CLAUSE
    The rho grid MUST reach down to rho ~ 0.1 and MUST include rho <= 10.
    The three candidates converge as rho -> infinity: at rho = 100 they agree
    to 2%, which is inside replicate noise, so a loosely-linked grid produces
    three "validated" formulas and decides nothing.  The separation is at low
    rho, where Lean/Sved predict ~1.0 and Ohta-Kimura predicts 0.4545 -- a
    factor of 2.2, far outside the error bars this design achieves.
    Second required asymmetry: run at TWO values of Ne (250 and 2000) with the
    same rho.  All three candidates depend on c and Ne only through rho, so any
    residual Ne-dependence in the measurement means all three are wrong and the
    finding is larger than the choice between them.

EXPECTED RUNTIME
    ~40 min on 16 cores.  6 rho x 2 Ne x 200 replicates x 20*Ne generations.
    Pure numpy, vectorised over replicates; memory < 1 GB.

REQUIREMENTS
    numpy only.  No msprime, no SLiM.  Runs anywhere.
"""

import json

import numpy as np

RHOS = [0.1, 0.5, 2.0, 10.0, 40.0, 100.0]
NES = [250, 2000]
REPS = 200
MU = 1e-4          # per locus per generation, symmetric two-allele
BURNIN_MULT = 20   # generations = BURNIN_MULT * Ne
SAMPLE_EVERY = 50


def evolve(ne, c, reps, gens, rng):
    """Vectorised two-locus Wright-Fisher on haplotype frequencies.

    State: (reps, 4) counts of haplotypes AB, Ab, aB, ab among 2*Ne gametes.
    """
    n = 2 * ne
    x = rng.multinomial(n, [0.25] * 4, size=reps).astype(np.float64) / n
    d_sq, denom = [], []
    for g in range(gens):
        pA = x[:, 0] + x[:, 1]
        pB = x[:, 0] + x[:, 2]
        D = x[:, 0] * x[:, 3] - x[:, 1] * x[:, 2]
        # recombination
        xr = x.copy()
        xr[:, 0] -= c * D
        xr[:, 1] += c * D
        xr[:, 2] += c * D
        xr[:, 3] -= c * D
        # Exact symmetric mutation at both loci, as a 4x4 haplotype transition.
        f = xr
        m = MU
        M = np.array([
            [(1 - m) ** 2, m * (1 - m), m * (1 - m), m * m],
            [m * (1 - m), (1 - m) ** 2, m * m, m * (1 - m)],
            [m * (1 - m), m * m, (1 - m) ** 2, m * (1 - m)],
            [m * m, m * (1 - m), m * (1 - m), (1 - m) ** 2],
        ])
        f = f @ M.T
        f = np.clip(f, 0, None)
        f /= f.sum(axis=1, keepdims=True)
        # drift
        x = np.stack([rng.multinomial(n, fi) for fi in f]).astype(np.float64) / n
        if g > BURNIN_MULT * ne // 2 and g % SAMPLE_EVERY == 0:
            pA = x[:, 0] + x[:, 1]
            pB = x[:, 0] + x[:, 2]
            D = x[:, 0] * x[:, 3] - x[:, 1] * x[:, 2]
            d_sq.append(D ** 2)
            denom.append(pA * (1 - pA) * pB * (1 - pB))
    return np.concatenate(d_sq), np.concatenate(denom)


def main():
    rng = np.random.default_rng(20260802)
    out = []
    for ne in NES:
        for rho in RHOS:
            c = rho / (4.0 * ne)
            gens = BURNIN_MULT * ne
            ds, dn = evolve(ne, c, REPS, gens, rng)
            sigma_d2 = float(ds.mean() / dn.mean())
            a = (1 - c) ** 2
            rec = dict(
                Ne=ne, rho=rho, c=c,
                sigma_d2_measured=sigma_d2,
                lean_driftLDEquilibrium=float(a / (2 * ne) / (1 - a * (1 - 1 / (2 * ne)))),
                sved=float(1.0 / (1.0 + rho)),
                ohta_kimura=float((10 + rho) / ((2 + rho) * (11 + rho))),
            )
            out.append(rec)
            print(json.dumps(rec), flush=True)
    json.dump(out, open("h2_results.json", "w"), indent=1)


if __name__ == "__main__":
    main()
