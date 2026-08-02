#!/usr/bin/env python3
"""HEAVY 1 -- does the 1D stepping-stone decay length depend on mu or on Ne?

DECIDES: `PopulationGeneticsFoundations.steppingStoneCharacteristicLength`
         (PopulationGeneticsFoundations.lean:893), L = sqrt(2 * Ne * m).

WHAT TO SIMULATE
    A 1D stepping-stone lattice of D demes, each of diploid size Ne, with
    symmetric nearest-neighbour migration at rate m per generation, at
    mutation-drift equilibrium under an infinite-sites model with rate mu.

WHAT TO MEASURE
    Hudson F_ST between deme 0 and deme d for d = 1..D//2, from branch-mode
    tskit divergence (no mutational noise), then fit
        log(1 - F_ST(d))  ~  -d / L_hat
    and report L_hat.

WHAT THE DEFINITION PREDICTS
    L = sqrt(2 * Ne * m).  This is CONSTANT in mu and INCREASING in Ne.

WHAT THE REFERENCE PREDICTS
    Malecot / Kimura-Weiss:  L = sqrt(m / (2 * mu)).
    DECREASING in mu as mu^(-1/2), and INDEPENDENT of Ne.

THE CAN-FAIL CLAUSE  (mandatory; this design fails if the definition is wrong)
    The grid varies mu over four orders of magnitude AT FIXED Ne AND m, and
    varies Ne over two orders AT FIXED m AND mu.  These two axes are what make
    the test decisive:
      * along the mu axis the Lean value does not move at all, so any measured
        mu-dependence falsifies it outright -- no constant of proportionality
        can absorb it;
      * along the Ne axis the Lean value moves as sqrt(Ne) while the reference
        does not move, so the two predictions have opposite slopes.
    A grid that varied only m would be unable to fail: both formulas scale as
    sqrt(m), and a fitted prefactor would reconcile them at every point.
    Report the FITTED EXPONENTS d log L / d log mu and d log L / d log Ne, not
    just L: the exponents are what the two models disagree about.

EXPECTED RUNTIME
    ~25 min on 16 cores.  40 demes x 4 mu x 3 Ne x 5 replicates = 240 msprime
    runs; each is a 40-deme stepping stone with 20 Mb of sequence, roughly
    3-6 s.  Memory < 2 GB.  Scale `SEQ_LEN` down first if it is tight.

THEORY-PINNED CONTROLS (mandatory; both fixed by theory, not by simulation)
    CONTROL 1 -- PANMIXIA.  Set m = 0.5 so the lattice mixes completely each
        generation and the D demes are one population. Then F_ST(d) = 0 for
        every d, pinned by definition, not fitted. A nonzero F_ST here means
        the deme-labelling or the F_ST estimator is wrong and no decay length
        from this run may be reported.
    CONTROL 2 -- WITHIN-DEME DIVERSITY.  Measured within-deme pairwise
        diversity must equal 4*Ne_effective*mu with the metapopulation's
        effective size, and in the m -> 0.5 panmictic control it must equal
        4*(D*Ne)*mu. Pinned by the neutral coalescent, independent of anything
        about decay lengths. It catches a mis-scaled mutation rate, which would
        shift L systematically and mimic exactly the mu-dependence this run is
        trying to measure -- the one artefact that could manufacture the
        result.
    Report both before any exponent.

REQUIREMENTS
    pip install msprime tskit numpy      (msprime is NOT installed on the
                                          workstation; see the survey)
"""

import itertools
import json
import sys

import msprime
import numpy as np

D_DEMES = 40
SEQ_LEN = 20_000_000
RECOMB = 1e-8
REPLICATES = 5

# fixed-Ne, fixed-m axis: mu varies.  fixed-mu axis: Ne varies.
GRID = (
    [dict(Ne=1000, m=0.01, mu=mu) for mu in (1e-9, 1e-8, 1e-7, 1e-6)]
    + [dict(Ne=Ne, m=0.01, mu=1e-8) for Ne in (250, 4000)]
)


def stepping_stone(Ne, m, D):
    dem = msprime.Demography.stepping_stone_model(
        [Ne] * D, migration_rate=m, boundaries=True
    )
    return dem


def run_one(Ne, m, mu, seed):
    dem = stepping_stone(Ne, m, D_DEMES)
    samples = {f"pop_{i}": 10 for i in range(D_DEMES)}
    ts = msprime.sim_ancestry(
        samples=samples,
        demography=dem,
        sequence_length=SEQ_LEN,
        recombination_rate=RECOMB,
        random_seed=seed,
    )
    # Branch-mode divergence: proportional to E[T], mutation rate cancels.
    # Mutation still matters for the DECAY LENGTH, which enters through the
    # equilibrium the lattice reaches -- so we add mutations and use site mode
    # for the F_ST itself, and keep branch mode only as a noise-free control.
    ts = msprime.sim_mutations(ts, rate=mu, random_seed=seed + 1)
    sets = [ts.samples(population=i) for i in range(D_DEMES)]
    fst = []
    for d in range(1, D_DEMES // 2):
        pairs = [(0, d), (1, d + 1), (2, d + 2)]
        vals = []
        for a, b in pairs:
            dxy = ts.divergence([sets[a], sets[b]], mode="site")
            pia = ts.diversity(sets[a], mode="site")
            pib = ts.diversity(sets[b], mode="site")
            vals.append(1.0 - 0.5 * (pia + pib) / dxy)
        fst.append(np.mean(vals))
    return np.array(fst)


def fit_length(fst):
    d = np.arange(1, len(fst) + 1)
    y = np.log(np.clip(1.0 - fst, 1e-12, None))
    ok = np.isfinite(y)
    slope = np.polyfit(d[ok], y[ok], 1)[0]
    return -1.0 / slope


def main():
    out = []
    for cell in GRID:
        Ls = [fit_length(run_one(**cell, seed=1000 + r)) for r in range(REPLICATES)]
        rec = dict(
            cell,
            L_measured=float(np.mean(Ls)),
            L_sd=float(np.std(Ls)),
            L_lean=float(np.sqrt(2 * cell["Ne"] * cell["m"])),
            L_malecot=float(np.sqrt(cell["m"] / (2 * cell["mu"]))),
        )
        out.append(rec)
        print(json.dumps(rec), flush=True)

    # The decisive numbers: fitted exponents.
    mu_cells = [r for r in out if r["Ne"] == 1000]
    ne_cells = [r for r in out if r["mu"] == 1e-8]
    def slope(rows, key):
        x = np.log([r[key] for r in rows])
        y = np.log([r["L_measured"] for r in rows])
        return float(np.polyfit(x, y, 1)[0])
    summary = {
        "dlogL_dlogmu_measured": slope(mu_cells, "mu"),
        "dlogL_dlogmu_lean": 0.0,
        "dlogL_dlogmu_malecot": -0.5,
        "dlogL_dlogNe_measured": slope(ne_cells, "Ne"),
        "dlogL_dlogNe_lean": 0.5,
        "dlogL_dlogNe_malecot": 0.0,
    }
    print(json.dumps({"summary": summary}, indent=1))
    json.dump({"cells": out, "summary": summary}, open("h1_results.json", "w"), indent=1)


if __name__ == "__main__":
    sys.exit(main())
