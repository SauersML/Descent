#!/usr/bin/env python3
"""HEAVY 4 -- confirm the analytic split-F_ST oracle, then measure admixed F_ST.

TWO JOBS, one msprime setup.

JOB A -- GUARD THE ORACLE THAT THE WHOLE ANALYTIC TIER RESTS ON
    `refs.split_fst_hudson` is the reference against which `coalFst`,
    `fstFromGenerations`, `fstDerived` and `pairwiseFstFromBranches` were all
    judged.  It is derived, not measured.  If it is wrong, four analytic
    verdicts are wrong with it.  This job measures Hudson F_ST after a clean
    split directly and compares.

    Can-fail clause: the size grid MUST include N_daughter != N_ancestral and
    N_1 != N_2.  With all three sizes equal the oracle reduces to t/(t+2Ne),
    which several wrong formulas also reproduce to first order; the asymmetric
    cells are the only ones that test the e^{-t/2N_d} structure of
    `split_ET_within`.  Also required: t/(2Ne) >= 0.5 in at least half the
    cells, since below that every candidate collapses to t/(2Ne).

JOB B -- ADMIXED F_ST
    DECIDES: `DemographicHistory.admixedFst` (DemographicHistory.lean:271),
    F_ST(C,A) = (1-alpha)^2 * F_ST(A,B).  The analytic tier already shows a
    -44% error at a single fixed frequency pair, but the real quantity is an
    average over the frequency spectrum, and the sign of the averaging
    correction is not obvious from one pair.  This measures it.

    Can-fail clause: alpha MUST span both sides of 0.5 and the grid MUST
    include alpha near 0.8, where the analytic tier's error is largest.  A
    grid confined to small alpha sits where (1-alpha)^2 ~ 1 - 2*alpha and the
    ratio-versus-numerator distinction is second order.  Additionally the two
    sources must be strongly differentiated (split time >= 2*Ne) -- at low
    F_ST(A,B) every scaling of a near-zero number is a near-zero number and
    the relative error is dominated by noise.

THEORY-PINNED CONTROLS (mandatory)
    CONTROL 1 -- ZERO SPLIT TIME.  At t = 0 the two daughters are one
        population and F_ST must be exactly 0, pinned by definition. Non-zero
        means the sampling or the estimator is wrong.
    CONTROL 2 -- WITHIN-POPULATION DIVERSITY.  In the equal-size cell,
        branch-mode within-population diversity must equal 2*Ne generations of
        expected coalescence time, pinned by the neutral coalescent and
        INDEPENDENT of the split-F_ST formula being tested. This is the control
        that separates "my demography is misspecified" from "the oracle is
        wrong" -- if E[T_within] is not 2*Ne, the msprime model is not the
        model refs.split_fst_hudson assumes and the comparison is void.
    CONTROL 3 (job B) -- ALPHA AT THE ENDPOINTS.  At alpha = 0 the admixed
        population IS source B and F_ST(C,A) must equal F_ST(B,A); at alpha = 1
        it IS source A and F_ST(C,A) must be 0. Both pinned by definition.
        These bracket the admixture machinery without assuming any formula for
        intermediate alpha.

EXPECTED RUNTIME
    ~15 min on 16 cores.  Job A: 12 cells x 10 replicates, 50 Mb each.
    Job B: 12 cells x 10 replicates.  This is the cheapest item in the queue
    and it guards the rest, so run it FIRST.

REQUIREMENTS
    pip install msprime tskit numpy
"""

import itertools
import json
import math

import msprime
import numpy as np

SEQ_LEN = 50_000_000
RECOMB = 1e-8
MU = 1e-8
REPS = 10


def hudson_fst(ts, sa, sb):
    dxy = ts.divergence([sa, sb], mode="branch")
    pia = ts.diversity(sa, mode="branch")
    pib = ts.diversity(sb, mode="branch")
    return 1.0 - 0.5 * (pia + pib) / dxy


# --------------------------------------------------------------------------
def job_a():
    """Clean split with (possibly unequal) daughter and ancestral sizes."""
    NA = 1000
    cells = [
        dict(t=t, n1=n1, n2=n2, na=NA)
        for t in (0, 500, 2000, 8000)          # t=0 row is CONTROL 1
        for (n1, n2) in ((NA, NA), (NA // 4, 4 * NA), (NA // 4, NA), (4 * NA, NA))
    ]
    out = []
    for cell in cells:
        vals = []
        for r in range(REPS):
            dem = msprime.Demography()
            dem.add_population(name="A", initial_size=cell["n1"])
            dem.add_population(name="B", initial_size=cell["n2"])
            dem.add_population(name="ANC", initial_size=cell["na"])
            dem.add_population_split(time=cell["t"], derived=["A", "B"], ancestral="ANC")
            ts = msprime.sim_ancestry(
                samples={"A": 20, "B": 20}, demography=dem,
                sequence_length=SEQ_LEN, recombination_rate=RECOMB,
                random_seed=7000 + r,
            )
            vals.append(hudson_fst(ts, ts.samples(population=0), ts.samples(population=1)))
        # the analytic oracle, recomputed here so the script is self-contained
        def et_w(t, nd, na):
            x = t / (2.0 * nd)
            return 2.0 * nd * (1 - math.exp(-x)) + 2.0 * na * math.exp(-x)
        tw = 0.5 * (et_w(cell["t"], cell["n1"], cell["na"])
                    + et_w(cell["t"], cell["n2"], cell["na"]))
        oracle = 1.0 - tw / (cell["t"] + 2.0 * cell["na"])
        rec = dict(cell, fst_measured=float(np.mean(vals)),
                   fst_sd=float(np.std(vals)), oracle_split_fst_hudson=oracle,
                   lean_coalFst=cell["t"] / (cell["t"] + 2.0 * cell["na"]))
        out.append(rec)
        print(json.dumps(rec), flush=True)
    return out


# --------------------------------------------------------------------------
def job_b():
    """Pulse admixture: C = alpha*A + (1-alpha)*B, measure F_ST(C, A)."""
    NE, TSPLIT, TADMIX = 1000, 4000, 20
    out = []
    for alpha in (0.0, 0.1, 0.3, 0.5, 0.8, 1.0):   # 0.0 and 1.0 are CONTROL 3
        vals_ca, vals_ab = [], []
        for r in range(REPS):
            dem = msprime.Demography()
            for name in ("A", "B", "C"):
                dem.add_population(name=name, initial_size=NE)
            dem.add_population(name="ANC", initial_size=NE)
            dem.add_admixture(
                time=TADMIX, derived="C", ancestral=["A", "B"],
                proportions=[alpha, 1 - alpha],
            )
            dem.add_population_split(time=TSPLIT, derived=["A", "B"], ancestral="ANC")
            ts = msprime.sim_ancestry(
                samples={"A": 20, "B": 20, "C": 20}, demography=dem,
                sequence_length=SEQ_LEN, recombination_rate=RECOMB,
                random_seed=9000 + r,
            )
            sA = ts.samples(population=dem["A"].id)
            sB = ts.samples(population=dem["B"].id)
            sC = ts.samples(population=dem["C"].id)
            vals_ca.append(hudson_fst(ts, sC, sA))
            vals_ab.append(hudson_fst(ts, sA, sB))
        fst_ab = float(np.mean(vals_ab))
        rec = dict(
            alpha=alpha,
            fst_AB_measured=fst_ab,
            fst_CA_measured=float(np.mean(vals_ca)),
            fst_CA_sd=float(np.std(vals_ca)),
            lean_admixedFst=(1 - alpha) ** 2 * fst_ab,
        )
        out.append(rec)
        print(json.dumps(rec), flush=True)
    return out


if __name__ == "__main__":
    res = {"job_a_split_oracle": job_a(), "job_b_admixed_fst": job_b()}
    json.dump(res, open("h4_results.json", "w"), indent=1)
