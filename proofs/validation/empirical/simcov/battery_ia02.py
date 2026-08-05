"""Battery ia02: `hetMutationFloor` under infinite alleles, on a DISCRETE genome.

`battery_bulk20.py` `group_b` returned VOID because its Ewens `E[K]` control
missed by inf sems, and the control was right to fire. The design called

    msprime.sim_ancestry(..., sequence_length=1, discrete_genome=False)
    msprime.sim_mutations(..., model=msprime.InfiniteAlleles(),
                          discrete_genome=False)

and `InfiniteAlleles` needs a DISCRETE genome. On a continuous one every
mutation lands at its own real-valued position, so a single locus carrying `k`
mutations is reported as `k` separate biallelic SITES rather than one site with
`k+1` allelic states. `group_b` then read `mts.variants()` and took the FIRST
variant, which has two alleles no matter how large `theta` is -- so the measured
allele count `K` sat near 2 across a hundredfold sweep in `theta` while Ewens
predicts it rising from 1.4 to 25, and the control diverged.

That is why this battery exists rather than a patch to a docstring: the same
trap has now bitten `hetMutationFloor` TWICE IN OPPOSITE DIRECTIONS -- once
scoring it a 21-sem falsification, once voiding it -- and neither reading was
about the definition. The fix is `sequence_length=1` with msprime's default
discrete genome, so every mutation falls on the single integer site and the
infinite-alleles states accumulate there.

THE CONTROL IS THE POINT AND IT IS NOT DROPPED. Ewens' sampling formula gives
`E[K] = sum_i theta/(theta+i-1)` for a sample of `n` genes, an independent
classical result that no body under test appears in. It is checked FIRST, and
if it misses, no verdict is read off this run. A design that cannot reproduce a
known result has no standing to report a new one.

Competitors on the same cells, so the MATCH is not free:
    theta/(1+theta)     the body
    theta/(1+2*theta)   the diploid-convention slip
    2*theta/(1+2*theta) the same slip with the numerator carried too

Conventions:
  * `theta = 4*Ne*mu` is computed from the simulation's OWN `Ne` and `mu`, which
    are exact inputs rather than estimates, so there is no nominal-versus-
    realised gap to close here -- unlike a genetic correlation read off a finite
    effect vector.
  * heterozygosity is `1 - sum p_i^2` over the WHOLE sample with the unbiased
    `n/(n-1)` correction, never conditioned on the sample being polymorphic.

FRESHNESS: prints FRESHNESS=OK only if its own source carries the token below,
and `dump_results` records this file's SHA inside the results.
"""
import os

import numpy as np

import simlib
from battery_core import RESULTS, dump_results, record

FRESH_TOKEN = "SIMCOV-BATTERY-IA02-FULMAR-20260804"


def freshness():
    try:
        src = open(os.path.abspath(__file__)).read()
    except Exception:
        print("FRESHNESS=STALE (cannot read own source)")
        return
    print("FRESHNESS=%s (token %s)"
          % ("OK" if src.count(FRESH_TOKEN) >= 2 else "STALE", FRESH_TOKEN))


def one_locus(msprime, Ne, mu, seed):
    """(unbiased heterozygosity, allele count) at ONE discrete infinite-alleles
    locus.

    `sequence_length=1` with msprime's DEFAULT discrete genome puts every
    mutation on the single integer site, which is what makes the site's allelic
    states the infinite-alleles states of the sample. No `discrete_genome=False`
    anywhere: that is the defect this battery exists to correct.
    """
    ts = msprime.sim_ancestry(samples=50, population_size=Ne,
                              sequence_length=1, random_seed=seed)
    mts = msprime.sim_mutations(ts, rate=mu, model=msprime.InfiniteAlleles(),
                                random_seed=seed + 100000)
    var = next(iter(mts.variants()), None)
    if var is None:
        states = np.zeros(mts.num_samples, dtype=int)
    else:
        states = np.asarray(var.genotypes)
    _, counts = np.unique(states, return_counts=True)
    n = states.size
    p = counts / n
    return (float(n / (n - 1.0) * (1.0 - np.sum(p ** 2))), float(counts.size))


def main():
    freshness()
    print("FRESHNESS token literal: SIMCOV-BATTERY-IA02-FULMAR-20260804")
    import msprime

    Ne, reps = 1000, 200
    n_genes = 100
    thetas = (0.1, 0.5, 1.0, 3.0, 10.0)

    # ---- the control FIRST, before any verdict is read off this engine -----
    print("\n=== control: Ewens E[K] against the same samples")
    ewens_rows = []
    measured = {}
    for theta in thetas:
        mu = theta / (4.0 * Ne)
        hets, ks = [], []
        for r in range(reps):
            h, k = one_locus(msprime, Ne, mu, 900001 + r)
            hets.append(h)
            ks.append(k)
        measured[theta] = (simlib.summarize(hets), simlib.summarize(ks))
        ewens = sum(theta / (theta + i - 1.0) for i in range(1, n_genes + 1))
        sk = measured[theta][1]
        off = abs(ewens - sk["mean"]) / max(sk["sem"], 1e-12)
        print("  theta=%5.1f   Ewens E[K] = %6.2f   measured K = %6.2f ± %.2f"
              "   (%.2f sems)" % (theta, ewens, sk["mean"], sk["sem"], off))
        ewens_rows.append(dict(design="theta=%.1f" % theta, lean=ewens,
                               truth=sk["mean"], sem=sk["sem"]))

    ctrl_theta = 1.0
    sk = measured[ctrl_theta][1]
    ctrl_ewens = sum(ctrl_theta / (ctrl_theta + i - 1.0)
                     for i in range(1, n_genes + 1))
    control = dict(design="theta=1.0 [Ewens E(K), independent of every body "
                          "under test]",
                   lean=ctrl_ewens, truth=sk["mean"], sem=sk["sem"])

    reg_k = ("single-locus infinite-alleles mutation at coalescent "
             "equilibrium, Ne = 1000, 100 sampled genes, %d replicates, "
             "sequence_length = 1 on msprime's DEFAULT DISCRETE genome so all "
             "mutations fall on one site; the observable is the realised "
             "number of distinct allelic states" % reps)
    record("[control] Ewens expected allele count on the same samples",
           "PortabilityDrift.lean", "sum_i theta/(theta+i-1)", ewens_rows,
           regime=reg_k, realised_inputs=True)

    # ---- the body, on the same samples ------------------------------------
    print("\n=== hetMutationFloor, with two competing readings")
    cells, c_den, c_both = [], [], []
    for theta in thetas:
        s = measured[theta][0]
        lab = "theta=4*Ne*mu=%.1f" % theta
        print("  %-22s H = %.5f ± %.5f | body %.5f  1+2t %.5f  2t/(1+2t) %.5f"
              % (lab, s["mean"], s["sem"], theta / (1 + theta),
                 theta / (1 + 2 * theta), 2 * theta / (1 + 2 * theta)))
        cells.append(dict(design=lab, lean=theta / (1.0 + theta),
                          truth=s["mean"], sem=s["sem"]))
        c_den.append(dict(design=lab, lean=theta / (1.0 + 2.0 * theta),
                          truth=s["mean"], sem=s["sem"]))
        c_both.append(dict(design=lab,
                           lean=2.0 * theta / (1.0 + 2.0 * theta),
                           truth=s["mean"], sem=s["sem"]))
    reg_h = ("the same samples as the control above; heterozygosity is "
             "1 - sum p_i^2 over the WHOLE sample with the unbiased n/(n-1) "
             "correction, never conditioned on polymorphism. theta = 4*Ne*mu "
             "comes from the simulation's own exact Ne and mu, so no nominal-"
             "versus-realised substitution occurs. theta is swept a "
             "hundredfold, over which the three readings separate by up to "
             "a factor of two")
    record("hetMutationFloor", "PortabilityDrift.lean",
           "4 * Ne * mu / (1 + 4 * Ne * mu)", cells, regime=reg_h,
           control=control, realised_inputs=True)
    record("hetMutationFloor [denominator 1 + 2*theta, competing]",
           "PortabilityDrift.lean", "theta / (1 + 2*theta)", c_den,
           regime=reg_h, control=control, realised_inputs=True)
    record("hetMutationFloor [2*theta/(1 + 2*theta), competing]",
           "PortabilityDrift.lean", "2*theta / (1 + 2*theta)", c_both,
           regime=reg_h, control=control, realised_inputs=True)

    dump_results("battery_ia02_results.json")
    print("\n================ SUMMARY ================")
    for r in RESULTS:
        w = r.get("worst", {}) or {}
        print("%-24s %-58s worst %9.2f sems, %8.2f%% rel"
              % (r["verdict"], r["name"][:58], w.get("sems_off", float("nan")),
                 100 * w.get("rel_err", float("nan"))))


if __name__ == "__main__":
    main()
