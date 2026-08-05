"""Battery 38: do theta and bigM ADD in the equilibrium denominator?

`EvolutionaryParameters.fstEquilibrium = 1 / (1 + theta + bigM)` asserts that
mutation and migration enter the identity-by-descent denominator ADDITIVELY.
That is a real claim with obvious alternatives -- they could compose
multiplicatively, `1/((1+theta)(1+bigM))`, or the smaller could be negligible --
and the alternatives coincide with the body whenever either parameter is near
zero. So the design puts BOTH at order one simultaneously, which is the only
regime where additivity is on trial.

Oracle: a two-deme island model under msprime's INFINITE ALLELES model, with the
observable the probability that two alleles drawn from DIFFERENT demes are
identical by state. Under mutation-drift-migration balance that identity
probability is what `1/(1 + theta + bigM)` predicts. Nothing evaluates the body.

Competitors on the same cells:
  1 / ((1 + theta) * (1 + bigM))   -- multiplicative composition
  1 / (1 + theta)                  -- migration ignored
  1 / (1 + bigM)                   -- mutation ignored

Control: with mutation switched almost off, the identity probability must
approach the pure migration-drift value, which is the regime the corpus's
`fstMigrationDriftEquilibrium` is written for.
"""
import json
import math

import numpy as np

import simlib
from battery_core import RESULTS, record

NE = 500


def identities(theta, bigM, reps=40, seed=38001):
    """(F_within, F_between): identity-by-state probabilities.

    The first version returned only F_between and compared it directly against
    `1/(1 + theta + bigM)`. That was the wrong observable: `fstEquilibrium` is a
    DIFFERENTIATION measure, and in identity terms
    `F_ST = (F_within - F_between) / (1 - F_within's complement)`. Reading it as
    a bare identity probability made the control demand 0.33 where the truth is
    ~1 -- with mutation switched off nobody carries a derived allele, so every
    pair is identical whatever the migration rate.
    """
    import msprime
    mu = theta / (4.0 * NE)
    m = bigM / (4.0 * NE)
    dem = msprime.Demography.island_model([NE, NE], migration_rate=m)
    vals = []
    for r in range(reps):
        ts = msprime.sim_ancestry(samples={"pop_0": 25, "pop_1": 25},
                                  demography=dem, sequence_length=1,
                                  random_seed=seed + r)
        mts = msprime.sim_mutations(ts, rate=mu,
                                    model=msprime.InfiniteAlleles(),
                                    random_seed=seed + 7000 + r)
        st = None
        for v in mts.variants():
            st = np.asarray(v.genotypes)
            break
        if st is None:
            # No mutation fell on this replicate: every sample carries the
            # ancestral allele, so BOTH identities are 1. Appending a bare
            # float here instead of the pair crashed a re-run whose seeds
            # happened to produce a mutation-free replicate -- the original
            # seeds never took this path, so the bug sat latent.
            vals.append((1.0, 1.0))
            continue
        A = st[mts.samples(population=0)]
        B = st[mts.samples(population=1)]
        between = float(np.mean(A[:, None] == B[None, :]))
        wa = float((np.sum(A[:, None] == A[None, :]) - A.size)
                   / max(A.size * (A.size - 1), 1))
        wb = float((np.sum(B[:, None] == B[None, :]) - B.size)
                   / max(B.size * (B.size - 1), 1))
        vals.append(((wa + wb) / 2.0, between))
    w = simlib.summarize([v[0] for v in vals])
    b = simlib.summarize([v[1] for v in vals])
    return w, b


def main():
    cells, c_mult, c_theta, c_m = [], [], [], []
    control = None
    for theta, bigM in ((1.0, 1.0), (2.0, 0.5), (0.5, 2.0), (3.0, 3.0)):
        sw, sb = identities(theta, bigM)
        # F_ST from identity probabilities
        fst = (sw["mean"] - sb["mean"]) / max(1 - sb["mean"], 1e-9)
        sem = math.hypot(sw["sem"], sb["sem"]) / max(1 - sb["mean"], 1e-9)
        s = dict(mean=fst, sem=sem)
        lean = 1.0 / (1 + theta + bigM)
        lab = "theta=%.1f bigM=%.1f" % (theta, bigM)
        print("  %-22s F_w=%.4f F_b=%.4f  F_ST=%.5f ± %.5f | add %.5f  mult %.5f  "
              "theta-only %.5f  M-only %.5f"
              % (lab, sw["mean"], sb["mean"], s["mean"], s["sem"], lean,
                 1.0 / ((1 + theta) * (1 + bigM)),
                 1.0 / (1 + theta), 1.0 / (1 + bigM)))
        cells.append(dict(design=lab, lean=lean, truth=s["mean"],
                          sem=max(s["sem"], 1e-6)))
        c_mult.append(dict(design=lab, lean=1.0 / ((1 + theta) * (1 + bigM)),
                           truth=s["mean"], sem=max(s["sem"], 1e-6)))
        c_theta.append(dict(design=lab, lean=1.0 / (1 + theta),
                            truth=s["mean"], sem=max(s["sem"], 1e-6)))
        c_m.append(dict(design=lab, lean=1.0 / (1 + bigM), truth=s["mean"],
                        sem=max(s["sem"], 1e-6)))
    # Control: at HIGH migration the two demes merge into ONE population of
    # size 2*Ne, so the within-deme identity is the panmictic infinite-alleles
    # value at the METAPOPULATION theta -- which is 2*theta, not theta, because
    # `theta` here is scaled by the deme size. A previous version demanded
    # 1/(1+theta) and failed for exactly that factor of two, which is the same
    # deme-count blindness the corpus records on `fstMigrationDriftEquilibrium`.
    # The panmictic law itself is separately VALIDATED as `hetMutationFloor`
    # (battery_bulk20b) over a hundredfold theta sweep.
    theta_c = 1.0
    cw, cb = identities(theta_c, 200.0, seed=38900)
    expect = 1.0 / (1 + 2 * theta_c)
    print("  CONTROL theta=%.1f bigM=200: F_within=%.5f ± %.5f "
          "(1/(1+2*theta)=%.5f)" % (theta_c, cw["mean"], cw["sem"], expect))
    control = dict(design="high migration [F_within = 1/(1+2*theta)]",
                   lean=expect, truth=cw["mean"], sem=max(cw["sem"], 1e-6))
    reg = ("two-deme island model at Ne = 500 under msprime's INFINITE ALLELES "
           "model; the observable is the probability that two alleles drawn "
           "from DIFFERENT demes are identical by state, over all ordered cross "
           "pairs and 40 replicates. theta and bigM are both held at order one "
           "so their composition is on trial rather than one of them vanishing")
    record("EvolutionaryParameters.fstEquilibrium", "DGP.lean",
           "1 / (1 + theta + bigM)", cells, regime=reg, control=control)
    record("fstEquilibrium [multiplicative composition, competing]", "DGP.lean",
           "1 / ((1 + theta) * (1 + bigM))", c_mult, regime=reg,
           control=control)
    record("fstEquilibrium [migration ignored, competing]", "DGP.lean",
           "1 / (1 + theta)", c_theta, regime=reg, control=control)
    record("fstEquilibrium [mutation ignored, competing]", "DGP.lean",
           "1 / (1 + bigM)", c_m, regime=reg, control=control)
    json.dump(RESULTS, open("battery_bulk38_results.json", "w"), indent=1,
              default=str)
    print("\n================ SUMMARY ================")
    for r in RESULTS:
        w = r.get("worst", {})
        print("%-22s %-52s worst %9.2f sems, %7.2f%% rel"
              % (r["verdict"], r["name"], w.get("sems_off", float("nan")),
                 100 * w.get("rel_err", float("nan"))))


if __name__ == "__main__":
    main()
