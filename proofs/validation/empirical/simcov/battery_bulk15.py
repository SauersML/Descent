"""Battery 30: the heterozygosity recurrences, on the model they actually declare.

Battery 29 ran these against a BIALLELIC Wright-Fisher sim and got 13% off after
fifteen iterations. That was the oracle's fault, and the arithmetic says exactly
why. Under biallelic two-way mutation at rate `mu`, `p - 1/2` contracts by
`(1 - 2 mu)` and `H = 2p(1-p) = 1/2 - 2(p - 1/2)^2`, so the exact input term is

    H' = H_drift + 2 mu (1 - 2 H_drift)          [biallelic]

whereas the Lean body has

    H' = H_drift + 2 mu (1 - H_drift)            [infinite alleles]

and the docstring declares the second: "creates new heterozygosity at rate 2 mu
from homozygous sites" is the infinite-alleles statement, where a new mutation is
always a novel allele and a homozygote becomes heterozygous with probability
2 mu. So the definition is being read correctly and the previous oracle was the
wrong model.

That mistake is worth stating separately, because it is a fact about the HARNESS:
the two forms differ by `2 mu H`, which is O(mu) per step, so at ONE step it hides
under the noise and only compounding exposes it. `hetStepWithMutation` carries a
VALIDATED status earned against that same biallelic oracle at one step, and this
battery re-runs it here to find out whether that status survives.

Both candidate input terms are carried through as competing predictions so the
data chooses between them rather than the choice being argued.

Positive control: the plateau homozygosity must reproduce `1/(1 + theta)`, which
is independently validated as `fstMutationDriftEquilibrium`, so the engine has to
reproduce a known answer before its trajectory is believed.
"""
import json
import math

import numpy as np

from battery_core import RESULTS, record


def ia_het_trajectory(Ne, mu, gens, reps, seed):
    """Infinite-alleles Wright-Fisher; unbiased heterozygosity per generation.

    Starts monomorphic, so the trajectory rises from H = 0 and spends its whole
    length far from the plateau -- which is where a recurrence's slope is
    actually under test.
    """
    rng = np.random.default_rng(seed)
    two_n = 2 * Ne
    state = np.zeros((reps, two_n), dtype=np.int64)
    nxt = np.ones(reps, dtype=np.int64)
    Hm, Hs = [], []
    for g in range(gens + 1):
        vals = np.empty(reps)
        for r in range(reps):
            c = np.bincount(state[r]).astype(float)
            # unbiased homozygosity: sampling without replacement within the deme
            vals[r] = 1.0 - (c * (c - 1)).sum() / (two_n * (two_n - 1))
        Hm.append(float(vals.mean()))
        Hs.append(float(vals.std(ddof=1) / math.sqrt(reps)))
        if g == gens:
            break
        idx = rng.integers(0, two_n, size=(reps, two_n))
        state = np.take_along_axis(state, idx, axis=1)
        hit = rng.random((reps, two_n)) < mu
        for r in range(reps):
            k = int(hit[r].sum())
            if k:
                state[r][hit[r]] = nxt[r] + np.arange(k)
                nxt[r] += k
            _, state[r] = np.unique(state[r], return_inverse=True)
        nxt[:] = state.max(axis=1) + 1
    return np.array(Hm), np.array(Hs)


def main():
    STEPS = 15
    cells_ia, cells_bi, cells_step, cells_affine = [], [], [], []
    ctrl = None
    for Ne, mu in ((100, 2e-3), (50, 5e-3), (200, 1e-3)):
        theta = 4 * Ne * mu
        gens = 12 * Ne
        H, S = ia_het_trajectory(Ne, mu, gens, reps=220, seed=25000 + Ne)
        plateau = float(H[-3 * Ne:].mean())
        known = theta / (1 + theta)
        print("  Ne=%d mu=%.0e theta=%.2f: plateau H = %.4f, known "
              "theta/(1+theta) = %.4f  (%+.1f%%)"
              % (Ne, mu, theta, plateau, known, 100 * (plateau - known) / known))
        if ctrl is None:
            ctrl = dict(design="plateau H vs the validated theta/(1+theta) "
                               "(Ne=%d, theta=%.2f)" % (Ne, theta),
                        lean=known, truth=plateau,
                        sem=float(H[-3 * Ne:].std(ddof=1)
                                  / math.sqrt(3 * Ne)))

        # iterate from a start well off the plateau
        for t0 in (Ne // 4, Ne // 2, Ne):
            h0 = float(H[t0])
            lab = "Ne=%d theta=%.2f, t=%d->%d (H0=%.4f)" % (Ne, theta, t0,
                                                            t0 + STEPS, h0)
            hi = hb = h0
            for _ in range(STEPS):
                hi = (1 - 1 / (2 * Ne)) * hi + 2 * mu * (1 - hi)
                hb = (1 - 1 / (2 * Ne)) * hb + 2 * mu * (1 - 2 * hb)
            tgt, sem = float(H[t0 + STEPS]), float(S[t0 + STEPS])
            cells_ia.append(dict(design=lab, lean=hi, truth=tgt, sem=sem))
            cells_bi.append(dict(design=lab, lean=hb, truth=tgt, sem=sem))

            lam, Hstar = 1 - 1 / (2 * Ne) - 2 * mu, theta / (1 + theta)
            a = h0
            for _ in range(STEPS):
                a = lam * a + (1 - lam) * Hstar
            cells_affine.append(dict(design=lab, lean=a, truth=tgt, sem=sem))

            # and the SINGLE step, the reading hetStepWithMutation carries
            cells_step.append(dict(design="Ne=%d theta=%.2f, one step at t=%d"
                                          % (Ne, theta, t0),
                                   lean=(1 - 1 / (2 * Ne)) * h0
                                        + 2 * mu * (1 - h0),
                                   truth=float(H[t0 + 1]),
                                   sem=float(S[t0 + 1])))

    record("hetMutationDriftRecurrence", "PopulationGeneticsFoundations.lean",
           "H' = (1 - 1/(2Ne)) H + 2 mu (1 - H), iterated 15 times", cells_ia,
           regime="INFINITE-ALLELES Wright-Fisher, which is the model the "
                  "docstring declares; started monomorphic so the whole "
                  "trajectory sits far from the plateau where the slope is "
                  "what is being measured", control=ctrl)
    record("hetMutationDriftRecurrence [biallelic input term 2mu(1 - 2H), the "
           "competing candidate]", "PopulationGeneticsFoundations.lean",
           "H' = (1 - 1/(2Ne)) H + 2 mu (1 - 2 H), iterated 15 times", cells_bi,
           regime="the same infinite-alleles trajectory; this is the term that "
                  "is exact for a BIALLELIC model, carried through so the data "
                  "chooses between the two readings", control=ctrl)
    record("hetMutationRecurrence", "PopulationGeneticsFoundations.lean",
           "H' = lam H + (1 - lam) Hstar, lam = 1 - 1/(2Ne) - 2mu, "
           "Hstar = theta/(1+theta)", cells_affine,
           regime="the same trajectory in affine coordinates, compared against "
                  "the SIMULATION rather than against the sibling recurrence",
           control=ctrl)
    record("hetStepWithMutation [re-run on the infinite-alleles oracle]",
           "PortabilityDrift.lean", "(1 - 1/(2Ne)) H + 2 mu (1 - H)",
           cells_step,
           regime="ONE step, the reading this definition already carries a "
                  "VALIDATED status for; re-measured here because that status "
                  "was earned against a biallelic oracle whose input term "
                  "differs by O(mu) per step", control=ctrl)

    json.dump(RESULTS, open("battery_bulk15_results.json", "w"), indent=1,
              default=str)
    print("\n\n================ SUMMARY ================")
    for r in RESULTS:
        w = r.get("worst", {})
        print("%-20s %-62s worst %9.2f sems, %7.2f%% rel"
              % (r["verdict"], r["name"], w.get("sems_off", float("nan")),
                 100 * w.get("rel_err", float("nan"))))


if __name__ == "__main__":
    main()
