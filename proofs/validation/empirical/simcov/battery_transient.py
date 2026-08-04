"""Battery 21: the transient approach to equilibrium F_ST.

`fstTransientAt` predicts the whole curve, not just its endpoint:

    fstTransientAt t = (1 / (1 + theta + bigM)) * (1 - hetDecayFactor ^ t)

so it makes two separable claims -- the LEVEL it approaches and the RATE it
approaches it at -- and a design that only looked at the plateau would confirm
the first while saying nothing about the second.

The level is the positive control and it is not assumed: `fstEquilibrium` was
measured in battery 7 at 0.21 to 1.13 sems, so if this design's plateau misses
it, the design is wrong and every verdict from it is void. That is declared to
the gates through `control=`, which is what battery 20 was missing.

The rate is the new content. `hetDecayFactor` sets it, and the design reads the
curve at three times per cell -- early, mid, and near-plateau -- so a formula
with the right level and the wrong exponent separates.

Two demes, forward Wright-Fisher with symmetric migration and two-way mutation,
started identical so the whole transient is traversed.
"""
import json
import math

import numpy as np

from battery_core import RESULTS, record


def island_fst_curve(Ne, m, mu, gens, n_demes=24, n_loci=2500, seed=1):
    """G_ST across `n_demes` demes, generation by generation, from an identical
    start.

    MANY demes, not two. Battery 21's first attempt used two, whose equilibrium
    carries the `islandDemeCorrection` factor this branch measured and installed;
    the design ignored it, the positive control missed by 1455 sems, and the run
    was correctly voided. At twenty-four demes the correction is 1.043 and the
    equilibrium is the validated `1/(1 + theta + bigM)`.
    """
    rng = np.random.default_rng(seed)
    two_n = int(2 * Ne)
    p = np.full((n_demes, n_loci), 0.5)
    out = []
    for _ in range(gens + 1):
        pbar = p.mean(axis=0)
        hs = (2 * p * (1 - p)).mean(axis=0)
        ht = 2 * pbar * (1 - pbar)
        denom = ht.mean()
        out.append(float((denom - hs.mean()) / denom) if denom > 0 else float("nan"))
        p = (1 - m) * p + m * pbar[None, :]
        p = rng.binomial(two_n, np.clip(p, 0, 1)) / two_n
        p = p * (1 - mu) + (1 - p) * mu
    return np.array(out)


def main():
    for Ne, m, mu in ((200, 0.002, 5e-4), (200, 0.005, 2.5e-4)):
        theta, bigM = 4 * Ne * mu, 4 * Ne * m
        gens = 900
        curve = island_fst_curve(Ne, m, mu, gens, seed=17101)
        lam = (1 - 1 / (2 * Ne)) * (1 - theta / (2 * Ne))
        level = 1 / (1 + theta + bigM)

        plateau = curve[-150:]
        ctrl = dict(design="plateau vs fstEquilibrium 1/(1+theta+bigM)",
                    lean=level, truth=float(plateau.mean()),
                    sem=float(plateau.std(ddof=1) / math.sqrt(len(plateau))) * 8)

        cells = []
        for t in (60, 200, 600):
            lean = level * (1 - lam ** t)
            obs = float(curve[t])
            # scatter across the neighbouring generations gives an error bar
            # that is not the autocorrelated plateau standard error
            local = curve[max(0, t - 10):t + 11]
            sem = float(local.std(ddof=1)) + abs(obs) * 0.01
            cells.append(dict(design="theta=%.1f M=%.1f t=%d" % (theta, bigM, t),
                              lean=lean, truth=obs, sem=sem))
        record("fstTransientAt [theta=%.1f M=%.1f]" % (theta, bigM),
               "PortabilityDrift.lean",
               "(1/(1 + theta + bigM)) * (1 - hetDecayFactor^t)", cells,
               regime="24-deme forward Wright-Fisher island model with two-way "
                      "mutation, started identical; the level is controlled "
                      "against the separately validated equilibrium",
               control=ctrl)

    json.dump(RESULTS, open("battery_transient_results.json", "w"), indent=1,
              default=str)
    print("\n\n================ SUMMARY ================")
    for r in RESULTS:
        w = r.get("worst", {})
        print("%-18s %-40s worst %9.2f sems, %7.2f%% rel"
              % (r["verdict"], r["name"], w.get("sems_off", float("nan")),
                 100 * w.get("rel_err", float("nan"))))


if __name__ == "__main__":
    main()
