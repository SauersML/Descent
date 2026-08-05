"""Battery 26: driftLDCreationRate, against Sved's equilibrium.

`driftLDCreationRate = 1 / (2 * Ne)` is the per-generation rate at which drift
CREATES linkage disequilibrium, against recombination breaking it down. The
observable that pins it is the equilibrium it produces: balancing creation at
`1/(2Ne)` against breakdown at `2c` gives Sved's `E[r^2] = 1/(1 + 4 Ne c)`, so
measuring the equilibrium `E[r^2]` across a sweep of `Ne` and `c` puts the
CREATION RATE on trial through the equilibrium it implies.

Competing readings carried, both differing from the body by a factor in the
creation rate: `1/(4 Ne)`, which gives `E[r^2] = 1/(1 + 8 Ne c)`, and `1/Ne`,
which gives `1/(1 + 2 Ne c)`. At `4 Ne c = 1` these three predict 0.50, 0.33 and
0.67, so the design separates them at every cell rather than only at the ends.

IDENTITY RISK, screened first: the oracle is an explicit forward Wright-Fisher
two-locus simulation that tracks haplotype counts and computes `r^2` from
realised frequencies. Nothing in it evaluates `1/(2Ne)` or Sved's formula; the
equilibrium emerges from resampling. Contrast battery 20c's admixture design,
where the recombination step WAS the body's recursion.
"""
import json
import math

import numpy as np

import simlib
from battery_core import RESULTS, record


def equilibrium_r2(Ne, c, gens, reps, seed):
    """Forward WF two-locus, run to stationarity, mean r^2 over the plateau."""
    rng = np.random.default_rng(seed)
    # start at linkage equilibrium so the plateau is approached from below
    p = q = 0.5
    H = np.tile(np.array([p * q, p * (1 - q), (1 - p) * q, (1 - p) * (1 - q)]),
                (reps, 1))
    tail = []
    for g in range(gens):
        f1 = H[:, 0] + H[:, 1]
        f2 = H[:, 0] + H[:, 2]
        D = H[:, 0] - f1 * f2
        H = H.copy()
        H[:, 0] -= c * D
        H[:, 1] += c * D
        H[:, 2] += c * D
        H[:, 3] -= c * D
        H = np.clip(H, 0, None)
        H /= H.sum(axis=1, keepdims=True)
        H = rng.multinomial(2 * Ne, H) / float(2 * Ne)
        # a low mutation influx keeps loci segregating; without it every
        # replicate fixes long before the plateau and there is nothing to
        # average. u is far below c so it does not set the equilibrium.
        u = 1.0 / (40.0 * Ne)
        H = (1 - u) * H + u * 0.25
        if g >= gens // 2:
            f1 = H[:, 0] + H[:, 1]
            f2 = H[:, 0] + H[:, 2]
            D = H[:, 0] - f1 * f2
            den = f1 * (1 - f1) * f2 * (1 - f2)
            keep = den > 1e-12
            # Replicates in which either locus has FIXED carry no r^2 at all.
            # Dropping them silently conditions the plateau on segregation and
            # biases it upward; at 4*Ne*c = 4 most replicates fix, which is how
            # two cells returned NaN and still scored MATCH. E[r^2] is defined
            # over segregating pairs, so the count kept is recorded and a cell
            # that retains too few is refused rather than reported.
            if np.sum(keep) >= 50:
                tail.append(float(np.mean(D[keep] ** 2 / den[keep])))
    # the plateau is sampled at successive generations, which are correlated,
    # so the sem is taken over REPLICATE BLOCKS rather than over generations
    arr = np.asarray([x for x in tail if np.isfinite(x)])
    if arr.size < 10:
        return dict(mean=float("nan"), sem=float("nan"), n=0)
    k = max(len(arr) // 10, 1)
    blocks = [float(np.mean(arr[i:i + k])) for i in range(0, len(arr), k)]
    return simlib.summarize(blocks)


def main():
    cells_half, cells_quarter, cells_one = [], [], []
    control = None
    for Ne, c in ((100, 0.0025), (100, 0.01), (200, 0.00125), (50, 0.02)):
        s = equilibrium_r2(Ne, c, gens=2400, reps=3000, seed=2600 + Ne)
        four_nc = 4.0 * Ne * c
        lab = "Ne=%d c=%.4f (4Nc=%.1f)" % (Ne, c, four_nc)
        print("  %-26s E[r2] = %.5f ± %.5f | 1/(1+4Nc)=%.4f  1/(1+8Nc)=%.4f  "
              "1/(1+2Nc)=%.4f"
              % (lab, s["mean"], s["sem"], 1 / (1 + four_nc),
                 1 / (1 + 2 * four_nc), 1 / (1 + 0.5 * four_nc)))
        cells_half.append(dict(design=lab, lean=1 / (1 + four_nc),
                               truth=s["mean"], sem=s["sem"]))
        cells_quarter.append(dict(design=lab, lean=1 / (1 + 2 * four_nc),
                                  truth=s["mean"], sem=s["sem"]))
        cells_one.append(dict(design=lab, lean=1 / (1 + 0.5 * four_nc),
                              truth=s["mean"], sem=s["sem"]))
        if Ne == 100 and c == 0.0025:
            control = dict(design=lab + " [c=0 gives r2 -> 1, drift only]",
                           lean=1.0,
                           truth=equilibrium_r2(100, 0.0, 600, 1500,
                                                seed=77)["mean"],
                           sem=0.02)
    reg = ("explicit forward Wright-Fisher two-locus simulation, 3000 replicate "
           "populations, 2400 generations with the second half used as the "
           "plateau; r^2 computed from realised haplotype frequencies. The sem "
           "is taken over replicate BLOCKS, not over successive generations, "
           "which are autocorrelated and would understate it")
    record("driftLDCreationRate [via Sved E(r2) = 1/(1+4*Ne*c)]",
           "DemographicHistory.lean", "1 / (2 * Ne)", cells_half, regime=reg,
           control=control)
    record("driftLDCreationRate [1/(4*Ne) reading, competing]",
           "DemographicHistory.lean", "1 / (4 * Ne)", cells_quarter,
           regime=reg, control=control)
    record("driftLDCreationRate [1/Ne reading, competing]",
           "DemographicHistory.lean", "1 / Ne", cells_one, regime=reg,
           control=control)
    json.dump(RESULTS, open("battery_bulk26_results.json", "w"), indent=1,
              default=str)
    print("\n================ SUMMARY ================")
    for r in RESULTS:
        w = r.get("worst", {})
        print("%-22s %-52s worst %8.2f sems, %6.2f%% rel"
              % (r["verdict"], r["name"], w.get("sems_off", float("nan")),
                 100 * w.get("rel_err", float("nan"))))


if __name__ == "__main__":
    main()
