"""selectionMigrationEquilibrium = s/(s+m)  (PopulationGeneticsFoundations.lean:197)

Docstring: "For a selected allele with advantage s in one population and
migration rate m: p_eq ~ s/(s+m) in the favored population."

The classical continent-island result is p_eq = 1 - m/s for m < s, and the
allele is LOST for m >= s: migration swamps selection.  s/(s+m) instead returns
1/2 at m = s and stays positive for arbitrarily large m, so the two differ
qualitatively, not just numerically.

Ground truth: iterate the deterministic recursion to equilibrium under both
orderings of the selection and migration steps, so the answer does not depend
on that arbitrary choice.
"""
from __future__ import annotations

import json
import sys

import numpy as np


def lean(s, m):
    return s / (s + m)


def classical(s, m):
    return max(0.0, 1.0 - m / s)


def iterate(s, m, sel_first=True, iters=2_000_000):
    p = 0.5
    for _ in range(iters):
        prev = p
        if sel_first:
            p = p * (1 + s) / (1 + s * p)      # selection favours the allele
            p = (1 - m) * p                    # immigrants carry it at freq 0
        else:
            p = (1 - m) * p
            p = p * (1 + s) / (1 + s * p)
        if abs(p - prev) < 1e-14:
            break
        if p < 1e-15:
            return 0.0
    return float(p)


def main():
    rows = []
    print(f"{'s':>6} {'m':>6} {'m/s':>6} {'sim(sel1st)':>12} {'sim(mig1st)':>12} "
          f"{'classical':>10} {'lean s/(s+m)':>13}")
    for s in (0.1, 0.2):
        for ratio in (0.1, 0.3, 0.5, 0.8, 1.0, 1.5, 2.0):
            m = s * ratio
            a = iterate(s, m, True)
            b = iterate(s, m, False)
            rows.append(dict(s=s, m=m, ratio=ratio, sim_sel_first=a,
                             sim_mig_first=b, classical=classical(s, m),
                             lean=lean(s, m)))
            print(f"{s:6.2f} {m:6.3f} {ratio:6.2f} {a:12.5f} {b:12.5f} "
                  f"{classical(s, m):10.5f} {lean(s, m):13.5f}")
    with open(sys.argv[1] if len(sys.argv) > 1 else "selmig.json", "w") as fh:
        json.dump(rows, fh)
    print("\nAt m >= s the allele is lost (simulation -> 0) but the definition "
          "returns >= 1/2.")


if __name__ == "__main__":
    main()
