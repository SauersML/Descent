"""Battery sld03: `sharedLDRetention` after the body was corrected, on the SAME
design that falsified it.

`battery_transfer.py`'s `test_ld_decay_defs` falsified `exp(-2·r·t_div)` at 13.09
sems and +10.8% relative at `r = 0.05, t = 40`, and the error grew with `r`
exactly as `exp(-2rt)` against `(1-r)^(2t)` requires. The body has now been
corrected to `(1 - recomb)^(2·t_div)`, which is `discreteRecombinationSurvival`
squared at a real generation count.

THE DESIGN IS UNCHANGED, deliberately. Same three `(r, t)` cells, same 400000
replicates, same oracle -- an ancestral haplotype survives intact iff no
recombination falls in `t` meioses, drawn as an exact Bernoulli count with no
model slack anywhere -- and the shared-LD observable is that survival SQUARED,
because two lineages must independently avoid recombination. A corrected body
has to be put back to the measurement that rejected the old one; a new design
that happens to agree would be answering a different question.

The superseded exponential is carried as the competitor, so the run says both
things at once: the corrected body matches, and the body it replaced is
rejected on the same cells. `(1-r)^t` is carried too -- the ploidy factor
dropped -- because `Conventions.sharedLDRetention_uses_ploidy` states that the
exponent's factor of two is the ploidy, and a convention theorem with no
measurement behind it is a naming claim.

FRESHNESS: prints FRESHNESS=OK only if its own source carries the token below,
and `dump_results` records this file's SHA inside the results.
"""
import math
import os

import numpy as np

from battery_core import RESULTS, dump_results, record

FRESH_TOKEN = "SIMCOV-BATTERY-SLD03-GANNET-20260804"


def freshness():
    try:
        src = open(os.path.abspath(__file__)).read()
    except Exception:
        print("FRESHNESS=STALE (cannot read own source)")
        return
    print("FRESHNESS=%s (token %s)"
          % ("OK" if src.count(FRESH_TOKEN) >= 2 else "STALE", FRESH_TOKEN))


def main():
    freshness()
    print("FRESHNESS token literal: SIMCOV-BATTERY-SLD03-GANNET-20260804")
    rng = np.random.default_rng(4201)
    reps = 400000
    cells, c_exp, c_ploidy, cells_disc = [], [], [], []
    control = None
    for r_rate, t in ((0.01, 20), (0.01, 100), (0.05, 40)):
        surv = float(np.mean(rng.random((reps, t)).min(axis=1) >= r_rate))
        sem1 = math.sqrt(surv * (1 - surv) / reps)
        truth = surv ** 2
        sem = 2 * surv * sem1
        lab = "r=%.2f t=%d" % (r_rate, t)
        exact = (1 - r_rate) ** (2 * t)
        old = math.exp(-2 * r_rate * t)
        print("  %-14s two-lineage survival = %.6f ± %.6f | corrected %.6f  "
              "superseded exp %.6f (%+.1f%%)  ploidy-dropped %.6f"
              % (lab, truth, sem, exact, old, 100 * (old / truth - 1),
                 (1 - r_rate) ** t))
        cells.append(dict(design=lab, lean=exact, truth=truth, sem=sem))
        c_exp.append(dict(design=lab, lean=old, truth=truth, sem=sem))
        c_ploidy.append(dict(design=lab, lean=(1 - r_rate) ** t, truth=truth,
                             sem=sem))
        # the ONE-lineage survival on the same draws: an independently known
        # quantity that is not this body, so it can fail
        cells_disc.append(dict(design=lab, lean=(1 - r_rate) ** t, truth=surv,
                               sem=sem1))
        if r_rate == 0.01 and t == 20:
            control = dict(
                design=lab + " [one lineage: discreteRecombinationSurvival]",
                lean=(1 - r_rate) ** t, truth=surv, sem=sem1)

    reg = ("two lineages each surviving t_div meioses without recombination, "
           "400000 replicates, drawn as an exact Bernoulli count with no model "
           "slack; the observable is the single-lineage survival SQUARED. This "
           "is the identical design that falsified the superseded exponential "
           "body, re-run against the corrected one -- same cells, same "
           "replicate count, same oracle")
    record("sharedLDRetention", "DGP.lean", "(1 - recomb)^(2 * t_div)", cells,
           regime=reg, control=control, realised_inputs=True)
    record("sharedLDRetention [superseded exp(-2*r*t) body, competing]",
           "DGP.lean", "exp(-2 * recomb * t_div)", c_exp, regime=reg,
           control=control, realised_inputs=True)
    record("sharedLDRetention [ploidy factor dropped, competing]",
           "DGP.lean", "(1 - recomb)^t_div", c_ploidy, regime=reg,
           control=control, realised_inputs=True)
    record("discreteRecombinationSurvival", "DGP.lean",
           "(1 - recombRate)^tmrca", cells_disc,
           regime="probability no recombination occurs in tmrca meioses, on "
                  "the same draws", realised_inputs=True)

    dump_results("battery_sld03_results.json")
    print("\n================ SUMMARY ================")
    for r in RESULTS:
        w = r.get("worst", {}) or {}
        print("%-24s %-56s worst %9.2f sems, %8.2f%% rel"
              % (r["verdict"], r["name"][:56], w.get("sems_off", float("nan")),
                 100 * w.get("rel_err", float("nan"))))


if __name__ == "__main__":
    main()
