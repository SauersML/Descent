"""Battery 46: the cohort observed effect, given its declared interaction model.

Rebuilt because `cohortObservedEffect` cites `simcov/battery_bulk46.py` for a
table of sems and no such file was ever committed.

WHAT IS AND IS NOT UNDER TEST, because this is the definition where the two are
easiest to confuse. Multiplication remains a DECLARED interaction model rather
than a conclusion drawn from cohort data; a cohort study showing effects that
combine additively would contradict the declaration, not this body. What the
simulation adds is that, GIVEN the declaration, the body is the right function
of it -- the observable is the realised marginal OLS effect in a sample whose
genetic effect was scaled by the modifier, and the SUM reading is rejected on
the same cells.

The modifier is swept across 1 -- 0.5, 0.6, 1.0, 1.8 -- because 1 is the only
place a sum and a product can be confused for one another, and one cell gives
the genetic effect a NEGATIVE sign, where the two readings differ in sign as
well as in magnitude.

FRESHNESS: prints FRESHNESS=OK only if its own source carries the token below,
and `dump_results` records this file's SHA inside the results.
"""
import math
import os

import numpy as np

from battery_core import RESULTS, dump_results, record

FRESH_TOKEN = "SIMCOV-BATTERY-BULK46-HOBBY-20260805"

# `realised_inputs=True`: the genetic effect and the modifier are the exact
# constants the phenotypes were built from, not estimates off the same
# individuals the OLS slope is measured on.
MODEL = dict(realised_inputs=True, argument_source="model")


def freshness():
    try:
        src = open(os.path.abspath(__file__)).read()
    except OSError:
        print("FRESHNESS=STALE (cannot read own source)")
        return
    print("FRESHNESS=%s (token %s)"
          % ("OK" if src.count(FRESH_TOKEN) >= 2 else "STALE", FRESH_TOKEN))


def blocked(vals):
    a = np.asarray(vals, float)
    return float(a.mean()), float(a.std(ddof=1) / math.sqrt(a.size))


def group_cohort():
    print("\n===== GROUP COHORT  cohortObservedEffect = genetic * modifier")
    rng = np.random.default_rng(46001)
    n_blocks, per_block = 20, 100000

    cells, c_sum = [], []
    control = None
    for g_eff, mod in ((0.8, 0.5), (0.4, 0.6), (0.7, 1.8), (-0.6, 1.8)):
        slopes = []
        for _ in range(n_blocks):
            g = rng.standard_normal(per_block)
            y = (g_eff * mod) * g + rng.standard_normal(per_block)
            slopes.append(float(np.dot(g, y) / np.dot(g, g)))
        got, sem = blocked(slopes)
        lab = "gen=%+.1f mod=%.1f" % (g_eff, mod)
        print("  %-18s measured %+.5f +/- %.5f   product %+.5f   sum %+.5f"
              % (lab, got, sem, g_eff * mod, g_eff + mod))
        cells.append(dict(design=lab, lean=g_eff * mod, truth=got,
                          sem=max(sem, 1e-12)))
        c_sum.append(dict(design=lab, lean=g_eff + mod, truth=got,
                          sem=max(sem, 1e-12)))

    # POSITIVE CONTROL: at a modifier of exactly 1 the observed effect must be
    # the raw genetic effect, on the same code path. It can fail -- a
    # standardisation slip in the dosage, a scale error in the noise -- and it
    # is not the cell under test.
    slopes = []
    for _ in range(n_blocks):
        g = rng.standard_normal(per_block)
        y = 0.9 * g + rng.standard_normal(per_block)
        slopes.append(float(np.dot(g, y) / np.dot(g, g)))
    cmean, csem = blocked(slopes)
    print("  CONTROL modifier=1, genetic=0.9: measured %+.5f +/- %.5f"
          % (cmean, csem))
    control = dict(design="modifier=1 [observed effect = raw genetic effect]",
                   lean=0.9, truth=cmean, sem=max(csem, 1e-12))

    reg = ("2e6 individuals in 20 independent blocks of 1e5, standardised "
           "dosage so the marginal OLS slope IS the effect; the phenotype is "
           "built as (genetic * modifier) * dosage + noise. The modifier is "
           "swept across 1, the only value where a sum and a product coincide, "
           "and one cell gives the genetic effect a NEGATIVE sign. What is "
           "measured is that the body is the right function OF the declared "
           "multiplicative interaction, not that the interaction is "
           "multiplicative")
    record("cohortObservedEffect", "LongitudinalPortability.lean",
           "geneticEffect * environmentModifier", cells, regime=reg,
           control=control, **MODEL)
    record("cohortObservedEffect [sum reading, competing]",
           "LongitudinalPortability.lean",
           "geneticEffect + environmentModifier", c_sum, regime=reg,
           control=control, **MODEL)


def main():
    freshness()
    print("FRESHNESS token literal: SIMCOV-BATTERY-BULK46-HOBBY-20260805")
    group_cohort()
    dump_results("battery_bulk46_results.json",
                 battery_source=os.path.abspath(__file__))
    print("\n================ SUMMARY ================")
    for r in RESULTS:
        w = r.get("worst", {})
        print("%-12s %-58s worst %9.2f sems, %7.2f%% rel"
              % (r["verdict"], r["name"], w.get("sems_off", float("nan")),
                 100 * w.get("rel_err", float("nan"))))


if __name__ == "__main__":
    main()
