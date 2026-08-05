"""Battery 56: neutralPortability, against the linear form it replaced.

Rebuilt because `neutralPortability` cites `simcov/battery_bulk56.py` for a
table of sems and no such file was ever committed.

THE SUPERSEDED LINEAR FORM was `r2_0 * max 0 (1 - 2*fst)`, and the point of this
run is that it fails INSIDE the `fst << 0.5` range its own note claimed for it,
not merely outside. So the design puts a cell at `fst = 0.05` -- as far inside
the claimed regime as it goes -- and both forms are evaluated there.

WHY THE SIGNATURE SUFFICES for the corrected body. The correct retention depends
on the signal-to-noise ratio, which looks like an argument this body does not
have. It has it implicitly: `r2_0 = V_A/(V_A+V_E)`, so `V_E/V_A = (1-r2_0)/r2_0`
and the chart ratio can be written in `r2_0` and `fst` alone. The corrected body
is that, and it reduces to `r2_0` at `fst = 0` as it must.

REGIME, inherited from `neutralDriftR2Ratio` and load-bearing here for the same
reason: the score TRACKS the attenuated signal. A score keeping weights on
variants that have stopped being shared carries them as noise and falls faster
than either form, which is a third construction and not a verdict on either.

FRESHNESS: prints FRESHNESS=OK only if its own source carries the token below,
and `dump_results` records this file's SHA inside the results.
"""
import math
import os

import numpy as np

from battery_core import RESULTS, dump_results, record

FRESH_TOKEN = "SIMCOV-BATTERY-BULK56-BUZZARD-20260805"

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


def main():
    freshness()
    print("FRESHNESS token literal: SIMCOV-BATTERY-BULK56-BUZZARD-20260805")
    rng = np.random.default_rng(56001)
    m, n_ind, n_blocks = 3000, 40000, 10
    v_a, v_e = 1.0, 1.0
    r2_0 = v_a / (v_a + v_e)

    cells, c_linear = [], []
    control = None
    for fst in (0.05, 0.15, 0.30, 0.45):
        vals = []
        for _ in range(n_blocks):
            beta = rng.standard_normal(m) * math.sqrt(v_a / m)
            shared = rng.random(m) >= fst
            g_t = rng.standard_normal((n_ind, m))
            y_t = (g_t @ (beta * shared)
                   + rng.standard_normal(n_ind) * math.sqrt(v_e))
            score = g_t @ (beta * shared)          # the score TRACKS
            vals.append(float(np.corrcoef(score, y_t)[0, 1]) ** 2)
        got, sem = blocked(vals)
        lean = r2_0 * (1 - fst) / ((1 - fst) * r2_0 + (1 - r2_0))
        lin = r2_0 * max(0.0, 1 - 2 * fst)
        lab = "fst=%.2f r2_0=%.2f" % (fst, r2_0)
        print("  %-20s measured R2 %.5f +/- %.5f   corrected %.5f   "
              "superseded linear %.5f" % (lab, got, sem, lean, lin))
        cells.append(dict(design=lab, lean=lean, truth=got,
                          sem=max(sem, 1e-12)))
        c_linear.append(dict(design=lab, lean=lin, truth=got,
                             sem=max(sem, 1e-12)))

    # POSITIVE CONTROL at fst = 0, where both forms agree and the answer is
    # independently known: the body must reduce to r2_0, and the measured
    # R-squared of a correctly specified score on the same code path is
    # V_A/(V_A+V_E). It can fail on a variance-scaling slip.
    vals = []
    for _ in range(n_blocks):
        beta = rng.standard_normal(m) * math.sqrt(v_a / m)
        g = rng.standard_normal((n_ind, m))
        y = g @ beta + rng.standard_normal(n_ind) * math.sqrt(v_e)
        vals.append(float(np.corrcoef(g @ beta, y)[0, 1]) ** 2)
    cmean, csem = blocked(vals)
    print("  CONTROL fst=0: measured R2 %.5f +/- %.5f (known r2_0 = %.5f)"
          % (cmean, csem, r2_0))
    control = dict(design="fst=0 [R2 must be r2_0 = V_A/(V_A+V_E)]",
                   lean=r2_0, truth=cmean, sem=max(csem, 1e-12))

    reg = ("3000 variants and 400000 individuals per population (10 blocks of "
           "40000) at V_A = V_E = 1 so r2_0 = 0.5; a fraction fst of the "
           "signal stops being shared and THE SCORE TRACKS the attenuated "
           "signal. The observable is the realised R-squared in the target. "
           "The sweep includes fst = 0.05, as far INSIDE the superseded "
           "linear form's claimed fst << 0.5 range as the design goes")
    record("neutralPortability", "PortabilityBounds.lean",
           "r2_0 * (1 - fst) / ((1 - fst) * r2_0 + (1 - r2_0))", cells,
           regime=reg, control=control, **MODEL)
    record("neutralPortability [superseded linear r2_0*max 0 (1-2*fst), "
           "competing]", "PortabilityBounds.lean",
           "r2_0 * max 0 (1 - 2 * fst)", c_linear, regime=reg,
           control=control, **MODEL)

    dump_results("battery_bulk56_results.json",
                 battery_source=os.path.abspath(__file__))
    print("\n================ SUMMARY ================")
    for r in RESULTS:
        w = r.get("worst", {})
        print("%-12s %-62s worst %9.2f sems, %7.2f%% rel"
              % (r["verdict"], r["name"], w.get("sems_off", float("nan")),
                 100 * w.get("rel_err", float("nan"))))


if __name__ == "__main__":
    main()
