"""Battery 49: the neutral-drift R-squared ratio.

Rebuilt because `neutralDriftR2Ratio` cites `simcov/battery_bulk49.py` for a
table of sems and no such file was ever committed.

THE REGIME IS LOAD-BEARING and the design has to honour it. The body assumes the
score TRACKS the attenuated signal. A score that keeps weights on variants which
have stopped being shared carries them as pure noise, and its R-squared then
falls as (1-fst)^2/((1-fst)V_A + V_E) instead -- faster than this body. An
earlier run scored with the FULL source weight vector and measured 0.707 where
the body predicts 0.889; that it reproduced the other chart to three digits is
what identified it as measuring a different construction rather than refuting
this one. This design scores with the ATTENUATED weights, and carries the
full-weight reading as a competitor so the distinction is in the record rather
than in a note.

WHY A RATIO. Taking the ratio of two realised R-squared values cancels the
absolute scale, so no heritability convention enters the comparison.

Power: the naive `1 - fst` -- the ratio of the SIGNAL variances rather than of
the R-squared values -- rides along. The two differ because R-squared saturates
in signal variance, so they agree only as V_E dominates; the design holds V_A
and V_E comparable, which is where they separate.

FRESHNESS: prints FRESHNESS=OK only if its own source carries the token below,
and `dump_results` records this file's SHA inside the results.
"""
import math
import os

import numpy as np

from battery_core import RESULTS, dump_results, record

FRESH_TOKEN = "SIMCOV-BATTERY-BULK49-HARRIER49-20260805"


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


def r2_of(score, y):
    """Realised squared correlation between a score and a phenotype."""
    return float(np.corrcoef(score, y)[0, 1]) ** 2


def group_a():
    print("\n===== GROUP A  neutralDriftR2Ratio")
    rng = np.random.default_rng(49001)
    m, n_ind, n_blocks = 3000, 40000, 10

    cells, c_naive, c_fullweight = [], [], []
    control = None
    for v_a, v_e, fst in ((1.0, 1.0, 0.2), (1.0, 1.0, 0.5), (2.0, 1.0, 0.3)):
        ratios, full_ratios = [], []
        for _ in range(n_blocks):
            beta = rng.standard_normal(m) * math.sqrt(v_a / m)
            shared = rng.random(m) >= fst
            g_s = rng.standard_normal((n_ind, m))
            g_t = rng.standard_normal((n_ind, m))
            y_s = g_s @ beta + rng.standard_normal(n_ind) * math.sqrt(v_e)
            y_t = (g_t @ (beta * shared)
                   + rng.standard_normal(n_ind) * math.sqrt(v_e))
            r2_src = r2_of(g_s @ beta, y_s)
            # THE REGIME: the score tracks the attenuated signal.
            r2_tgt = r2_of(g_t @ (beta * shared), y_t)
            # The other construction, carried so the distinction is recorded:
            # the score keeps the FULL source weights, so the dropped variants
            # enter as pure noise.
            r2_full = r2_of(g_t @ beta, y_t)
            ratios.append(r2_tgt / r2_src)
            full_ratios.append(r2_full / r2_src)
        got, sem = blocked(ratios)
        fgot, _ = blocked(full_ratios)
        pres = lambda f: (v_a * (1 - f)) / (v_a * (1 - f) + v_e)
        lean = pres(fst) / pres(0.0)
        lab = "V_A=%.1f V_E=%.1f fst=%.1f" % (v_a, v_e, fst)
        print("  %-24s measured %.5f +/- %.5f   body %.5f   naive 1-fst %.5f "
              "  (full-weight construction measured %.5f)"
              % (lab, got, sem, lean, 1 - fst, fgot))
        cells.append(dict(design=lab, lean=lean, truth=got,
                          sem=max(sem, 1e-12)))
        c_naive.append(dict(design=lab, lean=1 - fst, truth=got,
                            sem=max(sem, 1e-12)))
        c_fullweight.append(dict(design=lab, lean=lean, truth=fgot,
                                 sem=max(sem, 1e-12)))
        if control is None:
            # POSITIVE CONTROL at fst = 0: source and target are the same
            # construction and the ratio must be 1. Independently known, same
            # code path, and the regime clause is not involved.
            ctl = []
            for _ in range(n_blocks):
                beta = rng.standard_normal(m) * math.sqrt(v_a / m)
                g_s = rng.standard_normal((n_ind, m))
                g_t = rng.standard_normal((n_ind, m))
                y_s = g_s @ beta + rng.standard_normal(n_ind) * math.sqrt(v_e)
                y_t = g_t @ beta + rng.standard_normal(n_ind) * math.sqrt(v_e)
                ctl.append(r2_of(g_t @ beta, y_t) / r2_of(g_s @ beta, y_s))
            cmean, csem = blocked(ctl)
            control = dict(design="fst=0 [same construction: ratio is 1]",
                           lean=1.0, truth=cmean, sem=max(csem, 1e-12))

    reg = ("3000 variants and 400000 individuals per population (10 blocks of "
           "40000); a fraction fst of the signal stops being shared and THE "
           "SCORE TRACKS THE ATTENUATED SIGNAL, which is the regime this body "
           "declares. The observable is the RATIO of realised R-squared "
           "values, so no heritability convention enters. V_A and V_E are held "
           "comparable, which is where this body and the naive signal-variance "
           "ratio separate")
    record("neutralDriftR2Ratio", "HumanDemography.lean",
           "presentDayR2 V_A V_E fst / presentDayR2 V_A V_E 0", cells,
           regime=reg, control=control, realised_inputs=True,
           argument_source="model")
    record("neutralDriftR2Ratio [naive 1 - fst, competing]",
           "HumanDemography.lean", "1 - fst", c_naive, regime=reg,
           control=control, realised_inputs=True, argument_source="model")
    record("neutralDriftR2Ratio [scored with the FULL source weights, "
           "competing construction]", "HumanDemography.lean",
           "presentDayR2 V_A V_E fst / presentDayR2 V_A V_E 0, against a score "
           "that keeps the unshared weights", c_fullweight, regime=reg,
           control=control, realised_inputs=True, argument_source="model")


def main():
    freshness()
    print("FRESHNESS token literal: SIMCOV-BATTERY-BULK49-HARRIER49-20260805")
    group_a()
    dump_results("battery_bulk49_results.json",
                 battery_source=os.path.abspath(__file__))
    print("\n================ SUMMARY ================")
    for r in RESULTS:
        w = r.get("worst", {})
        print("%-12s %-64s worst %9.2f sems, %7.2f%% rel"
              % (r["verdict"], r["name"], w.get("sems_off", float("nan")),
                 100 * w.get("rel_err", float("nan"))))


if __name__ == "__main__":
    main()
