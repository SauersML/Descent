"""Battery 52: the allele-frequency mismatch penalty, now a variance ratio.

Rebuilt because `alleleFreqMismatchPenalty` cites `simcov/battery_bulk52.py`
for a table of sems and no such file was ever committed.

THE DESIGN IS THE ONE THAT REFUTED THE SUPERSEDED BODY, put back to the
corrected one. The superseded body was `exp(-|pTarget - pSource|)`, and the
whole content of the refutation is that retention cannot be a function of the
GAP alone: three cells share `|dp| = 0.2` at different places in the unit
interval, and a body seeing only the gap must return the same number for all
three while the measurement spans a factor of nearly three across them. Those
three cells are kept, because a corrected body has to be put back to the
measurement that rejected the old one.

The third cell is the sharper problem and is kept for that reason too: moving a
frequency from 0.7 toward 0.5 RAISES the variant's genotype variance and so its
contribution, and retention there exceeds one. A quantity called a penalty,
bounded above by one for every argument, cannot represent that at all.

The observable is the fraction of a variant's predictive contribution that
survives transport: with a FIXED effect, the ratio of realised score-phenotype
covariance in the target to that in the source. Competitors on the same cells:
the superseded exponential, and the SQUARE ROOT of the variance ratio -- what a
STANDARDIZED score would give -- so the exponent is settled and not just the
shape.

FRESHNESS: prints FRESHNESS=OK only if its own source carries the token below,
and `dump_results` records this file's SHA inside the results.
"""
import math
import os

import numpy as np

from battery_core import RESULTS, dump_results, record

FRESH_TOKEN = "SIMCOV-BATTERY-BULK52-SHRIKE-20260805"

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


def contribution(rng, p, beta, n):
    """Realised score-phenotype covariance for one variant at frequency p.

    The genotype is an UNSTANDARDISED allele count -- Binomial(2, p) -- because
    that is what makes the retention a statement about the genotype variance.
    A standardised dosage would divide it out and the design would be measuring
    a different quantity, which is exactly what the square-root competitor is.
    """
    g = rng.binomial(2, p, size=n).astype(float)
    y = beta * g + rng.standard_normal(n)
    return float(np.cov(beta * g, y)[0, 1]), float(g.mean() / 2.0)


def main():
    freshness()
    print("FRESHNESS token literal: SIMCOV-BATTERY-BULK52-SHRIKE-20260805")
    rng = np.random.default_rng(52001)
    n_blocks, per_block = 30, 100000
    beta = 0.4

    cells, c_exp, c_sqrt = [], [], []
    control = None
    for ps, pt in ((0.50, 0.30), (0.30, 0.10), (0.70, 0.50), (0.20, 0.40)):
        ratios, src_freqs = [], []
        for _ in range(n_blocks):
            cs, fs = contribution(rng, ps, beta, per_block)
            ct, _ = contribution(rng, pt, beta, per_block)
            ratios.append(ct / cs)
            src_freqs.append(fs)
        got, sem = blocked(ratios)
        fmean, fsem = blocked(src_freqs)
        lean = (2 * pt * (1 - pt)) / (2 * ps * (1 - ps))
        old = math.exp(-abs(pt - ps))
        root = math.sqrt(lean)
        lab = "p_s=%.2f p_t=%.2f" % (ps, pt)
        print("  %-18s measured %.5f +/- %.5f   variance ratio %.5f   "
              "superseded exp %.5f   sqrt %.5f"
              % (lab, got, sem, lean, old, root))
        cells.append(dict(design=lab, lean=lean, truth=got,
                          sem=max(sem, 1e-12)))
        c_exp.append(dict(design=lab, lean=old, truth=got,
                          sem=max(sem, 1e-12)))
        c_sqrt.append(dict(design=lab, lean=root, truth=got,
                           sem=max(sem, 1e-12)))
        if control is None:
            control = dict(design=lab + " [counted source allele frequency]",
                           lean=ps, truth=fmean, sem=max(fsem, 1e-12))

    reg = ("3e6 individuals per population (30 blocks of 1e5) with an "
           "UNSTANDARDISED allele count Binomial(2, p) and a FIXED effect; the "
           "observable is the ratio of realised score-phenotype covariance in "
           "the target to that in the source. Three cells share |dp| = 0.2 at "
           "different places in the unit interval, which is the design that "
           "refuted the superseded exponential: a body seeing only the gap "
           "must return one number for all three. One cell moves a frequency "
           "TOWARD 0.5, where retention exceeds one")
    record("alleleFreqMismatchPenalty", "PortabilityDrift.lean",
           "(2 * pTarget * (1 - pTarget)) / (2 * pSource * (1 - pSource))",
           cells, regime=reg, control=control, **MODEL)
    record("alleleFreqMismatchPenalty [superseded exp(-|dp|), competing]",
           "PortabilityDrift.lean", "exp (-|pTarget - pSource|)", c_exp,
           regime=reg, control=control, **MODEL)
    record("alleleFreqMismatchPenalty [square root -- a standardized score, "
           "competing]", "PortabilityDrift.lean",
           "sqrt((2*pTarget*(1-pTarget)) / (2*pSource*(1-pSource)))", c_sqrt,
           regime=reg, control=control, **MODEL)

    dump_results("battery_bulk52_results.json",
                 battery_source=os.path.abspath(__file__))
    print("\n================ SUMMARY ================")
    for r in RESULTS:
        w = r.get("worst", {})
        print("%-12s %-62s worst %9.2f sems, %7.2f%% rel"
              % (r["verdict"], r["name"], w.get("sems_off", float("nan")),
                 100 * w.get("rel_err", float("nan"))))


if __name__ == "__main__":
    main()
