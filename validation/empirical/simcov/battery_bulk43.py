"""Battery 43: the liability threshold, and the ancestry-averaged effect.

WHY THIS FILE IS BEING WRITTEN NOW. `liabilityThreshold` and
`globalAncestryAveragedEffect` both carried `Empirical status: VALIDATED
(simcov/battery_bulk43.py)` with a full table of sems, and no file of that name
had ever been committed. The numbers were real when they were produced and
nobody can check them, which is the same position as no numbers at all -- the
ledger guard says so, and it is right. This is that battery, rebuilt to the
design its own citation describes, so the evidence is in the repository beside
the claim.

group_a  liabilityThreshold = Phi^-1(1 - K). The observable needs no model at
         all: the empirical (1-K) quantile of standard-normal draws. The sign
         slip Phi^-1(K) rides along and coincides with the body only at K = 1/2,
         so the sweep crosses the median rather than resting on it.

group_b  globalAncestryAveragedEffect = alpha*b1 + (1-alpha)*b2. The observable
         is the realised MARGINAL OLS slope across an admixed sample -- what a
         GWAS ignoring local ancestry estimates. The SWAPPED weights ride along;
         the two coincide only at alpha = 1/2, and one cell gives the two
         ancestries effects of opposite sign, where the swap lands the average
         on the wrong side of zero.

FRESHNESS: prints FRESHNESS=OK only if its own source carries the token below,
and `dump_results` records this file's SHA inside the results.
"""
import math
import os

import numpy as np

from battery_core import RESULTS, dump_results, record

FRESH_TOKEN = "SIMCOV-BATTERY-BULK43-KESTREL-20260805"

# `realised_inputs=True` throughout, and the reason it is not a fudge: `K`,
# `alpha`, `beta1` and `beta2` are the exact constants the draws were generated
# with, never estimated off the same draws the oracle measures. There is no
# nominal/realised gap of size O(1/sqrt(N)) for a finding to be confused with.
MODEL = dict(realised_inputs=True, argument_source="model")


def freshness():
    try:
        src = open(os.path.abspath(__file__)).read()
    except OSError:
        print("FRESHNESS=STALE (cannot read own source)")
        return
    print("FRESHNESS=%s (token %s)"
          % ("OK" if src.count(FRESH_TOKEN) >= 2 else "STALE", FRESH_TOKEN))


def blocked(vals, n_blocks):
    """(mean, sem) over independent blocks of a single long draw.

    The sem has to come from replicates rather than from a closed form: a
    quantile's asymptotic standard error assumes a density the design should not
    have to assert. Blocks of the same draw are independent by construction.
    """
    a = np.asarray(vals, float)
    return float(a.mean()), float(a.std(ddof=1) / math.sqrt(a.size))


# ---------------------------------------------------------------------------
# group A -- liabilityThreshold
# ---------------------------------------------------------------------------
def group_a():
    print("\n===== GROUP A  liabilityThreshold = Phi^-1(1 - K)")
    from scipy.stats import norm
    rng = np.random.default_rng(43001)
    n_blocks, per_block = 20, 200000
    liab = rng.standard_normal((n_blocks, per_block))

    cells, c_sign = [], []
    for K in (0.01, 0.05, 0.2, 0.5, 0.8):
        q = np.quantile(liab, 1.0 - K, axis=1)
        got, sem = blocked(q, n_blocks)
        lean = float(norm.ppf(1.0 - K))
        slip = float(norm.ppf(K))
        lab = "K=%.2f" % K
        print("  %-8s measured %+.5f +/- %.5f   body %+.5f   sign slip %+.5f"
              % (lab, got, sem, lean, slip))
        cells.append(dict(design=lab, lean=lean, truth=got,
                          sem=max(sem, 1e-9)))
        c_sign.append(dict(design=lab, lean=slip, truth=got,
                           sem=max(sem, 1e-9)))

    # POSITIVE CONTROL, and deliberately not the one the earlier run used. That
    # one counted the tail mass above the MEASURED quantile, which is K by
    # construction of a quantile and so could not fail; the harness detected it
    # as DEGENERATE. This one asks the draws a question whose answer is known
    # and has nothing to do with K: the median of a standard normal is 0.
    med = np.median(liab, axis=1)
    cmean, csem = blocked(med, n_blocks)
    print("  CONTROL median of the same draws: %+.5f +/- %.5f (known 0)"
          % (cmean, csem))
    control = dict(design="median of the same draws [known to be 0]",
                   lean=0.0, truth=cmean, sem=max(csem, 1e-9))

    reg = ("4e6 standard-normal liabilities in 20 independent blocks of 2e5; "
           "the observable is the empirical (1-K) quantile, which needs no "
           "model. K is swept from the far tail to above the median so the "
           "threshold CHANGES SIGN across the design")
    record("liabilityThreshold", "PortabilityDrift.lean",
           "Function.invFun Phi (1 - K)", cells, regime=reg, control=control,
           **MODEL)
    record("liabilityThreshold [sign slip Phi^-1(K), competing]",
           "PortabilityDrift.lean", "Function.invFun Phi K", c_sign,
           regime=reg, control=control, **MODEL)


# ---------------------------------------------------------------------------
# group B -- globalAncestryAveragedEffect
# ---------------------------------------------------------------------------
def group_b():
    print("\n===== GROUP B  globalAncestryAveragedEffect")
    rng = np.random.default_rng(43002)
    n_blocks, per_block = 20, 100000

    cells, c_swap = [], []
    control = None
    for alpha, b1, b2 in ((0.2, 1.0, 0.4), (0.3, 0.8, 0.2),
                          (0.5, 1.0, -1.0), (0.8, 0.5, -0.3)):
        slopes, fracs = [], []
        for blk in range(n_blocks):
            # Standardised dosage, so the marginal OLS slope IS the effect and
            # no genotype-variance convention enters the comparison.
            g = rng.standard_normal(per_block)
            anc1 = rng.random(per_block) < alpha
            beta = np.where(anc1, b1, b2)
            y = beta * g + rng.standard_normal(per_block)
            slopes.append(float(np.dot(g, y) / np.dot(g, g)))
            fracs.append(float(anc1.mean()))
        got, sem = blocked(slopes, n_blocks)
        fmean, fsem = blocked(fracs, n_blocks)
        lean = alpha * b1 + (1 - alpha) * b2
        swap = (1 - alpha) * b1 + alpha * b2
        lab = "alpha=%.1f b1=%+.1f b2=%+.1f" % (alpha, b1, b2)
        print("  %-26s measured %+.5f +/- %.5f   body %+.5f   swapped %+.5f"
              % (lab, got, sem, lean, swap))
        cells.append(dict(design=lab, lean=lean, truth=got,
                          sem=max(sem, 1e-9)))
        c_swap.append(dict(design=lab, lean=swap, truth=got,
                           sem=max(sem, 1e-9)))
        if control is None:
            # The realised ancestry-1 fraction on the SAME draws recovers the
            # alpha the sample was built with. It can fail -- a mis-scaled
            # Bernoulli, an off-by-one in the mask -- and it is not the
            # quantity under test.
            control = dict(design=lab + " [realised ancestry-1 fraction]",
                           lean=alpha, truth=fmean, sem=max(fsem, 1e-9))

    reg = ("2e6 individuals in 20 independent blocks of 1e5, standardised "
           "dosage, a fraction alpha carrying the first ancestry's effect and "
           "the rest the second; the observable is the realised MARGINAL OLS "
           "slope over the whole admixed sample -- what a GWAS ignoring local "
           "ancestry estimates. alpha is swept across 1/2, where the swapped "
           "reading coincides with the body, and one cell gives the two "
           "ancestries effects of OPPOSITE SIGN")
    record("globalAncestryAveragedEffect", "HaplotypeTheory.lean",
           "alpha * beta1 + (1 - alpha) * beta2", cells, regime=reg,
           control=control, **MODEL)
    record("globalAncestryAveragedEffect [weights swapped, competing]",
           "HaplotypeTheory.lean", "(1 - alpha) * beta1 + alpha * beta2",
           c_swap, regime=reg, control=control, **MODEL)
    # The body IS `ancestrySpecificEffect` at the same three arguments, so the
    # same cells measure that declaration too. Recorded under its own name
    # rather than left implicit: the ledger anchors on declaration names, and a
    # measurement nobody filed under a name is a measurement that name does not
    # have.
    record("ancestrySpecificEffect", "HaplotypeTheory.lean",
           "alpha * beta_pop1 + (1 - alpha) * beta_pop2", cells, regime=reg,
           control=control, **MODEL)
    record("ancestrySpecificEffect [weights swapped, competing]",
           "HaplotypeTheory.lean", "(1 - alpha) * beta_pop1 + alpha * beta_pop2",
           c_swap, regime=reg, control=control, **MODEL)


def main():
    freshness()
    print("FRESHNESS token literal: SIMCOV-BATTERY-BULK43-KESTREL-20260805")
    group_a()
    group_b()
    dump_results("battery_bulk43_results.json",
                 battery_source=os.path.abspath(__file__))
    print("\n================ SUMMARY ================")
    for r in RESULTS:
        w = r.get("worst", {})
        print("%-12s %-62s worst %9.2f sems, %7.2f%% rel"
              % (r["verdict"], r["name"], w.get("sems_off", float("nan")),
                 100 * w.get("rel_err", float("nan"))))


if __name__ == "__main__":
    main()
