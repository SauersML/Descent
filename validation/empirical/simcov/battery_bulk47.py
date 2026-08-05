"""Battery 47: the drift half of selectedDriftFactor, and the prevalence DGP.

Rebuilt because `selectedDriftFactor`, `fstFromDriftFactor` and
`prevalenceDGP_trueExpectation` all cite `simcov/battery_bulk47.py` for tables
of sems, and no such file was ever committed.

group_a  selectedDriftFactor AT s_correction = 0, and fstFromDriftFactor on the
         same runs. The two are the same measurement read in the two
         directions: the observable is the realised heterozygosity ratio
         H_t/H_0, which IS the drift factor, and 1 - H_t/H_0 is the fraction of
         ancestral heterozygosity lost.

         WHAT THIS DOES NOT MEASURE, stated here because the declaration's own
         docstring makes the point at length and a battery that quietly
         overreached would undo it: `s_correction` has no operational
         definition anywhere in the corpus, so a simulation cannot set it
         without inventing one, and whatever it then measures is a property of
         the invention. It is held at ZERO throughout. What is established is
         the drift half of the law.

         Which `F` group_a measures, since `fstFromDriftFactor`'s docstring
         warns the formula does not fix it: the PER-BRANCH drift coefficient,
         Wright's `F` against the ancestor within ONE lineage. A single
         population losing heterozygosity measures that and nothing else -- it
         is not the pairwise Hudson F_ST of `fstFromTau`.

group_b  prevalenceDGP_trueExpectation = prevalence(c) + effect * p. Binary
         outcomes drawn at the stated conditional rate; the observable is the
         realised mean. The MULTIPLICATIVE reading pi*(1 + beta*p) -- the other
         obvious way to let a score shift a prevalence -- rides along. The two
         coincide at p = 0, so the design sweeps p away from zero and one cell
         gives beta a NEGATIVE sign, where the two readings move the prevalence
         in different directions.

FRESHNESS: prints FRESHNESS=OK only if its own source carries the token below,
and `dump_results` records this file's SHA inside the results.
"""
import math
import os

import numpy as np

from battery_core import RESULTS, dump_results, record

FRESH_TOKEN = "SIMCOV-BATTERY-BULK47-GOSHAWK-20260805"

# `realised_inputs=True`: Ne and t are an integer and a loop counter; the
# prevalence and the effect in group B are the exact rates the Bernoulli draws
# were made at. Nothing in either prediction is estimated off the same sample
# the oracle measures.
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


# ---------------------------------------------------------------------------
# group A -- the drift factor, forward Wright-Fisher
# ---------------------------------------------------------------------------
def wf_retention(ne, t, n_pops, n_loci, seed):
    """Per-population H_t/H_0 under Wright-Fisher with NO mutation.

    H is averaged over ALL loci including those that have fixed. Conditioning
    on still-segregating loci inflates H exactly where drift has done its work;
    battery_wf_drift carries that trap explicitly and shows the design is
    sensitive to it.
    """
    rng = np.random.default_rng(seed)
    two_n = 2 * ne
    p = rng.uniform(0.05, 0.95, size=(n_pops, n_loci))
    h0 = (2 * p * (1 - p)).mean(axis=1)
    for _ in range(t):
        p = rng.binomial(two_n, p) / two_n
    return (2 * p * (1 - p)).mean(axis=1) / h0


def group_a():
    print("\n===== GROUP A  selectedDriftFactor at s=0, and fstFromDriftFactor")
    n_pops, n_loci = 3000, 400

    cells, c_haploid = [], []
    loss_cells, loss_haploid = [], []
    control = None
    for ne, t in ((50, 30), (100, 40), (200, 80), (100, 120)):
        ret = wf_retention(ne, t, n_pops, n_loci, seed=47000 + 10 * ne + t)
        got, sem = blocked(ret)
        lean = (1 - 1.0 / (2 * ne)) ** t
        hap = (1 - 1.0 / ne) ** t
        lab = "Ne=%d t=%d" % (ne, t)
        print("  %-12s measured %.5f +/- %.5f   body %.5f   haploid %.5f"
              % (lab, got, sem, lean, hap))
        cells.append(dict(design=lab, lean=lean, truth=got,
                          sem=max(sem, 1e-12)))
        c_haploid.append(dict(design=lab, lean=hap, truth=got,
                              sem=max(sem, 1e-12)))
        loss_cells.append(dict(design=lab, lean=1 - lean, truth=1 - got,
                               sem=max(sem, 1e-12)))
        loss_haploid.append(dict(design=lab, lean=1 - hap, truth=1 - got,
                                 sem=max(sem, 1e-12)))

    # POSITIVE CONTROL: the mean allele frequency. Wright-Fisher drift is a
    # martingale, so E[p_t] = p_0 exactly at every t, independently of the
    # heterozygosity law under test. A ploidy slip in `two_n` or a
    # normalisation error in the binomial moves it and the control fails.
    rng = np.random.default_rng(47999)
    two_n = 2 * 100
    p = rng.uniform(0.05, 0.95, size=(n_pops, n_loci))
    p0bar = p.mean(axis=1)
    for _ in range(120):
        p = rng.binomial(two_n, p) / two_n
    ratio = p.mean(axis=1) / p0bar
    cmean, csem = blocked(ratio)
    print("  CONTROL E[p_t]/p_0 at Ne=100 t=120: %.5f +/- %.5f (known 1)"
          % (cmean, csem))
    control = dict(design="Ne=100 t=120 [E[p_t]/p_0, martingale]", lean=1.0,
                   truth=cmean, sem=max(csem, 1e-12))

    reg = ("forward Wright-Fisher over 3000 replicate populations of 400 "
           "independent biallelic loci, mutation rate ZERO, heterozygosity "
           "averaged over ALL loci including fixed ones; the observable is the "
           "realised H_t/H_0, which IS the drift factor. Ne in 50, 100, 200 "
           "and t in 30, 40, 80, 120 swept independently, with (Ne, t) = "
           "(100, 40) and (200, 80) reaching nearly the same factor by "
           "different routes so a body depending on them separately would "
           "separate there. s_correction is held at ZERO: it has no "
           "operational definition, so no simulation can set it without "
           "inventing one")
    record("selectedDriftFactor", "PhenomeWidePortability.lean",
           "(1 - 1 / (2 * Ne) + s_correction)^t at s_correction = 0", cells,
           regime=reg, control=control, **MODEL)
    record("selectedDriftFactor [haploid slip (1 - 1/Ne)^t, competing]",
           "PhenomeWidePortability.lean", "(1 - 1 / Ne)^t", c_haploid,
           regime=reg, control=control, **MODEL)
    record("fstFromDriftFactor", "PhenomeWidePortability.lean",
           "1 - driftFactor", loss_cells,
           regime=reg + "; read as the LOSS 1 - H_t/H_0, which is the "
                        "PER-BRANCH drift coefficient and not a pairwise F_ST",
           control=control, **MODEL)
    record("fstFromDriftFactor [haploid drift factor, competing]",
           "PhenomeWidePortability.lean", "1 - (1 - 1 / Ne)^t", loss_haploid,
           regime=reg + "; read as the LOSS", control=control, **MODEL)


# ---------------------------------------------------------------------------
# group B -- prevalenceDGP_trueExpectation
# ---------------------------------------------------------------------------
def group_b():
    print("\n===== GROUP B  prevalenceDGP_trueExpectation = prevalence + effect*p")
    rng = np.random.default_rng(47002)
    n_blocks, per_block = 30, 100000

    cells, c_mult = [], []
    control = None
    for prev, beta, p in ((0.10, 0.20, 0.8), (0.30, 0.15, 1.5),
                          (0.50, -0.25, 1.2), (0.20, 0.30, 2.0)):
        rate = prev + beta * p
        means = [float((rng.random(per_block) < rate).mean())
                 for _ in range(n_blocks)]
        got, sem = blocked(means)
        mult = prev * (1 + beta * p)
        lab = "prev=%.2f beta=%+.2f p=%.1f" % (prev, beta, p)
        print("  %-26s measured %.5f +/- %.5f   additive %.5f   "
              "multiplicative %.5f" % (lab, got, sem, rate, mult))
        cells.append(dict(design=lab, lean=rate, truth=got,
                          sem=max(sem, 1e-12)))
        c_mult.append(dict(design=lab, lean=mult, truth=got,
                           sem=max(sem, 1e-12)))
        if control is None:
            # At p = 0 the realised rate must recover the prevalence, on the
            # same draws and the same code path, and the two readings agree
            # there so the control is not the cell under test.
            zeros = [float((rng.random(per_block) < prev).mean())
                     for _ in range(n_blocks)]
            zmean, zsem = blocked(zeros)
            control = dict(design="p=0 [realised rate recovers prevalence]",
                           lean=prev, truth=zmean, sem=max(zsem, 1e-12))

    reg = ("3e6 binary outcomes per cell in 30 independent blocks of 1e5, "
           "drawn at the stated conditional rate; the observable is the "
           "realised mean. p is swept AWAY from zero, where the additive and "
           "multiplicative readings coincide, and one cell gives beta a "
           "NEGATIVE sign where the two move the prevalence in different "
           "directions")
    record("prevalenceDGP_trueExpectation", "DGP.lean",
           "prevalence c + pgs_effect * p", cells, regime=reg, control=control,
           **MODEL)
    record("prevalenceDGP_trueExpectation [multiplicative shift, competing]",
           "DGP.lean", "prevalence c * (1 + pgs_effect * p)", c_mult,
           regime=reg, control=control, **MODEL)


def main():
    freshness()
    print("FRESHNESS token literal: SIMCOV-BATTERY-BULK47-GOSHAWK-20260805")
    group_a()
    group_b()
    dump_results("battery_bulk47_results.json",
                 battery_source=os.path.abspath(__file__))
    print("\n================ SUMMARY ================")
    for r in RESULTS:
        w = r.get("worst", {})
        print("%-12s %-62s worst %9.2f sems, %7.2f%% rel"
              % (r["verdict"], r["name"], w.get("sems_off", float("nan")),
                 100 * w.get("rel_err", float("nan"))))


if __name__ == "__main__":
    main()
