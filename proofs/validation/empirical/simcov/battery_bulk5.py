"""Battery 18: one-locus quantitative genetics, epistasis, attenuation.

These are the classical decompositions, and each has an oracle that is a
REGRESSION rather than an algebraic rearrangement:

  fisherAverageEffect   the slope of genotypic value on dosage under
                        Hardy-Weinberg. Fitting that slope is what "average
                        effect" MEANS, so the oracle is the fit and not a
                        rewriting of the formula.
  dominanceVariance     the variance of the residual left by that fit.
  epistaticVariance     the variance of the two-locus interaction term after
                        both main effects are removed.
  reliabilityRatio      the attenuation of a regression slope when the predictor
                        carries measurement error, measured by comparing the
                        fitted slope against the noiseless one.

Every design puts a nonzero value in every component so that a formula which
silently dropped one would show. A dominance test at `p = 1/2` alone, for
instance, cannot see the `(1 - 2p)` in the average effect -- that term vanishes
there, which is the blindness `BlindnessRegistry` instance 8 records.
"""
import json
import math

import numpy as np

from battery_core import RESULTS, record


def test_fisher_average_effect():
    """The slope of genotypic value on dosage, fitted."""
    rng = np.random.default_rng(14001)
    cells = []
    n = 4000000
    for p, a, d in ((0.3, 1.0, 0.5), (0.7, 1.0, 0.5), (0.5, 1.0, 0.8),
                    (0.2, 0.6, -0.4)):
        x = rng.binomial(2, p, n).astype(float)
        # genotypic values -a, d, +a on dosages 0, 1, 2
        gval = np.where(x == 0, -a, np.where(x == 1, d, a))
        xc = x - x.mean()
        slope = float(xc @ (gval - gval.mean()) / (xc @ xc))
        cells.append(dict(design="p=%.1f a=%.1f d=%.1f" % (p, a, d),
                          lean=a + d * (1 - 2 * p), truth=slope,
                          sem=float(np.std(gval) / math.sqrt(n))))
    record("fisherAverageEffect", "EpistasisAndNonAdditivity.lean",
           "a + d * (1 - 2*p)", cells,
           regime="least-squares slope of genotypic value on dosage under "
                  "Hardy-Weinberg, four million individuals")


def test_dominance_variance():
    """The variance of the residual left by the additive fit."""
    rng = np.random.default_rng(14101)
    cells = []
    n = 4000000
    for ps, ds in (([0.3], [0.5]), ([0.3, 0.6], [0.5, -0.4]),
                   ([0.2, 0.5, 0.8], [0.3, 0.6, 0.2])):
        tot_resid = np.zeros(n)
        lean = 0.0
        for p, d in zip(ps, ds):
            x = rng.binomial(2, p, n).astype(float)
            # pure dominance: genotypic value 0, d, 0 on dosages 0, 1, 2
            gval = np.where(x == 1, d, 0.0)
            xc = x - x.mean()
            slope = float(xc @ (gval - gval.mean()) / (xc @ xc))
            tot_resid = tot_resid + (gval - gval.mean() - slope * xc)
            lean += (2 * p * (1 - p) * d) ** 2
        obs = float(tot_resid.var())
        cells.append(dict(design="%d loci" % len(ps), lean=lean, truth=obs,
                          sem=obs * math.sqrt(2.0 / n)))
    record("dominanceVariance", "EpistasisAndNonAdditivity.lean",
           "sum_i (2 p_i (1-p_i) d_i)^2", cells,
           regime="variance of the residual left by the additive fit at each "
                  "locus, summed over independent loci")


def test_epistatic_variance():
    """The variance of the two-locus interaction after both main effects."""
    rng = np.random.default_rng(14201)
    cells = []
    n = 4000000
    for p1, p2, b12 in ((0.3, 0.4, 1.0), (0.5, 0.5, 0.7), (0.2, 0.8, 1.5)):
        x1 = rng.binomial(2, p1, n).astype(float)
        x2 = rng.binomial(2, p2, n).astype(float)
        inter = b12 * (x1 - x1.mean()) * (x2 - x2.mean())
        # remove both main effects by least squares before taking the variance
        A = np.column_stack([np.ones(n), x1 - x1.mean(), x2 - x2.mean()])
        coef, *_ = np.linalg.lstsq(A, inter, rcond=None)
        resid = inter - A @ coef
        obs = float(resid.var())
        lean = b12 ** 2 * (2 * p1 * (1 - p1)) * (2 * p2 * (1 - p2))
        cells.append(dict(design="p1=%.1f p2=%.1f b12=%.1f" % (p1, p2, b12),
                          lean=lean, truth=obs, sem=obs * math.sqrt(2.0 / n)))
    record("epistaticVariance", "EpistasisAndNonAdditivity.lean",
           "b12^2 * 2p1(1-p1) * 2p2(1-p2)", cells,
           regime="variance of the interaction term after both main effects "
                  "are removed by least squares")


def test_attenuation():
    """reliabilityRatio and pgsAttenuationFactor, against a fitted slope."""
    rng = np.random.default_rng(14301)
    cells_rel, cells_att = [], []
    n = 2000000
    for r2, s2 in ((0.5, 0.5), (0.2, 0.8), (0.8, 0.2)):
        true_signal = rng.normal(0, math.sqrt(r2), n)
        noise = rng.normal(0, math.sqrt(s2), n)
        observed = true_signal + noise
        y = true_signal + rng.normal(0, 1.0, n)
        # slope of y on the NOISY predictor, relative to the slope on the clean
        oc, tc = observed - observed.mean(), true_signal - true_signal.mean()
        b_noisy = float(oc @ (y - y.mean()) / (oc @ oc))
        b_clean = float(tc @ (y - y.mean()) / (tc @ tc))
        cells_rel.append(dict(design="r2=%.1f s2=%.1f" % (r2, s2),
                              lean=r2 / (r2 + s2), truth=b_noisy / b_clean,
                              sem=abs(b_noisy / b_clean) * 3.0 / math.sqrt(n)))
    for r2 in (0.1, 0.4, 0.9):
        # pgsAttenuationFactor = sqrt(r2_gwas): the correlation a score achieves
        g = rng.normal(0, 1, n)
        y = math.sqrt(r2) * g + rng.normal(0, math.sqrt(1 - r2), n)
        cells_att.append(dict(design="r2=%.1f" % r2, lean=math.sqrt(r2),
                              truth=float(np.corrcoef(g, y)[0, 1]),
                              sem=1.0 / math.sqrt(n)))
    record("reliabilityRatio", "StratificationConfounding.lean",
           "r2 / (r2 + sigma2_noise)", cells_rel,
           regime="ratio of the slope fitted on a noisy predictor to the slope "
                  "fitted on the clean one, two million individuals")
    record("pgsAttenuationFactor", "StratificationConfounding.lean",
           "sqrt(r2_gwas)", cells_att,
           regime="correlation between score and outcome at a given r-squared")


def test_gwas_heritability():
    """gwasHeritability = h2_true * avg_r2_tag, with explicit tag SNPs."""
    rng = np.random.default_rng(14401)
    cells = []
    n, m = 200000, 60
    for h2, rho in ((0.5, 0.9), (0.5, 0.6), (0.8, 0.8)):
        causal = rng.normal(0, 1, (n, m))
        # each tag correlates with its causal variant at rho
        tag = rho * causal + math.sqrt(1 - rho ** 2) * rng.normal(0, 1, (n, m))
        beta = rng.normal(0, math.sqrt(h2 / m), m)
        y = causal @ beta + rng.normal(0, math.sqrt(1 - h2), n)
        # heritability captured by regressing on the TAGS
        A = tag - tag.mean(0)
        coef, *_ = np.linalg.lstsq(A, y - y.mean(), rcond=None)
        captured = float(np.var(A @ coef) / np.var(y))
        cells.append(dict(design="h2=%.1f rho=%.1f" % (h2, rho),
                          lean=h2 * rho ** 2, truth=captured,
                          sem=captured * math.sqrt(4.0 / n) + m / n))
    record("gwasHeritability", "AncestrySpecificArchitecture.lean",
           "h2_true * avg_r2_tag", cells,
           regime="variance explained by regressing on TAG variants that "
                  "correlate with the causal ones at r-squared = rho^2")


def main():
    for fn in (test_fisher_average_effect, test_dominance_variance,
               test_epistatic_variance, test_attenuation,
               test_gwas_heritability):
        try:
            fn()
        except Exception:
            import traceback
            traceback.print_exc()
    json.dump(RESULTS, open("battery_bulk5_results.json", "w"), indent=1,
              default=str)
    print("\n\n================ SUMMARY ================")
    for r in RESULTS:
        w = r.get("worst", {})
        print("%-12s %-44s worst %9.2f sems, %7.2f%% rel"
              % (r["verdict"], r["name"], w.get("sems_off", float("nan")),
                 100 * w.get("rel_err", float("nan"))))


if __name__ == "__main__":
    main()
