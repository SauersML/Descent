"""Battery 20: tagging heritability redone, selected drift, enrichment by fit.

Two of these are redesigns of comparisons the previous batteries got wrong, and
the redesign is the point in each case.

  gwasHeritability -- battery 18 compared against the NOMINAL h2 while the
      realised sum of squared effects at sixty loci has a standard deviation of
      about 0.09, so the run whose nominal h2 was 0.5 had a realised 0.41 and
      the apparent 42-sem gap was the difference between those two numbers.
      Here the comparison is against the realised effect mass on the same draw,
      with the loci raised to 400 so the two differ by less than a percent.

  heritabilityEnrichment -- battery 14 drew effects with the variances the
      definition states and then measured their mean square, which tests the
      random number generator. Here the oracle is a FIT: two SNP categories are
      simulated, a phenotype is built, and the per-SNP variance explained is
      recovered by regression in each category separately. Nothing in that path
      is generated from the enrichment formula.

`selectedDriftFactor` and `fstFromDriftFactor` are new: the first is a
per-generation retention with a selection correction, the second its complement.
"""
import json
import math

import numpy as np

from battery_core import RESULTS, record


def test_gwas_heritability_redone():
    rng = np.random.default_rng(16001)
    cells = []
    n, m = 120000, 400
    for h2, rho in ((0.5, 0.9), (0.5, 0.6), (0.8, 0.8)):
        causal = rng.normal(0, 1, (n, m))
        tag = rho * causal + math.sqrt(1 - rho ** 2) * rng.normal(0, 1, (n, m))
        beta = rng.normal(0, math.sqrt(h2 / m), m)
        realised_h2 = float((beta ** 2).sum())
        y = causal @ beta + rng.normal(0, math.sqrt(1 - h2), n)
        # variance explained by the TAGS, out of sample: fit on half, score on
        # the other half, so the estimate is not inflated by overfitting
        h = n // 2
        A1 = tag[:h] - tag[:h].mean(0)
        y1 = y[:h] - y[:h].mean()
        coef, *_ = np.linalg.lstsq(A1, y1, rcond=None)
        A2 = tag[h:] - tag[h:].mean(0)
        pred = A2 @ coef
        y2 = y[h:] - y[h:].mean()
        captured = float(np.cov(pred, y2)[0, 1] ** 2
                         / (np.var(pred) * np.var(y2)) * np.var(y2) / np.var(y))
        cells.append(dict(design="h2r=%.3f rho=%.1f" % (realised_h2, rho),
                          lean=realised_h2 * rho ** 2, truth=captured,
                          sem=captured * math.sqrt(4.0 / h)))
    record("gwasHeritability", "AncestrySpecificArchitecture.lean",
           "h2_true * avg_r2_tag", cells,
           regime="out-of-sample variance explained by TAG variants correlated "
                  "with the causal ones at r-squared = rho^2, compared against "
                  "the REALISED effect mass on the same draw")


def test_selected_drift_factor():
    """selectedDriftFactor = (1 - 1/(2Ne) + s_correction)^t, against WF."""
    rng = np.random.default_rng(16101)
    cells_d, cells_f = [], []
    for Ne, s_corr, t in ((200, 0.0, 60), (200, 0.001, 60), (500, 0.0005, 100)):
        n_loci, reps = 3000, 400
        two_n = int(2 * Ne)
        p = np.full((reps, n_loci), 0.5)
        H0 = float((2 * p * (1 - p)).mean())
        for _ in range(t):
            p = rng.binomial(two_n, p) / two_n
            if s_corr:
                # a per-generation restoring term of size s_corr, which is what
                # a positive selection correction to the drift factor means
                p = p + s_corr * (0.5 - p) * 0.0 + 0.0
                # heterozygosity is replenished at rate s_corr toward its start
                het = 2 * p * (1 - p)
                boost = s_corr
                p = 0.5 - (0.5 - p) * math.sqrt(max(1.0 - boost, 0.0))
        H = float((2 * p * (1 - p)).mean())
        obs = H / H0
        lean = (1 - 1 / (2 * Ne) + s_corr) ** t
        cells_d.append(dict(design="Ne=%d s=%.4f t=%d" % (Ne, s_corr, t),
                            lean=lean, truth=obs, sem=obs * 0.006))
        cells_f.append(dict(design="Ne=%d s=%.4f t=%d" % (Ne, s_corr, t),
                            lean=1 - lean, truth=1 - obs,
                            sem=(1 - obs) * 0.006))
    # WHAT THESE TWO ROWS ACTUALLY MEASURE, added 2026-08-11 after they were
    # adjudicated. They are kept as measurement history rather than deleted, and
    # they are SUPERSEDED by battery_bulk47 -- see adjudications.json under both
    # declaration names.
    #
    # The `s_corr` branch above applies `p <- 0.5 - (0.5 - p) sqrt(1 - s)` after
    # each generation. With `H = 2p(1-p) = 0.5 - 2d^2` that map sends
    # `H -> H + s(0.5 - H)`: AFFINE toward a fixed point, where both bodies below
    # are a CONSTANT MULTIPLIER. The two coincide only at `s = 0`. Solving the
    # simulator's own recurrence independently of the bodies
    # (`probe_bulk7a.py`), the measurement tracks that affine model at 0.10 and
    # 1.03 sems and misses the bodies by 312 and 385 -- on a bar taken from the
    # 400 replicates, which is 32x smaller than the `obs * 0.006` asserted below
    # and is why the ledger carries 9.50 and 79.25 instead.
    #
    # At `s = 0` the body matches at 1.06 sems, agreeing with bulk47's 1.42 over
    # four cells. Do not "repair" this arm: nothing produces a constant
    # multiplicative boost to heterozygosity except a simulator applying the
    # formula, so any design pinning `s_correction` this way is a generative
    # self-test, which is why the body's own head records the parameter as
    # unpinned.
    record("selectedDriftFactor", "PhenomeWidePortability.lean",
           "(1 - 1/(2*Ne) + s_correction)^t", cells_d,
           regime="realised heterozygosity retention under Wright-Fisher drift "
                  "with a per-generation restoring term")
    record("fstFromDriftFactor", "PhenomeWidePortability.lean",
           "1 - driftFactor", cells_f,
           regime="complement of the same measured retention")


def test_heritability_enrichment_by_fit():
    """heritabilityEnrichment recovered by regression, not by construction."""
    rng = np.random.default_rng(16201)
    cells = []
    n = 200000
    for mc, mt, h2c, h2rest in ((100, 900, 0.30, 0.30), (100, 900, 0.10, 0.50),
                                (200, 800, 0.40, 0.20)):
        # category A has mc SNPs carrying h2c; the rest carry h2rest
        Xa = rng.normal(0, 1, (n, mc))
        Xb = rng.normal(0, 1, (n, mt))
        ba = rng.normal(0, math.sqrt(h2c / mc), mc)
        bb = rng.normal(0, math.sqrt(h2rest / mt), mt)
        y = Xa @ ba + Xb @ bb + rng.normal(
            0, math.sqrt(max(1 - h2c - h2rest, 0.05)), n)
        vy = float(np.var(y))
        # per-SNP variance explained, recovered by regression in each category
        def per_snp(X):
            Xc = X - X.mean(0)
            coef, *_ = np.linalg.lstsq(Xc, y - y.mean(), rcond=None)
            return float(np.var(Xc @ coef) / vy / X.shape[1])
        pa, pb = per_snp(Xa), per_snp(Xb)
        total_per_snp = (pa * mc + pb * mt) / (mc + mt)
        obs = pa / total_per_snp
        lean = (h2c / mc) / ((h2c + h2rest) / (mc + mt))
        cells.append(dict(design="mc=%d h2c=%.2f h2rest=%.2f" % (mc, h2c, h2rest),
                          lean=lean, truth=obs, sem=obs * math.sqrt(8.0 / n)))
    record("heritabilityEnrichment", "PolygenicArchitecture.lean",
           "(h2_cat/M_cat) / (h2_total/M_total)", cells,
           regime="per-SNP variance explained recovered by regression in each "
                  "category separately; nothing on this path is generated from "
                  "the enrichment formula")


def main():
    for fn in (test_gwas_heritability_redone, test_selected_drift_factor,
               test_heritability_enrichment_by_fit):
        try:
            fn()
        except Exception:
            import traceback
            traceback.print_exc()
    json.dump(RESULTS, open("battery_bulk7_results.json", "w"), indent=1,
              default=str)
    print("\n\n================ SUMMARY ================")
    for r in RESULTS:
        w = r.get("worst", {})
        print("%-14s %-40s worst %9.2f sems, %7.2f%% rel"
              % (r["verdict"], r["name"], w.get("sems_off", float("nan")),
                 100 * w.get("rel_err", float("nan"))))


if __name__ == "__main__":
    main()
