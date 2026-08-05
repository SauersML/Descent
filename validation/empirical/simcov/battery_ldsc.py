"""Battery 14: LD score regression, effect-size summaries, and a ploidy fork.

`ldsrExpectedBetaSq = h2/M * ell_j + 1/N` is the load-bearing law of LD score
regression: the expected squared MARGINAL effect at a SNP is linear in that
SNP's LD score, with slope `h2/M` and intercept `1/N`. Both the slope and the
intercept carry interpretation in practice -- the slope is used to estimate
heritability, the intercept to detect confounding -- so a design that fixes only
one of them tests half the claim.

The oracle is an explicit GWAS: real coalescent LD, causal effects drawn with
per-SNP variance `h2/M`, a phenotype built from them, and single-SNP marginal
regressions run exactly as a GWAS would. `E[beta_hat_j^2]` is then averaged over
replicate studies at each SNP, and regressed on the SNP's measured LD score.
Slope and intercept are read off that regression and compared against the two
the definition predicts -- so the test is of the LAW, not of one fitted number.

Also settled here: `genotypeVarianceHWE` and `hweHeterozygosity` are the same
body as the already-validated `Conventions.hweGenotypeVariance`, under three
names in three files.
"""
import json
import math

import numpy as np

from battery_core import RESULTS, record


def ld_panel(n_ind, n_sites, seed, seq_len=4e5):
    """Standardised diploid dosages with real coalescent LD."""
    import msprime
    ts = msprime.sim_ancestry(samples=n_ind, population_size=10000,
                              sequence_length=seq_len,
                              recombination_rate=1e-8, random_seed=seed)
    ts = msprime.sim_mutations(ts, rate=1e-8, random_seed=seed + 3)
    gm = ts.genotype_matrix()
    f = gm.mean(axis=1)
    keep = (f > 0.05) & (f < 0.95)
    gm = gm[keep]
    idx = np.linspace(0, gm.shape[0] - 1, n_sites).astype(int)
    gm = gm[idx]
    h = gm.reshape(gm.shape[0], -1, 2)
    dose = h.sum(axis=2).T.astype(float)
    z = (dose - dose.mean(0)) / dose.std(0)
    return z


def test_ldsc():
    rng = np.random.default_rng(11001)
    M = 120
    z = ld_panel(3000, M, seed=41)
    n = z.shape[0]
    R = np.corrcoef(z, rowvar=False)
    # LD score with the standard finite-sample correction subtracted, since the
    # measured r^2 is upward biased by 1/n at every off-diagonal pair
    r2 = R ** 2
    ell = (r2 - (1 - r2) / (n - 2)).sum(axis=1)

    cells_slope, cells_icpt = [], []
    for h2 in (0.2, 0.5):
        reps = 400
        acc = np.zeros(M)
        for _ in range(reps):
            beta = rng.normal(0, math.sqrt(h2 / M), M)
            y = z @ beta + rng.normal(0, math.sqrt(1 - h2), n)
            y = (y - y.mean()) / y.std()
            # single-SNP marginal effects, exactly as a GWAS computes them
            bhat = (z * y[:, None]).sum(axis=0) / (z ** 2).sum(axis=0)
            acc += bhat ** 2
        mean_b2 = acc / reps
        # regress E[bhat^2] on the LD score: slope and intercept are the claim
        A = np.vstack([ell, np.ones(M)]).T
        (slope, icpt), res, _, _ = np.linalg.lstsq(A, mean_b2, rcond=None)
        # standard errors of the regression coefficients
        resid = mean_b2 - A @ np.array([slope, icpt])
        s2 = float(resid @ resid) / (M - 2)
        cov = s2 * np.linalg.inv(A.T @ A)
        cells_slope.append(dict(design="h2=%.1f slope" % h2, lean=h2 / M,
                                truth=float(slope),
                                sem=float(math.sqrt(cov[0, 0]))))
        cells_icpt.append(dict(design="h2=%.1f intercept" % h2, lean=1.0 / n,
                               truth=float(icpt),
                               sem=float(math.sqrt(cov[1, 1]))))
    record("ldsrExpectedBetaSq [slope = h2/M]", "CovarianceStructure.lean",
           "h2/M * ell_j + 1/N", cells_slope,
           regime="explicit GWAS on a recombining coalescent panel, marginal "
                  "effects squared and averaged over 400 replicate studies, "
                  "then regressed on the measured LD score")
    record("ldsrExpectedBetaSq [intercept = 1/N]", "CovarianceStructure.lean",
           "h2/M * ell_j + 1/N", cells_icpt,
           regime="same regression; the intercept is what LDSC reads as "
                  "confounding, so it is half the claim")


def test_effect_summaries():
    """spikeAndSlabVariance, expectedSquaredEffect, heritabilityEnrichment."""
    rng = np.random.default_rng(11101)
    cells_ss, cells_es, cells_he = [], [], []
    for pi, s_large, s_small in ((0.01, 1.0, 0.001), (0.1, 0.5, 0.01),
                                 (0.5, 0.2, 0.05)):
        M = 400000
        big = rng.random(M) < pi
        beta = np.where(big, rng.normal(0, math.sqrt(s_large), M),
                        rng.normal(0, math.sqrt(s_small), M))
        lean = pi * s_large + (1 - pi) * s_small
        obs = float(beta.var())
        cells_ss.append(dict(design="pi=%.2f" % pi, lean=lean, truth=obs,
                             sem=obs * math.sqrt(2.0 / M)))
    for h2, M in ((0.2, 1000), (0.5, 1000), (0.5, 5000)):
        n = 400000
        beta = rng.normal(0, math.sqrt(h2 / M), n)
        cells_es.append(dict(design="h2=%.1f M=%d" % (h2, M), lean=h2 / M,
                             truth=float((beta ** 2).mean()),
                             sem=float((beta ** 2).mean()) * math.sqrt(2.0 / n)))
    for h2c, Mc, h2t, Mt in ((0.3, 100, 0.6, 1000), (0.1, 500, 0.6, 1000)):
        # enrichment is the ratio of per-SNP heritability in a category to the
        # genome-wide per-SNP heritability; simulate both and take the ratio
        nc = 400000
        bc = rng.normal(0, math.sqrt(h2c / Mc), nc)
        bt = rng.normal(0, math.sqrt(h2t / Mt), nc)
        lean = (h2c / Mc) / (h2t / Mt)
        obs = float((bc ** 2).mean() / (bt ** 2).mean())
        cells_he.append(dict(design="h2c=%.1f Mc=%d" % (h2c, Mc), lean=lean,
                             truth=obs, sem=obs * math.sqrt(4.0 / nc)))
    record("spikeAndSlabVariance", "PolygenicArchitecture.lean",
           "pi*sigma_large + (1-pi)*sigma_small", cells_ss,
           regime="variance of a two-component mixture of effect sizes")
    record("expectedSquaredEffect", "PolygenicArchitecture.lean", "h2 / M",
           cells_es, regime="mean squared effect under a per-SNP variance h2/M")
    record("heritabilityEnrichment", "PolygenicArchitecture.lean",
           "(h2_cat/M_cat) / (h2_total/M_total)", cells_he,
           regime="ratio of per-SNP heritability in a category to genome-wide")


def test_hwe_fork():
    """genotypeVarianceHWE and hweHeterozygosity against the validated body."""
    rng = np.random.default_rng(11201)
    cells = []
    for p in (0.05, 0.25, 0.5):
        g = rng.binomial(2, p, 2000000).astype(float)
        cells.append(dict(design="p=%.2f" % p, lean=2 * p * (1 - p),
                          truth=float(g.var()),
                          sem=float(g.var()) * math.sqrt(2.0 / 2000000)))
    record("genotypeVarianceHWE / hweHeterozygosity", "AncestrySpecificPower.lean",
           "2 * p * (1 - p)", cells,
           regime="the same body as Conventions.hweGenotypeVariance, under "
                  "three names in three files; measured against the realised "
                  "dosage variance")


def test_expected_effect_multiplier():
    """expectedEffectMultiplier = (p(1-p))^(1+alpha), the frequency coupling."""
    rng = np.random.default_rng(11301)
    cells = []
    for alpha in (-1.0, -0.5, 0.0):
        # under the alpha model the per-SNP contribution to genetic variance is
        # 2 p(1-p) * beta^2 with Var(beta) proportional to (p(1-p))^alpha, so
        # the per-SNP variance contribution scales as (p(1-p))^(1+alpha)
        M = 300000
        p = rng.uniform(0.05, 0.95, M)
        beta = rng.normal(0, 1, M) * (p * (1 - p)) ** (alpha / 2.0)
        contrib = 2 * p * (1 - p) * beta ** 2
        # compare the mean contribution in a high-frequency band against a
        # low-frequency band; the ratio is the multiplier evaluated at the two
        lo = (p > 0.08) & (p < 0.12)
        hi = (p > 0.45) & (p < 0.55)
        lean = (((0.5 * 0.5) ** (1 + alpha)) / ((0.1 * 0.9) ** (1 + alpha)))
        obs = float(contrib[hi].mean() / contrib[lo].mean())
        sem = obs * math.sqrt(2.0 / hi.sum() + 2.0 / lo.sum())
        cells.append(dict(design="alpha=%.1f" % alpha, lean=lean, truth=obs,
                          sem=sem))
    record("expectedEffectMultiplier", "RareVariantPortability.lean",
           "(p*(1-p))^(1 + alpha)", cells,
           regime="ratio of per-SNP variance contribution between a p=0.5 band "
                  "and a p=0.1 band under the alpha model")


def main():
    for fn in (test_ldsc, test_effect_summaries, test_hwe_fork,
               test_expected_effect_multiplier):
        try:
            fn()
        except Exception:
            import traceback
            traceback.print_exc()
    json.dump(RESULTS, open("battery_ldsc_results.json", "w"), indent=1,
              default=str)
    print("\n\n================ SUMMARY ================")
    for r in RESULTS:
        w = r.get("worst", {})
        print("%-12s %-50s worst %9.2f sems, %7.2f%% rel"
              % (r["verdict"], r["name"], w.get("sems_off", float("nan")),
                 100 * w.get("rel_err", float("nan"))))


if __name__ == "__main__":
    main()
