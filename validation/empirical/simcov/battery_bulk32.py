"""Battery 32: does the LD projection give the marginal effects a GWAS recovers?

`targetSourceEffectProjection` and its siblings are all the same shape --
`Sigma_tag_causal.mulVec beta` -- and they all rest on one claim: that applying
the LD cross-covariance to the CAUSAL effect vector yields the MARGINAL effects
an association scan actually estimates. That claim is measurable. Given
standardized variants, the marginal slope of the phenotype on tag j is
`cov(X_j, y) / var(X_j) = sum_c Sigma[j,c] * beta_c`, which is exactly the
matrix-vector product -- but whether the simulation agrees is a fact about the
genotypes, not about the algebra, because the oracle regresses simulated
phenotypes on simulated genotypes and never forms Sigma from beta.

Competitors on the same cells:

  beta padded to the tag panel   -- no LD projection at all, i.e. treating the
                                    marginal effect as the causal effect
  Sigma^2 . beta                 -- the projection applied twice, which is what
                                    a confusion between r and r^2 at the vector
                                    level would produce

LD is AR(1) with correlation rho between adjacent variants, so Sigma is dense
and non-trivial rather than diagonal, and rho is swept.
"""
import json
import math

import numpy as np

from battery_core import RESULTS, record


def main():
    rng = np.random.default_rng(32001)
    n, m = 400000, 40
    cells, c_none, c_sq = [], [], []
    control = None
    for rho in (0.9, 0.7, 0.4):
        # AR(1) LD: Sigma[i,j] = rho^|i-j|
        idx = np.arange(m)
        Sigma = rho ** np.abs(idx[:, None] - idx[None, :])
        L = np.linalg.cholesky(Sigma + 1e-10 * np.eye(m))
        X = rng.normal(0, 1, (n, m)) @ L.T          # standardized, LD = Sigma
        # a sparse causal subset
        beta = np.zeros(m)
        causal = np.array([5, 12, 23, 31])
        beta[causal] = rng.normal(0, 0.3, causal.size)
        g = X @ beta
        y = g + rng.normal(0, math.sqrt(max(1 - g.var(), 1e-6)), n)
        # measured marginal slopes: one univariate regression per variant
        marg = np.array([float(np.cov(X[:, j], y, ddof=1)[0, 1]
                               / X[:, j].var(ddof=1)) for j in range(m)])
        sem = float(np.std(y, ddof=1) / math.sqrt(n))
        pred = Sigma @ beta
        pred_sq = Sigma @ (Sigma @ beta)
        # report the worst-fitting coordinate, with the selection corrected for
        for name, p, bucket in (("projection", pred, cells),
                                ("no projection", beta, c_none),
                                ("projection twice", pred_sq, c_sq)):
            k = int(np.argmax(np.abs(p - marg)))
            bucket.append(dict(design="rho=%.1f worst coord j=%d" % (rho, k),
                               lean=float(p[k]), truth=float(marg[k]),
                               sem=sem))
        print("  rho=%.1f  worst |pred-marg| = %.5f (projection), %.5f (none), "
              "%.5f (twice);  sem %.5f"
              % (rho, float(np.max(np.abs(pred - marg))),
                 float(np.max(np.abs(beta - marg))),
                 float(np.max(np.abs(pred_sq - marg))), sem))
        if rho == 0.9:
            # control: at a CAUSAL variant with no LD neighbours in the panel
            # the marginal slope is the causal effect itself. Coordinate 5 has
            # neighbours, so use the realised total genetic variance instead --
            # an independent quantity on the same run.
            control = dict(design="rho=0.9 [realised Var(g) vs beta'.Sigma.beta]",
                           lean=float(beta @ Sigma @ beta),
                           truth=float(g.var(ddof=1)),
                           sem=float(g.var(ddof=1)) * math.sqrt(2.0 / n))
    reg = ("40 standardized variants with AR(1) LD (Sigma[i,j] = rho^|i-j|), "
           "four causal among them, 400000 individuals; the phenotype is built "
           "from the CAUSAL variants and the observable is the vector of "
           "univariate marginal slopes, one regression per variant. Reported at "
           "the worst-fitting coordinate of each candidate, which is the "
           "hardest cell for that candidate rather than an average that would "
           "hide a local miss")
    record("targetSourceEffectProjection [Sigma . beta as marginal effects]",
           "PortabilityDrift.lean", "Sigma_tag_causal.mulVec beta", cells,
           regime=reg, control=control, selected_from=40)
    record("[competing] no LD projection: marginal = causal effect",
           "PortabilityDrift.lean", "beta", c_none, regime=reg,
           control=control, selected_from=40)
    record("[competing] projection applied twice", "PortabilityDrift.lean",
           "Sigma . (Sigma . beta)", c_sq, regime=reg, control=control,
           selected_from=40)
    json.dump(RESULTS, open("battery_bulk32_results.json", "w"), indent=1,
              default=str)
    print("\n================ SUMMARY ================")
    for r in RESULTS:
        w = r.get("worst", {})
        print("%-22s %-52s worst %9.2f sems, %7.2f%% rel"
              % (r["verdict"], r["name"], w.get("sems_off", float("nan")),
                 100 * w.get("rel_err", float("nan"))))


if __name__ == "__main__":
    main()
