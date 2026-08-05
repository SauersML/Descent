"""battery_dgpcov4.  FRESHNESS GUARD: DGPCOV4-2026-08-04-D

C3: multiTraitDiscoveryNCP under BOTH readings of `priorVariance`, on the same
    cells.  The composition passes a `multiTraitEffectiveSampleSize` -- whose
    `1/n` slots are sampling VARIANCES of the effect estimate -- into
    `discoveryNCP`, which supplies the genotype variance itself.  The two agree
    exactly iff `priorVariance` is the prior variance of the STANDARDIZED effect
    (beta * sqrt(2p(1-p))), and disagree by a genotype-variance factor on the
    borrowed term otherwise.  Both are computed here; the design sweeps maf at
    fixed n*2p(1-p), so the realized noncentrality is invariant across the sweep
    and only a scale error can move with maf.

    argument_source: mean(chi2)-1 over independent replicate cohort PAIRS with
    genotypes drawn and OLS run; the borrowing weights are the inverse-variance
    rule fixed before any formula is evaluated; beta1 is held FIXED so the
    statistic is a frequentist noncentrality and shrinkage is not credited.
"""
import json
import numpy as np

GUARD = "DGPCOV4-2026-08-04-D"
rng = np.random.default_rng(555)
rows = []
beta1 = 0.05
reps = 8000
for (p, n1, n2, rg, tau2_std) in ((0.50, 4000, 8000, 0.7, 2.0e-4),
                                  (0.30, 6667, 13334, 0.7, 2.0e-4),
                                  (0.10, 11111, 22222, 0.7, 2.0e-4),
                                  (0.30, 6667, 13334, 0.7, 2.0e-5),
                                  (0.10, 11111, 22222, 0.7, 2.0e-5)):
    gv_nom = 2 * p * (1 - p)
    tau2_dosage = tau2_std / gv_nom          # the prior actually drawn from
    b2 = rg * beta1 + np.sqrt((1 - rg ** 2) * tau2_dosage) * rng.normal(size=reps)

    def cohort(n, beta_vec):
        bh = np.empty(len(beta_vec) if hasattr(beta_vec, "__len__") else reps)
        vv = np.empty_like(bh)
        blk = 400
        m = len(bh)
        for s in range(0, m, blk):
            e = min(s + blk, m)
            g = rng.binomial(2, p, size=(e - s, n)).astype(float)
            bv = (beta_vec[s:e, None] if hasattr(beta_vec, "__len__")
                  else beta_vec)
            y = bv * g + rng.normal(0, 1.0, size=(e - s, n))
            gc = g - g.mean(axis=1, keepdims=True)
            sxx = (gc ** 2).sum(axis=1)
            bb = (gc * (y - y.mean(axis=1, keepdims=True))).sum(axis=1) / sxx
            r = (y - y.mean(axis=1, keepdims=True)) - bb[:, None] * gc
            bh[s:e] = bb
            vv[s:e] = (r ** 2).sum(axis=1) / (n - 2) / sxx
        return bh, vv

    bh1, v1 = cohort(n1, np.full(reps, beta1))
    bh2, v2 = cohort(n2, b2)
    w1 = 1.0 / v1
    w2 = rg ** 2 / ((1 - rg ** 2) * tau2_dosage + v2)
    bt = (w1 * bh1 + w2 * (bh2 / rg)) / (w1 + w2)
    chi2 = bt ** 2 * (w1 + w2)
    ncp = float(chi2.mean() - 1.0)
    se = float(chi2.std(ddof=1) / np.sqrt(reps))
    gv_real = float(np.mean(1.0 / (v1 * n1)))
    maf_hat = float((1 - np.sqrt(max(1 - 2 * gv_real, 0.0))) / 2)

    def compose(prior):
        neff = n1 + rg ** 2 / ((1 - rg ** 2) * prior + 1.0 / n2)
        return neff * beta1 ** 2 * 1.0 ** 2 * gv_real

    body_std = compose(tau2_std)          # priorVariance on the standardized scale
    body_dos = compose(tau2_dosage)       # priorVariance on the dosage scale
    c_n1 = n1 * beta1 ** 2 * gv_real
    c_small = (n1 + rg ** 2 * n2) * beta1 ** 2 * gv_real
    rows.append(dict(p=p, n1=n1, n2=n2, rg=rg, tau2_std=tau2_std,
                     tau2_dosage=tau2_dosage, gv_realized=gv_real,
                     maf_implied=maf_hat, n1_times_gv=n1 * gv_real,
                     ncp_measured=ncp, se=se,
                     body_priorVariance_standardized=body_std,
                     sems_standardized=abs(ncp - body_std) / se,
                     body_priorVariance_dosage=body_dos,
                     sems_dosage=abs(ncp - body_dos) / se,
                     competitor_n1_alone=c_n1,
                     sems_n1_alone=abs(ncp - c_n1) / se,
                     competitor_small_prior=c_small,
                     sems_small_prior=abs(ncp - c_small) / se))

out = {"group_c3_multiTraitDiscoveryNCP_convention": rows, "_guard": GUARD}
json.dump(out, open("battery_dgpcov4_results.json", "w"), indent=1, default=float)
print("FRESHNESS=%s" % GUARD)
for r in rows:
    print("p=%.2f tau2std=%.0e | meas=%.4f+-%.4f | std=%.4f (%.1f sems) "
          "dosage=%.4f (%.1f) n1only=%.4f (%.1f) small=%.4f (%.1f)"
          % (r["p"], r["tau2_std"], r["ncp_measured"], r["se"],
             r["body_priorVariance_standardized"], r["sems_standardized"],
             r["body_priorVariance_dosage"], r["sems_dosage"],
             r["competitor_n1_alone"], r["sems_n1_alone"],
             r["competitor_small_prior"], r["sems_small_prior"]))
