"""battery_dgpcov3.  FRESHNESS GUARD: DGPCOV3-2026-08-04-C

C2  multiTraitDiscoveryNCP: is the composition
      discoveryNCP (multiTraitEffectiveSampleSize n1 n2 rg tau2) beta maf ld
    the realized noncentrality of the cross-trait-borrowing Wald test?

    The estimator is fixed FIRST and independently of the formula: beta2hat is
    an unbiased measurement of rg*beta1 with variance (1-rg^2)tau^2 + v2, so
    inverse-variance combination with beta1hat is the borrowing rule.  beta1 is
    HELD FIXED (not drawn from the prior), so the measured chi-square is a
    frequentist noncentrality and prior shrinkage is not credited as
    information.

    argument_source: the measured NCP is mean(chi2)-1 over independent
    replicate cohort pairs, with genotypes drawn and OLS actually run; maf and
    the tag-causal r are REMEASURED from the draws.  The prediction is computed
    from the Lean bodies at the raw arguments a caller would supply.

    Design: maf is swept at FIXED 1/v1 = n*2p(1-p), so the realized NCP is
    invariant across the sweep by construction while the composed prediction is
    not, if and only if the composition mixes a precision scale with a count
    scale.

A2  gwasDiscovered: the discovery probability the predicate's boundary marks,
    across a range of noncentralities.

SUPERSEDED, group C2 ONLY.  C2 supplies `priorVariance` on the DOSAGE effect
scale and reports the Lean composition off by 10 to 23 sems.  That is a
convention error in this script, not a defect in the body: `multiTraitEffective
SampleSize` reads its `1/n` slots as sampling variances, so its prior is on the
standardized effect scale, and on that reading the body matches at 0.1 to 1.3
sems.  `battery_dgpcov4.py` runs both readings on the same cells and is the
record.  The C2 numbers are kept because the dosage-scale column of
`battery_dgpcov4.py` reproduces them, and because the size of the error is the
argument for pinning the convention in the docstring.  Group A2 stands.
"""
import json
import numpy as np
from scipy import stats

GUARD = "DGPCOV3-2026-08-04-C"
out = {}
rng = np.random.default_rng(31337)


def gwas(n, p, beta, reps_g):
    """One OLS per cohort; returns (bhat, var_bhat, realized maf)."""
    g = rng.binomial(2, p, size=(reps_g, n)).astype(float)
    y = beta * g + rng.normal(0, 1.0, size=(reps_g, n))
    gc = g - g.mean(axis=1, keepdims=True)
    sxx = (gc ** 2).sum(axis=1)
    bh = (gc * (y - y.mean(axis=1, keepdims=True))).sum(axis=1) / sxx
    resid = (y - y.mean(axis=1, keepdims=True)) - bh[:, None] * gc
    s2 = (resid ** 2).sum(axis=1) / (n - 2)
    return bh, s2 / sxx, g.mean() / 2


rows = []
beta1 = 0.05
reps = 6000
for (p, n1, n2, rg, tau2) in ((0.50, 4000, 8000, 0.7, 4e-4),
                              (0.30, 6667, 13334, 0.7, 4e-4),
                              (0.10, 11111, 22222, 0.7, 4e-4),
                              (0.30, 6667, 13334, 0.7, 4e-5),
                              (0.10, 11111, 22222, 0.7, 4e-5)):
    vg_nom = 2 * p * (1 - p)
    b2 = rg * beta1 + np.sqrt((1 - rg ** 2) * tau2) * rng.normal(size=reps)
    bh1, v1, maf1 = gwas(n1, p, beta1, reps)
    bh2 = np.empty(reps)
    v2 = np.empty(reps)
    # trait-2 effect differs per replicate, so run cohorts in blocks
    blk = 500
    for s in range(0, reps, blk):
        e = min(s + blk, reps)
        g = rng.binomial(2, p, size=(e - s, n2)).astype(float)
        y = b2[s:e, None] * g + rng.normal(0, 1.0, size=(e - s, n2))
        gc = g - g.mean(axis=1, keepdims=True)
        sxx = (gc ** 2).sum(axis=1)
        bb = (gc * (y - y.mean(axis=1, keepdims=True))).sum(axis=1) / sxx
        resid = (y - y.mean(axis=1, keepdims=True)) - bb[:, None] * gc
        s2 = (resid ** 2).sum(axis=1) / (n2 - 2)
        bh2[s:e] = bb
        v2[s:e] = s2 / sxx
    # borrowing: bh2/rg is an unbiased reading of beta1 with variance
    # ((1-rg^2)tau2 + v2)/rg^2
    w1 = 1.0 / v1
    w2 = rg ** 2 / ((1 - rg ** 2) * tau2 + v2)
    bt = (w1 * bh1 + w2 * (bh2 / rg)) / (w1 + w2)
    sd = 1.0 / np.sqrt(w1 + w2)
    chi2 = (bt / sd) ** 2
    ncp_obs = float(chi2.mean() - 1.0)
    se = float(chi2.std(ddof=1) / np.sqrt(reps))
    # realized precision-scale inputs
    prec1 = float(np.mean(w1))
    prec2_raw = float(np.mean(1.0 / v2))
    vg_real = float(np.mean(1.0 / (v1 * n1)))          # realized genotype variance
    # THE LEAN COMPOSITION, at the arguments a caller supplies
    neff_corpus = n1 + rg ** 2 / ((1 - rg ** 2) * tau2 + 1.0 / n2)
    body = neff_corpus * beta1 ** 2 * 1.0 ** 2 * (2 * maf1 * (1 - maf1))
    # the precision-scale reading of the same formula
    neff_prec = prec1 + rg ** 2 / ((1 - rg ** 2) * tau2 + 1.0 / prec2_raw)
    prec_form = neff_prec * beta1 ** 2
    comp_n1 = n1 * beta1 ** 2 * (2 * maf1 * (1 - maf1))
    comp_small = (n1 + rg ** 2 * n2) * beta1 ** 2 * (2 * maf1 * (1 - maf1))
    rows.append(dict(p=p, n1=n1, n2=n2, rg=rg, tau2=tau2,
                     maf_realized=maf1, vg_realized=vg_real,
                     n1_times_vg=n1 * vg_real,
                     ncp_measured=ncp_obs, se=se,
                     body_composition=body, sems_body=abs(ncp_obs - body) / se,
                     precision_scale_form=prec_form,
                     sems_precision_scale=abs(ncp_obs - prec_form) / se,
                     competitor_n1_alone=comp_n1,
                     sems_n1_alone=abs(ncp_obs - comp_n1) / se,
                     competitor_small_prior=comp_small,
                     sems_small_prior=abs(ncp_obs - comp_small) / se))
out["group_c2_multiTraitDiscoveryNCP"] = rows

# ------------------------------------------------------------------ A2 ------
a2 = []
for (n, beta, p) in ((2000, 0.02, 0.3), (2000, 0.05, 0.3), (4000, 0.08, 0.3),
                     (8000, 0.12, 0.3)):
    reps = 20000
    bh, v, maf = gwas(n, p, beta, reps)
    chi2 = bh ** 2 / v
    lam_body = n * beta ** 2 * 1.0 * 2 * maf * (1 - maf)
    ncp_obs = float(chi2.mean() - 1.0)
    se = float(chi2.std(ddof=1) / np.sqrt(reps))
    a2.append(dict(n=n, beta=beta, maf_realized=maf, ncp_measured=ncp_obs,
                   se=se, body=lam_body, sems_body=abs(ncp_obs - lam_body) / se,
                   competitor_ploidy_half=lam_body / 2,
                   sems_ploidy_half=abs(ncp_obs - lam_body / 2) / se,
                   power_at_predicate_boundary=float((chi2 > lam_body).mean()),
                   power_theory_ncx2=float(stats.ncx2.sf(lam_body, 1, lam_body)),
                   power_se=float(np.sqrt(0.25 / reps))))
out["group_a2_gwasDiscovered_boundary"] = a2

out["_guard"] = GUARD
json.dump(out, open("battery_dgpcov3_results.json", "w"), indent=1, default=float)
print("FRESHNESS=%s" % GUARD)
print(json.dumps(out, indent=1, default=float))
