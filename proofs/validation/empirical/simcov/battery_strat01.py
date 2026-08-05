"""Battery strat01: is the standardized residual PGS bias LINEAR in confounding?

WHAT IS ON TRIAL, and what is deliberately not.  `PCCorrectability.Diagnostic`
carries two definitions:

    pgsStratificationRiskCoefficient = sqrt(L*Sbar) * sqrt(H') / sigma_beta
                                         * ascertainmentAmplification(Phi, Lambda)
    standardizedResidualPGSBias      = pgsStratificationRiskCoefficient * confounding

The COEFFICIENT's functional form is NOT tested here and this battery records no
verdict on it.  Its shape is transcribed from Blanc, Mawass and Berg, and the
corpus states nowhere what the bias is standardized BY -- under a coherent sum
over ascertained variants the exponent on `L` is 1 and under a root-mean-square
over the loading geometry it is 1/2, so any oracle I write for it would be
testing my reconstruction rather than the definition.  That one is reported
upward as not done.

What IS tested is the SECOND definition's own claim, in its own words:
"linear in the confounding magnitude once the study design and residual
target-axis geometry are fixed".  That claim is independent of the coefficient's
formula -- whatever the coefficient is, the bias is asserted to be proportional
to `confounding` at fixed design -- and it is the claim
`criticalConfoundingMagnitude` inverts and `signal_exceeds_threshold_iff_...`
relies on.  A diagnostic that reports how much confounding it would take to
produce an observed signal is wrong by exactly the amount the proportionality is
wrong.

CONVENTIONS, declared before any number is read.
  * `confounding` is the coefficient `c` of the ancestry coordinate in the
    expected phenotype: `y = c*a + noise`, with `a` standardized.  A slope on a
    standardized axis, not a variance and not a variance ratio.
  * The bias observable is the regression SLOPE of the polygenic score on the
    TARGET panel's ancestry axis, divided by `sigma_beta`.  A slope over an
    effect scale, so it is unitless in effect units, which is what
    "standardized" is taken to mean.  `sigma_beta` is a fixed design constant
    here and cancels out of every ratio this battery reports, so no reading of
    it can create or hide the effect under test.
  * The GWAS is a CONFOUNDED NULL: no variant has a causal effect, so every
    nonzero estimate is stratification.

TWO ARMS, and the difference between them is the whole finding.

  ARM F -- the ascertained SNP SET held fixed across the confounding sweep.
    Selected once at a reference confounding level and reused.  This arm is
    REPORTED AND NOT RECORDED: with the set fixed, the marginal estimate is
    `c * Cov(a, g_l) / Var(g_l)` plus c-independent noise, so linearity is
    algebra and a battery that recorded it would be reporting the RNG.  It is
    run anyway, because a design that cannot reproduce the tautology when the
    tautology holds has a bug rather than a finding.

  ARM A -- the ascertainment THRESHOLD held fixed instead, and the SNP set
    re-selected at each confounding level, which is what a real GWAS does and
    what the corpus's own `ascertainmentAmplification(Phi, Lambda)` factor
    exists to model.  This is the recorded arm.  The corpus carries
    ascertainment as a MULTIPLIER on a coefficient, so it asserts that
    ascertainment does not disturb the proportionality.

THE PREDICTION IS OUT OF SAMPLE.  The coefficient is measured as
`bias(c0)/c0` on FOUR replicates at a single anchor `c0`, and the prediction
`K*c` is then compared against measurements on EIGHT DISJOINT replicates at
confounding levels spanning eightfold away from the anchor.  Nothing in the
anchor replicates forces the far cells to be any particular multiple of it.
That is why `argument_source="model"` is honest here: no input is estimated from
the replicates the oracle measures.

COMPETITOR: `K * c0 * (c/c0)^2`, the quadratic that agrees with the body EXACTLY
at the anchor and diverges from it in both directions.  A rival that matches
where the coefficient was calibrated is the only kind that tests the shape
rather than the calibration.

CONTROL: the same pipeline, same code path, with the confounder switched off and
a REAL additive genetic effect of known size put in instead.  The mean marginal
estimate at causal variants must recover it.  Independent of every body under
test, and it fails on any error in the genotype simulation, the marginal
regression or the standardization.

FRESHNESS: prints FRESHNESS=OK only if its own source carries the token below.
"""
import math
import os

import numpy as np

from battery_core import RESULTS, dump_results, record

FRESH_TOKEN = "SIMCOV-BATTERY-STRAT01-GODWIT-20260805"


def freshness():
    try:
        src = open(os.path.abspath(__file__)).read()
    except Exception:
        print("FRESHNESS=STALE (cannot read own source)")
        return
    print("FRESHNESS=%s (token %s)"
          % ("OK" if src.count(FRESH_TOKEN) >= 2 else "STALE", FRESH_TOKEN))


SIGMA_BETA = 0.02          # fixed design constant; cancels from every ratio


def draw_panel(rng, n, p0, u, sigma_f=1.0):
    """Genotypes for `n` individuals with an ancestry gradient at every SNP."""
    a = rng.normal(0, sigma_f, n).astype(np.float32)
    p = np.clip(p0[None, :] + np.outer(a, u), 0.01, 0.99).astype(np.float32)
    g = rng.binomial(2, p).astype(np.float32)
    return a, g


def one_rep(rng, n_gwas, n_target, L, c, thresh, fixed_set=None,
            causal_beta=None):
    """One GWAS panel, one target panel, one standardized bias.

    Returns (standardized bias, ascertained index set, mean estimate at causal
    variants when `causal_beta` is supplied).
    """
    p0 = rng.uniform(0.15, 0.5, L).astype(np.float32)
    u = rng.normal(0, 0.05, L).astype(np.float32)      # ancestry loadings

    a, g = draw_panel(rng, n_gwas, p0, u)
    y = c * a + rng.normal(0, 1, n_gwas).astype(np.float32)
    if causal_beta is not None:
        y = y + (g - g.mean(0)) @ causal_beta

    gc = g - g.mean(0)
    yc = y - y.mean()
    var = (gc * gc).mean(0)
    var[var <= 0] = np.inf
    beta = (gc * yc[:, None]).mean(0) / var
    resid_var = float(yc.var())
    se = np.sqrt(resid_var / (n_gwas * var))
    z = beta / se

    picked = np.flatnonzero(np.abs(z) > thresh) if fixed_set is None else fixed_set

    causal_hat = None
    if causal_beta is not None:
        idx = np.flatnonzero(causal_beta != 0)
        causal_hat = float(np.mean(beta[idx] / causal_beta[idx]))

    if len(picked) == 0:
        return 0.0, picked, causal_hat

    at, gt = draw_panel(rng, n_target, p0, u)
    pgs = gt[:, picked] @ beta[picked]
    slope = float(np.cov(pgs, at)[0, 1] / at.var())
    return slope / SIGMA_BETA, picked, causal_hat


def sweep(seed0, reps, cs, arm, n_gwas=8000, n_target=8000, L=1500,
          thresh=3.0, c_ref=0.4):
    rng = np.random.default_rng(seed0)
    out = {}
    for c in cs:
        vals, nhits = [], []
        for r in range(reps):
            sub = np.random.default_rng(seed0 + 7919 * r + int(1000 * c))
            fixed = None
            if arm == "F":
                # ascertain ONCE at the reference level, on this replicate's own
                # panel, then reuse the same set at every confounding level
                _, fixed, _ = one_rep(np.random.default_rng(seed0 + 7919 * r),
                                      n_gwas, n_target, L, c_ref, thresh)
            b, picked, _ = one_rep(sub, n_gwas, n_target, L, c, thresh,
                                   fixed_set=fixed)
            vals.append(b)
            nhits.append(len(picked))
        out[c] = (float(np.mean(vals)),
                  float(np.std(vals, ddof=1) / math.sqrt(reps)),
                  float(np.mean(nhits)))
    return out


def main():
    freshness()
    print("FRESHNESS token literal: SIMCOV-BATTERY-STRAT01-GODWIT-20260805")

    cs = (0.15, 0.3, 0.4, 0.8, 1.2)
    c_ref = 0.4
    reps_anchor, reps_test = 4, 8

    # ---- ARM A: threshold fixed, SNP set re-ascertained at every level ------
    anchor = sweep(11117, reps_anchor, (c_ref,), arm="A")
    K = anchor[c_ref][0] / c_ref
    print("\n  arm A anchor: c=%.2f bias %.4f ± %.4f over %d hits -> K = %.4f"
          % (c_ref, anchor[c_ref][0], anchor[c_ref][1], anchor[c_ref][2], K))

    test = sweep(880011, reps_test, cs, arm="A")
    body, quad = [], []
    for c in cs:
        mean, sem, nh = test[c]
        lab = "c=%.2f (mean %.0f ascertained)" % (c, nh)
        print("  %-30s linear K*c %.4f   quadratic %.4f   measured %.4f ± %.4f"
              % (lab, K * c, K * c_ref * (c / c_ref) ** 2, mean, sem))
        body.append(dict(design=lab, lean=K * c, truth=mean, sem=sem))
        quad.append(dict(design=lab, lean=K * c_ref * (c / c_ref) ** 2,
                         truth=mean, sem=sem))

    # ---- ARM F: SNP set fixed. Reported, not recorded. ---------------------
    print("\n  arm F (ascertained set held fixed across the sweep -- linearity "
          "is algebra here, so this is a design check and is NOT recorded):")
    anchorF = sweep(22227, reps_anchor, (c_ref,), arm="F", c_ref=c_ref)
    KF = anchorF[c_ref][0] / c_ref
    testF = sweep(990022, reps_test, cs, arm="F", c_ref=c_ref)
    for c in cs:
        mean, sem, nh = testF[c]
        print("    c=%.2f  linear %.4f  measured %.4f ± %.4f  (%.1f sems)"
              % (c, KF * c, mean, sem,
                 abs(KF * c - mean) / sem if sem > 0 else float("nan")))

    # ---- control: no confounder, a real additive effect of known size ------
    rng = np.random.default_rng(4242)
    L = 1500
    cb = np.zeros(L, dtype=np.float32)
    cb[:200] = 0.05
    ratios = []
    for r in range(6):
        _, _, hat = one_rep(np.random.default_rng(5150 + r), 8000, 8000, L,
                            0.0, 3.0, causal_beta=cb)
        ratios.append(hat)
    control = dict(design="no confounder, true additive effects: the mean "
                          "marginal estimate recovers the effect it was given",
                   lean=1.0, truth=float(np.mean(ratios)),
                   sem=float(np.std(ratios, ddof=1) / math.sqrt(len(ratios))))
    print("\n  CONTROL %s: predicted %.4f measured %.4f ± %.4f"
          % (control["design"], control["lean"], control["truth"],
             control["sem"]))

    reg = ("confounded null: 1500 candidate variants with an ancestry-gradient "
           "allele frequency, 8000 GWAS individuals and 8000 target "
           "individuals, no variant causal, phenotype c*a + noise on a "
           "standardized ancestry axis. Variants are ascertained at a FIXED "
           "|z| > 3 threshold and re-selected at every confounding level, "
           "which is the regime the corpus's own ascertainmentAmplification "
           "factor models. The observable is the regression slope of the "
           "polygenic score on the TARGET panel's ancestry axis over "
           "sigma_beta. The coefficient is measured on four replicates at "
           "c = 0.4 and the prediction compared on eight disjoint replicates "
           "across an eightfold range of c")
    MODEL = dict(regime=reg, control=control, realised_inputs=True,
                 argument_source="model")

    record("standardizedResidualPGSBias", "Diagnostic.lean",
           "pgsStratificationRiskCoefficient * confounding, i.e. K * c", body,
           **MODEL)
    record("standardizedResidualPGSBias [quadratic in confounding, competing]",
           "Diagnostic.lean", "K * c_ref * (c / c_ref)^2", quad, **MODEL)

    dump_results("battery_strat01_results.json")
    print("\n================ SUMMARY ================")
    for rec in RESULTS:
        w = rec.get("worst", {}) or {}
        print("%-24s %-58s worst %9.2f sems, %8.2f%% rel"
              % (rec["verdict"], rec["name"][:58], w.get("sems_off", float("nan")),
                 100 * w.get("rel_err", float("nan"))))


if __name__ == "__main__":
    main()
