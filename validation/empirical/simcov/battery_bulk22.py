"""Battery 22: the cross-ancestry recalibration and tagging scalars.

Everything here is measured from SIMULATED INDIVIDUALS -- genotypes drawn,
phenotypes built, then realised correlations, regression slopes and variance
ratios read off the sample. No body under test is ever used to generate the data
it is compared against, which is the distinction between a measurement and the
generative self-test that `expectedSquaredEffect` turned out to be.

Where a body's reading is ambiguous, the competing reading is carried on the
same cells so the data chooses:

  `taggedEffect = causalEffect * tagR2` -- the marginal effect of a tag SNP is
      `beta_causal * r` in the standardized parametrization, not `beta_causal *
      r^2`. Both are carried. This one is decidable: at r = 0.5 they differ
      twofold.

  `prevalenceScaledR2 = h2 * K(1-K)` -- on the observed 0/1 scale the variance a
      liability-threshold genetic value explains is `h2_liab * phi(t)^2`, and
      the R-squared is that over `K(1-K)`. The body is neither, so both the
      variance reading and the ratio reading are carried and reported.
"""
import json
import math

import numpy as np
from scipy import stats

import simlib
from battery_core import RESULTS, record


def r2_of(pred, y):
    """Realised squared correlation -- the R^2 an optimal linear recalibration
    of `pred` attains, since a linear rescale cannot change the correlation."""
    return float(np.corrcoef(pred, y)[0, 1] ** 2)


def group_a():
    """ancestryRecalibratedR2, effectTurnoverR2Loss, ancestryRecalibratedSlope."""
    rng = np.random.default_rng(22001)
    n, m, h2 = 200000, 400, 0.5
    cells_r2, cells_loss, cells_slope, cells_slope_alt = [], [], [], []
    control = None
    for rho, alpha in ((0.9, 1.0), (0.7, 1.0), (0.5, 1.0), (0.9, 1.6), (0.7, 0.6)):
        bs = rng.normal(0, math.sqrt(h2 / m), m)
        bt = rho * bs + math.sqrt(max(1 - rho ** 2, 0)) * rng.normal(
            0, math.sqrt(h2 / m), m)
        # source population
        Gs = rng.normal(0, 1, (n, m))
        gs = Gs @ bs
        ys = gs + rng.normal(0, math.sqrt(max(1 - gs.var(), 1e-6)), n)
        pgs_s = Gs @ bs
        r2_source = r2_of(pgs_s, ys)
        # target population: genotypes scaled by alpha, so the SOURCE-weighted
        # score has variance alpha^2 times its source variance
        Gt = rng.normal(0, 1, (n, m)) * alpha
        gt = Gt @ bt
        yt = gt + rng.normal(0, math.sqrt(max(1 - gt.var(), 1e-6)), n)
        pgs_t = Gt @ bs                      # source weights, target genotypes
        r2_target = r2_of(pgs_t, yt)
        # realised OLS slope of target phenotype on the source-weighted score
        slope = float(np.cov(pgs_t, yt, ddof=1)[0, 1] / pgs_t.var(ddof=1))
        # realised source slope and score-scale ratio, both measured
        b_source = float(np.cov(pgs_s, ys, ddof=1)[0, 1] / pgs_s.var(ddof=1))
        alpha_meas = float(pgs_t.std(ddof=1) / pgs_s.std(ddof=1))
        sem_r2 = 2 * abs(r2_target) * math.sqrt(max(1 - r2_target, 1e-6) / n)
        sem_slope = abs(slope) * math.sqrt(2.0 / n) + 1e-9
        lab = "rho=%.1f alpha=%.1f" % (rho, alpha)
        print("  %-18s r2_src=%.4f r2_tgt=%.4f (lean %.4f) | slope=%.4f "
              "(lean %.4f, alt %.4f)"
              % (lab, r2_source, r2_target, r2_source * rho ** 2, slope,
                 rho * b_source / alpha_meas, rho * b_source * alpha_meas))
        cells_r2.append(dict(design=lab, lean=r2_source * rho ** 2,
                             truth=r2_target, sem=max(sem_r2, 1e-5)))
        cells_loss.append(dict(design=lab, lean=r2_source * (1 - rho ** 2),
                               truth=r2_source - r2_target,
                               sem=max(sem_r2, 1e-5)))
        cells_slope.append(dict(design=lab, lean=rho * b_source / alpha_meas,
                                truth=slope, sem=sem_slope))
        cells_slope_alt.append(dict(design=lab,
                                    lean=rho * b_source * alpha_meas,
                                    truth=slope, sem=sem_slope))
        if rho == 0.9 and alpha == 1.0:
            # control: with source weights in the SOURCE population the slope
            # is 1 by construction of the simulated phenotype -- an independent
            # fact about the design, measured not asserted
            control = dict(design=lab + " [source-population slope = 1]",
                           lean=1.0, truth=b_source,
                           sem=abs(b_source) * math.sqrt(2.0 / n) + 1e-9)
    reg = ("400 causal variants, standardized genotypes, 200000 individuals per "
           "population; target effects are rho-correlated with source effects "
           "and the target genotype scale is alpha. Every quantity compared "
           "against is a REALISED sample statistic -- squared correlation, OLS "
           "slope, score standard deviation -- never a parameter fed in")
    record("ancestryRecalibratedR2", "AncestryCalibration.lean",
           "r2Source * rhoSq", cells_r2, regime=reg, control=control)
    record("effectTurnoverR2Loss", "AncestryCalibration.lean",
           "r2Source * (1 - rhoSq)", cells_loss, regime=reg, control=control)
    record("ancestryRecalibratedSlope", "AncestryCalibration.lean",
           "rho * (bSource * alpha) / alpha ^ 2  =  rho * bSource / alpha",
           cells_slope, regime=reg, control=control)
    record("ancestryRecalibratedSlope [rho*b*alpha reading, competing]",
           "AncestryCalibration.lean", "rho * bSource * alpha",
           cells_slope_alt, regime=reg, control=control)


def group_b():
    """taggedEffect = causalEffect * tagR2, against the r-not-r^2 reading."""
    rng = np.random.default_rng(22002)
    n = 2000000
    cells, cells_alt = [], []
    control = None
    for beta_c, r in ((0.3, 0.9), (0.3, 0.5), (0.5, 0.7), (0.2, 0.3)):
        # a causal variant and a tag correlated with it at r, both standardized
        gc = rng.normal(0, 1, n)
        gt = r * gc + math.sqrt(max(1 - r ** 2, 0)) * rng.normal(0, 1, n)
        y = beta_c * gc + rng.normal(0, math.sqrt(max(1 - beta_c ** 2, 1e-6)), n)
        # the tag's MARGINAL effect: the OLS slope of y on the tag
        slope = float(np.cov(gt, y, ddof=1)[0, 1] / gt.var(ddof=1))
        sem = math.sqrt((1 - slope ** 2) / n) + 1e-9
        lab = "beta_c=%.1f r=%.1f (r2=%.2f)" % (beta_c, r, r ** 2)
        print("  %-26s tag slope = %.5f ± %.5f  | lean(r2) %.5f  alt(r) %.5f"
              % (lab, slope, sem, beta_c * r ** 2, beta_c * r))
        cells.append(dict(design=lab, lean=beta_c * r ** 2, truth=slope,
                          sem=sem))
        cells_alt.append(dict(design=lab, lean=beta_c * r, truth=slope,
                              sem=sem))
        if r == 0.9:
            control = dict(design=lab + " [causal slope = beta_c]",
                           lean=beta_c,
                           truth=float(np.cov(gc, y, ddof=1)[0, 1]
                                       / gc.var(ddof=1)),
                           sem=math.sqrt((1 - beta_c ** 2) / n) + 1e-9)
    reg = ("one causal variant and one tag at correlation r, both standardized, "
           "2e6 individuals; the observable is the tag's realised marginal OLS "
           "slope. r is swept so r and r^2 separate by up to threefold")
    # THE CHALLENGER IS THE BODY NOW. `AncestrySpecificArchitecture.lean` reads
    # `causalEffect * tagR`, and this battery is why: it recorded `* tagR2` as
    # the corpus row, `* r` as the challenger, and the corpus took the
    # challenger. The labels stayed, so the ledger has carried a FALSIFIED
    # corpus row for a formula the corpus corrected away from -- which that
    # declaration's docstring has to spend a paragraph explaining, ending "the
    # ledger cannot say this about itself". It can, once the roles are right.
    # realised_inputs=True: `r` is the correlation the design IMPOSED between
    # the two standardized variants and `beta_c` the effect it assigned, both
    # exact rather than estimated off these individuals, so there is no
    # nominal-versus-realised gap the disagreement could be.
    record("taggedEffect", "AncestrySpecificArchitecture.lean",
           "causalEffect * tagR", cells_alt, regime=reg, control=control,
           realised_inputs=True)
    record("taggedEffect [the superseded causalEffect * tagR2, competing]",
           "AncestrySpecificArchitecture.lean", "causalEffect * tagR2", cells,
           regime=reg, control=control, realised_inputs=True)


def group_c():
    """prevalenceScaledR2 = h2 * K(1-K), both readings."""
    rng = np.random.default_rng(22003)
    n = 3000000
    cells_var, cells_r2, cells_std = [], [], []
    control = None
    for h2, K in ((0.5, 0.01), (0.5, 0.1), (0.5, 0.5), (0.2, 0.05)):
        g = rng.normal(0, math.sqrt(h2), n)
        liab = g + rng.normal(0, math.sqrt(1 - h2), n)
        t = stats.norm.isf(K)
        Y = (liab > t).astype(float)
        K_meas = float(Y.mean())
        # variance of the observed-scale phenotype explained by the genetic value
        var_expl = float(np.cov(g, Y, ddof=1)[0, 1] ** 2 / g.var(ddof=1))
        r2_obs = var_expl / Y.var(ddof=1)
        phi_t = float(stats.norm.pdf(t))
        lab = "h2=%.1f K=%.2f" % (h2, K)
        sem_v = var_expl * math.sqrt(2.0 / n) * 3
        print("  %-16s K_meas=%.4f  var_expl=%.6f  R2_obs=%.5f | "
              "lean h2*K(1-K)=%.6f  standard h2*phi^2=%.6f"
              % (lab, K_meas, var_expl, r2_obs, h2 * K * (1 - K),
                 h2 * phi_t ** 2))
        cells_var.append(dict(design=lab, lean=h2 * K * (1 - K),
                              truth=var_expl, sem=max(sem_v, 1e-9)))
        cells_r2.append(dict(design=lab + " [as R^2]", lean=h2 * K * (1 - K),
                             truth=r2_obs,
                             sem=max(r2_obs * math.sqrt(2.0 / n) * 3, 1e-9)))
        cells_std.append(dict(design=lab, lean=h2 * phi_t ** 2,
                              truth=var_expl, sem=max(sem_v, 1e-9)))
        if K == 0.1:
            control = dict(design=lab + " [realised prevalence = K]",
                           lean=K, truth=K_meas,
                           sem=math.sqrt(K * (1 - K) / n))
    reg = ("liability-threshold model, 3e6 individuals, liability = genetic "
           "value + noise with the genetic value at heritability h2 and the "
           "threshold set to give prevalence K; the observables are the "
           "variance of the binary outcome explained by the genetic value and "
           "the corresponding R^2. K is swept fiftyfold, over which "
           "K(1-K) and phi(t)^2 move in opposite directions")
    record("prevalenceScaledR2 [read as explained VARIANCE]",
           "AncestryCalibration.lean", "h2 * (prevalence * (1 - prevalence))",
           cells_var, regime=reg, control=control)
    record("prevalenceScaledR2 [read as an R^2]", "AncestryCalibration.lean",
           "h2 * (prevalence * (1 - prevalence))", cells_r2, regime=reg,
           control=control)
    record("[competing] liability-scale standard h2 * phi(t)^2",
           "AncestryCalibration.lean", "h2 * phi(threshold)^2", cells_std,
           regime=reg, control=control)


def main():
    for fn in (group_b, group_c, group_a):
        print("\n===== %s =====" % fn.__name__)
        try:
            fn()
        except Exception as e:
            print("*** %s RAISED %r" % (fn.__name__, e))
            import traceback
            traceback.print_exc()
    json.dump(RESULTS, open("battery_bulk22_results.json", "w"), indent=1,
              default=str)
    print("\n================ SUMMARY ================")
    for r in RESULTS:
        w = r.get("worst", {})
        print("%-22s %-52s worst %9.2f sems, %7.2f%% rel"
              % (r["verdict"], r["name"], w.get("sems_off", float("nan")),
                 100 * w.get("rel_err", float("nan"))))


if __name__ == "__main__":
    main()
