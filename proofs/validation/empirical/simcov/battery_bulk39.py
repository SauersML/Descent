"""Battery 39: the ancestry recalibration trio, with both earlier faults fixed.

`battery_bulk22.py` group A reported four falsifications here and they were
withdrawn unrecorded, for two reasons that are both fixed now:

  NOMINAL vs REALISED rho. The prediction was fed the rho the effects were drawn
  at, while the drawn vectors realise a correlation off by O(1/sqrt(m)) -- 5% at
  m = 400, which is the whole size of the discrepancy that run reported. Here
  rho is MEASURED from the drawn vectors.

  THE alpha CONVENTION. `ancestryRecalibratedSlope` transports the numerator by
  alpha and the denominator by alpha^2, which is the optimal slope only if alpha
  is a ratio of STANDARD DEVIATIONS. That run used an sd ratio but could not say
  whether the body wanted it; the definition's docstring now states the sd
  convention explicitly, so the comparison is well posed.

Bodies under test, all read against realised sample statistics:

  ancestryRecalibratedR2   r2Source * rhoSq        vs realised target R^2
  effectTurnoverR2Loss     r2Source * (1 - rhoSq)  vs realised R^2 shortfall
  ancestryRecalibratedSlope rho*b*alpha/alpha^2    vs realised OLS slope

Competitors: for the slope, the variance-ratio reading `rho*b/sqrt(alpha)` that
the docstring says the body is NOT; for the R2, `r2Source * rho` (unsquared).
"""
import json
import math

import numpy as np

from battery_core import RESULTS, record


def main():
    rng = np.random.default_rng(39001)
    n, m = 400000, 4000
    cells_r2, cells_loss, cells_slope = [], [], []
    c_r2_lin, c_slope_var = [], []
    control = None
    for rho_nom, scale in ((0.9, 1.0), (0.7, 1.0), (0.5, 1.0),
                           (0.8, 1.5), (0.6, 0.7)):
        h2 = 0.5
        bs = rng.normal(0, math.sqrt(h2 / m), m)
        bt = rho_nom * bs + math.sqrt(max(1 - rho_nom ** 2, 0)) * rng.normal(
            0, math.sqrt(h2 / m), m)
        # REALISED effect correlation, not the nominal one
        rho = float(np.dot(bs, bt) / (np.linalg.norm(bs) * np.linalg.norm(bt)))
        # source population
        Gs = rng.normal(0, 1, (n, m))
        pgs_s = Gs @ bs
        ys = pgs_s + rng.normal(0, math.sqrt(max(1 - pgs_s.var(), 1e-6)), n)
        r2_src = float(np.corrcoef(pgs_s, ys)[0, 1] ** 2)
        b_src = float(np.cov(pgs_s, ys, ddof=1)[0, 1] / pgs_s.var(ddof=1))
        # Target genotypes stay STANDARDIZED, so the target heritability is set
        # by `bt` alone. The score-scale ratio is created by rescaling the
        # WEIGHTS instead. An earlier version scaled the target genotypes, which
        # changed Var(Gt.bt) by scale^2 and so changed the target heritability --
        # a confound, since `ancestryRecalibratedR2` has no alpha in it at all
        # and cannot be tested against cells whose h2 moved for another reason.
        Gt = rng.normal(0, 1, (n, m))
        gt = Gt @ bt
        yt = gt + rng.normal(0, math.sqrt(max(1 - gt.var(), 1e-6)), n)
        pgs_t = Gt @ (scale * bs)             # rescaled source weights
        r2_tgt = float(np.corrcoef(pgs_t, yt)[0, 1] ** 2)
        slope = float(np.cov(pgs_t, yt, ddof=1)[0, 1] / pgs_t.var(ddof=1))
        # alpha as a STANDARD-DEVIATION ratio, the documented convention
        alpha = float(pgs_t.std(ddof=1) / pgs_s.std(ddof=1))
        sem_r2 = 2 * abs(r2_tgt) * math.sqrt(max(1 - r2_tgt, 1e-6) / n)
        sem_sl = abs(slope) * math.sqrt(2.0 / n) + 1e-9
        lab = "rho=%.2f alpha=%.2f" % (rho, alpha)
        print("  %-22s r2_src=%.4f r2_tgt=%.4f (lean %.4f) | slope=%.4f "
              "(lean %.4f)"
              % (lab, r2_src, r2_tgt, r2_src * rho ** 2, slope,
                 rho * b_src / alpha))
        cells_r2.append(dict(design=lab, lean=r2_src * rho ** 2, truth=r2_tgt,
                             sem=max(sem_r2, 1e-9)))
        c_r2_lin.append(dict(design=lab, lean=r2_src * rho, truth=r2_tgt,
                             sem=max(sem_r2, 1e-9)))
        cells_loss.append(dict(design=lab, lean=r2_src * (1 - rho ** 2),
                               truth=r2_src - r2_tgt, sem=max(sem_r2, 1e-9)))
        cells_slope.append(dict(design=lab, lean=rho * b_src / alpha,
                                truth=slope, sem=sem_sl))
        c_slope_var.append(dict(design=lab,
                                lean=rho * b_src / math.sqrt(alpha),
                                truth=slope, sem=sem_sl))
        if rho_nom == 0.9 and scale == 1.0:
            # control: in the SOURCE population the source-weighted score has
            # slope 1 against its own phenotype, by construction of the sim
            control = dict(design=lab + " [source slope = 1]", lean=1.0,
                           truth=b_src,
                           sem=abs(b_src) * math.sqrt(2.0 / n) + 1e-9)
    reg = ("800 causal variants, standardized genotypes, 400000 individuals per "
           "population, both with STANDARDIZED genotypes so the target "
           "heritability is set by its own effects alone; the score-scale ratio "
           "is produced by rescaling the WEIGHTS, which moves alpha without "
           "touching h2. rho is the REALISED correlation of the drawn effect "
           "vectors and alpha the REALISED score sd ratio -- every input "
           "measured, none nominal. m = 4000 puts the finite-panel residual "
           "near 1.6%")
    record("ancestryRecalibratedR2", "AncestryCalibration.lean",
           "r2Source * rhoSq", cells_r2, regime=reg, control=control)
    record("ancestryRecalibratedR2 [rho unsquared, competing]",
           "AncestryCalibration.lean", "r2Source * rho", c_r2_lin, regime=reg,
           control=control)
    record("effectTurnoverR2Loss", "AncestryCalibration.lean",
           "r2Source * (1 - rhoSq)", cells_loss, regime=reg, control=control)
    record("ancestryRecalibratedSlope", "AncestryCalibration.lean",
           "rho * (bSource * alpha) / alpha^2, alpha an sd ratio", cells_slope,
           regime=reg, control=control)
    record("ancestryRecalibratedSlope [variance-ratio reading, competing]",
           "AncestryCalibration.lean", "rho * bSource / sqrt(alpha)",
           c_slope_var, regime=reg, control=control)
    json.dump(RESULTS, open("battery_bulk39_results.json", "w"), indent=1,
              default=str)
    print("\n================ SUMMARY ================")
    for r in RESULTS:
        w = r.get("worst", {})
        print("%-22s %-52s worst %9.2f sems, %7.2f%% rel"
              % (r["verdict"], r["name"], w.get("sems_off", float("nan")),
                 100 * w.get("rel_err", float("nan"))))


if __name__ == "__main__":
    main()
