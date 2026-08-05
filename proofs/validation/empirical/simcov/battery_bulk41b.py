"""Battery 41b: the recalibration trio, and a screening design with resolution.

GROUP A -- `ancestryRecalibratedR2`, `effectTurnoverR2Loss`,
`ancestryRecalibratedSlope`. `battery_bulk22.py` reported all three FALSIFIED at
353, 353 and 185 sems. Two design faults were doing that work, and both are
fixed here so what remains is about the bodies:

  1. NOMINAL rho. Battery 22 evaluated the predictions at the rho that generated
     the effect vectors, while m = 400 vectors have a realised correlation off
     by O(1/sqrt(m)) ~ 5%, and at n = 200000 that is hundreds of sems.
     Battery 41 fixed this and the disagreement survived, so it was not the
     whole story.
  2. A TARGET HERITABILITY ABOVE ONE. Both batteries built the target phenotype
     as `gt + N(0, sqrt(max(1 - Var(gt), 1e-6)))`. At alpha = 1.6 the genetic
     variance is 1.28, the residual clamps to zero, and the target R-squared
     jumps to 0.82 against a prediction of 0.43 -- a factor of two that is the
     clamp, not the formula. Here the target residual is scaled to hold the
     target heritability at its declared value for every alpha.

  What remains after both fixes is a REGIME question, and the design answers it
  by splitting the cells. `r2Source * rhoSq` is the target R-squared only when
  the two populations have the SAME heritability: in general
  `r2_target = rho^2 * h2_target`, and `r2Source = h2_source`. Cells where the
  drawn target effect vector is rescaled to the source vector's norm (equal
  heritability) are run beside cells where it is not, on one code path.

GROUP G -- `screeningBreakEvenPrevalence`. Battery 40 scored MATCH at 0.00 sems,
and that number is the tell: the break-even prevalences were all near 0.005
while the prevalence grid had spacing 0.0068, so the error bar was 35% of the
quantity and a competing form differing by 1% matched too. The harm-to-benefit
ratio here puts the crossing between 0.1 and 0.5 and the grid is refined there,
so the competing readings separate.

FRESHNESS: prints FRESHNESS=OK only if its own source carries the token below.
"""
import json
import math
import os

import numpy as np

from battery_core import RESULTS, record

FRESH_TOKEN = "SIMCOV-BATTERY41B-PEREGRINE-20260804"


def freshness():
    try:
        src = open(os.path.abspath(__file__)).read()
    except Exception:
        print("FRESHNESS=STALE (cannot read own source)")
        return
    print("FRESHNESS=%s (token %s)"
          % ("OK" if src.count(FRESH_TOKEN) >= 2 else "STALE", FRESH_TOKEN))


def r2_of(pred, y):
    return float(np.corrcoef(pred, y)[0, 1] ** 2)


def group_a():
    rng = np.random.default_rng(41201)
    n, m, h2 = 200000, 400, 0.5
    eq_r2, eq_loss, eq_slope = [], [], []
    un_r2 = []
    c_nom, c_alt = [], []
    control = None
    designs = ((0.9, 1.0, True), (0.7, 1.0, True), (0.5, 1.0, True),
               (0.9, 1.6, True), (0.7, 0.6, True),
               (0.9, 1.0, False), (0.5, 1.0, False))
    for rho, alpha, equal_h2 in designs:
        bs = rng.normal(0, math.sqrt(h2 / m), m)
        bt = rho * bs + math.sqrt(max(1 - rho ** 2, 0)) * rng.normal(
            0, math.sqrt(h2 / m), m)
        if equal_h2:
            # Hold the TARGET heritability equal to the source's by rescaling
            # the target effect vector to the source vector's norm. This does
            # not touch the correlation between them, which is the quantity
            # under test.
            bt = bt * math.sqrt(float(bs @ bs) / float(bt @ bt))
        rho_hat = float(bs @ bt / math.sqrt((bs @ bs) * (bt @ bt)))
        Gs = rng.normal(0, 1, (n, m))
        gs = Gs @ bs
        # residual scaled to the DECLARED heritability, so h2 never clamps
        ys = gs + rng.normal(0, math.sqrt(gs.var() * (1 - h2) / h2), n)
        r2_source = r2_of(gs, ys)
        Gt = rng.normal(0, 1, (n, m)) * alpha
        gt = Gt @ bt
        yt = gt + rng.normal(0, math.sqrt(gt.var() * (1 - h2) / h2), n)
        pgs_t = Gt @ bs
        r2_target = r2_of(pgs_t, yt)
        slope = float(np.cov(pgs_t, yt, ddof=1)[0, 1] / pgs_t.var(ddof=1))
        b_source = float(np.cov(gs, ys, ddof=1)[0, 1] / gs.var(ddof=1))
        alpha_meas = float(pgs_t.std(ddof=1) / gs.std(ddof=1))
        sem_r2 = max(2 * abs(r2_target) * math.sqrt(max(1 - r2_target, 1e-6) / n),
                     1e-5)
        sem_slope = abs(slope) * math.sqrt(2.0 / n) + 1e-9
        tag = "equal h2" if equal_h2 else "UNEQUAL h2"
        lab = "rho=%.1f alpha=%.1f %s (realised rho %.4f)" % (rho, alpha, tag,
                                                              rho_hat)
        print("  %-48s r2_src=%.5f r2_tgt=%.5f body %.5f | slope=%.5f "
              "body %.5f" % (lab, r2_source, r2_target,
                             r2_source * rho_hat ** 2, slope,
                             rho_hat * b_source / alpha_meas))
        row_r2 = dict(design=lab, lean=r2_source * rho_hat ** 2,
                      truth=r2_target, sem=sem_r2)
        if equal_h2:
            eq_r2.append(row_r2)
            eq_loss.append(dict(design=lab,
                                lean=r2_source * (1 - rho_hat ** 2),
                                truth=r2_source - r2_target, sem=sem_r2))
            eq_slope.append(dict(design=lab,
                                 lean=rho_hat * b_source / alpha_meas,
                                 truth=slope, sem=sem_slope))
            c_nom.append(dict(design=lab, lean=r2_source * rho ** 2,
                              truth=r2_target, sem=sem_r2))
            c_alt.append(dict(design=lab,
                              lean=rho_hat * b_source * alpha_meas,
                              truth=slope, sem=sem_slope))
        else:
            un_r2.append(row_r2)
        if rho == 0.9 and alpha == 1.0 and equal_h2:
            control = dict(design=lab + " [source-population slope = 1]",
                           lean=1.0, truth=b_source,
                           sem=abs(b_source) * math.sqrt(2.0 / n) + 1e-9)
    reg = ("400 causal variants, standardized genotypes, 200000 individuals per "
           "population, declared heritability 0.5 held by scaling each "
           "population's residual to its own genetic variance -- so no cell "
           "clamps a negative residual, which is what made battery 22's "
           "alpha = 1.6 cell read a factor of two high. The target effect "
           "vector is rho-correlated with the source vector and RESCALED to "
           "its norm, so the two populations have equal heritability; the "
           "target genotype scale is alpha. Every prediction uses the REALISED "
           "correlation between the two drawn effect vectors")
    reg_un = reg.replace("and RESCALED to \n           its norm, so the two "
                         "populations have equal heritability",
                         "and NOT rescaled, so the two heritabilities differ "
                         "by the sampling scatter in the vector norms")
    record("ancestryRecalibratedR2", "AncestryCalibration.lean",
           "r2Source * rhoSq  [equal heritability, realised rhoSq]", eq_r2,
           regime=reg, control=control)
    record("ancestryRecalibratedR2 [nominal rho, the battery-22 reading, "
           "competing]", "AncestryCalibration.lean",
           "r2Source * rhoSq  [NOMINAL rhoSq]", c_nom, regime=reg,
           control=control)
    record("ancestryRecalibratedR2 [UNEQUAL heritability, the regime boundary]",
           "AncestryCalibration.lean", "r2Source * rhoSq", un_r2,
           regime=reg_un, control=control)
    record("effectTurnoverR2Loss", "AncestryCalibration.lean",
           "r2Source * (1 - rhoSq)  [equal heritability, realised rhoSq]",
           eq_loss, regime=reg, control=control)
    record("ancestryRecalibratedSlope", "AncestryCalibration.lean",
           "rho * bSource / alpha  [realised rho]", eq_slope, regime=reg,
           control=control)
    record("ancestryRecalibratedSlope [rho*b*alpha reading, competing]",
           "AncestryCalibration.lean", "rho * bSource * alpha", c_alt,
           regime=reg, control=control)


def group_g():
    rng = np.random.default_rng(41207)
    n = 2000000
    cells, c_swap, c_odds, c_ratio = [], [], [], []
    control = None
    # harm comparable to benefit, so the crossing sits where a grid can resolve
    designs = ((0.90, 0.90, 1.0, 1.5), (0.80, 0.95, 1.0, 3.0),
               (0.95, 0.70, 1.0, 1.0), (0.70, 0.99, 1.0, 20.0))
    for sens, spec, benefit, harm in designs:
        grid = np.linspace(0.02, 0.70, 69)
        nb = []
        for pi in grid:
            disease = rng.random(n) < pi
            pos = np.where(disease, rng.random(n) < sens, rng.random(n) >= spec)
            tp = float(np.mean(pos & disease))
            fp = float(np.mean(pos & ~disease))
            nb.append(benefit * tp - harm * fp)
        nb = np.asarray(nb)
        sgn = np.where(nb >= 0)[0]
        if len(sgn) == 0 or sgn[0] == 0:
            print("  *** no interior crossing for sens=%.2f spec=%.2f harm=%.1f"
                  % (sens, spec, harm))
            continue
        j = sgn[0]
        x0, x1, y0, y1 = grid[j - 1], grid[j], nb[j - 1], nb[j]
        pi_star = x0 + (x1 - x0) * (-y0) / (y1 - y0)
        slope = (y1 - y0) / (x1 - x0)
        sem = math.sqrt(max(harm, benefit) ** 2 / n) / abs(slope)
        lean = ((1 - spec) * harm) / (sens * benefit + (1 - spec) * harm)
        lab = "sens=%.2f spec=%.2f harm=%.1f" % (sens, spec, harm)
        print("  %-30s pi* = %.5f ± %.5f | body %.5f  swap %.5f  odds %.5f  "
              "specraw %.5f"
              % (lab, pi_star, sem, lean,
                 (sens * benefit) / (sens * benefit + (1 - spec) * harm),
                 ((1 - spec) * harm) / (sens * benefit),
                 (spec * harm) / (sens * benefit + spec * harm)))
        cells.append(dict(design=lab, lean=lean, truth=pi_star, sem=sem))
        c_swap.append(dict(design=lab,
                           lean=(sens * benefit)
                           / (sens * benefit + (1 - spec) * harm),
                           truth=pi_star, sem=sem))
        c_odds.append(dict(design=lab,
                           lean=((1 - spec) * harm) / (sens * benefit),
                           truth=pi_star, sem=sem))
        c_ratio.append(dict(design=lab, lean=(spec * harm)
                            / (sens * benefit + spec * harm), truth=pi_star,
                            sem=sem))
        if abs(spec - 0.90) < 1e-9 and abs(harm - 1.5) < 1e-9:
            pi_c = 0.30
            disease = rng.random(n) < pi_c
            pos = np.where(disease, rng.random(n) < sens, rng.random(n) >= spec)
            nb_c = (benefit * float(np.mean(pos & disease))
                    - harm * float(np.mean(pos & ~disease)))
            control = dict(
                design="pi=0.30 [net benefit = b*pi*sens - h*(1-pi)*(1-spec)]",
                lean=benefit * pi_c * sens - harm * (1 - pi_c) * (1 - spec),
                truth=nb_c,
                sem=math.sqrt((benefit ** 2 + harm ** 2) / n))
    reg = ("a simulated screening programme over 2e6 individuals at 69 "
           "prevalences from 0.02 to 0.70, test outcomes drawn at the stated "
           "sensitivity and specificity, net benefit = benefit per true "
           "positive minus harm per false positive; the observable is the "
           "prevalence at which the MEASURED net benefit crosses zero, read by "
           "interpolation. The harm-to-benefit ratio is chosen so the crossing "
           "is interior to the grid, which battery 40's design was not")
    record("screeningBreakEvenPrevalence", "PGSCalibrationTheory.lean",
           "(1-spec)*harm / (sens*benefit + (1-spec)*harm)", cells, regime=reg,
           control=control)
    record("screeningBreakEvenPrevalence [numerator swapped, competing]",
           "PGSCalibrationTheory.lean",
           "sens*benefit / (sens*benefit + (1-spec)*harm)", c_swap, regime=reg,
           control=control)
    record("screeningBreakEvenPrevalence [odds form, competing]",
           "PGSCalibrationTheory.lean", "(1-spec)*harm / (sens*benefit)",
           c_odds, regime=reg, control=control)
    record("screeningBreakEvenPrevalence [spec not complemented, competing]",
           "PGSCalibrationTheory.lean",
           "spec*harm / (sens*benefit + spec*harm)", c_ratio, regime=reg,
           control=control)


GROUPS = (("A recalibration trio, heritability held", group_a),
          ("G screeningBreakEvenPrevalence, crossing resolvable", group_g))


def main():
    freshness()
    print("FRESHNESS token literal: SIMCOV-BATTERY41B-PEREGRINE-20260804")
    for label, fn in GROUPS:
        print("\n===== %s =====" % label)
        try:
            fn()
        except Exception as e:
            print("*** %s RAISED %r" % (label, e))
            import traceback
            traceback.print_exc()
    json.dump(RESULTS, open("battery_bulk41b_results.json", "w"), indent=1,
              default=str)
    print("\n================ SUMMARY ================")
    for r in RESULTS:
        w = r.get("worst", {}) or {}
        print("%-22s %-64s worst %9.2f sems, %7.2f%% rel"
              % (r["verdict"], r["name"], w.get("sems_off", float("nan")),
                 100 * w.get("rel_err", float("nan"))))


if __name__ == "__main__":
    main()
