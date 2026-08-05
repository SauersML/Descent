"""Battery 33: the equal-variance Gaussian AUC, and the calibrated Brier score.

  A. `equalVarianceGaussianAUCFromSignalVariance vSignal vNoise
        = Phi(sqrt(vSignal / (2 * vNoise)))`
     Oracle: two Gaussian score distributions with equal variance and a mean
     separation, and the AUC COUNTED as the rank statistic -- the fraction of
     case/control pairs the score orders correctly. Nothing evaluates Phi to
     build it. Competitors: the factor 2 dropped, and the square root dropped;
     both are the errors this shape actually attracts.

  B. `calibratedBrierFromVariances pi vSignal vResidual
        = pi*(1-pi) * (1 - vSignal/(vSignal+vResidual))`
     Oracle: a CALIBRATED predictor -- the true conditional probability given a
     noisy linear signal -- with the Brier score measured as the realised mean
     squared error against the binary outcome. Competitors: the variance factor
     `pi*(1-pi)` dropped, and the explained fraction not complemented.
"""
import json
import math

import numpy as np
from scipy import stats

from battery_core import RESULTS, record


def group_a():
    rng = np.random.default_rng(33001)
    n = 800000
    cells, c_nofac, c_nosqrt = [], [], []
    control = None
    for vSignal, vNoise in ((1.0, 1.0), (2.0, 1.0), (0.5, 1.0), (2.0, 4.0)):
        delta = math.sqrt(vSignal)
        sigma = math.sqrt(vNoise)
        ctrl = rng.normal(0.0, sigma, n)
        case = rng.normal(delta, sigma, n)
        # AUC as the rank statistic: P(case score > control score)
        auc = float(np.mean(case > ctrl) + 0.5 * np.mean(case == ctrl))
        sem = math.sqrt(max(auc * (1 - auc), 1e-12) / n)
        lean = float(stats.norm.cdf(math.sqrt(vSignal / (2 * vNoise))))
        lab = "vS=%.1f vN=%.1f" % (vSignal, vNoise)
        print("  %-16s AUC counted %.5f ± %.5f | lean %.5f  nofac %.5f  "
              "nosqrt %.5f"
              % (lab, auc, sem, lean,
                 float(stats.norm.cdf(math.sqrt(vSignal / vNoise))),
                 float(stats.norm.cdf(vSignal / (2 * vNoise)))))
        cells.append(dict(design=lab, lean=lean, truth=auc, sem=sem))
        c_nofac.append(dict(design=lab,
                            lean=float(stats.norm.cdf(math.sqrt(vSignal / vNoise))),
                            truth=auc, sem=sem))
        c_nosqrt.append(dict(design=lab,
                             lean=float(stats.norm.cdf(vSignal / (2 * vNoise))),
                             truth=auc, sem=sem))
        if vSignal == 1.0 and vNoise == 1.0:
            # control: with NO separation the AUC is exactly 1/2, counted on
            # the same code path
            z = rng.normal(0.0, sigma, n)
            a0 = float(np.mean(z > ctrl) + 0.5 * np.mean(z == ctrl))
            control = dict(design="no separation [AUC = 1/2]", lean=0.5,
                           truth=a0, sem=math.sqrt(0.25 / n))
    reg = ("two Gaussian score distributions with EQUAL variance and a mean "
           "separation of sqrt(vSignal); 800000 pairs, AUC counted as the "
           "fraction of case/control pairs ordered correctly")
    record("equalVarianceGaussianAUCFromSignalVariance", "DGP.lean",
           "Phi(sqrt(vSignal / (2 * vNoise)))", cells, regime=reg,
           control=control)
    record("equalVarianceGaussianAUC [factor 2 dropped, competing]",
           "DGP.lean", "Phi(sqrt(vSignal / vNoise))", c_nofac, regime=reg,
           control=control)
    record("equalVarianceGaussianAUC [square root dropped, competing]",
           "DGP.lean", "Phi(vSignal / (2 * vNoise))", c_nosqrt, regime=reg,
           control=control)


def group_b():
    rng = np.random.default_rng(33002)
    n = 2000000
    cells, c_novar, c_nocomp = [], [], []
    control = None
    for pi, vSignal, vResidual in ((0.5, 1.0, 1.0), (0.2, 1.0, 3.0),
                                   (0.1, 2.0, 1.0), (0.35, 0.5, 2.0)):
        # latent signal + residual, thresholded to give prevalence pi
        s = rng.normal(0, math.sqrt(vSignal), n)
        e = rng.normal(0, math.sqrt(vResidual), n)
        t = stats.norm.isf(pi) * math.sqrt(vSignal + vResidual)
        Y = ((s + e) > t).astype(float)
        # the CALIBRATED predictor: P(Y=1 | s), available in closed form
        phat = stats.norm.sf((t - s) / math.sqrt(vResidual))
        brier = float(np.mean((Y - phat) ** 2))
        sem = float(np.std((Y - phat) ** 2, ddof=1) / math.sqrt(n))
        frac = vSignal / (vSignal + vResidual)
        lean = pi * (1 - pi) * (1 - frac)
        lab = "pi=%.2f vS=%.1f vR=%.1f" % (pi, vSignal, vResidual)
        print("  %-24s Brier %.6f ± %.6f | lean %.6f" % (lab, brier, sem, lean))
        cells.append(dict(design=lab, lean=lean, truth=brier, sem=sem))
        c_novar.append(dict(design=lab, lean=1 - frac, truth=brier, sem=sem))
        c_nocomp.append(dict(design=lab, lean=pi * (1 - pi) * frac,
                             truth=brier, sem=sem))
        if pi == 0.5 and vSignal == 1.0:
            # control: an UNINFORMATIVE predictor scores pi*(1-pi) exactly
            control = dict(design="constant predictor [Brier = pi(1-pi)]",
                           lean=pi * (1 - pi),
                           truth=float(np.mean((Y - float(Y.mean())) ** 2)),
                           sem=float(np.std((Y - float(Y.mean())) ** 2,
                                            ddof=1) / math.sqrt(n)))
    reg = ("latent signal plus residual thresholded to prevalence pi, 2e6 "
           "individuals; the predictor is the CALIBRATED conditional "
           "probability given the signal, and the Brier score is its realised "
           "mean squared error against the binary outcome")
    record("calibratedBrierFromVariances", "DGP.lean",
           "pi*(1-pi) * (1 - vSignal/(vSignal+vResidual))", cells, regime=reg,
           control=control)
    record("calibratedBrier [variance factor dropped, competing]", "DGP.lean",
           "1 - vSignal/(vSignal+vResidual)", c_novar, regime=reg,
           control=control)
    record("calibratedBrier [fraction not complemented, competing]",
           "DGP.lean", "pi*(1-pi) * vSignal/(vSignal+vResidual)", c_nocomp,
           regime=reg, control=control)


def main():
    for fn in (group_a, group_b):
        print("\n===== %s =====" % fn.__name__)
        try:
            fn()
        except Exception as e:
            print("*** %s RAISED %r" % (fn.__name__, e))
            import traceback
            traceback.print_exc()
    json.dump(RESULTS, open("battery_bulk33_results.json", "w"), indent=1,
              default=str)
    print("\n================ SUMMARY ================")
    for r in RESULTS:
        w = r.get("worst", {})
        print("%-22s %-52s worst %9.2f sems, %7.2f%% rel"
              % (r["verdict"], r["name"], w.get("sems_off", float("nan")),
                 100 * w.get("rel_err", float("nan"))))


if __name__ == "__main__":
    main()
