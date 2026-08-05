"""TransferLearningPGS battery -- 52 definitions, none previously tested.

  :1380 sourceShrinkageMSE gapSq noiseVar nTarget lam
            = gapSq*lam^2 + (noiseVar/nTarget)*(1-lam)^2
  :1387 optimalSourceShrinkageWeight gapSq noiseVar nTarget
            = (noiseVar/nTarget) / (gapSq + noiseVar/nTarget)
  :633  importanceWeightESS sum_w sum_w_sq = sum_w^2 / sum_w_sq
  :106  effectGeneticCorrelation                (cosine of two effect vectors)
  :115  additiveGeneticVariance beta = sum beta^2

Two checks are done here:
  * INTERNAL -- is optimalSourceShrinkageWeight the exact minimiser of
    sourceShrinkageMSE?  (numeric minimisation over lambda)
  * EXTERNAL -- does sourceShrinkageMSE describe the actual MSE of the shrunk
    estimator lam*beta_source + (1-lam)*beta_target_hat?  (Monte Carlo)
"""
from __future__ import annotations

import json
import sys

import numpy as np


def lean_mse(gapSq, noiseVar, nTarget, lam):
    return gapSq * lam**2 + (noiseVar / nTarget) * (1 - lam) ** 2


def lean_opt(gapSq, noiseVar, nTarget):
    return (noiseVar / nTarget) / (gapSq + noiseVar / nTarget)


def main():
    rows = []
    print("=== optimalSourceShrinkageWeight is the minimiser of sourceShrinkageMSE ===")
    print(f"{'gapSq':>8} {'noiseVar':>9} {'nTarget':>8} {'lean lam*':>10} "
          f"{'numeric argmin':>15} {'err%':>8}")
    for gapSq in (0.01, 0.1, 1.0):
        for noiseVar in (1.0, 4.0):
            for nT in (100, 1000):
                lams = np.linspace(0, 1, 2_000_001)
                mse = lean_mse(gapSq, noiseVar, nT, lams)
                numeric = float(lams[int(np.argmin(mse))])
                lean = lean_opt(gapSq, noiseVar, nT)
                rows.append(dict(check="internal", gapSq=gapSq, noiseVar=noiseVar,
                                 nTarget=nT, lean=lean, numeric=numeric))
                print(f"{gapSq:8.2f} {noiseVar:9.1f} {nT:8d} {lean:10.6f} "
                      f"{numeric:15.6f} {100*(lean-numeric)/max(numeric,1e-9):8.3f}")

    print("\n=== does sourceShrinkageMSE describe the real MSE of the shrunk estimator? ===")
    print(f"{'gapSq':>8} {'noiseVar':>9} {'nTarget':>8} {'lam':>6} "
          f"{'MC MSE':>10} {'lean':>10} {'err%':>7}")
    rng = np.random.default_rng(7)
    for gapSq in (0.01, 0.25):
        for noiseVar in (1.0,):
            for nT in (100, 1000):
                for lam in (0.0, 0.3, 0.7, 1.0):
                    reps = 400_000
                    gap = np.sqrt(gapSq)
                    beta_true = 0.0
                    beta_source = beta_true + gap          # biased by the gap
                    # target estimate: unbiased, variance noiseVar / nTarget
                    b_hat = beta_true + rng.normal(
                        0, np.sqrt(noiseVar / nT), size=reps)
                    est = lam * beta_source + (1 - lam) * b_hat
                    mc = float(np.mean((est - beta_true) ** 2))
                    lean = lean_mse(gapSq, noiseVar, nT, lam)
                    rows.append(dict(check="external", gapSq=gapSq, nTarget=nT,
                                     lam=lam, mc=mc, lean=lean))
                    print(f"{gapSq:8.2f} {noiseVar:9.1f} {nT:8d} {lam:6.1f} "
                          f"{mc:10.6f} {lean:10.6f} {100*(lean-mc)/mc:7.2f}")

    print("\n=== importanceWeightESS = (sum w)^2 / sum w^2 ===")
    print(f"{'setting':>28} {'lean ESS':>10} {'nominal n':>10}")
    for name, w in (("all weights equal (n=1000)", np.ones(1000)),
                    ("one dominant weight", np.r_[1000.0, np.ones(999)]),
                    ("lognormal weights", rng.lognormal(0, 1.5, 1000))):
        ess = float(w.sum() ** 2 / (w**2).sum())
        rows.append(dict(check="ess", setting=name, ess=ess))
        print(f"{name:>28} {ess:10.1f} {len(w):10d}")

    with open(sys.argv[1] if len(sys.argv) > 1 else "tl.json", "w") as fh:
        json.dump(rows, fh)


if __name__ == "__main__":
    main()
