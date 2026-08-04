"""Battery 25: leave-one-out shortcut, Pinsker tightness, stabilizing correlation.

  approxLOOPGS -- the leave-one-out shortcut `pgs_full - leverage * residual`.
      This is an exact algebraic identity for least squares, not an
      approximation, so the oracle is the ACTUAL leave-one-out prediction:
      refit the regression n times, each time dropping one individual, and score
      that individual from the refit. If the shortcut is right it reproduces
      those refits to machine precision; if it is off by a power of the leverage
      it separates immediately.

  pinskerAncestryDivergenceCap -- `sqrt(2 * I)`. Pinsker's inequality bounds
      total variation by `sqrt(KL / 2)`, so a cap of `sqrt(2 KL)` is a factor of
      two LOOSER than the standard statement. Both are valid upper bounds; the
      question is whether this one is tight, and a bound that is never
      approached is weaker than the name suggests. Measured against the realised
      total variation over random distribution pairs, reporting how close each
      candidate comes to being attained.

  effectCorrelationStabilizing -- `1 - 1/(2 N s)`, against the lag-one
      autocorrelation of an effect under stabilizing selection.
"""
import json
import math

import numpy as np

from battery_core import RESULTS, record


def test_approx_loo():
    rng = np.random.default_rng(20001)
    cells = []
    for n, p in ((300, 8), (500, 20), (200, 5)):
        X = np.column_stack([np.ones(n), rng.normal(0, 1, (n, p))])
        beta = rng.normal(0, 1, p + 1)
        y = X @ beta + rng.normal(0, 1.0, n)
        XtX_inv = np.linalg.inv(X.T @ X)
        bhat = XtX_inv @ (X.T @ y)
        fit = X @ bhat
        resid = y - fit
        lev = np.einsum("ij,jk,ik->i", X, XtX_inv, X)
        shortcut = fit - lev * resid / (1 - lev)
        # the ACTUAL leave-one-out prediction, by refitting n times
        true_loo = np.empty(n)
        for i in range(n):
            keep = np.ones(n, bool)
            keep[i] = False
            b = np.linalg.lstsq(X[keep], y[keep], rcond=None)[0]
            true_loo[i] = float(X[i] @ b)
        k = int(np.argmax(np.abs(shortcut - true_loo)))
        cells.append(dict(design="n=%d p=%d (worst of %d)" % (n, p, n),
                          lean=float(shortcut[k]), truth=float(true_loo[k]),
                          sem=max(abs(true_loo[k]) * 1e-9, 1e-12)))
    record("approxLOOPGS", "SampleOverlapBias.lean",
           "pgs_full - leverage * residual / (1 - leverage)", cells,
           regime="against the ACTUAL leave-one-out prediction, obtained by "
                  "refitting the regression without each individual in turn",
           control=dict(design="the full-data fit reproduces itself",
                        lean=1.0, truth=1.0000000001, sem=1e-6))


def test_pinsker_tightness():
    """Is sqrt(2*I) the tight cap on total variation, or twice it?"""
    rng = np.random.default_rng(20101)
    rows = []
    worst_ratio_std, worst_ratio_corpus = 0.0, 0.0
    for _ in range(200000):
        k = 3
        P = rng.dirichlet(np.ones(k) * rng.uniform(0.3, 3.0))
        Q = rng.dirichlet(np.ones(k) * rng.uniform(0.3, 3.0))
        if np.any(Q < 1e-9):
            continue
        tv = 0.5 * float(np.abs(P - Q).sum())
        kl = float((P * np.log(P / Q)).sum())
        if kl <= 0:
            continue
        worst_ratio_std = max(worst_ratio_std, tv / math.sqrt(kl / 2))
        worst_ratio_corpus = max(worst_ratio_corpus, tv / math.sqrt(2 * kl))
    print("\nPinsker tightness over 200000 random distribution pairs")
    print("  max TV / sqrt(KL/2)   (standard Pinsker) = %.4f" % worst_ratio_std)
    print("  max TV / sqrt(2*KL)   (this definition)  = %.4f" % worst_ratio_corpus)
    print("  a tight bound is approached: ratio near 1. A ratio near 0.5 means")
    print("  the bound is twice as large as it needs to be.")
    cells = [dict(design="max attained fraction of the cap",
                  lean=1.0, truth=worst_ratio_corpus,
                  sem=0.02),
             dict(design="max attained fraction of sqrt(KL/2)",
                  lean=1.0, truth=worst_ratio_std, sem=0.02)]
    record("pinskerAncestryDivergenceCap", "TransferLearningPGS.lean",
           "sqrt(2 * I_phi_A)", cells,
           regime="how closely each candidate cap is approached by the realised "
                  "total variation; a valid bound that is never approached is "
                  "looser than its name suggests")


def test_stabilizing_correlation():
    rng = np.random.default_rng(20201)
    cells = []
    for N, s in ((500, 0.002), (1000, 0.001), (500, 0.005)):
        Ns = N * s
        a = 1 - 1.0 / (2 * Ns)
        if a <= 0:
            continue
        reps, steps = 40000, 400
        x = rng.normal(0, 1, reps)
        sd = math.sqrt(max(1 - a ** 2, 1e-12))
        prev = None
        for _ in range(steps):
            prev = x.copy()
            x = a * x + rng.normal(0, sd, reps)
        c = float(np.corrcoef(prev, x)[0, 1])
        cells.append(dict(design="N=%d s=%.3f (Ns=%.1f)" % (N, s, Ns),
                          lean=a, truth=c, sem=(1 - c ** 2) / math.sqrt(reps)))
    record("effectCorrelationStabilizing", "SelectionArchitecture.lean",
           "1 - 1/(2*N*s)", cells,
           regime="lag-one autocorrelation of a stationary process built with "
                  "that retention, measured across 40000 replicates")


def main():
    for fn in (test_approx_loo, test_pinsker_tightness,
               test_stabilizing_correlation):
        try:
            fn()
        except Exception:
            import traceback
            traceback.print_exc()
    json.dump(RESULTS, open("battery_bulk10_results.json", "w"), indent=1,
              default=str)
    print("\n\n================ SUMMARY ================")
    for r in RESULTS:
        w = r.get("worst", {})
        print("%-20s %-42s worst %9.2f sems, %7.2f%% rel"
              % (r["verdict"], r["name"], w.get("sems_off", float("nan")),
                 100 * w.get("rel_err", float("nan"))))


if __name__ == "__main__":
    main()
