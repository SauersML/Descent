"""Check the prevalence-free AUC charts in PortabilityDrift.lean.

    equalVarianceGaussianAUCFromSNR         snr   = Phi(sqrt(snr / 2))
    equalVarianceGaussianAUCFromSignalVariance vS vE
                                                  = Phi(sqrt(vS / (2 * vE)))
    equalVarianceGaussianAUCFromExplainedR2 r2    = Phi(sqrt(r2 / (2 * (1 - r2))))
    presentDayEqualVarianceGaussianAUC      ...   = Phi(sqrt(snr / 2))

None of these takes a disease prevalence.  Under the liability-threshold model
the AUC of a score against case/control status depends on prevalence, because
cases are a truncated tail of the liability distribution and the truncation
point sets how far the case and control score distributions separate.

Ground truth here is the exact AUC = P(S_case > S_control) computed two ways:
Gauss-Legendre integration of the bivariate normal, and a large Monte Carlo.

RESOLVED.  These four were named `liabilityAUCFrom*` and `presentDayAUC` when
this check was written, and the run reported below is what retired those names:
RMSE 0.1199 over 25 cells against the exact bivariate-normal AUC, every cell
biased low, worst at R2 = 0.20 and prevalence 0.001 where the exact AUC is
0.8686 and the chart returns 0.6382, 26.5 per cent low.  The charts are correct
for the equal-variance Gaussian model and were renamed to it; the binary-trait
formula the old names promised is `liabilityThresholdAUCFromExplainedR2`, which
takes prevalence and measures at pooled RMSE 0.0121.  Keep running this: it is
the instrument that holds the equal-variance charts to the model they now name,
and its failure against the liability-threshold oracle is the expected result,
not a regression.

TWENTY-FIVE CELLS WAS TOO COARSE FOR THE CLAIM MADE FROM IT.  "Every cell
biased low, worst at R2 = 0.20 and prevalence 0.001" is a statement about where
a SURFACE peaks, and a 5x5 grid cannot locate a peak; the worst cell was simply
the corner of the box.  Both axes are now swept log-spaced -- R2 over more than
two decades, prevalence over more than three -- so the shape of the residual
is visible and the worst cell is a maximum rather than an edge.

TWO DEFINITIONS ADDED BECAUSE NOTHING ELSE MEASURED THEM.  The reconciliation
found 22 in-slice statements belonging to no model family at all, and two of
them were reachable from here at no extra cost, because the exact
bivariate-normal AUC this file already computes is their oracle too:

  liabilityThresholdAUCFromExplainedR2        in PortabilityDrift.lean
  equalVarianceGaussianAUCFromSignalVariance  in DGP.lean

AND THEY ARE CLAIMS ABOUT DIFFERENT ESTIMANDS.  This is the exact pair that
caused the confusion these names were renamed to end, so it is stated here
rather than left to be rediscovered:

  liabilityThresholdAUCFromExplainedR2 TAKES A PREVALENCE and is the AUC of a
  score against case/control status for a BINARY trait under the
  liability-threshold model.  Its oracle is the exact bivariate-normal AUC at
  that prevalence, which is what `exact_auc` computes here.

  equalVarianceGaussianAUCFromSignalVariance TAKES NO PREVALENCE and is
  correct for the equal-variance Gaussian model, where the score
  distributions differ only in mean.  It is not a binary-trait formula and it
  is not wrong for failing to be one.

Compare either against the other's oracle and you get a large disagreement and
conclude you have found a defect.  That is what happened, and it is why four
declarations were renamed rather than repaired.

The first is the binary-trait formula the retired names promised, and
PortabilityDrift.lean quotes it at RMSE 0.0121 against a 0.0120 seed-to-seed
noise floor -- a number measured elsewhere, on a handful of points, which this
file now measures on the whole grid.  The second is algebraically the SNR
chart at snr = vSignal / vNoise and is tested anyway, because it is a separate
definition in a separate file and can drift from the chart it currently
equals.  The printed gap between them is a transcription check, not a
discovery: anything above rounding means one of the two moved.

NO LINE NUMBERS ANYWHERE IN THIS FILE, DELIBERATELY.  This file cited four
declarations by line number, those lines came to hold unrelated text, and a
reader checking whether the finding still applied could not tell a fixed
defect from a lost name.  A declaration name is greppable and survives an edit
above it.

WHERE THE ERROR BARS COME FROM, AND WHERE THEY DO NOT.  `exact` is a
quadrature, not a sample: its uncertainty is discretisation, so it is computed
at two grid resolutions and the difference is reported as `exact_grid_delta`.
The residual against the Lean chart therefore has NO Monte Carlo error at all,
which is the whole reason the quadrature is the oracle.  The Monte Carlo is an
INDEPENDENT CHECK ON THE QUADRATURE, run over several seeds so it carries a
standard error of its own; where the prevalence is so low that a feasible
sample yields too few cases to estimate anything, the Monte Carlo is recorded
as skipped WITH ITS REASON rather than quietly returning a number nobody should
believe.
"""
from __future__ import annotations

import argparse
import math
import os
import sys
import time
from concurrent.futures import ProcessPoolExecutor

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

import numpy as np  # noqa: E402
from scipy import stats, integrate  # noqa: E402

import simprov  # noqa: E402

Phi = stats.norm.cdf
phi = stats.norm.pdf

# Default grid.  The five old R2 values (0.01 .. 0.30) and the five old
# prevalences (0.5 .. 0.001) sit inside these ranges, so the retired numbers
# stay comparable to the swept surface.
DEFAULT_R2 = [round(x, 6) for x in simprov.log_grid(0.002, 0.5, 15)]
DEFAULT_K = [float("%.6g" % x) for x in simprov.log_grid(0.5, 1e-4, 13)]
DEFAULT_REPS = 20
DEFAULT_SEED = 7

# Monte Carlo sizing.  The sample is grown as the prevalence falls so that the
# case arm keeps enough members to estimate an AUC, and capped so that one cell
# cannot eat the run.
MC_TARGET_CASES = 20000
MC_N_MIN = 4_000_000
MC_N_MAX = 40_000_000
MC_MIN_CASES = 1000
MC_CHUNK = 2_000_000


def lean_equalVarianceGaussianAUCFromExplainedR2(r2):
    """equalVarianceGaussianAUCFromExplainedR2
    `Phi (Real.sqrt (r2 / (2 * (1 - r2))))`"""
    return float(Phi(np.sqrt(r2 / (2 * (1 - r2)))))


def lean_equalVarianceGaussianAUCFromSNR(snr):
    """equalVarianceGaussianAUCFromSNR
    `Phi (Real.sqrt (snr / 2))`"""
    return float(Phi(np.sqrt(snr / 2)))


def lean_equalVarianceGaussianAUCFromSignalVariance(vSignal, vNoise):
    """DGP.lean, equalVarianceGaussianAUCFromSignalVariance
    `Phi (Real.sqrt (vSignal / (2 * vNoise)))`

    Algebraically the SNR chart at snr = vSignal / vNoise, and tested anyway:
    it is a separate definition in a separate file, so it can drift from the
    chart it currently equals, and an identity nobody measures is an identity
    nobody will notice breaking.
    """
    return float(Phi(np.sqrt(vSignal / (2 * vNoise))))


def lean_liabilityThreshold(K):
    """PortabilityDrift.lean, liabilityThreshold
    `Function.invFun Phi (1 - K)`"""
    return float(stats.norm.ppf(1 - K))


def lean_liabilityCaseMean(K):
    """PortabilityDrift.lean, liabilityCaseMean
    `standardNormalPdf (liabilityThreshold K) / K`"""
    return float(phi(lean_liabilityThreshold(K)) / K)


def lean_liabilityControlMean(K):
    """PortabilityDrift.lean, liabilityControlMean
    `-liabilityCaseMean K * K / (1 - K)`"""
    return float(-lean_liabilityCaseMean(K) * K / (1 - K))


def lean_liabilityCaseVariance(r2, K):
    """PortabilityDrift.lean, liabilityCaseVariance
    `1 - r2 * liabilityCaseMean K * (liabilityCaseMean K - liabilityThreshold K)`"""
    i = lean_liabilityCaseMean(K)
    return float(1 - r2 * i * (i - lean_liabilityThreshold(K)))


def lean_liabilityControlVariance(r2, K):
    """PortabilityDrift.lean, liabilityControlVariance
    `1 - r2 * liabilityControlMean K * (liabilityControlMean K - liabilityThreshold K)`"""
    ic = lean_liabilityControlMean(K)
    return float(1 - r2 * ic * (ic - lean_liabilityThreshold(K)))


def lean_liabilityThresholdAUCFromExplainedR2(r2, K):
    """PortabilityDrift.lean, liabilityThresholdAUCFromExplainedR2.

    The chart that DOES take a prevalence.

    `Phi ((liabilityCaseMean K - liabilityControlMean K) * Real.sqrt r2 /
      Real.sqrt (liabilityCaseVariance r2 K + liabilityControlVariance r2 K))`

    PortabilityDrift.lean quotes this at RMSE 0.0121 against a 0.0120
    seed-to-seed noise floor. That number came from elsewhere; this is the
    first instrument to hold it to the exact bivariate-normal oracle, on a
    grid rather than at a handful of points.
    """
    num = ((lean_liabilityCaseMean(K) - lean_liabilityControlMean(K))
           * math.sqrt(r2))
    den = math.sqrt(lean_liabilityCaseVariance(r2, K)
                    + lean_liabilityControlVariance(r2, K))
    return float(Phi(num / den))


def exact_auc(rho, K, npts=20001):
    """AUC of score S (corr rho with liability L) for cases L > T, P(L>T)=K.

    P(S_case > S_ctrl) = E_{s}[ f_case(s) * F_ctrl(s) ] integrated exactly.
    S ~ N(0,1) marginally; density of S among cases is
        f_case(s) = phi(s) * P(L > T | S=s) / K,
    with L | S=s ~ N(rho s, 1 - rho^2).
    """
    T = stats.norm.isf(K)
    sd = np.sqrt(1 - rho**2)

    def p_case_given_s(s):
        return stats.norm.sf((T - rho * s) / sd)

    def f_case(s):
        return phi(s) * p_case_given_s(s) / K

    def f_ctrl(s):
        return phi(s) * (1 - p_case_given_s(s)) / (1 - K)

    # F_ctrl(s) via cumulative integration on a fine grid, then integrate
    grid = np.linspace(-9, 9, npts)
    fc = f_ctrl(grid)
    Fctrl = integrate.cumulative_trapezoid(fc, grid, initial=0.0)
    Fctrl /= Fctrl[-1]
    return float(np.trapezoid(f_case(grid) * Fctrl, grid))


def mc_n_for(K):
    """Sample size that puts about MC_TARGET_CASES individuals in the case arm."""
    return int(min(MC_N_MAX, max(MC_N_MIN, math.ceil(MC_TARGET_CASES / K))))


def mc_auc(rho, K, seed, n=None, cap=400_000):
    """Monte Carlo AUC, chunked so a 4e7-draw cell does not hold 4e7 floats.

    Returns (auc, n_cases_kept, n_drawn) or (nan, cases, n) when the case arm is
    too thin to estimate anything.
    """
    n = mc_n_for(K) if n is None else int(n)
    rng = np.random.default_rng(seed)
    T = stats.norm.isf(K)
    r = math.sqrt(max(0.0, 1 - rho**2))
    case_parts, ctrl_parts = [], []
    n_case = n_ctrl = 0
    drawn = 0
    while drawn < n:
        k = min(MC_CHUNK, n - drawn)
        drawn += k
        s = rng.standard_normal(k)
        l = rho * s + r * rng.standard_normal(k)
        hit = l > T
        c = s[hit]
        n_case += len(c)
        if sum(len(x) for x in case_parts) < cap:
            case_parts.append(c)
        d = s[~hit]
        n_ctrl += len(d)
        if sum(len(x) for x in ctrl_parts) < cap:
            ctrl_parts.append(d[:cap])
    if n_case < MC_MIN_CASES:
        return float("nan"), n_case, drawn
    a = np.concatenate(case_parts)[:cap]
    b = np.sort(np.concatenate(ctrl_parts)[:cap])
    # P(a > b) + 1/2 P(a == b), by rank rather than by an m x m comparison
    lo = np.searchsorted(b, a, side="left")
    hi = np.searchsorted(b, a, side="right")
    auc = float((lo.mean() + hi.mean()) / (2.0 * len(b)))
    return auc, n_case, drawn


def _job(args):
    r2, K, rep, seed = args
    rho = math.sqrt(r2)
    auc, n_case, drawn = mc_auc(rho, K, seed)
    return dict(r2=r2, K=K, rep=rep, seed=seed, mc=auc,
                mc_cases=n_case, mc_draws=drawn)


def main(argv=None):
    ap = argparse.ArgumentParser(
        description="Sweep the equal-variance Gaussian AUC charts against the "
                    "exact liability-threshold AUC.")
    ap.add_argument("--r2", type=simprov.parse_floats, default=DEFAULT_R2,
                    help="variance explained values, comma separated")
    ap.add_argument("--prevalence", type=simprov.parse_floats, default=DEFAULT_K,
                    help="prevalence values, comma separated")
    ap.add_argument("--no-mc", action="store_true",
                    help="quadrature only; skips the Monte Carlo cross-check")
    simprov.add_sweep_args(ap, DEFAULT_REPS, "auc.json", DEFAULT_SEED)
    args = ap.parse_args(argv)

    cells_spec = [(r2, K) for r2 in args.r2 for K in args.prevalence]
    reps = 0 if args.no_mc else args.reps
    jobs = [(r2, K, rep, args.seed + 7919 * rep + int(round(1e6 * r2)) * 31
             + int(round(1e7 * K)))
            for (r2, K) in cells_spec for rep in range(reps)]
    print("%d cells x %d Monte Carlo replicates = %d samples on %d workers"
          % (len(cells_spec), reps, len(jobs), args.jobs), flush=True)

    t0 = time.time()
    if jobs:
        with ProcessPoolExecutor(max_workers=args.jobs) as ex:
            records = list(ex.map(_job, jobs, chunksize=1))
    else:
        records = []
    print("Monte Carlo wall time %.1f s" % (time.time() - t0), flush=True)

    cells = []
    print("%6s %8s %10s %11s %10s %9s %8s"
          % ("R2", "K", "exact AUC", "MC +/- SE", "lean", "resid", "err%"))
    for ci, (r2, K) in enumerate(cells_spec):
        rho = math.sqrt(r2)
        ex_lo = exact_auc(rho, K, npts=20001)
        ex_hi = exact_auc(rho, K, npts=80001)
        blk = records[ci * reps:(ci + 1) * reps] if reps else []
        mc = simprov.summarize([b["mc"] for b in blk])
        lean_r2 = lean_equalVarianceGaussianAUCFromExplainedR2(r2)
        lt = lean_liabilityThresholdAUCFromExplainedR2(r2, K)
        resid = lean_r2 - ex_hi
        cell = dict(
            r2=r2, K=K, reps=reps,
            exact=ex_hi,
            exact_coarse=ex_lo,
            # The oracle's own error bar: discretisation, not sampling.
            exact_grid_delta=ex_hi - ex_lo,
            mc=mc["mean"], mc_se=mc["se"], mc_sd=mc["sd"], mc_n=mc["n"],
            mc_skipped=(mc["n"] == 0),
            mc_skip_reason=(None if mc["n"] else
                            ("--no-mc" if args.no_mc else
                             "case arm below %d at K=%g" % (MC_MIN_CASES, K))),
            mc_minus_exact=(None if mc["mean"] is None else mc["mean"] - ex_hi),
            lean_fromR2=lean_r2,
            lean_fromSNR=lean_equalVarianceGaussianAUCFromSNR(r2 / (1 - r2)),
            lean_fromSignalVariance=(
                lean_equalVarianceGaussianAUCFromSignalVariance(r2, 1 - r2)),
            # The chart that DOES take a prevalence, against the same oracle.
            lean_liabilityThreshold=lt,
            residual_liabilityThreshold=lt - ex_hi,
            residual=resid,
            rel_err_pct=100.0 * resid / ex_hi)
        cells.append(cell)
        mcs = ("%.4f+/-%.4f" % (mc["mean"], mc["se"])
               if mc["mean"] is not None and mc["se"] is not None
               else ("%.4f" % mc["mean"] if mc["mean"] is not None else "skipped"))
        print("%6.4f %8.5f %10.4f %11s %10.4f %9.4f %8.1f"
              % (r2, K, ex_hi, mcs, lean_r2, resid, cell["rel_err_pct"]))

    rmse = math.sqrt(sum(c["residual"] ** 2 for c in cells) / len(cells))
    rmse_lt = math.sqrt(sum(c["residual_liabilityThreshold"] ** 2
                            for c in cells) / len(cells))
    worst_lt = max(cells, key=lambda c: abs(c["residual_liabilityThreshold"]))
    sv_gap = max(abs(c["lean_fromSignalVariance"] - c["lean_fromSNR"])
                 for c in cells)
    worst = max(cells, key=lambda c: abs(c["rel_err_pct"]))
    grid_worst = max(abs(c["exact_grid_delta"]) for c in cells)
    print("")
    print("pooled RMSE of the chart against the exact AUC: %.4f over %d cells"
          % (rmse, len(cells)))
    print("pooled RMSE of liabilityThresholdAUCFromExplainedR2, the chart that "
          "DOES take a prevalence: %.4f over the same cells" % rmse_lt)
    print("  worst cell: R2 = %.4f, K = %g, exact %.4f, chart %.4f"
          % (worst_lt["r2"], worst_lt["K"], worst_lt["exact"],
             worst_lt["lean_liabilityThreshold"]))
    print("  PortabilityDrift.lean quotes 0.0121 against a 0.0120 noise "
          "floor. That was measured elsewhere on a handful of points; the "
          "number above is this grid.")
    print("equalVarianceGaussianAUCFromSignalVariance vs FromSNR, largest gap "
          "over the grid: %.2e (they are algebraically equal, so anything "
          "above rounding is a transcription drift)" % sv_gap)
    print("worst cell: R2 = %.4f, K = %g, exact %.4f, chart %.4f, %.1f%% off"
          % (worst["r2"], worst["K"], worst["exact"], worst["lean_fromR2"],
             worst["rel_err_pct"]))
    print("largest quadrature grid delta: %.2e  (the oracle's own uncertainty; "
          "it must be small against the residual above)" % grid_worst)
    if reps:
        devs = [abs(c["mc_minus_exact"]) / c["mc_se"]
                for c in cells
                if c["mc_minus_exact"] is not None and c["mc_se"]]
        if devs:
            print("Monte Carlo vs quadrature: worst |MC - exact| / SE = %.2f "
                  "over %d cells with a usable case arm"
                  % (max(devs), len(devs)))

    p = simprov.write(args.output, "popgen_defs/check_auc.py",
                      dict(r2=args.r2, prevalence=args.prevalence,
                           mc_target_cases=MC_TARGET_CASES,
                           mc_n_min=MC_N_MIN, mc_n_max=MC_N_MAX,
                           mc_min_cases=MC_MIN_CASES, no_mc=args.no_mc),
                      args.seed, reps, cells, records)
    print("-> %s (%d cells, %d replicate records)"
          % (p, len(cells), len(records)))


if __name__ == "__main__":
    main()
