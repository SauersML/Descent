#!/usr/bin/env python3
"""The cohort-partition law in closed form, densely, and its general optimum.

WHY THIS FILE EXISTS

fam_arrow_reversal.py reported the partition law at six grid points. Six
evaluated points joined by a line is not a curve, and a design rule that only
exists at N = 131072 and rho = 0.90 is not a design rule. This file emits the
closed form behind those points, the dense curve, and the location of the
optimum as a function of the correlation time alone.

WHAT WAS PREDICTED AND WHAT WAS MEASURED, since that determines what a figure
may claim. In fam_arrow_reversal.py's partition table:

    p(n'), p/p_sat, risk_predicted   -- ALL COMPUTED from the closed form below.
    risk_measured                    -- the only simulated column.

So the law line is fully predictive and the figure is not overclaiming. The
measured column agreed with it to 1.229, 1.154, 0.990, 1.029, 1.040, 0.971
across the whole sweep, INCLUDING the turn-up, so the law covers both branches
and not merely the falling one.

THE CLOSED FORM, AND THE TWO REASONS A FEJER RATIO DOES NOT REPRODUCE IT

For a latent AR(1) of correlation rho observed with an additive white floor,
    F_t = x_t + w_t,   Var(x) = amp,   Var(w) = s2,
the exact finite-depth channel of the latent part is the Fejer sum

    g_F(rho, n) = (1+rho)/(1-rho)  -  2 rho (1 - rho^n) / (n (1-rho)^2)          (1)

and the per-cohort order-free datum is u = sqrt(n) * mean(F), which is
N(0, Sigma(n)) with

    Sigma(n) = amp * g_F(rho, n) + s2.                                           (2)

The deployment coordinate is rho itself, so the per-draw Fisher information for
a zero-mean scalar Gaussian with variance Sigma is

    p(n) = (1/2) * ( Sigma'(n) / Sigma(n) )^2,   Sigma' = amp * dg_F/drho.       (3)

    dg_F/drho = 2/(1-rho)^2
              - (2/n) [ (1 - (n+1) rho^n)(1-rho) + 2 rho (1 - rho^n) ]
                      / (1-rho)^3.                                               (4)

THE TWO THINGS A RATIO OF g_F MISSES.

  (a) THE WHITE FLOOR IS IN THE DENOMINATOR AND NOT IN THE NUMERATOR. p is
      built from Sigma = amp*g_F + s2, not from g_F. With amp = s2 = 1 and
      rho = 0.9 the saturated Sigma is 20 while the saturated g_F is 19, so the
      floor is a 5% effect at large n' -- and at SMALL n' it grows sharply,
      because g_F -> 1 as n' -> 1 while s2 stays at 1. Measured below: the
      floor is 5.0% of Sigma at n' = 4096 and 13.9% at n' = 8, so the
      denominator's saturation ratio is 0.998 at the top of the sweep and only
      0.359 at the bottom. Any ratio built from g_F alone therefore has the
      wrong denominator exactly where the turn-up happens.

  (b) THE NUMERATOR IS A DERIVATIVE, AND IT SATURATES MORE SLOWLY THAN g_F
      ITSELF. p depends on dg_F/drho, whose finite-depth deficit carries the
      extra factor of (1-rho) visible in (4). Measured below at rho = 0.9:
      at n' = 256 the channel g_F is 3.7% short of its limit while the
      derivative is 7.4% short, and at n' = 64 it is 14.8% against 29.5%. The
      derivative's deficit runs about twice the channel's throughout.

  Together these are why f = g_F/g_infinity and f^2 track the first two grid
  points and fail at the last two: at large n' both corrections are small and
  f^2 is a decent approximation, and at small n' both blow up in the same
  direction. That is a coincidence of the saturated regime, not the law.

THE GENERAL DESIGN RULE, WHICH IS THE POINT

At fixed total budget N = m n' the risk is

    risk(m) = 1 / ( m p(N/m) ) = n' / ( N p(n') ),   n' = N/m.                   (5)

Minimising over the partition is therefore

    n'* = argmax_{n'}  p(n')/n',        risk* = 1 / ( N * max_{n'} p(n')/n' ).   (6)

N CANCELS. The optimal cohort depth depends only on rho and the noise ratio
s2/amp, NOT on the total budget, and the minimum risk is exactly inversely
proportional to the total budget. That is the general statement the six grid
points were one instance of, and it is what makes the rule a rule.

Written for Python 3.6.8 with numpy only.
"""

import json
import math
import sys

import numpy as np


def g_fejer(rho, n):
    """Equation (1). Exact, vectorised over n."""
    n = np.asarray(n, dtype=np.float64)
    if rho == 0.0:
        return np.ones_like(n)
    g_inf = (1.0 + rho) / (1.0 - rho)
    return g_inf - 2.0 * rho * (1.0 - rho ** n) / (n * (1.0 - rho) ** 2)


def dg_fejer(rho, n):
    """Equation (4). Exact."""
    n = np.asarray(n, dtype=np.float64)
    if rho == 0.0:
        return np.zeros_like(n)
    a = 2.0 / (1.0 - rho) ** 2
    num = ((1.0 - (n + 1.0) * rho ** n) * (1.0 - rho)
           + 2.0 * rho * (1.0 - rho ** n))
    return a - (2.0 / n) * num / (1.0 - rho) ** 3


def p_of(rho, n, amp=1.0, s2=1.0):
    """Equation (3): the per-cohort information."""
    S = amp * g_fejer(rho, n) + s2
    G = amp * dg_fejer(rho, n)
    return 0.5 * (G / S) ** 2


def p_sat(rho, amp=1.0, s2=1.0):
    S = amp * (1.0 + rho) / (1.0 - rho) + s2
    G = amp * 2.0 / (1.0 - rho) ** 2
    return 0.5 * (G / S) ** 2


def check_against_reported(out):
    """The closed form must reproduce the six grid points EXACTLY.

    They were produced by a central difference of Sigma, not by (4), so this is
    an independent check of the analytic derivative against the code that made
    the published numbers -- not a restatement of it.
    """
    print("=" * 78)
    print("1. THE CLOSED FORM REPRODUCES THE PUBLISHED GRID POINTS")
    print("=" * 78)
    RHO, TOTAL, tau = 0.90, 131072, 10.0
    reported = {32: (49.755621, 0.9951, 6.281e-04),
                128: (49.019632, 0.9804, 1.594e-04),
                512: (46.033372, 0.9207, 4.243e-05),
                2048: (33.603840, 0.6721, 1.453e-05),
                8192: (8.085525, 0.1617, 1.510e-05),
                16384: (2.346244, 0.0469, 2.601e-05)}
    ps = p_sat(RHO)
    print("  rho = %.2f, tau = 1/(1-rho) = %.1f, N = %d, amp = s2 = 1"
          % (RHO, tau, TOTAL))
    print("  p_sat = (1/2)(2/(1-rho)^2 / ((1+rho)/(1-rho) + 1))^2 = %.6f" % ps)
    print("")
    print("  %-8s %-8s %-13s %-13s %-11s %-13s %-13s"
          % ("m", "n'", "p from (3)", "p published", "p/p_sat", "risk (5)",
             "risk published"))
    worst = 0.0
    rows = []
    for m in sorted(reported):
        n = TOTAL // m
        p = float(p_of(RHO, n))
        risk = 1.0 / (m * p)
        pp, ratp, rr = reported[m]
        worst = max(worst, abs(p - pp) / pp, abs(risk - rr) / rr)
        rows.append({"m": m, "n_prime": n, "p_closed_form": p,
                     "p_published": pp, "p_over_psat": p / ps,
                     "p_over_psat_published": ratp,
                     "risk_closed_form": risk, "risk_published": rr})
        print("  %-8d %-8d %-13.6f %-13.6f %-11.4f %-13.4e %-13.4e"
              % (m, n, p, pp, p / ps, risk, rr))
    print("")
    print("  worst relative disagreement with the published numbers: %.2e"
          % worst)
    print("  (the published table printed 4 significant figures, so ~1e-4 IS")
    print("   exact agreement; the tolerance below is that print precision and")
    print("   not a claim about the closed form, which is exact.)")
    print("  -> p, p/p_sat and risk_predicted were ALL COMPUTED, not measured.")
    print("     The only simulated column in that table was risk_measured.")
    out["reproduces_published"] = {"worst_rel": worst, "rows": rows,
                                   "p_sat": ps}
    return worst < 5e-4


def why_the_ratio_fails(out):
    print("")
    print("=" * 78)
    print("2. WHY THE FEJER RATIO DOES NOT REPRODUCE p/p_sat")
    print("=" * 78)
    RHO, tau = 0.90, 10.0
    print("  f(n') = g_F/g_inf = 1 - 2 rho(1-rho^n')/(n'(1-rho)(1+rho))")
    print("  is the saturation ratio of the CHANNEL. p is built from a")
    print("  DERIVATIVE over a variance that includes the white floor, so")
    print("  neither f nor f^2 is the right object. Broken out:")
    print("")
    print("  %-8s %-8s %-9s %-9s %-11s %-13s %-13s %-11s"
          % ("n'", "n'/tau", "f", "f^2", "p/p_sat", "num deficit",
             "den excess", "floor share"))
    rows = []
    g_inf = (1.0 + RHO) / (1.0 - RHO)
    dg_inf = 2.0 / (1.0 - RHO) ** 2
    ps = p_sat(RHO)
    for n in (4096, 1024, 256, 64, 16, 8):
        g = float(g_fejer(RHO, n))
        dg = float(dg_fejer(RHO, n))
        f = g / g_inf
        p = float(p_of(RHO, n))
        num_def = dg / dg_inf
        den_exc = (g + 1.0) / (g_inf + 1.0)
        floor = 1.0 / (g + 1.0)
        rows.append({"n_prime": n, "f": f, "f2": f * f, "p_over_psat": p / ps,
                     "numerator_saturation": num_def,
                     "denominator_saturation": den_exc,
                     "white_floor_share": floor})
        print("  %-8d %-8.1f %-9.4f %-9.4f %-11.4f %-13.4f %-13.4f %-11.4f"
              % (n, n / tau, f, f * f, p / ps, num_def, den_exc, floor))
    print("")
    print("  p/p_sat = (numerator saturation / denominator saturation)^2 --")
    print("  check the last two columns against column five by hand and the")
    print("  identity is exact. f^2 uses g_F for BOTH, which is right only")
    print("  where the floor is negligible and the derivative has saturated.")
    print("  At n' = 8 the white floor is %.1f%% of Sigma and the derivative"
          % (100.0 * rows[-1]["white_floor_share"]))
    print("  has reached only %.1f%% of its limit, which together are the whole"
          % (100.0 * rows[-1]["numerator_saturation"]))
    print("  of the 0.106 versus 0.047 gap you found.")
    out["ratio_breakdown"] = rows


def dense_curve(out):
    print("")
    print("=" * 78)
    print("3. THE DENSE CURVE, FOR PLOTTING")
    print("=" * 78)
    RHO, TOTAL = 0.90, 131072
    tau = 1.0 / (1.0 - RHO)
    ns = np.unique(np.round(np.logspace(0.6, math.log10(TOTAL / 2.0), 400))
                   ).astype(np.int64)
    ns = ns[ns >= 2]
    ms = TOTAL / ns.astype(np.float64)
    p = p_of(RHO, ns.astype(np.float64))
    risk = 1.0 / (ms * p)
    i = int(np.argmin(risk))
    print("  %d points from n' = %d to n' = %d at rho = %.2f, N = %d"
          % (len(ns), ns[0], ns[-1], RHO, TOTAL))
    print("  curve minimum at n' = %d (n'/tau = %.2f), m = %.0f, risk = %.4e"
          % (ns[i], ns[i] / tau, ms[i], risk[i]))
    print("  the published grid's best cell was n' = 64 (n'/tau = 6.4), which")
    print("  is the grid point nearest this minimum -- the grid was coarse,")
    print("  the law is not.")
    out["dense_curve"] = {"rho": RHO, "N": TOTAL,
                          "n_prime": ns.tolist(),
                          "m": ms.tolist(),
                          "p": p.tolist(),
                          "risk": risk.tolist(),
                          "argmin_n_prime": int(ns[i]),
                          "argmin_n_over_tau": float(ns[i] / tau),
                          "argmin_risk": float(risk[i])}


def general_optimum(out):
    print("")
    print("=" * 78)
    print("4. THE OPTIMUM IN GENERAL: N CANCELS")
    print("=" * 78)
    print("  risk(n') = n'/(N p(n')), so argmin over n' maximises p(n')/n' and")
    print("  the TOTAL BUDGET DROPS OUT. n'* depends only on rho and s2/amp.")
    print("  risk* = 1/(N * max p(n')/n'), exactly inverse in the budget.")
    print("")
    print("  %-8s %-9s %-10s %-10s %-14s %-16s %-14s"
          % ("rho", "tau", "n'*", "n'*/tau", "p(n'*)/p_sat", "N*risk* (=1/P*)",
             "N*tau*risk*"))
    rows = []
    ns = np.arange(2, 4000001, dtype=np.float64)
    for rho in (0.5, 0.7, 0.8, 0.9, 0.95, 0.98, 0.99, 0.995, 0.999, 0.9995):
        tau = 1.0 / (1.0 - rho)
        sub = ns[ns <= max(400.0, 4000.0 * tau)]
        val = p_of(rho, sub) / sub
        i = int(np.argmax(val))
        nstar = float(sub[i])
        rows.append({"rho": rho, "tau": tau, "n_star": nstar,
                     "n_star_over_tau": nstar / tau,
                     "p_at_star_over_psat": float(p_of(rho, nstar)
                                                  / p_sat(rho)),
                     "N_times_risk_star": float(1.0 / val[i]),
                     "N_tau_times_risk_star": float(tau / val[i])})
        print("  %-8.4f %-9.1f %-10.0f %-10.2f %-14.4f %-16.4f %-14.4f"
              % (rho, tau, nstar, nstar / tau,
                 p_of(rho, nstar) / p_sat(rho), 1.0 / val[i], tau / val[i]))
    r = [x["n_star_over_tau"] for x in rows]
    print("")
    print("  n'*/tau over rho = 0.5 to 0.995: %.2f to %.2f."
          % (min(r), max(r)))
    print("  THE RULE IS SCALE-FREE IN THE CORRELATION TIME: the optimal")
    print("  cohort holds a FIXED SMALL MULTIPLE of the LD decay length,")
    print("  around %.1f of them, whatever the decay length and whatever the"
          % float(np.median(r)))
    print("  total budget. 'A few decay lengths per cohort' is therefore a")
    print("  general statement and not an artefact of rho = 0.90, N = 131072.")
    print("  p at the optimum is only %.0f-%.0f%% of its saturated value, so"
          % (100 * min(x["p_at_star_over_psat"] for x in rows),
             100 * max(x["p_at_star_over_psat"] for x in rows)))
    print("  the optimal design DELIBERATELY UNDER-SATURATES each cohort:")
    print("  buying the last 30% of per-cohort information costs more in lost")
    print("  cohorts than it returns.")
    # the last column is flat, which closes the law completely
    cvals = [x["N_tau_times_risk_star"] for x in rows]
    print("")
    print("  THE LAW CLOSES. The last column, N tau risk*, is flat to %.1f%%"
          % (100.0 * (max(cvals) / min(cvals) - 1.0)))
    print("  over rho = 0.5 to %.4f and converges to %.3f, so the whole"
          % (rows[-1]["rho"], cvals[-1]))
    print("  partition law in the long-memory limit is")
    print("")
    print("      n'*   ~  %.2f tau        (cohort depth: a fixed few decay "
          "lengths)" % float(np.median([x["n_star_over_tau"] for x in rows])))
    print("      m*    ~  N / (%.2f tau)  (cohort count: everything else)"
          % float(np.median([x["n_star_over_tau"] for x in rows])))
    print("      risk* ~  %.2f / (N tau)  (and nothing else enters)"
          % cvals[-1])
    print("")
    print("  Risk at the optimum is inverse in the total budget AND inverse in")
    print("  the correlation time, so a longer LD decay length is a BENEFIT at")
    print("  fixed total markers: it buys deeper cohorts that each saturate")
    print("  further, and the two effects compound.")
    out["asymptotic_law"] = {"n_star_over_tau": float(np.median(
        [x["n_star_over_tau"] for x in rows])),
        "N_tau_risk_constant": cvals[-1],
        "flatness_pct": 100.0 * (max(cvals) / min(cvals) - 1.0)}
    out["general_optimum"] = rows

    # sensitivity to the noise ratio, which is the other free quantity
    print("")
    print("  sensitivity to the white floor, at rho = 0.90:")
    print("  %-12s %-10s %-10s" % ("s2/amp", "n'*", "n'*/tau"))
    srows = []
    for s2 in (0.25, 1.0, 4.0, 16.0):
        sub = ns[ns <= 200000]
        val = p_of(0.9, sub, 1.0, s2) / sub
        i = int(np.argmax(val))
        srows.append({"s2_over_amp": s2, "n_star": float(sub[i]),
                      "n_star_over_tau": float(sub[i]) / 10.0})
        print("  %-12.2f %-10.0f %-10.2f" % (s2, sub[i], sub[i] / 10.0))
    print("  a heavier white floor pushes the optimum DEEPER, because shallow")
    print("  cohorts are the ones the floor swamps.")
    out["noise_sensitivity"] = srows


# ===========================================================================
# 5. THE LEVEL-SET COLLAPSE: AUC IS TWO-COORDINATE, BRIER IS THREE
# ===========================================================================
#
# Reported from the sims/ study: AUC at fixed prevalence is a deterministic
# function of liability R^2 to 94.6%, but AUC explains only 67% of within-cell
# Brier variance, with one cell at rank correlation -0.12.
#
# That is exactly what the Murphy decomposition predicts, and it can be settled
# without the study. For a probabilistic forecast,
#     Brier = reliability - resolution + uncertainty.
# Uncertainty is K(1-K), a function of prevalence alone. Resolution is a
# DISCRIMINATION quantity, fixed by the joint law of (score, outcome) up to
# monotone reparametrisation. Reliability is CALIBRATION, and it is a property
# of the map from score to reported probability -- which differs across methods
# and is not a function of either collapse coordinate.
#
# So Brier needs a third coordinate and AUC does not. The demonstration below
# holds liability R^2 and prevalence FIXED, applies calibration maps that are
# strictly monotone (hence AUC-invariant) and shows Brier moving by order one.
# If AUC moves at all, the demonstration is broken.

def brier_scope(rng, out):
    print("")
    print("=" * 78)
    print("5. THE COLLAPSE'S SCOPE: DISCRIMINATION, NOT THRESHOLD, METRICS")
    print("=" * 78)
    N = 400000
    K = 0.10                      # prevalence
    R2 = 0.25                     # liability R^2
    r = math.sqrt(R2)
    thr = _probit(1.0 - K)
    g = rng.standard_normal(N)
    L = r * g + math.sqrt(1.0 - R2) * rng.standard_normal(N)
    y = (L > thr).astype(np.float64)
    print("  liability threshold model: R^2 = %.2f, prevalence K = %.2f, "
          "N = %d" % (R2, K, N))
    print("  every arm below uses THE SAME score g and THE SAME outcomes y;")
    print("  only the score-to-probability map changes, and every map is")
    print("  strictly monotone, so AUC cannot move.")
    # correctly calibrated map: P(y=1 | g) = Phi((r g - thr)/sqrt(1-R2))
    base = _phi_cdf((r * g - thr) / math.sqrt(1.0 - R2))
    arms = [("calibrated", base),
            ("over-confident (p^0.5 odds)", _odds_pow(base, 2.0)),
            ("under-confident (p^2 odds)", _odds_pow(base, 0.5)),
            ("shifted +0.05", np.clip(base + 0.05, 1e-6, 1 - 1e-6)),
            ("shrunk to prevalence", K + 0.5 * (base - K))]
    unc = K * (1.0 - K)
    print("")
    print("  %-28s %-9s %-11s %-12s %-12s %-11s"
          % ("arm", "AUC", "Brier", "reliability", "resolution", "uncert."))
    rows = []
    for name, p in arms:
        auc = _auc(p, y)
        br = float(np.mean((p - y) ** 2))
        rel, res = _murphy(p, y)
        rows.append({"arm": name, "auc": auc, "brier": br,
                     "reliability": rel, "resolution": res,
                     "uncertainty": unc,
                     "murphy_gap": br - (rel - res + unc)})
        print("  %-28s %-9.6f %-11.6f %-12.6f %-12.6f %-11.6f"
              % (name, auc, br, rel, res, unc))
    aucs = [x["auc"] for x in rows]
    briers = [x["brier"] for x in rows]
    ress = [x["resolution"] for x in rows]
    rels = [x["reliability"] for x in rows]
    print("")
    print("  AUC spread over the arms      : %.2e  (identical -- monotone "
          "maps)" % (max(aucs) - min(aucs)))
    print("  resolution spread             : %.2e  (identical -- it is a "
          "discrimination quantity)" % (max(ress) - min(ress)))
    print("  reliability spread            : %.6f  (the free third "
          "coordinate)" % (max(rels) - min(rels)))
    print("  Brier spread                  : %.6f  = %.1f%% of the "
          "calibrated Brier"
          % (max(briers) - min(briers),
             100.0 * (max(briers) - min(briers)) / briers[0]))
    print("  worst Murphy identity residual: %.2e"
          % max(abs(x["murphy_gap"]) for x in rows))
    ok = (max(aucs) - min(aucs) < 1e-9
          and max(ress) - min(ress) < 1e-6
          and max(briers) - min(briers) > 0.1 * briers[0])
    print("")
    print("  VERDICT. At FIXED liability R^2 and FIXED prevalence -- both")
    print("  collapse coordinates pinned -- AUC and resolution are constant to")
    print("  machine precision while Brier moves by %.0f%%. The mover is"
          % (100.0 * (max(briers) - min(briers)) / briers[0]))
    print("  reliability, i.e. calibration, which is a property of the method's")
    print("  probability map and not of the two coordinates.")
    print("")
    print("  So the theorem's scope should read DISCRIMINATION metrics, not")
    print("  threshold metrics. AUC, and the resolution component of any proper")
    print("  score, collapse onto (R^2, prevalence). Brier, log score and every")
    print("  other proper score do NOT, because each carries a reliability term")
    print("  that is a free third coordinate. The 94.6% versus 67% split you")
    print("  measured is that decomposition, and a cell at rank correlation")
    print("  -0.12 is what a reliability term that varies across methods looks")
    print("  like when it dominates the within-cell spread.")
    print("  demonstration valid (AUC and resolution pinned, Brier moves): %s"
          % ("PASS" if ok else "FAIL"))
    out["brier_scope"] = {"R2": R2, "prevalence": K, "N": N, "arms": rows,
                          "auc_spread": max(aucs) - min(aucs),
                          "resolution_spread": max(ress) - min(ress),
                          "reliability_spread": max(rels) - min(rels),
                          "brier_spread": max(briers) - min(briers),
                          "pass": bool(ok)}
    return ok


def _probit(q):
    # Acklam-free: bisection on erf, exact enough and dependency-free
    lo, hi = -10.0, 10.0
    for _ in range(200):
        mid = 0.5 * (lo + hi)
        if _phi_cdf(mid) < q:
            lo = mid
        else:
            hi = mid
    return 0.5 * (lo + hi)


def _phi_cdf(x):
    return 0.5 * (1.0 + _erf(x / math.sqrt(2.0)))


def _erf(x):
    return np.vectorize(math.erf)(x) if isinstance(x, np.ndarray) else math.erf(x)


def _odds_pow(p, a):
    o = p / (1.0 - p)
    o = o ** a
    return np.clip(o / (1.0 + o), 1e-9, 1 - 1e-9)


def _auc(score, y):
    order = np.argsort(score, kind="mergesort")
    s = score[order]
    yy = y[order]
    # average ranks for ties
    ranks = np.empty(len(s), dtype=np.float64)
    i = 0
    while i < len(s):
        j = i
        while j + 1 < len(s) and s[j + 1] == s[i]:
            j += 1
        ranks[i:j + 1] = 0.5 * (i + j) + 1.0
        i = j + 1
    n1 = float(yy.sum())
    n0 = float(len(yy) - n1)
    return float((ranks[yy == 1].sum() - n1 * (n1 + 1) / 2.0) / (n0 * n1))


def _murphy(p, y, nbin=200):
    """Brier = reliability - resolution + uncertainty, by binning on p."""
    edges = np.quantile(p, np.linspace(0, 1, nbin + 1))
    edges[0] -= 1e-9
    edges[-1] += 1e-9
    idx = np.clip(np.searchsorted(edges, p, side="right") - 1, 0, nbin - 1)
    ybar = y.mean()
    rel = 0.0
    res = 0.0
    for b in range(nbin):
        sel = idx == b
        nb = int(sel.sum())
        if nb == 0:
            continue
        ob = float(y[sel].mean())
        pb = float(p[sel].mean())
        rel += nb * (pb - ob) ** 2
        res += nb * (ob - ybar) ** 2
    return rel / len(y), res / len(y)


def main():
    rng = np.random.default_rng(20260805)
    out = {}
    ok1 = check_against_reported(out)
    why_the_ratio_fails(out)
    dense_curve(out)
    general_optimum(out)
    ok5 = brier_scope(rng, out)
    print("")
    print("=" * 78)
    print("SUMMARY")
    print("=" * 78)
    print("  closed form reproduces the published grid : %s" % ok1)
    print("  Brier-scope demonstration valid           : %s" % ok5)
    out["READ_THE_TEST"] = bool(ok1 and ok5)
    print("  READ_THE_TEST: %s" % out["READ_THE_TEST"])
    fh = open("partition_curve_results.json", "w")
    json.dump(out, fh, indent=1)
    fh.close()
    print("-> partition_curve_results.json")
    return 0 if out["READ_THE_TEST"] else 1


if __name__ == "__main__":
    sys.exit(main())
