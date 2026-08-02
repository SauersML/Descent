#!/usr/bin/env python3
"""Family simulator: THE ORDER-FREE ENSEMBLE CHANNEL. numpy only.

FIRST CONTACT BETWEEN Sec. 14 OF FoldedSpectrum.lean / EnsembleChannel.lean AND
ANY NUMBER. Nothing in this arm has ever been measured. Every prediction below
is stated by the corpus with NO FREE CONSTANT, so a disagreement is a result
and not a calibration.

WHAT THE FORMAL CORE CLAIMS (`EnsembleChannel.lean`)

  T1  THE CHANNEL.  `Var(sample mean of the feature) -> L/n'`, with
      `L = whiteFloor + longRunVariance`.  An order-free sample -- the multiset
      of feature values with time order destroyed -- still sees dependence,
      through sampling fluctuation. At n'=3 this is formalized exactly by
      `three_mul_sampleMeanVariance3`.

  T2  THE FEJER CHANNEL IS INCOMPLETE. `equal_fejer_channel_witness` and
      `unequal_symmetric_fourth_channel_witness` prove that two positive-symbol
      covariance profiles can agree in the sample-mean channel while a
      symmetric Gaussian fourth-order statistic differs. This test measures
      the same separation in a process simulation.

  T3  ENSEMBLE DECONVOLUTION (EXPLORATORY, NOT A LEAN THEOREM). Across m
      targets, estimate the visible scale-mixture law and measure its empirical
      rate. Uniform deconvolution rates remain open.

  T4  COMPOUND PREDICTOR GEOMETRY. `ensembleSquaredLoss_decomposition` and
      `ensemblePredictorSquaredLoss_decomposition` prove the two Pythagorean
      legs. Full recovery on a curve additionally requires the visible
      observation to be injective on that curve; this arm checks injectivity
      numerically instead of inferring it from dimension.

  T5  LIMIT OF THE MEAN CHANNEL. Two priors can share `(mass,L)` and have
      different transported risk. The mean channel cannot distinguish them;
      the fourth-order order-free channel can, confirming that `(mass,L)` is
      not the complete visible algebra.

THE PROCESS, AND WHY EVERY PREDICTION IS CLOSED-FORM

  Latent 2-D chain with eigenvalue lambda = rho e^{i theta}:
      x_t = rho R(theta) x_{t-1} + eta_t,   eta ~ N(0, sigma^2 I)
      F_t = x_t[0] + sqrt(s2) * eps_t,      eps ~ N(0,1)   [the white floor]
  Because rho R(theta) is a scaled rotation, the stationary state covariance is
  EXACTLY (sigma^2/(1-rho^2)) I -- an isotropic fixed point, no Lyapunov solve
  and no burn-in.  Writing `amp` for the stationary variance of x[0]:
      gamma(0) = amp + s2
      gamma(k) = amp * rho^k * cos(k theta)          (k >= 1)
      L        = s2 + amp * (1-rho^2)/(1 - 2 rho cos theta + rho^2)
                 = whiteFloor + longRunVariance, matching the corpus split.
  Every chain starts from its exact stationary law, so "past the mixing time"
  is a statement about the FLUCTUATION LIMIT only, never about equilibration.

  n' IS FINITE AND THE CORPUS LIMIT IS NOT.  The exact finite-depth channel is
  the Fejer sum
      n' Var(mean) = gamma(0) + 2 sum_{k=1}^{n'-1} (1 - k/n') gamma(k)   (FN)
  which is what EnsembleChannel.lean's `fejerChannel3` is at n'=3.  L is its
  n'->infinity limit.  EVERY CELL REPORTS BOTH: measured-vs-FN is the
  INSTRUMENT check (must agree to sampling error, or the simulator is wrong),
  measured-vs-L is the CORPUS claim (must agree once n' beats the mixing time,
  and the gap FN-L is the exact size of the hypothesis `depthSufficient`).
  That split is the whole reason a disagreement here can be attributed.

CONTROLS, EACH OF WHICH MUST BE SHOWN FIRING

  C0  Closed-form Fejer sum vs brute-force summation of gamma(k).  Pins the
      analytic reference itself before any sampling is compared to it.
  C1  White noise, rho = 0.  Then L = FN = gamma(0) exactly at every n', so any
      departure is the estimator and not the mixing hypothesis.
  C2  ANTIPERSISTENT cell, cos theta < 0, where L < gamma(0).  A simulator that
      confuses L with the marginal variance, or drops the cos(k theta), passes
      every persistent cell and fails this one.  The rho grid alone cannot
      separate "L" from "gamma(0) * something increasing in rho"; this cell can.
  C3  T2's POSITIVE CONTROL: a pair with the SAME marginal and DIFFERENT L.
      The mean channel must separate it.  Without C3, "no difference detected"
      in T2 is indistinguishable from a dead instrument -- the failure mode
      that has recurred in this project.
  C4  T4's identity check on ORACLE visibles: Var(b) = Var(E[b|v]) +
      E[Var(b|v)] must hold to arithmetic precision, and the SHEET arm must
      show E[Var(b|v)] > 0 while the CURVE arm shows it = 0.  A curve arm that
      passes because both arms are degenerate is not a test.
  C5  T5's POSITIVE CONTROL: a third prior differing in the L LAW.  The same
      ensemble discriminator that fails to separate P from Q must separate
      P from R, at large effect size.

CAN-FAIL CLAUSES

  T1: the rho grid must reach BOTH rho = 0 (where L = gamma(0) and dependence
      is invisible) and rho >= 0.99 (where L/gamma(0) > 100).  A grid confined
      to moderate rho cannot separate the Fejer channel from the marginal
      variance times any mild increasing function.  It must also contain
      theta > pi/2, where L < gamma(0): sign, not just magnitude.
  T2: the two processes must have IDENTICAL marginal law and IDENTICAL L to
      machine precision -- constructed algebraically, not tuned -- and spectra
      differing by order one off zero (here f(pi) = 1 vs 1/9).  If L differs
      even slightly the test is a triviality.
  T5: the two priors' (mass, L) laws must be identical BY CONSTRUCTION, not
      approximately.  Achieved by using the TWO ROOTS of the same
      (gamma0, L, theta) inversion: same visible pair exactly, two different
      memories.

VECTORISATION.  Replicates and cohorts are batched, but every replicate draws
its OWN normals at every step -- the batch axis is a distinct-draw axis, never
a shared-state axis.  No replicate reuses another's randomness.

Written for Python 3.6.8 with numpy only: no f-strings, no dataclasses, no
walrus, no scipy.
"""

import argparse
import json
import math
import os
import sys
import time

import numpy as np

SEED = 20260802

# ---------------------------------------------------------------------------
# Depth per target.  Chosen so that n' / mixing-time is reported, never assumed.
# ---------------------------------------------------------------------------
N_PRIME = 4000          # T1 main grid
REPS_T1 = 20000         # -> relative SE on n' Var(mean) of sqrt(2/R) = 1.0%
N_T2 = 2000
REPS_T2 = 40000
N_T3 = 500
POOL_T3 = 640000        # cohorts in the T3 pool
N_T4 = 1000
M_T4 = 400
ENS_T4 = 40
N_T5 = 500
M_T5 = 1000
ENS_T5 = 200
REPS_T1B = 20000
DEPTHS_T1B = (32, 64, 128, 256, 512, 1024, 2048, 4096)
NTRUE_T3 = 4000000
ORACLE_T4 = 400000
ORACLE_T5 = 2000000
ISSERLIS_SUBSAMPLE = 20000


def configure_profile(profile):
    """Select a bounded development run or the registered full experiment."""
    global N_PRIME, REPS_T1, N_T2, REPS_T2, N_T3, POOL_T3
    global N_T4, M_T4, ENS_T4, N_T5, M_T5, ENS_T5
    global REPS_T1B, DEPTHS_T1B, NTRUE_T3, ORACLE_T4, ORACLE_T5
    global ISSERLIS_SUBSAMPLE
    if profile == "full":
        return
    if profile != "quick":
        raise ValueError("profile must be 'quick' or 'full'")
    N_PRIME, REPS_T1 = 512, 4000
    N_T2, REPS_T2 = 256, 8000
    N_T3, POOL_T3 = 128, 128000
    N_T4, M_T4, ENS_T4 = 128, 200, 20
    N_T5, M_T5, ENS_T5 = 128, 300, 30
    REPS_T1B = 3000
    DEPTHS_T1B = (32, 128, 512)
    NTRUE_T3 = 200000
    ORACLE_T4 = 50000
    ORACLE_T5 = 100000
    ISSERLIS_SUBSAMPLE = 5000


# ===========================================================================
# 1. CLOSED FORMS FOR THE LATENT-ROTATION PROCESS
# ===========================================================================

def gamma_k(amp, s2, rho, theta, k):
    """Autocovariance of F at lag k (k scalar or array, k >= 0)."""
    k = np.asarray(k, dtype=np.float64)
    base = amp * (rho ** k) * np.cos(k * theta)
    return np.where(k == 0, amp + s2, base)


def long_run_L(amp, s2, rho, theta):
    """L = whiteFloor + longRunVariance, the corpus zero-frequency evaluation."""
    denom = 1.0 - 2.0 * rho * np.cos(theta) + rho * rho
    return s2 + amp * (1.0 - rho * rho) / denom


def fejer_channel(amp, s2, rho, theta, n):
    """EXACT n' Var(sample mean) = g0 + 2 sum_{k=1}^{n-1} (1-k/n) g(k).

    Closed form via complex geometric sums with z = rho e^{i theta}:
        sum_{k=1}^{N} z^k   = z (1 - z^N) / (1 - z)
        sum_{k=1}^{N} k z^k = z (1 - (N+1) z^N + N z^{N+1}) / (1-z)^2
    and gamma(k) = amp * Re(z^k) for k >= 1.  Vectorised over parameter arrays.
    """
    amp = np.asarray(amp, dtype=np.float64)
    s2 = np.asarray(s2, dtype=np.float64)
    rho = np.asarray(rho, dtype=np.float64)
    theta = np.asarray(theta, dtype=np.float64)
    N = float(n) - 1.0
    z = rho * np.exp(1j * theta)
    one_minus = 1.0 - z
    # rho = 0 makes z = 0; the sums are then 0 and the formulae are 0/1.
    s1 = np.where(np.abs(z) < 1e-15, 0.0 + 0j,
                  z * (1.0 - z ** N) / np.where(np.abs(one_minus) < 1e-15,
                                                1.0 + 0j, one_minus))
    s2c = np.where(np.abs(z) < 1e-15, 0.0 + 0j,
                   z * (1.0 - (N + 1.0) * z ** N + N * z ** (N + 1.0))
                   / np.where(np.abs(one_minus) < 1e-15, 1.0 + 0j,
                              one_minus ** 2))
    tail = np.real(s1) - np.real(s2c) / float(n)
    return (amp + s2) + 2.0 * amp * tail


def fejer_bruteforce(amp, s2, rho, theta, n):
    """C0: the same quantity by direct summation.  No shared code path."""
    tot = amp + s2
    for k in range(1, n):
        tot += 2.0 * (1.0 - k / float(n)) * amp * (rho ** k) * math.cos(k * theta)
    return tot


def mixing_time(rho):
    """Relaxation time of the latent chain: |lambda|^t decays as e^{-t/tau}."""
    if rho <= 0.0:
        return 0.0
    if rho >= 1.0:
        return float("inf")
    return 1.0 / (1.0 - rho)


# ===========================================================================
# 2. THE SIMULATOR.  Exact stationary start, batched over independent draws.
# ===========================================================================

def simulate_stats(amp, s2, rho, theta, n, rng, want_m2=False, chunk=None):
    """Sample mean (and second moment) of F over n steps, per cohort.

    amp, s2, rho, theta are arrays of length M -- one entry per INDEPENDENT
    cohort/replicate.  Every cohort draws its own innovations at every step:
    the batch axis is a distinct-draw axis.  The chain starts from its exact
    stationary law N(0, amp * I), so there is no burn-in and no burn-in bug.
    """
    amp = np.asarray(amp, dtype=np.float64)
    s2 = np.asarray(s2, dtype=np.float64)
    rho = np.asarray(rho, dtype=np.float64)
    theta = np.asarray(theta, dtype=np.float64)
    M = amp.shape[0]
    if chunk is None:
        chunk = M
    out_mean = np.empty(M)
    out_m2 = np.empty(M) if want_m2 else None
    for lo in range(0, M, chunk):
        hi = min(lo + chunk, M)
        a = amp[lo:hi]
        sd_state = np.sqrt(a)
        sd_inn = np.sqrt(a * (1.0 - rho[lo:hi] ** 2))
        sd_white = np.sqrt(s2[lo:hi])
        c = rho[lo:hi] * np.cos(theta[lo:hi])
        s = rho[lo:hi] * np.sin(theta[lo:hi])
        x0 = rng.standard_normal(hi - lo) * sd_state
        x1 = rng.standard_normal(hi - lo) * sd_state
        acc = np.zeros(hi - lo)
        acc2 = np.zeros(hi - lo) if want_m2 else None
        for _ in range(n):
            e0 = rng.standard_normal(hi - lo)
            e1 = rng.standard_normal(hi - lo)
            nx0 = c * x0 - s * x1 + sd_inn * e0
            nx1 = s * x0 + c * x1 + sd_inn * e1
            x0, x1 = nx0, nx1
            f = x0 + sd_white * rng.standard_normal(hi - lo)
            acc += f
            if want_m2:
                acc2 += f * f
        out_mean[lo:hi] = acc / float(n)
        if want_m2:
            out_m2[lo:hi] = acc2 / float(n)
    return out_mean, out_m2


# ===========================================================================
# TEST 1: THE CHANNEL
# ===========================================================================

def test1(rng, out):
    print("")
    print("=" * 74)
    print("TEST 1  THE CHANNEL:  n' Var(sample mean of F)  ->  L")
    print("=" * 74)

    # ---- C0: the analytic reference before anything is sampled ------------
    worst = 0.0
    for (a, s, r, th, nn) in ((1.0, 1.0, 0.0, 0.0, 50),
                              (1.0, 0.5, 0.7, 0.0, 400),
                              (2.0, 1.0, 0.9, 2.4, 300),
                              (1.0, 0.0, 0.99, 0.35, 800)):
        cf = float(fejer_channel(np.array([a]), np.array([s]), np.array([r]),
                                 np.array([th]), nn)[0])
        bf = fejer_bruteforce(a, s, r, th, nn)
        worst = max(worst, abs(cf - bf) / max(abs(bf), 1e-12))
    c0 = worst < 1e-10
    print("  C0 closed-form Fejer vs brute-force sum: worst rel diff %.2e -> %s"
          % (worst, "PASS" if c0 else "FAIL"))

    # ---- the grid ---------------------------------------------------------
    # can-fail: reaches rho = 0 (L = gamma0) and rho = 0.995 (L/gamma0 >> 1),
    # and carries theta > pi/2 cells where L < gamma0.
    cells = [
        (0.0, 0.0), (0.3, 0.0), (0.6, 0.0), (0.8, 0.0),
        (0.9, 0.0), (0.95, 0.0), (0.99, 0.0), (0.995, 0.0),
        (0.9, 0.6), (0.9, 1.2), (0.9, 2.2), (0.95, 2.6),
        (0.6, math.pi), (0.9, math.pi),
    ]
    amp, s2 = 1.0, 1.0
    rows = []
    print("")
    print("  amp = %.1f (signal), s2 = %.1f (white floor), n' = %d, reps = %d"
          % (amp, s2, N_PRIME, REPS_T1))
    print("  %-6s %-6s %-9s %-9s %-11s %-11s %-9s %-9s %-8s"
          % ("rho", "theta", "gamma0", "L", "measured", "Fejer(n')",
             "vs L", "vs Fejer", "n'/tau"))
    for (r, th) in cells:
        a_arr = np.full(REPS_T1, amp)
        s_arr = np.full(REPS_T1, s2)
        r_arr = np.full(REPS_T1, r)
        t_arr = np.full(REPS_T1, th)
        mean, _ = simulate_stats(a_arr, s_arr, r_arr, t_arr, N_PRIME, rng,
                                 chunk=REPS_T1)
        meas = float(N_PRIME * np.mean(mean ** 2))
        se = meas * math.sqrt(2.0 / REPS_T1)
        L = float(long_run_L(amp, s2, r, th))
        FN = float(fejer_channel(np.array([amp]), np.array([s2]), np.array([r]),
                                 np.array([th]), N_PRIME)[0])
        tau = mixing_time(r)
        ratio = float("inf") if tau == 0 else N_PRIME / tau
        rows.append({"rho": r, "theta": th, "gamma0": amp + s2, "L": L,
                     "fejer_n": FN, "measured": meas, "se": se,
                     "rel_err_vs_L": (meas - L) / L,
                     "rel_err_vs_fejer": (meas - FN) / FN,
                     "z_vs_fejer": (meas - FN) / se,
                     "n_over_tau": ratio})
        print("  %-6.3f %-6.2f %-9.4f %-9.4f %-11.4f %-11.4f %+8.4f %+9.4f %-8.1f"
              % (r, th, amp + s2, L, meas, FN, (meas - L) / L,
                 (meas - FN) / FN, ratio))
    out["T1_channel"] = rows

    # C1: white noise cell must sit on gamma0 exactly.
    white = [x for x in rows if x["rho"] == 0.0][0]
    c1 = abs(white["z_vs_fejer"]) < 4.0
    print("")
    print("  C1 white noise rho=0 (L = gamma0 = %.2f exactly): measured %.4f, "
          "z = %+.2f -> %s"
          % (white["L"], white["measured"], white["z_vs_fejer"],
             "PASS" if c1 else "FAIL"))

    # C2: antipersistent cells, L < gamma0. Fires only if such cells exist AND
    # the measurement lands below gamma0 -- the sign test the rho grid cannot do.
    anti = [x for x in rows if x["L"] < x["gamma0"] - 1e-9]
    c2 = len(anti) >= 2 and all(x["measured"] < x["gamma0"] for x in anti)
    print("  C2 antipersistent cells with L < gamma0 (%d of them, smallest "
          "L/gamma0 = %.4f): all measured below gamma0 -> %s"
          % (len(anti), min(x["L"] / x["gamma0"] for x in anti) if anti else -1,
             "PASS" if c2 else "FAIL"))

    # The claim: measured == L, no free constant.
    ok_vs_L = [x for x in rows if abs(x["rel_err_vs_L"]) < 0.02]
    worstL = max(abs(x["rel_err_vs_L"]) for x in rows)
    worstF = max(abs(x["z_vs_fejer"]) for x in rows)
    print("")
    print("  CLAIM   worst |measured - L| / L over the grid  : %.4f  (%d/%d "
          "cells within 2%%)" % (worstL, len(ok_vs_L), len(rows)))
    print("  INSTRUMENT worst |measured - Fejer(n')| in SE   : %.2f sigma"
          % worstF)

    out["T1_controls"] = {"C0_closed_form_pass": bool(c0),
                          "C0_worst_rel": worst,
                          "C1_white_pass": bool(c1),
                          "C2_antipersistent_pass": bool(c2),
                          "C2_n_cells": len(anti),
                          "worst_rel_err_vs_L": worstL,
                          "worst_z_vs_fejer": worstF}
    return c0 and c1 and c2


def test1b(rng, out):
    """Where the fluctuation limit starts to bite as rho -> 1.

    This checks the approach to the asymptotic long-run variance and the exact
    finite-depth deficit predicted by the Fejer sum. It does not assert that
    depth beyond a mixing threshold has zero design value.
    """
    print("")
    print("-" * 74)
    print("T1b  WHERE THE LIMIT BITES.  Fixed rho, sweeping depth n'.")
    print("-" * 74)
    amp, s2 = 1.0, 1.0
    rows = []
    reps = REPS_T1B
    for r in (0.9, 0.99):
        tau = mixing_time(r)
        L = float(long_run_L(amp, s2, r, 0.0))
        print("  rho = %.3f, tau = 1/(1-rho) = %.1f, L = %.4f" % (r, tau, L))
        print("    %-7s %-8s %-11s %-11s %-11s %-10s"
              % ("n'", "n'/tau", "measured", "Fejer(n')", "err vs L", "err vs FN"))
        for n in DEPTHS_T1B:
            a_arr = np.full(reps, amp)
            s_arr = np.full(reps, s2)
            r_arr = np.full(reps, r)
            t_arr = np.zeros(reps)
            mean, _ = simulate_stats(a_arr, s_arr, r_arr, t_arr, n, rng,
                                     chunk=reps)
            meas = float(n * np.mean(mean ** 2))
            FN = float(fejer_channel(np.array([amp]), np.array([s2]),
                                     np.array([r]), np.array([0.0]), n)[0])
            rows.append({"rho": r, "n_prime": n, "n_over_tau": n / tau,
                         "measured": meas, "L": L, "fejer_n": FN,
                         "rel_err_vs_L": (meas - L) / L,
                         "rel_err_vs_fejer": (meas - FN) / FN})
            print("    %-7d %-8.1f %-11.4f %-11.4f %+10.4f %+10.4f"
                  % (n, n / tau, meas, FN, (meas - L) / L, (meas - FN) / FN))
    out["T1b_depth_sweep"] = rows

    # The deficit vs L must shrink MONOTONICALLY in n'.  A wrong formula does
    # not improve monotonically with the hypothesis it is supposed to need;
    # this is the instrument check that caught three errors elsewhere today.
    #
    # TOLERANCE, and why it is what it is. n' Var(mean) is an average of
    # squares of Gaussians, so its relative standard error is sqrt(2/reps) =
    # 1.0% at reps = 20000, INDEPENDENT of n'. The first run declared FAIL on a
    # 3e-3 tolerance at the rho = 0.9 tail, where the deficits are 0.0066 ->
    # 0.0126 at n' = 2048 -> 4096: both are inside one standard error of zero,
    # so the sequence has reached its noise floor and there is nothing left to
    # be monotone about. The criterion is therefore "no INCREASE larger than
    # 3 standard errors", which is the strongest statement the reps support.
    # This widens a tolerance that was unsatisfiable by construction; it does
    # not weaken any grid, depth or replicate count, none of which changed.
    se_rel = math.sqrt(2.0 / reps)
    tol = 3.0 * se_rel
    mono = True
    worst_rise = 0.0
    for r in (0.9, 0.99):
        errs = [abs(x["rel_err_vs_L"]) for x in rows if x["rho"] == r]
        for i in range(1, len(errs)):
            worst_rise = max(worst_rise, errs[i] - errs[i - 1])
            if errs[i] > errs[i - 1] + tol:
                mono = False
    print("")
    print("  worst INCREASE in |measured - L|/L along the depth sweep: %+.4f "
          "(3 SE = %.4f)" % (worst_rise, tol))
    print("  C-mono |measured - L|/L shrinks monotonically as depth grows: %s"
          % ("PASS" if mono else "FAIL"))
    out["T1b_monotone_pass"] = bool(mono)
    return mono


# ===========================================================================
# TEST 2: OFF-ZERO INVISIBILITY, WITH A CONTROL THAT MUST FIRE
# ===========================================================================
#
# Three Gaussian MA processes, all with marginal EXACTLY N(0,1):
#   A  b = (1, 0, 0)                 white.  L = 1.  f(w) == 1.
#   B  b = (2/3, 2/3, -1/3)          sum b = 1 and sum b^2 = 1 EXACTLY, so
#                                    gamma0 = 1 and L = (sum b)^2 = 1, IDENTICAL
#                                    to A, while f(pi) = |2/3-2/3-1/3|^2 = 1/9.
#                                    This is the off-zero perturbation.
#   C  b = (0.8, 0.6, 0)             gamma0 = 1 but L = 1.96.  POSITIVE CONTROL.
#
# For a symmetric statistic (1/n) sum f(F_i), n Var -> sum_k Cov(f(F_0),f(F_k)),
# and for a standardised Gaussian pair with correlation r:
#   f = x   : Cov = r                -> channel = sum gamma      = L
#   f = x^2 : Cov = 2 r^2            -> channel = 2 sum gamma^2
#   f = x^3 : Cov = 9r + 6r^3        -> channel = 9 sum gamma + 6 sum gamma^3
#   f = x^4 : Cov = 72 r^2 + 24 r^4  -> channel = 72 sum g^2 + 24 sum g^4
#   f = 1{x<=t}: Cov = sum_{j>=1} (phi(t) He_{j-1}(t))^2 r^j / j!
# All closed form, no free constant.  A and B agree on the x and x^3 channels
# and differ on x^2 and x^4 -- exactly EnsembleChannel.lean's claim.

MA_A = np.array([1.0, 0.0, 0.0])
MA_B = np.array([2.0 / 3.0, 2.0 / 3.0, -1.0 / 3.0])
MA_C = np.array([0.8, 0.6, 0.0])


def ma_gammas(b):
    K = len(b)
    return np.array([float(np.dot(b[:K - k], b[k:])) for k in range(K)])


def ma_channels(b):
    g = ma_gammas(b)
    g_all = np.concatenate([g[::-1][:-1], g])       # lags -K+1 .. K-1
    s1 = float(g_all.sum())
    s2 = float((g_all ** 2).sum())
    s3 = float((g_all ** 3).sum())
    s4 = float((g_all ** 4).sum())
    return {"gamma": g.tolist(), "L": s1, "sum_g2": s2, "sum_g3": s3,
            "sum_g4": s4,
            "chan_x": s1, "chan_x2": 2.0 * s2,
            "chan_x3": 9.0 * s1 + 6.0 * s3,
            "chan_x4": 72.0 * s2 + 24.0 * s4}


def _normal_cdf(t):
    return 0.5 * (1.0 + math.erf(t / math.sqrt(2.0)))


def indicator_channel(b, t, jmax=400):
    """sum_k Cov(1{F_0<=t}, 1{F_k<=t}) via the Hermite expansion.

    INSTRUMENT REPAIR, found by the first run and diagnosed here rather than
    reported as a defect in the theory. The Hermite series
        Cov(1{X<=t},1{Y<=t}) = sum_{j>=1} (phi(t) He_{j-1}(t))^2 r^j / j!
    converges geometrically in r but only as a HARMONIC-type series at r = 1,
    which is exactly the k = 0 term. Truncating it at j = 40 undershot the
    lag-zero variance by 8% -- the first run reported 0.2299 where the exact
    answer is Phi(0)(1-Phi(0)) = 0.2500 -- and that 8% then appeared uniformly
    across all three indicator cells, in BOTH processes, which is the signature
    of a reference error and not of a measurement error. Diagnostic that
    settled it: the white-noise process A has channel exactly p(1-p) at every
    t, and the measurement hit that (0.13287 vs 0.133515 at t = -1) while the
    truncated series did not.

    The k = 0 term is therefore taken in closed form, p(1-p), and the series is
    used only for |k| >= 1 where |r| <= 2/9 here and forty terms are already
    exact to machine precision.
    """
    from numpy.polynomial import hermite_e as He
    g = ma_gammas(b)
    p = _normal_cdf(t)
    tot = p * (1.0 - p)                       # the k = 0 term, exactly
    nz = g[1:]
    phi = math.exp(-0.5 * t * t) / math.sqrt(2.0 * math.pi)
    fact = 1.0
    for j in range(1, jmax + 1):
        fact *= j
        if fact == float("inf"):
            break
        coef = np.zeros(j)
        coef[j - 1] = 1.0
        aj = phi * float(He.hermeval(t, coef))
        tot += (aj ** 2) * 2.0 * float((nz ** j).sum()) / fact
    return tot


def ma_fejer(b, n):
    g = ma_gammas(b)
    tot = g[0]
    for k in range(1, len(g)):
        if k < n:
            tot += 2.0 * (1.0 - k / float(n)) * g[k]
    return tot


def simulate_ma_stats(b, n, reps, rng, chunk=4000):
    """Per-replicate order-free statistics of a Gaussian MA sample."""
    K = len(b)
    ts = (-1.0, 0.0, 1.0)
    res = {"m1": [], "m2": [], "m3": [], "m4": [], "absm": [],
           "svar": [], "median": []}
    for t in ts:
        res["ind_%+.1f" % t] = []
    for lo in range(0, reps, chunk):
        hi = min(lo + chunk, reps)
        w = rng.standard_normal((hi - lo, n + K - 1))
        F = np.zeros((hi - lo, n))
        for j in range(K):
            if b[j] != 0.0:
                F += b[j] * w[:, K - 1 - j: K - 1 - j + n]
        res["m1"].append(F.mean(axis=1))
        res["m2"].append((F ** 2).mean(axis=1))
        res["m3"].append((F ** 3).mean(axis=1))
        res["m4"].append((F ** 4).mean(axis=1))
        res["absm"].append(np.abs(F).mean(axis=1))
        res["svar"].append(F.var(axis=1))
        res["median"].append(np.median(F, axis=1))
        for t in ts:
            res["ind_%+.1f" % t].append((F <= t).mean(axis=1))
    return dict((k, np.concatenate(v)) for k, v in res.items())


def test2(rng, out):
    print("")
    print("=" * 74)
    print("TEST 2  EQUAL FEJER CHANNEL, DIFFERENT SYMMETRIC CHANNELS")
    print("=" * 74)
    chA, chB, chC = ma_channels(MA_A), ma_channels(MA_B), ma_channels(MA_C)
    print("  A  b=(1,0,0)        gamma = %s" % np.round(chA["gamma"], 6).tolist())
    print("  B  b=(2/3,2/3,-1/3) gamma = %s" % np.round(chB["gamma"], 6).tolist())
    print("  C  b=(0.8,0.6,0)    gamma = %s" % np.round(chC["gamma"], 6).tolist())
    print("  marginal law: N(0,1) for all three, EXACTLY (gamma0 = %.12f, "
          "%.12f, %.12f)" % (chA["gamma"][0], chB["gamma"][0], chC["gamma"][0]))
    print("  L:  A %.12f   B %.12f   C %.12f   (A and B identical to machine "
          "precision)" % (chA["L"], chB["L"], chC["L"]))
    # spectrum off zero
    for name, b in (("A", MA_A), ("B", MA_B), ("C", MA_C)):
        fpi = abs(complex(b[0]) - complex(b[1]) + complex(b[2])) ** 2
        print("  spectral density at w = pi:  %s -> %.6f" % (name, fpi))

    statsA = simulate_ma_stats(MA_A, N_T2, REPS_T2, rng)
    statsB = simulate_ma_stats(MA_B, N_T2, REPS_T2, rng)
    statsC = simulate_ma_stats(MA_C, N_T2, REPS_T2, rng)

    def chan(s, key):
        v = s[key]
        c = N_T2 * float(np.var(v))
        se = c * math.sqrt(2.0 / len(v))
        return c, se

    preds = {
        "m1": (chA["chan_x"], chB["chan_x"], chC["chan_x"]),
        "m2": (chA["chan_x2"], chB["chan_x2"], chC["chan_x2"]),
        "m3": (chA["chan_x3"], chB["chan_x3"], chC["chan_x3"]),
        "m4": (chA["chan_x4"], chB["chan_x4"], chC["chan_x4"]),
    }
    for t in (-1.0, 0.0, 1.0):
        k = "ind_%+.1f" % t
        preds[k] = (indicator_channel(MA_A, t), indicator_channel(MA_B, t),
                    indicator_channel(MA_C, t))

    print("")
    print("  ORDER-FREE FLUCTUATION CHANNELS, n' Var(statistic).  A vs B have")
    print("  the same marginal AND the same L; the mean channel should agree")
    print("  while higher symmetric channels may separate. Predictions are closed-form.")
    print("  %-9s %-11s %-11s %-11s %-11s %-11s %-9s"
          % ("stat", "meas A", "pred A", "meas B", "pred B", "B-A", "sigma"))
    rows = []
    for key in ("m1", "m2", "m3", "m4", "absm", "svar", "median",
                "ind_-1.0", "ind_+0.0", "ind_+1.0"):
        cA, seA = chan(statsA, key)
        cB, seB = chan(statsB, key)
        cC, seC = chan(statsC, key)
        pA = preds.get(key, (None, None, None))[0]
        pB = preds.get(key, (None, None, None))[1]
        pC = preds.get(key, (None, None, None))[2]
        d = cB - cA
        sig = d / math.sqrt(seA ** 2 + seB ** 2)
        dC = cC - cA
        sigC = dC / math.sqrt(seA ** 2 + seC ** 2)
        rows.append({"stat": key, "measA": cA, "seA": seA, "predA": pA,
                     "measB": cB, "seB": seB, "predB": pB,
                     "measC": cC, "seC": seC, "predC": pC,
                     "B_minus_A": d, "B_minus_A_sigma": sig,
                     "C_minus_A": dC, "C_minus_A_sigma": sigC})
        print("  %-9s %-11.5f %-11s %-11.5f %-11s %+11.5f %+9.1f"
              % (key, cA, ("%.5f" % pA) if pA is not None else "--",
                 cB, ("%.5f" % pB) if pB is not None else "--", d, sig))
    out["T2_channels"] = rows

    # instrument: every closed-form prediction must be hit
    instr = []
    for r in rows:
        if r["predA"] is not None:
            instr.append(abs(r["measA"] - r["predA"]) / r["seA"])
            instr.append(abs(r["measB"] - r["predB"]) / r["seB"])
            instr.append(abs(r["measC"] - r["predC"]) / r["seC"])
    worst_instr = max(instr)
    print("")
    print("  INSTRUMENT: worst |measured - closed form| over all predicted "
          "channels = %.2f sigma" % worst_instr)

    # C3 POSITIVE CONTROL: A vs C differ in L only -- the mean channel MUST fire
    r_m1 = [r for r in rows if r["stat"] == "m1"][0]
    c3 = abs(r_m1["C_minus_A_sigma"]) > 10.0
    print("  C3 POSITIVE CONTROL, A vs C (same marginal, L = 1.00 vs 1.96):")
    print("     mean channel %.5f vs %.5f, difference %+.1f sigma -> %s"
          % (r_m1["measA"], r_m1["measC"], r_m1["C_minus_A_sigma"],
             "FIRED" if c3 else "DEAD"))

    # the verdict on the impossibility claim
    agree = [r for r in rows if abs(r["B_minus_A_sigma"]) < 4.0]
    disagree = [r for r in rows if abs(r["B_minus_A_sigma"]) >= 4.0]
    print("  A vs B: %d channels agree within 4 sigma, %d separate."
          % (len(agree), len(disagree)))
    for r in disagree:
        print("     SEPARATES: %-9s A %.5f  B %.5f  (%+.1f sigma, %.1f%% "
              "relative)"
              % (r["stat"], r["measA"], r["measB"], r["B_minus_A_sigma"],
                 100.0 * (r["measB"] - r["measA"]) / r["measA"]))

    # even the EXPECTATION of an order-free statistic separates at O(1/n)
    evA = float(np.mean(statsA["svar"]))
    evB = float(np.mean(statsB["svar"]))
    predA = chA["gamma"][0] - ma_fejer(MA_A, N_T2) / N_T2
    predB = chB["gamma"][0] - ma_fejer(MA_B, N_T2) / N_T2
    seev = math.sqrt(np.var(statsA["svar"]) / REPS_T2
                     + np.var(statsB["svar"]) / REPS_T2)
    print("  E[sample variance] at n' = %d:  A %.7f (pred %.7f), "
          "B %.7f (pred %.7f), difference %+.1f sigma"
          % (N_T2, evA, predA, evB, predB, (evB - evA) / seev))

    out["T2_verdict"] = {
        "C3_positive_control_fired": bool(c3),
        "C3_sigma": r_m1["C_minus_A_sigma"],
        "worst_instrument_sigma": worst_instr,
        "n_channels_agreeing": len(agree),
        "n_channels_separating": len(disagree),
        "separating_stats": [r["stat"] for r in disagree],
        "E_svar_A": evA, "E_svar_A_pred": predA,
        "E_svar_B": evB, "E_svar_B_pred": predB,
        "E_svar_sigma": (evB - evA) / seev,
    }
    return c3, len(disagree)


# ===========================================================================
# TEST 3: ENSEMBLE DECONVOLUTION AT RATE m^{-1/2}
# ===========================================================================
#
# Per cohort j the order-free datum is Z_j = n' (mean_j - mu_j)^2.  Given the
# cohort's parameters, mean_j is Gaussian with variance FN_j/n', so
#   E[Z | params] = FN_j,   E[Z^2 | params] = 3 FN_j^2   (chi^2_1).
# Hence over the prior:  E[FN] = E[Z]   and   E[FN^2] = E[Z^2]/3,
# which is the deconvolution: the chi^2_1 mixing kernel is inverted exactly.
# The truth is computed by a parameter-only Monte Carlo of 4e6 draws (closed
# form per draw, no simulation), so the reference carries no sampling cost.

def test3(rng, out):
    print("")
    print("=" * 74)
    print("TEST 3  ENSEMBLE DECONVOLUTION, rate m^{-1/2}")
    print("=" * 74)
    RHO_LO, RHO_HI = 0.10, 0.90
    TH_LO, TH_HI = 0.0, math.pi / 2.0
    AMP, S2 = 1.0, 1.0
    tau_max = mixing_time(RHO_HI)
    print("  prior: rho ~ U(%.2f, %.2f), theta ~ U(%.2f, %.2f), amp %.1f, "
          "s2 %.1f" % (RHO_LO, RHO_HI, TH_LO, TH_HI, AMP, S2))
    print("  n' = %d, worst mixing time %.1f, worst n'/tau = %.1f"
          % (N_T3, tau_max, N_T3 / tau_max))

    # ---- truth by parameter-only MC ---------------------------------------
    trng = np.random.default_rng(SEED + 777)
    NTRUE = NTRUE_T3
    r = trng.uniform(RHO_LO, RHO_HI, NTRUE)
    th = trng.uniform(TH_LO, TH_HI, NTRUE)
    FN_true = fejer_channel(np.full(NTRUE, AMP), np.full(NTRUE, S2), r, th, N_T3)
    L_true = long_run_L(AMP, S2, r, th)
    E1 = float(FN_true.mean())
    E2 = float((FN_true ** 2).mean())
    V = E2 - E1 ** 2
    print("  TRUTH (%d parameter draws, closed form):  E[FN] = %.6f, "
          "Var[FN] = %.6f" % (NTRUE, E1, V))
    print("         limit quantities:                   E[L]  = %.6f, "
          "Var[L]  = %.6f  (n'-deficit %.3f%%)"
          % (float(L_true.mean()),
             float((L_true ** 2).mean() - L_true.mean() ** 2),
             100.0 * (E1 - float(L_true.mean())) / float(L_true.mean())))

    # ---- one pool of cohorts, partitioned into DISJOINT ensembles ---------
    print("  simulating a pool of %d independent cohorts ..." % POOL_T3)
    pr = rng.uniform(RHO_LO, RHO_HI, POOL_T3)
    pth = rng.uniform(TH_LO, TH_HI, POOL_T3)
    means, _ = simulate_stats(np.full(POOL_T3, AMP), np.full(POOL_T3, S2),
                              pr, pth, N_T3, rng, chunk=160000)
    Z = N_T3 * means ** 2

    rows = []
    print("")
    print("  %-8s %-8s %-13s %-13s %-13s %-13s"
          % ("m", "ens", "RMSE E[L]", "RMSE Var[L]", "bias E[L]", "bias Var[L]"))
    for m in (25, 100, 400, 1600, 6400):
        nens = POOL_T3 // m
        blk = Z[: nens * m].reshape(nens, m)
        e1 = blk.mean(axis=1)
        e2 = (blk ** 2).mean(axis=1) / 3.0
        vv = e2 - e1 ** 2
        rmse1 = float(np.sqrt(np.mean((e1 - E1) ** 2)))
        rmsev = float(np.sqrt(np.mean((vv - V) ** 2)))
        rows.append({"m": m, "ensembles": nens,
                     "rmse_EL": rmse1, "rmse_VarL": rmsev,
                     "bias_EL": float(e1.mean() - E1),
                     "bias_VarL": float(vv.mean() - V),
                     "true_EL": E1, "true_VarL": V})
        print("  %-8d %-8d %-13.6f %-13.6f %+13.6f %+13.6f"
              % (m, nens, rmse1, rmsev, e1.mean() - E1, vv.mean() - V))
    out["T3_deconvolution"] = rows

    lm = np.log(np.array([x["m"] for x in rows], dtype=np.float64))
    s1 = float(np.polyfit(lm, np.log([x["rmse_EL"] for x in rows]), 1)[0])
    sv = float(np.polyfit(lm, np.log([x["rmse_VarL"] for x in rows]), 1)[0])
    print("")
    print("  fitted rate  d log RMSE / d log m :  E[L] %+.4f, Var[L] %+.4f "
          "(parametric benchmark -0.5)" % (s1, sv))
    ok = abs(s1 + 0.5) < 0.06 and abs(sv + 0.5) < 0.10
    # can-fail: an estimator that were merely CONSISTENT but slower, or biased,
    # would show a slope away from -1/2 or a bias not shrinking; both are visible
    # in the table above.
    biasok = abs(rows[-1]["bias_EL"]) < 3.0 * rows[-1]["rmse_EL"]
    print("  slope within tolerance of -1/2: %s ; largest-m bias inside "
          "sampling error: %s" % ("PASS" if ok else "FAIL",
                                  "PASS" if biasok else "FAIL"))
    out["T3_rate"] = {"slope_EL": s1, "slope_VarL": sv, "pass": bool(ok),
                      "bias_ok": bool(biasok)}
    return ok and biasok


# ===========================================================================
# TEST 4: THE COMPOUND PREDICTOR DECOMPOSITION
# ===========================================================================
#
# Deployment target b = gamma(1) = amp * rho * cos(theta): an off-zero spectral
# functional, invisible to the channel.  Visible pair v = (gamma0, L).
#   CURVE arm : one parameter xi, rho and theta both functions of xi, so v
#               determines xi determines b.  fiberVariance must be 0.
#   SHEET arm : rho and theta independent, so the level sets of L are not level
#               sets of b.  fiberVariance must be > 0.
# Rules:
#   source-centred (the envelope): a single constant, the source's b.
#   pooled/compound             : E[b | v], fitted across the m cohorts.
# The two EnsembleChannel decompositions supply the finite Pythagorean identities.
# The curve arm separately checks that the visible coordinate is injective; low
# dimension alone would not imply full recovery.

def curve_params(xi):
    """One-parameter family.  rho up, theta down: L and b both monotone in xi,
    so the visible L determines xi -- injectivity is checked, not assumed."""
    rho = 0.30 + 0.55 * xi
    theta = 1.20 - 0.90 * xi
    return rho, theta


def sheet_params(rng, m):
    return rng.uniform(0.30, 0.85, m), rng.uniform(0.30, 1.20, m)


def binned_regression(v, b, nbin):
    """E[b | v] by equal-count binning on the scalar visible coordinate."""
    order = np.argsort(v)
    vs, bs = v[order], b[order]
    edges = np.linspace(0, len(v), nbin + 1).astype(int)
    fit = np.empty(len(v))
    for i in range(nbin):
        lo, hi = edges[i], edges[i + 1]
        if hi > lo:
            fit[lo:hi] = bs[lo:hi].mean()
    inv = np.empty(len(v), dtype=int)
    inv[order] = np.arange(len(v))
    return fit[inv]


def binned_regression_predict(v_train, b_train, v_test, nbin):
    """Predict on held-out cohorts from bins fitted only on training cohorts."""
    order = np.argsort(v_train)
    vs, bs = v_train[order], b_train[order]
    edges = np.linspace(0, len(v_train), nbin + 1).astype(int)
    centers, means = [], []
    for i in range(nbin):
        lo, hi = edges[i], edges[i + 1]
        if hi > lo:
            centers.append(float(vs[lo:hi].mean()))
            means.append(float(bs[lo:hi].mean()))
    return np.interp(v_test, np.asarray(centers), np.asarray(means))


def test4(rng, out):
    print("")
    print("=" * 74)
    print("TEST 4  THE COMPOUND PREDICTOR DECOMPOSITION")
    print("=" * 74)
    AMP, S2 = 1.0, 1.0

    # ---- C4: the identity and the two arms, on ORACLE visibles ------------
    NT = ORACLE_T4
    trng = np.random.default_rng(SEED + 991)
    xi = trng.uniform(0.0, 1.0, NT)
    cr, cth = curve_params(xi)
    sr, sth = sheet_params(trng, NT)
    arms = {}
    for name, (r, th) in (("curve", (cr, cth)), ("sheet", (sr, sth))):
        L = long_run_L(AMP, S2, r, th)
        b = AMP * r * np.cos(th)
        pred = binned_regression(L, b, 400)
        varb = float(b.var())
        varpred = float(pred.var())
        resid = float(np.mean((b - pred) ** 2))
        arms[name] = {"var_b": varb, "mean_b": float(b.mean()),
                      "visible_predictable_variance": varpred,
                      "fiber_residual": resid,
                      "identity_gap": varb - (varpred + resid),
                      "L_min": float(L.min()), "L_max": float(L.max()),
                      "b_min": float(b.min()), "b_max": float(b.max())}
        print("  %-6s  Var(b) = %.6f   Var(E[b|L]) = %.6f   E[Var(b|L)] = "
              "%.6f   identity gap %.2e"
              % (name, varb, varpred, resid, varb - (varpred + resid)))
    # injectivity of the curve arm, checked not assumed
    g = np.linspace(0.0, 1.0, 2001)
    Lg = long_run_L(AMP, S2, *curve_params(g))
    bg = AMP * curve_params(g)[0] * np.cos(curve_params(g)[1])
    mono = bool(np.all(np.diff(Lg) > 0)) and bool(np.all(np.diff(bg) > 0))
    print("  curve arm: L strictly monotone in xi (%s), b strictly monotone "
          "(%s) -> visible determines blind" % (mono, mono))
    c4 = (mono
          and abs(arms["curve"]["identity_gap"]) < 1e-6
          and abs(arms["sheet"]["identity_gap"]) < 1e-6
          and arms["curve"]["fiber_residual"] < 0.02 * arms["curve"]["var_b"]
          and arms["sheet"]["fiber_residual"] > 0.05 * arms["sheet"]["var_b"])
    print("  C4 identity holds on both arms AND curve fiber ~ 0 AND sheet "
          "fiber > 0 -> %s" % ("PASS" if c4 else "FAIL"))
    print("     (the sheet arm is what makes the curve arm a result rather "
          "than a degeneracy: fiber/Var(b) = %.4f vs %.4f)"
          % (arms["curve"]["fiber_residual"] / arms["curve"]["var_b"],
             arms["sheet"]["fiber_residual"] / arms["sheet"]["var_b"]))
    out["T4_oracle"] = arms
    out["T4_C4_pass"] = bool(c4)

    # ---- the operational version: v estimated from order-free samples ----
    # Per cohort the visible L is seen only through ONE chi^2_1 draw, so the
    # pooled rule is attenuated.  B independent sub-panels per cohort reduce
    # that noise by 1/B; the shortfall must fall MONOTONICALLY in B toward the
    # oracle value.  That monotone approach is the instrument check: an
    # attenuation is an estimation cost, a wrong identity is not.
    #
    # TWO NESTED LEGS, WHICH THE FIRST RUN CONFLATED AND THIS RUN SEPARATES.
    # The first run reported a "recovered fraction" of 2.63 on the curve arm --
    # 263% of a variance -- which is impossible and was my instrument, not the
    # corpus. The source-centred penalty is Var(b) + (E[b] - b_src)^2, and the
    # squared bias is not part of the predictable variance at all. The core
    # states TWO decompositions and they stack:
    #   LEG 1  EnsembleChannel.lean `ensembleSquaredLoss_decomposition`:
    #          loss(source) = loss(centroid) + card * (centroid - source)^2,
    #          so moving from the source to the ensemble centroid gains
    #          exactly the squared displacement (E[b] - b_src)^2.
    #   LEG 2  `ensemblePredictorSquaredLoss_decomposition`, centered at E[b]:
    #          centroidPenalty - compoundPenalty = visiblePredictableVariance,
    #          so moving from the centroid to E[b|v] gains exactly Var(E[b|v]).
    # LEG 2 is the curve-prior claim and the only one with predictable variance,
    # so the recovered fraction is measured against the CENTROID rule. Both
    # legs are printed; neither is a free constant.
    print("")
    print("  OPERATIONAL: pooled rule fitted on ESTIMATED visibles, m = %d "
          "cohorts, n' = %d, %d ensembles" % (M_T4, N_T4, ENS_T4))
    print("  %-6s %-5s %-13s %-13s %-13s %-13s"
          % ("arm", "B", "source pen", "centroid pen", "pooled pen",
             "leg2 = cen-pool"))
    rows = []
    for name in ("curve", "sheet"):
        for B in (1, 4, 16):
            # All ENS_T4 ensembles x M_T4 cohorts x B sub-panels are simulated
            # in ONE batched call. The batch axis is a distinct-draw axis: every
            # entry gets its own innovations at every step, and the B sub-panels
            # of a cohort share the cohort's PARAMETERS and nothing else. This
            # is a speed fix only; replicates, depths and grids are unchanged.
            tot = ENS_T4 * M_T4
            if name == "curve":
                x = rng.uniform(0.0, 1.0, tot)
                r, th = curve_params(x)
            else:
                r, th = sheet_params(rng, tot)
            b = AMP * r * np.cos(th)
            rB = np.tile(r, B)
            tB = np.tile(th, B)
            mm, _ = simulate_stats(np.full(tot * B, AMP), np.full(tot * B, S2),
                                   rB, tB, N_T4, rng,
                                   chunk=min(tot * B, 200000))
            Lhat = (N_T4 * mm ** 2).reshape(B, tot).mean(axis=0)
            # source-centred rule: the source cohort is the xi = 0 end of
            # the family, i.e. the population the score was trained in.
            b_src = AMP * curve_params(0.0)[0] * math.cos(
                curve_params(0.0)[1]) if name == "curve" else \
                AMP * 0.30 * math.cos(0.30)
            bE = b.reshape(ENS_T4, M_T4)
            LE = Lhat.reshape(ENS_T4, M_T4)
            src_l, cen_l, pol_l = [], [], []
            for e in range(ENS_T4):
                src_l.append(float(np.mean((bE[e] - b_src) ** 2)))
                cen_l.append(float(np.mean((bE[e] - bE[e].mean()) ** 2)))
                # Two-fold cross-fitting: evaluating bins on their training cohorts
                # understated pooled loss and produced an impossible >100% recovery.
                mid = M_T4 // 2
                nbin = max(4, int(M_T4 / 40))
                fit = np.empty(M_T4)
                fit[mid:] = binned_regression_predict(
                    LE[e, :mid], bE[e, :mid], LE[e, mid:], nbin)
                fit[:mid] = binned_regression_predict(
                    LE[e, mid:], bE[e, mid:], LE[e, :mid], nbin)
                pol_l.append(float(np.mean((bE[e] - fit) ** 2)))
            src = float(np.mean(src_l))
            cen = float(np.mean(cen_l))
            pol = float(np.mean(pol_l))
            leg1 = src - cen        # ensembleSquaredLoss_decomposition
            leg2 = cen - pol        # conditional-predictor Pythagorean leg
            oracle_leg2 = arms[name]["visible_predictable_variance"]
            rows.append({"arm": name, "B": B, "source_penalty": src,
                         "centroid_penalty": cen, "pooled_penalty": pol,
                         "leg1_source_to_centroid": leg1,
                         "leg1_predicted_sq_displacement": src - cen,
                         "leg2_centroid_to_pooled": leg2,
                         "leg2_predicted_VarEbv": oracle_leg2,
                         "oracle_total_blind_Var_b": arms[name]["var_b"],
                         "oracle_fiber": arms[name]["fiber_residual"],
                         "fraction_of_predictable_variance_recovered":
                             leg2 / oracle_leg2})
            print("  %-6s %-5d %-13.6f %-13.6f %-13.6f %-13.6f"
                  % (name, B, src, cen, pol, leg2))
    out["T4_operational"] = rows

    print("")
    print("  LEG 2: centroid penalty - cross-fitted pooled penalty")
    print("  as a fraction of the oracle predictable variance Var(E[b|v]):")
    for r in rows:
        print("    %-6s B=%-3d  leg2 %.6f vs Var(E[b|v]) %.6f (ratio %.4f)"
              % (r["arm"], r["B"], r["leg2_centroid_to_pooled"],
                 r["leg2_predicted_VarEbv"],
                 r["fraction_of_predictable_variance_recovered"]))
    cur = [r for r in rows if r["arm"] == "curve"]
    monoB = all(cur[i]["fraction_of_predictable_variance_recovered"]
                >= cur[i - 1]["fraction_of_predictable_variance_recovered"] - 1e-3
                for i in range(1, len(cur)))
    print("  C-attenuation: recovered predictable fraction on the curve rises "
          "monotonically with B -> %s" % ("PASS" if monoB else "FAIL"))
    out["T4_attenuation_monotone"] = bool(monoB)
    return c4, monoB


# ===========================================================================
# TEST 5: THE EXACT LIMIT -- SAME VISIBLE PAIR, DIFFERENT RISK
# ===========================================================================
#
# Fix theta and gamma0 and s2.  The map rho -> g(rho,theta) is TWO-TO-ONE:
#     rho^2 (1+G) - 2 G cos(theta) rho + (G-1) = 0
# has two roots in (0,1) for admissible G.  The two roots give processes with
# IDENTICAL gamma0 and IDENTICAL L -- the visible pair agrees EXACTLY, by
# construction and not by tuning -- but different memory, different spectrum
# off zero, and different gamma(1), hence different transported risk.
#   prior P: the small-rho root.   prior Q: the large-rho root.
#   prior R (CONTROL): the small-rho root with a DIFFERENT G law, so the
#            visible pair differs and the discriminator must fire.

def rho_from_G(G, theta, branch):
    ct, st = math.cos(theta), math.sin(theta)
    disc = G * G * ct * ct - (G * G - 1.0)
    if np.any(disc < 0):
        raise ValueError("G out of range for this theta")
    root = np.sqrt(disc)
    return (G * ct + (root if branch > 0 else -root)) / (1.0 + G)


def test5(rng, out):
    print("")
    print("=" * 74)
    print("TEST 5  THE EXACT LIMIT: identical visible pair, different risk")
    print("=" * 74)
    THETA = 0.35
    AMP, S2 = 1.0, 1.0
    G_LO, G_HI = 1.05, 1.50
    GC_LO, GC_HI = 1.60, 2.30           # control prior R
    print("  theta = %.2f fixed, amp = %.1f, white floor s2 = %.1f, so "
          "gamma0 = %.1f for every cohort in every prior"
          % (THETA, AMP, S2, AMP + S2))
    print("  G = longRunVariance/amp ~ U(%.2f,%.2f) for P and Q; the SAME draw "
          "of G is used for the P cohort and the Q cohort, so the (mass, L) "
          "law is identical by construction, not by matching."
          % (G_LO, G_HI))

    # exact risks under the prior
    trng = np.random.default_rng(SEED + 313)
    NT = ORACLE_T5
    G = trng.uniform(G_LO, G_HI, NT)
    rP = rho_from_G(G, THETA, -1)
    rQ = rho_from_G(G, THETA, +1)
    bP = AMP * rP * math.cos(THETA)
    bQ = AMP * rQ * math.cos(THETA)
    LP = long_run_L(AMP, S2, rP, THETA)
    LQ = long_run_L(AMP, S2, rQ, THETA)
    print("  visible check: max |L_P - L_Q| over %d draws = %.3e "
          "(identical), L range [%.4f, %.4f]"
          % (NT, float(np.max(np.abs(LP - LQ))), float(LP.min()), float(LP.max())))
    print("  rho_P in [%.4f, %.4f];  rho_Q in [%.4f, %.4f]"
          % (rP.min(), rP.max(), rQ.min(), rQ.max()))
    riskP = float(np.mean(bP ** 2))
    riskQ = float(np.mean(bQ ** 2))
    print("  AGGREGATE TRANSPORTED RISK  E[gamma(1)^2] (source has no memory):")
    print("     prior P %.6f     prior Q %.6f     ratio %.2fx"
          % (riskP, riskQ, riskQ / riskP))
    # second-moment channel, which EnsembleChannel says is NOT determined by L
    def sum_g2(amp, s2, rho, theta, kmax=4000):
        k = np.arange(1, kmax + 1)
        g = amp * (rho[:, None] ** k) * np.cos(k * theta)
        return (amp + s2) ** 2 + 2.0 * (g ** 2).sum(axis=1)
    sg2P = float(np.mean(sum_g2(AMP, S2, rP[:ISSERLIS_SUBSAMPLE], THETA)))
    sg2Q = float(np.mean(sum_g2(AMP, S2, rQ[:ISSERLIS_SUBSAMPLE], THETA)))
    print("  fourth-order (Isserlis) channel 2*sum gamma(k)^2:  P %.4f  "
          "Q %.4f  (ratio %.2fx)" % (2 * sg2P, 2 * sg2Q, sg2Q / sg2P))

    tau_max = mixing_time(float(rQ.max()))
    print("  worst mixing time (prior Q, rho = %.4f) = %.1f, n' = %d, "
          "n'/tau = %.1f" % (rQ.max(), tau_max, N_T5, N_T5 / tau_max))

    # ---- the ensemble discriminators --------------------------------------
    def run_prior(kind, nens, m):
        # One batched call for all nens * m cohorts; the ensembles are DISJOINT
        # blocks of the batch, so they are independent by construction.
        tot = nens * m
        if kind == "R":
            g = rng.uniform(GC_LO, GC_HI, tot)
            r = rho_from_G(g, THETA, -1)
        else:
            g = rng.uniform(G_LO, G_HI, tot)
            r = rho_from_G(g, THETA, +1 if kind == "Q" else -1)
        mm, m2 = simulate_stats(np.full(tot, AMP), np.full(tot, S2), r,
                                np.full(tot, THETA), N_T5, rng,
                                want_m2=True, chunk=min(tot, 200000))
        d_mean = (N_T5 * mm ** 2).reshape(nens, m).mean(axis=1)
        d_m2 = (N_T5 * (m2 - (AMP + S2)) ** 2).reshape(nens, m).mean(axis=1)
        return d_mean, d_m2

    print("")
    print("  discriminators over %d ensembles of m = %d cohorts:"
          % (ENS_T5, M_T5))
    dP, qP = run_prior("P", ENS_T5, M_T5)
    dQ, qQ = run_prior("Q", ENS_T5, M_T5)
    dR, qR = run_prior("R", ENS_T5, M_T5)

    def welch(a, b):
        return (a.mean() - b.mean()) / math.sqrt(a.var(ddof=1) / len(a)
                                                 + b.var(ddof=1) / len(b))

    tPQ = welch(dP, dQ)
    tPR = welch(dP, dR)
    qPQ = welch(qP, qQ)
    qPR = welch(qP, qR)
    # THE CLAIM IS ABOUT L, WHICH IS THE LIMIT. AT FINITE DEPTH THE MEAN
    # CHANNEL IS THE FEJER SUM, AND THE FEJER SUM IS *NOT* A FUNCTION OF L
    # ALONE: it depends on rho and theta separately. P and Q share L exactly
    # and have rho 0.03-0.22 against 0.91-0.94, so their finite-depth channels
    # differ by a computable amount that vanishes as n' -> infinity. That
    # deficit is the ONLY thing the mean channel can see here, and it is
    # predicted with no free constant, so a residual t is attributed rather
    # than argued about.
    fnP = float(np.mean(fejer_channel(np.full(len(rP), AMP),
                                      np.full(len(rP), S2), rP,
                                      np.full(len(rP), THETA), N_T5)))
    fnQ = float(np.mean(fejer_channel(np.full(len(rQ), AMP),
                                      np.full(len(rQ), S2), rQ,
                                      np.full(len(rQ), THETA), N_T5)))
    print("    MEAN channel  E_ens[n' xbar^2]:  P %.5f  Q %.5f  R %.5f"
          % (dP.mean(), dQ.mean(), dR.mean()))
    print("      exact finite-depth prediction:  P %.5f  Q %.5f   "
          "(both -> E[L] = %.5f as n' -> inf)" % (fnP, fnQ, float(LP.mean())))
    print("      the P-Q gap the mean channel CAN see at n' = %d is %.5f "
          "(%.2f%% of L), and it vanishes with depth; the L it is claimed to "
          "see is identical to %.1e" % (N_T5, fnQ - fnP,
                                        100.0 * (fnQ - fnP) / float(LP.mean()),
                                        float(np.max(np.abs(LP - LQ)))))
    print("      P vs Q  t = %+8.2f     P vs R  t = %+8.2f  <- C5 control"
          % (tPQ, tPR))
    print("    FOURTH-ORDER channel E_ens[n' (m2-gamma0)^2]:  P %.4f  Q %.4f  "
          "R %.4f" % (qP.mean(), qQ.mean(), qR.mean()))
    print("      P vs Q  t = %+8.2f     P vs R  t = %+8.2f" % (qPQ, qPR))

    c5 = abs(tPR) > 10.0
    print("")
    print("  C5 POSITIVE CONTROL: the mean-channel discriminator separates P "
          "from a prior with a DIFFERENT L law -> %s (|t| = %.1f)"
          % ("FIRED" if c5 else "DEAD", abs(tPR)))
    print("  MEAN-CHANNEL FINITE-DEPTH CHECK: P and Q have the same limiting visible "
          "pair and %.2fx risk difference; at this depth |t| = %.2f -> %s"
          % (riskQ / riskP, abs(tPQ),
             "not separated" if abs(tPQ) < 3.0 else "separated by the predicted Fejer remainder"))
    print("  BUT the fourth-order ensemble observable separates P from Q at "
          "|t| = %.1f" % abs(qPQ))

    out["T5"] = {"theta": THETA, "G_range": [G_LO, G_HI],
                 "risk_P": riskP, "risk_Q": riskQ, "risk_ratio": riskQ / riskP,
                 "L_identical_max_abs_diff": float(np.max(np.abs(LP - LQ))),
                 "rho_P_range": [float(rP.min()), float(rP.max())],
                 "rho_Q_range": [float(rQ.min()), float(rQ.max())],
                 "isserlis_channel_P": 2 * sg2P, "isserlis_channel_Q": 2 * sg2Q,
                 "mean_channel_P": float(dP.mean()),
                 "mean_channel_Q": float(dQ.mean()),
                 "mean_channel_R": float(dR.mean()),
                 "mean_channel_P_fejer_predicted": fnP,
                 "mean_channel_Q_fejer_predicted": fnQ,
                 "t_mean_PQ": tPQ, "t_mean_PR": tPR,
                 "fourth_channel_P": float(qP.mean()),
                 "fourth_channel_Q": float(qQ.mean()),
                 "fourth_channel_R": float(qR.mean()),
                 "t_fourth_PQ": qPQ, "t_fourth_PR": qPR,
                 "C5_control_fired": bool(c5),
                 "mean_channel_not_separated_at_this_depth": bool(abs(tPQ) < 3.0)}
    return c5, abs(tPQ) < 3.0, abs(qPQ)


# ===========================================================================

def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--profile", choices=("quick", "full"), default="quick",
                        help="bounded development signal or registered full experiment")
    parser.add_argument("--output", default=os.path.join(
        os.path.dirname(os.path.abspath(__file__)), "fam_ensemble_channel_results.json"))
    args = parser.parse_args(argv)
    configure_profile(args.profile)
    t0 = time.time()
    rng = np.random.default_rng(SEED)
    out = {"profile": args.profile, "seed": SEED,
           "n_prime_T1": N_PRIME, "reps_T1": REPS_T1,
           "n_T2": N_T2, "reps_T2": REPS_T2, "n_T3": N_T3, "pool_T3": POOL_T3,
           "n_T4": N_T4, "m_T4": M_T4, "ens_T4": ENS_T4,
           "n_T5": N_T5, "m_T5": M_T5, "ens_T5": ENS_T5}

    t1_ok = test1(rng, out)
    t1b_ok = test1b(rng, out)
    c3_fired, n_sep = test2(rng, out)
    t3_ok = test3(rng, out)
    c4_ok, t4_mono = test4(rng, out)
    c5_fired, t5_blind, t5_fourth = test5(rng, out)

    print("")
    print("=" * 74)
    print("CONTROLS")
    print("=" * 74)
    print("  T1 C0 closed-form reference        : %s" % out["T1_controls"]["C0_closed_form_pass"])
    print("  T1 C1 white-noise cell             : %s" % out["T1_controls"]["C1_white_pass"])
    print("  T1 C2 antipersistent cells L<gamma0: %s" % out["T1_controls"]["C2_antipersistent_pass"])
    print("  T1b monotone approach to L         : %s" % out["T1b_monotone_pass"])
    print("  T2 C3 positive control FIRED       : %s" % c3_fired)
    print("  T3 rate + bias                     : %s" % t3_ok)
    print("  T4 C4 identity + non-degenerate arms: %s" % c4_ok)
    print("  T4 attenuation monotone in B       : %s" % t4_mono)
    print("  T5 C5 positive control FIRED       : %s" % c5_fired)
    ok = bool(t1_ok and t1b_ok and c3_fired and t3_ok and c4_ok and t4_mono
              and c5_fired)
    out["ALL_CONTROLS_FIRED"] = ok
    out["T2_channels_separating"] = n_sep
    out["T5_mean_channel_not_separated_at_this_depth"] = bool(t5_blind)
    out["T5_fourth_order_t"] = float(t5_fourth)
    out["READ_THE_TEST"] = ok
    print("")
    print("  READ_THE_TEST (every control fired): %s" % ok)
    print("  runtime %.1f s" % (time.time() - t0))
    fh = open(args.output, "w")
    json.dump(out, fh, indent=1)
    fh.close()
    print("-> %s" % args.output)
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
