#!/usr/bin/env python3
"""Family simulator: PERMEABILITY, COUPLING ORDER, AND THE CLOSING LAW.

Companion to fam_ensemble_channel.py, which measured the dimension-one case.
This file measures the CONSTANTS of the general theorem. Every claim below has
a predicted number, not a predicted shape, so each cell reports
measured / predicted as a RATIO. A ratio of 1.9 against a claim of 1.0 is the
finding; "looks consistent" is not a result.

THE FRAME
  Coupling order  r*(delta) = min { r >= 2 : D_delta Lambda_r(theta0) != 0 },
  Lambda_r the r-th joint cumulant structure; r = 2 is the long-run covariance
  Sigma. Three regimes:
     WALL         the level-0 (one-unit) law is unmoved -> zero information at
                  EVERY sample size, not merely vanishing information;
     MEMBRANE     r* = 2, information positive and explicit;
     OBSTRUCTION  r* = infinity, absolute blindness.

WHAT IS MEASURED

  C1  THE PERMEABILITY CONSTANT.
        p(delta) = 1/2 || Sigma^{-1/2} Gamma Sigma^{-1/2} ||^2_HS,  Gamma = D_delta Sigma
      is claimed to be the PER-DRAW Fisher information, so estimating a
      deployment coordinate from m estimator draws has RMSE (m p)^{-1/2}.
      THE CONSTANT IS THE CONTENT: an m^{-1/2} slope alone is satisfied by
      almost any sensible estimator and tests nothing. Run in dimension 2 with
      an ANISOTROPIC Sigma so the Hilbert-Schmidt norm does real work -- with
      Sigma proportional to the identity the HS norm degenerates to a scalar
      ratio times the dimension and the claim is untested.

      CAUTION OBSERVED: p is an ASYMPTOTIC per-draw information, so the CLT
      must have engaged at the depth used. Verified, not assumed: the draw
      distribution's excess kurtosis and its covariance are both reported
      against their Gaussian/Fejer targets before the constant is quoted.

  C2  THE WALL AT EVERY SAMPLE SIZE. A delta that fixes the one-unit law and
      moves dependence must leave level-0 statistics with ZERO signal, and --
      the part that makes it a wall rather than slow convergence -- the signal
      must not DECAY with n. Swept over three orders of magnitude in n.

  C3  THE SEALING LAW p ~ eta^2. Near the modulus-copy wall the permeability
      is claimed to vanish QUADRATICALLY in the support floor eta. The
      exponent is the whole claim: exponent 1 would make the document's
      1/(m eta^2) cost law wrong. Fitted on a log-log sweep of eta, on
      MEASURED information (1/(m RMSE^2)) and not only on the closed form.

  C4  ADDITIVITY OF THE CLOSING LAW.
        AggRisk = eps^2 [ d0/(2n) + sum_i 1/(2 m p_i) + r_perp^2 ]
                        * (1 + O(kappa (r + noise radii)))
      n, m and r_perp are varied INDEPENDENTLY on a full factorial grid and the
      three coefficients are fitted jointly, together with an n*m CROSS TERM
      that additivity says must be zero. A one-parameter sweep cannot see a
      cross term at all, which is why the grid is factorial.

  C5  COUNT AND ORDER: count = dim W, order = max_w r*. For a d-dimensional
      spectral family, d lagged second moments with nonsingular Jacobian
      [d gamma(k_i) / d h_j] complete the scheme. THE TEST THAT MATTERS IS THE
      NEGATIVE ONE: d-1 lags must fail by leaving a GENUINELY UNIDENTIFIED
      DIRECTION -- two distinct parameter points with identical observables --
      and not merely by fitting worse. Degenerate lag choices must fail too.

  C6  VALUE OF AN ADDED CORRELATED PROBE. For two quadratic-summary channels,
      precision-weighted information must equal first-channel information plus
      squared CONDITIONAL response divided by CONDITIONAL noise. A probe whose
      response is completely predicted through shared noise must add exactly
      zero; a response innovation must add strictly positive information.

  NOT ATTEMPTED, AND WHY. The deconvolution face predicts rate (log m)^{-beta}
  with pi/2 in the exponent, from |Gamma(1/2+it)| ~ sqrt(2 pi) e^{-pi|t|/2}.
  Going from m = 1e3 to m = 1e6 moves log m by a factor of two; no achievable m
  separates (log m)^{-beta} from a constant, let alone recovers pi/2. Recorded
  as analytically stated and NUMERICALLY OUT OF REACH. A fitted exponent here
  would be a number nobody should believe, and reporting one would be worse
  than reporting the gap.

CONTROLS THAT MUST BE SHOWN FIRING
  P1  C1's Sigma must be genuinely anisotropic: the condition number is
      reported, and a cell with Sigma proportional to I is run alongside to
      show the HS norm is not doing trivial work.
  P2  C2's POSITIVE CONTROL: a perturbation that DOES move the one-unit law,
      through the identical discriminator, must grow like sqrt(n). Without it
      "no signal" is indistinguishable from a dead statistic.
  P3  C3's sweep must span enough decades that exponent 1 and exponent 2 are
      separated by more than the error bars; the predicted ratio of p across
      the sweep is printed for both exponents so the reader can see the gap.
  P4  C4's cross-term coefficient must be estimable: its standard error is
      reported, and a DELIBERATELY NON-ADDITIVE synthetic risk is passed
      through the same fitter to show the fitter detects a cross term when one
      is present.
  P5  C5's negative arm must exhibit two parameter points with observables
      equal to within sampling error AND a deployment quantity differing by
      order one. Equal observables alone would be a weak test.

Written for Python 3.6.8 with numpy only.
"""

import argparse
import json
import math
import os
import sys
import time

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.dirname(
    os.path.abspath(__file__)))))

import simprov  # noqa: E402

SEED = 20260803

C1_NP = 800
C1_R_ENS = 200
C1_M_MAX = 1600
C1_M_GRID = (50, 200, 800, 1600)
C2_N_GRID = (1000, 10000, 100000, 1000000)
C2_DRAW_BUDGET = 2000000
C3_NP = 200
C3_M = 20000
C3_R = 200
C3_ETAS = (0.30, 0.15, 0.075, 0.0375)
C4_NP = 200
C4_N_GRID = (200, 800, 3200)
C4_M_GRID = (400, 1600, 6400)
C4_REP = 400
C5_NP = 400
C5_M = 240000
C5_M_GRID = (500, 2000, 8000)

# The knobs `--set` may override, each with a one-line meaning, so that
# `--help` is a complete account of what can be widened without reading the
# source.  Everything here is either a sample count (more replicates, smaller
# error bar) or a grid (more cells, visible curve); nothing here changes an
# estimand.
TUNABLES = {
    "C1_NP": "C1 chain depth n'",
    "C1_R_ENS": "C1 ensembles at the largest m (sets the total cohort pool)",
    "C1_M_MAX": "C1 largest draw count m",
    "C1_M_GRID": "C1 sweep over m",
    "C2_N_GRID": "C2 sweep over sample size n",
    "C2_DRAW_BUDGET": "C2 total one-unit draws per cell",
    "C3_NP": "C3 chain depth n'",
    "C3_M": "C3 draws per ensemble",
    "C3_R": "C3 ensembles per eta (the replicate count of the sealing law)",
    "C3_ETAS": "C3 sweep over the support floor eta",
    "C4_NP": "C4 chain depth n'",
    "C4_N_GRID": "C4 sweep over source sample size n",
    "C4_M_GRID": "C4 sweep over channel draw count m",
    "C4_REP": "C4 replicates per factorial cell",
    "C5_NP": "C5 chain depth n'",
    "C5_M": "C5 draws for the identifiability arm",
    "C5_M_GRID": "C5 sweep over m",
}


def configure_profile(profile):
    """Use a bounded development experiment by default; preserve the registered full run.

    `deep` is the full experiment with the SAMPLING widened and nothing else
    touched: more cells on the m and eta axes so the constants are read off a
    curve, and more ensembles per cell so the error bar is small against the
    deviation from 1.0 that each check is testing for.  Every estimand -- rho0,
    theta0, the paths, the closed forms -- is identical to `full`.
    """
    global C1_NP, C1_R_ENS, C1_M_MAX, C1_M_GRID
    global C2_N_GRID, C2_DRAW_BUDGET, C3_NP, C3_M, C3_R, C3_ETAS
    global C4_NP, C4_N_GRID, C4_M_GRID, C4_REP
    global C5_NP, C5_M, C5_M_GRID
    if profile == "full":
        return
    if profile == "deep":
        C1_R_ENS, C1_M_MAX = 600, 3200
        C1_M_GRID = (25, 50, 100, 200, 400, 800, 1600, 3200)
        C2_DRAW_BUDGET = 8000000
        C2_N_GRID = (300, 1000, 3000, 10000, 30000, 100000, 300000, 1000000)
        C3_M, C3_R = 20000, 800
        # Nine etas over a 16x range: the local slope of the closed form moves
        # from about 1.54 to about 1.96 across it, so the curvature that the
        # secant slope hides is directly visible.
        C3_ETAS = tuple(simprov.log_grid(0.30, 0.01875, 9))
        C4_N_GRID = (100, 200, 400, 800, 1600, 3200)
        C4_M_GRID = (200, 400, 800, 1600, 3200, 6400)
        C4_REP = 1200
        C5_M_GRID = (250, 500, 1000, 2000, 4000, 8000)
        return
    if profile != "quick":
        raise ValueError("profile must be 'quick', 'full' or 'deep'")
    C1_NP, C1_R_ENS, C1_M_MAX = 256, 40, 400
    C1_M_GRID = (25, 100, 400)
    C2_N_GRID, C2_DRAW_BUDGET = (500, 5000, 50000), 200000
    C3_NP, C3_M, C3_R = 128, 3000, 60
    C3_ETAS = (0.30, 0.15, 0.075, 0.0375)
    C4_NP = 128
    C4_N_GRID, C4_M_GRID, C4_REP = (100, 400, 1600), (100, 400, 1600), 80
    C5_NP, C5_M, C5_M_GRID = 200, 24000, (200, 800, 3200)


def apply_overrides(settings):
    """Apply `--set NAME=VALUE` after the profile, so a profile stays a baseline.

    Scalars parse as ints; anything with a comma or a decimal point becomes a
    tuple, which is how the grids are spelled.
    """
    applied = {}
    for s in settings:
        if "=" not in s:
            raise SystemExit("--set expects NAME=VALUE, got %r" % s)
        name, _, raw = s.partition("=")
        name = name.strip().upper()
        if name not in TUNABLES:
            raise SystemExit("--set: unknown knob %r; see --help for the list"
                             % name)
        parts = [p for p in raw.replace(",", " ").split() if p]
        vals = [float(p) if ("." in p or "e" in p.lower()) else int(p)
                for p in parts]
        value = vals[0] if len(vals) == 1 and "," not in raw else tuple(vals)
        globals()[name] = value
        applied[name] = value
    return applied


def resolved_config():
    """Every tunable's value as it stands, for the results file.

    A sweep that records its profile name but not the numbers behind it cannot
    be re-run from its own output, and the profile names have already been
    edited once.
    """
    return {name: (list(globals()[name])
                   if isinstance(globals()[name], tuple)
                   else globals()[name])
            for name in TUNABLES}


# ===========================================================================
# Shared engine: latent 2-D chain, eigenvalue lambda = rho e^{i theta}.
# rho R(theta) is a scaled rotation, so the stationary state covariance is
# exactly amp * I and every run starts in its own stationary law.
# ===========================================================================

def g_zero(rho, theta):
    """Zero-frequency evaluation of the latent chain, per unit state variance.
    sum_k rho^{|k|} cos(k theta) = (1-rho^2)/(1 - 2 rho cos theta + rho^2)."""
    return (1.0 - rho ** 2) / (1.0 - 2.0 * rho * np.cos(theta) + rho ** 2)


def g_zero_fejer(rho, theta, n):
    """The EXACT finite-depth version: n Var(mean) per unit state variance."""
    rho = np.asarray(rho, dtype=np.float64)
    theta = np.asarray(theta, dtype=np.float64)
    N = float(n) - 1.0
    z = rho * np.exp(1j * theta)
    om = 1.0 - z
    tiny = np.abs(z) < 1e-15
    s1 = np.where(tiny, 0j, z * (1.0 - z ** N) / np.where(np.abs(om) < 1e-15,
                                                          1 + 0j, om))
    s2 = np.where(tiny, 0j,
                  z * (1.0 - (N + 1.0) * z ** N + N * z ** (N + 1.0))
                  / np.where(np.abs(om) < 1e-15, 1 + 0j, om ** 2))
    return 1.0 + 2.0 * (np.real(s1) - np.real(s2) / float(n))


def sim_state_means(rho, theta, amp, n, rng, chunk=200000):
    """Sample mean of BOTH latent coordinates, per cohort. Stationary start.

    rho, theta, amp are per-cohort arrays; the batch axis is a distinct-draw
    axis and every cohort draws its own innovations at every step.
    """
    M = rho.shape[0]
    out = np.empty((M, 2))
    for lo in range(0, M, chunk):
        hi = min(lo + chunk, M)
        a = amp[lo:hi]
        sd0 = np.sqrt(a)
        sdi = np.sqrt(a * (1.0 - rho[lo:hi] ** 2))
        c = rho[lo:hi] * np.cos(theta[lo:hi])
        s = rho[lo:hi] * np.sin(theta[lo:hi])
        x0 = rng.standard_normal(hi - lo) * sd0
        x1 = rng.standard_normal(hi - lo) * sd0
        a0 = np.zeros(hi - lo)
        a1 = np.zeros(hi - lo)
        for _ in range(n):
            e0 = rng.standard_normal(hi - lo)
            e1 = rng.standard_normal(hi - lo)
            nx0 = c * x0 - s * x1 + sdi * e0
            nx1 = s * x0 + c * x1 + sdi * e1
            x0, x1 = nx0, nx1
            a0 += x0
            a1 += x1
        out[lo:hi, 0] = a0 / float(n)
        out[lo:hi, 1] = a1 / float(n)
    return out


# ===========================================================================
# C1. THE PERMEABILITY CONSTANT
# ===========================================================================
#
# Observation V_t = C x_t + w_t, w ~ N(0, W).  The long-run covariance of the
# latent chain is g(rho,theta) * amp * I exactly (scaled rotation), so
#     Sigma(rho) = amp * g(rho,theta) * C C^T + W
# and Gamma = d Sigma / d rho = amp * g'(rho,theta) * C C^T.
# C is deliberately NON-ORTHOGONAL and W is deliberately ANISOTROPIC, so
# Sigma is not a multiple of the identity and the Hilbert-Schmidt norm is not
# a disguised scalar.  With Sigma proportional to I the claim would reduce to
# p = (Gamma/Sigma)^2 * dim/2 and nothing about the HS structure would be
# tested; that degenerate cell is run alongside as control P1.

C_MIX = np.array([[1.0, 0.0], [1.0, 2.0]])
W_FLOOR = np.array([[0.60, 0.0], [0.0, 1.80]])
# THETA0 = 0 IS NOT AN ARBITRARY CHOICE, AND THE FIRST RUN IS WHY.
#
# Sigma depends on rho only through the scalar g(rho, theta) =
# (1-rho^2)/(1 - 2 rho cos theta + rho^2), and for theta != 0 THAT MAP IS
# TWO-TO-ONE: at theta = 0.40 it peaks at rho = 0.665, so g(0.55) = g(0.752)
# exactly. The first run used theta = 0.40 and got RMSE ratios of 0.84, 1.43,
# 2.69, 3.39 against the claimed 1.0, with an RMSE that barely fell as m rose
# 32-fold (0.148 -> 0.105) and a persistent bias of +0.03 to +0.07. That is
# not a wrong information constant; it is a BIMODAL LIKELIHOOD with a second
# mode at the conjugate root, and the profiled MLE jumping branches. The
# two-to-one structure is real -- it is the same construction that
# fam_ensemble_channel.py's Test 5 uses deliberately to build two priors with
# an identical visible pair -- and here it was sabotaging the estimator rather
# than being the object of study.
#
# At theta = 0 the map g = (1+rho)/(1-rho) is strictly monotone on (0,1), so
# rho is globally identified from Sigma and the MLE has one mode. The
# anisotropy that makes the Hilbert-Schmidt norm do real work comes from the
# non-orthogonal C and the unequal white floor W, NOT from theta, so nothing
# about the test is weakened by this: cond(Sigma) is still ~5.8 and the
# degenerate isotropic cell is still run alongside for comparison.
THETA0 = 0.0
AMP0 = 1.0


def sigma_of(rho, n=None, C=C_MIX, W=W_FLOOR, theta=THETA0, amp=AMP0):
    gg = g_zero(rho, theta) if n is None else float(g_zero_fejer(
        np.array([rho]), np.array([theta]), n)[0])
    return amp * gg * C.dot(C.T) + W


def gamma_of(rho, n=None, C=C_MIX, W=W_FLOOR, theta=THETA0, amp=AMP0, h=1e-5):
    """d Sigma / d rho.  Sigma is an exact closed form, so a central difference
    is exact to ~1e-10 -- this is differentiation of a formula, not of data."""
    return (sigma_of(rho + h, n, C, W, theta, amp)
            - sigma_of(rho - h, n, C, W, theta, amp)) / (2.0 * h)


def permeability(rho, n=None, C=C_MIX, W=W_FLOOR, theta=THETA0, amp=AMP0):
    S = sigma_of(rho, n, C, W, theta, amp)
    G = gamma_of(rho, n, C, W, theta, amp)
    ev, Q = np.linalg.eigh(S)
    Sinvh = Q.dot(np.diag(ev ** -0.5)).dot(Q.T)
    M = Sinvh.dot(G).dot(Sinvh)
    return 0.5 * float((M * M).sum())


def precompute_grid(n, grid):
    """Sigma^{-1} and log det Sigma at every grid point, once.

    Speed only: the profile likelihood evaluates the SAME Sigma(rho) for every
    ensemble, so building it inside the ensemble loop recomputed one 2x2
    inverse 1.5 million times. Nothing about the grid, the depth or the number
    of ensembles changes.
    """
    inv = np.empty((len(grid), 2, 2))
    ld = np.empty(len(grid))
    for i, r in enumerate(grid):
        Sg = sigma_of(r, n)
        inv[i] = np.linalg.inv(Sg)
        ld[i] = float(np.linalg.slogdet(Sg)[1])
    return inv, ld


def mle_rho_fast(U, grid, inv, ld):
    """Same profiled MLE as mle_rho, evaluated against the precomputed grid."""
    S = U.T.dot(U) / U.shape[0]
    ll = -0.5 * (ld + np.einsum("kij,ji->k", inv, S))
    i = int(np.argmax(ll))
    if 0 < i < len(grid) - 1:
        y0, y1, y2 = ll[i - 1], ll[i], ll[i + 1]
        d = y0 - 2 * y1 + y2
        if d != 0:
            off = 0.5 * (y0 - y2) / d
            return float(grid[i] + off * (grid[1] - grid[0]))
    return float(grid[i])


def mle_rho(U, n, grid, C=C_MIX, W=W_FLOOR):
    """Gaussian covariance MLE of rho from draws U (m x 2), U ~ N(0, Sigma(rho)).

    Profiled over the 1-D grid then refined parabolically.  The model uses the
    FINITE-DEPTH Sigma, so the estimator is not asked to absorb the Fejer
    deficit; that keeps a wrong constant attributable to the theorem rather
    than to the depth.
    """
    S = U.T.dot(U) / U.shape[0]
    ll = np.empty(len(grid))
    for i, r in enumerate(grid):
        Sg = sigma_of(r, n)
        sign, logdet = np.linalg.slogdet(Sg)
        ll[i] = -0.5 * (logdet + np.trace(np.linalg.solve(Sg, S)))
    i = int(np.argmax(ll))
    if 0 < i < len(grid) - 1:
        y0, y1, y2 = ll[i - 1], ll[i], ll[i + 1]
        d = y0 - 2 * y1 + y2
        if d != 0:
            off = 0.5 * (y0 - y2) / d
            return float(grid[i] + off * (grid[1] - grid[0]))
    return float(grid[i])


def c1(rng, out):
    print("")
    print("=" * 78)
    print("C1  THE PERMEABILITY CONSTANT   p = 1/2 ||S^-1/2 Gamma S^-1/2||^2_HS")
    print("=" * 78)
    RHO0 = 0.55
    NP = C1_NP
    S = sigma_of(RHO0, NP)
    G = gamma_of(RHO0, NP)
    cond = float(np.linalg.cond(S))
    p_fin = permeability(RHO0, NP)
    p_inf = permeability(RHO0, None)
    print("  rho0 = %.2f, theta = %.2f, depth n' = %d, mixing time %.1f, "
          "n'/tau = %.0f" % (RHO0, THETA0, NP, 1.0 / (1 - RHO0),
                             NP * (1 - RHO0)))
    print("  Sigma(n') =\n%s" % np.array2string(S, precision=5,
                                                prefix="    "))
    print("  Gamma     =\n%s" % np.array2string(G, precision=5, prefix="    "))
    print("  P1 CONTROL: condition number of Sigma = %.3f (anisotropic; at 1.0 "
          "the HS norm would be a disguised scalar)" % cond)
    print("  p(finite depth) = %.6f     p(asymptotic) = %.6f   (%.2f%% apart)"
          % (p_fin, p_inf, 100.0 * (p_fin - p_inf) / p_inf))

    # degenerate isotropic cell: C = I, W = I -> Sigma proportional to I
    Ciso, Wiso = np.eye(2), np.eye(2)
    Siso = sigma_of(RHO0, NP, Ciso, Wiso)
    p_iso = permeability(RHO0, NP, Ciso, Wiso)
    scalar_ratio = gamma_of(RHO0, NP, Ciso, Wiso)[0, 0] / Siso[0, 0]
    print("  P1 degenerate cell C=I,W=I: cond(Sigma) = %.3f, p = %.6f, and "
          "dim/2 * (Gamma/Sigma)^2 = %.6f -- identical, so that cell tests "
          "NOTHING about the HS structure"
          % (float(np.linalg.cond(Siso)), p_iso, 1.0 * scalar_ratio ** 2))

    # ---- the estimator draws ---------------------------------------------
    R_ENS = C1_R_ENS
    M_MAX = C1_M_MAX
    POOL = R_ENS * M_MAX
    print("")
    print("  simulating a pool of %d independent cohorts at depth %d ..."
          % (POOL, NP))
    means = sim_state_means(np.full(POOL, RHO0), np.full(POOL, THETA0),
                            np.full(POOL, AMP0), NP, rng)
    V = means.dot(C_MIX.T) + rng.standard_normal((POOL, 2)).dot(
        np.sqrt(W_FLOOR / float(NP)))
    U = math.sqrt(NP) * V

    # CLT AUDIT, verified rather than assumed
    emp = U.T.dot(U) / POOL
    kurt = [float(np.mean(U[:, j] ** 4) / np.mean(U[:, j] ** 2) ** 2 - 3.0)
            for j in range(2)]
    relS = float(np.max(np.abs(emp - S) / np.abs(S)))
    print("  CLT AUDIT: empirical Cov(u) vs Sigma(n'), worst relative "
          "deviation %.4f (%d draws)" % (relS, POOL))
    print("             excess kurtosis of the draw coordinates: %+.4f, %+.4f "
          "(Gaussian target 0; SE %.4f)"
          % (kurt[0], kurt[1], math.sqrt(24.0 / POOL)))
    clt_ok = abs(kurt[0]) < 0.05 and abs(kurt[1]) < 0.05 and relS < 0.03

    # Grid spacing 0.0005, i.e. 60x finer than the smallest predicted RMSE
    # (1/sqrt(1600 p)), so grid resolution cannot masquerade as an information
    # deficit. Global identifiability of rho from Sigma is CHECKED here rather
    # than assumed, because the first run's failure was exactly a violation of
    # it.
    grid = np.linspace(0.02, 0.96, 1881)
    gvals = np.array([sigma_of(r, NP)[0, 0] for r in grid])
    mono = bool(np.all(np.diff(gvals) > 0))
    print("  IDENTIFIABILITY: rho -> Sigma is strictly monotone over the MLE "
          "grid: %s (theta = %.2f). At theta != 0 it is two-to-one and the "
          "likelihood is bimodal." % (mono, THETA0))
    ginv, gld = precompute_grid(NP, grid)
    # agreement between the reference implementation and the precomputed one,
    # on a real block, so the speed fix cannot silently change the estimator
    chk = abs(mle_rho(U[:2000], NP, grid) - mle_rho_fast(U[:2000], grid,
                                                         ginv, gld))
    print("  speed-fix audit: reference MLE and precomputed MLE differ by "
          "%.2e on a 2000-draw block" % chk)
    rows = []
    print("")
    print("  %-8s %-8s %-13s %-13s %-11s %-9s"
          % ("m", "ens", "RMSE meas", "RMSE pred", "ratio", "bias"))
    for m in C1_M_GRID:
        nens = POOL // m
        est = np.empty(nens)
        for e in range(nens):
            est[e] = mle_rho_fast(U[e * m:(e + 1) * m], grid, ginv, gld)
        rmse = float(np.sqrt(np.mean((est - RHO0) ** 2)))
        pred = 1.0 / math.sqrt(m * p_fin)
        # RMSE over nens ensembles has relative standard error 1/sqrt(2 nens),
        # and the claim under test is that rmse/pred equals 1.0, so this is the
        # bar that the deviation has to clear. Reported per row rather than
        # left for the reader to reconstruct.
        rows.append({"m": m, "ensembles": nens, "rmse": rmse,
                     "rmse_predicted": pred, "ratio": rmse / pred,
                     "ratio_se": (rmse / pred) / math.sqrt(2.0 * nens)
                     if nens > 0 else None,
                     "bias": float(est.mean() - RHO0),
                     "bias_se": float(est.std(ddof=1) / math.sqrt(nens))
                     if nens > 1 else None,
                     "estimates": [float(x) for x in est]})
        print("  %-8d %-8d %-13.6f %-13.6f %-11.4f %+9.5f"
              % (m, nens, rmse, pred, rmse / pred, est.mean() - RHO0))
    ratios = [r["ratio"] for r in rows]
    zs = [((r["ratio"] - 1.0) / r["ratio_se"]) if r["ratio_se"] else None
          for r in rows]
    print("")
    print("  CONSTANT CHECK: measured RMSE / (m p)^{-1/2}, over the m grid: "
          "%s" % ", ".join("%.4f" % x for x in ratios))
    print("  with standard errors:  %s"
          % ", ".join("%.4f" % (r["ratio_se"] or float("nan")) for r in rows))
    print("  deviations from 1.0 in SE: %s"
          % ", ".join("n/a" if z is None else "%+.2f" % z for z in zs))
    print("  (a slope test alone would pass for any consistent estimator; the "
          "content is that these ratios are 1.0. Read the SE column first: a "
          "10 per cent tolerance applied to a ratio whose SE is 12 per cent "
          "is a check that cannot fail.)")
    ok = clt_ok and mono and all(abs(x - 1.0) < 0.10 for x in ratios[1:])
    out["C1"] = {"identifiable_monotone": bool(mono),
                 "rho0": RHO0, "n_prime": NP, "p_finite": p_fin,
                 "p_asymptotic": p_inf, "cond_sigma": cond,
                 "p_isotropic_cell": p_iso,
                 "clt_kurtosis": kurt, "clt_cov_rel_dev": relS,
                 "clt_ok": bool(clt_ok), "rows": rows,
                 "ratios": ratios, "ratio_z": zs, "pass": bool(ok)}
    return ok


# ===========================================================================
# C2. THE WALL, AT EVERY SAMPLE SIZE
# ===========================================================================
#
# A one-unit (level-0) observation of a Gaussian MA process is exactly
# N(0, sum b_j^2).  Any path b(delta) with sum b_j^2 constant therefore FIXES
# the level-0 law while moving every lag covariance: a wall for level-0
# statistics and a membrane at r* = 2.  The wall claim is not that the signal
# is small at large n; it is that there is no signal AT ANY n.

def wall_path(delta):
    """Unit-norm path: b(0) = (1,0,0) -> b(1) = (2/3,2/3,-1/3). Norm is 1 for
    every delta, so the one-unit law is N(0,1) throughout."""
    b0 = np.array([1.0, 0.0, 0.0])
    b1 = np.array([2.0 / 3.0, 2.0 / 3.0, -1.0 / 3.0])
    v = b1 - b0
    v = v - b0 * float(np.dot(b0, v))
    v = v / math.sqrt(float(np.dot(v, v)))
    ang = delta * math.acos(float(np.dot(b0, b1)))
    return math.cos(ang) * b0 + math.sin(ang) * v


def one_unit_draws(b, n, rng):
    """n INDEPENDENT one-unit observations of the MA process."""
    K = len(b)
    w = rng.standard_normal((n, K))
    return w.dot(b[::-1])


def ks_two_sample(a, b):
    a = np.sort(a)
    b = np.sort(b)
    allv = np.concatenate([a, b])
    ca = np.searchsorted(a, allv, side="right") / float(len(a))
    cb = np.searchsorted(b, allv, side="right") / float(len(b))
    return float(np.max(np.abs(ca - cb)))


def c2(rng, out):
    print("")
    print("=" * 78)
    print("C2  THE WALL: zero level-0 information AT EVERY SAMPLE SIZE")
    print("=" * 78)
    b0 = wall_path(0.0)
    b1 = wall_path(1.0)
    print("  b(0) = %s   b(1) = %s" % (np.round(b0, 6).tolist(),
                                       np.round(b1, 6).tolist()))
    print("  one-unit variance: %.14f vs %.14f  (level-0 law UNMOVED)"
          % (float(np.dot(b0, b0)), float(np.dot(b1, b1))))
    g0 = np.array([float(np.dot(b0[:3 - k], b0[k:])) for k in range(3)])
    g1 = np.array([float(np.dot(b1[:3 - k], b1[k:])) for k in range(3)])
    print("  lag covariances:   %s vs %s  (dependence MOVED, r* = 2)"
          % (np.round(g0, 6).tolist(), np.round(g1, 6).tolist()))
    # positive control: a delta that DOES move the one-unit law
    b_ctl = 1.06 * b0
    print("  P2 control arm b = 1.06 * b(0): one-unit variance %.6f (MOVED by "
          "%.1f%%)" % (float(np.dot(b_ctl, b_ctl)),
                       100.0 * (np.dot(b_ctl, b_ctl) - 1.0)))

    rows = []
    print("")
    print("  Kolmogorov two-sample statistic, standardised as sqrt(n/2) D_n.")
    print("  Under a wall this is O(1) forever; under a moved law it grows "
          "like sqrt(n).")
    print("  %-10s %-9s %-16s %-16s"
          % ("n", "reps", "WALL arm", "P2 control arm"))
    for n in C2_N_GRID:
        reps = max(6, int(C2_DRAW_BUDGET / n))
        w_stats, c_stats = [], []
        for _ in range(reps):
            x0 = one_unit_draws(b0, n, rng)
            x1 = one_unit_draws(b1, n, rng)
            xc = one_unit_draws(b_ctl, n, rng)
            w_stats.append(math.sqrt(n / 2.0) * ks_two_sample(x0, x1))
            c_stats.append(math.sqrt(n / 2.0) * ks_two_sample(x0, xc))
        wm, cm = float(np.mean(w_stats)), float(np.mean(c_stats))
        rows.append({"n": n, "reps": reps, "wall_stat": wm,
                     "control_stat": cm,
                     "wall_se": float(np.std(w_stats) / math.sqrt(reps)),
                     "control_se": float(np.std(c_stats) / math.sqrt(reps))})
        print("  %-10d %-9d %-16.4f %-16.4f" % (n, reps, wm, cm))
    wall_flat = (max(r["wall_stat"] for r in rows)
                 / min(r["wall_stat"] for r in rows)) < 1.6
    ctl_grows = rows[-1]["control_stat"] / rows[0]["control_stat"] > 8.0
    print("")
    print("  WALL arm    max/min over three decades of n = %.3f "
          "(flat -> no information at any n): %s"
          % (max(r["wall_stat"] for r in rows) / min(r["wall_stat"]
                                                     for r in rows),
             "PASS" if wall_flat else "FAIL"))
    print("  P2 CONTROL  grows by %.1fx over the same range (sqrt(n) would be "
          "%.1fx): %s"
          % (rows[-1]["control_stat"] / rows[0]["control_stat"],
             math.sqrt(float(C2_N_GRID[-1]) / C2_N_GRID[0]),
             "FIRED" if ctl_grows else "DEAD"))
    out["C2"] = {"rows": rows, "wall_flat": bool(wall_flat),
                 "control_fired": bool(ctl_grows),
                 "level0_var_wall": [float(np.dot(b0, b0)),
                                     float(np.dot(b1, b1))],
                 "lag_covs": [g0.tolist(), g1.tolist()]}
    return wall_flat and ctl_grows


# ===========================================================================
# C3. THE SEALING LAW  p ~ eta^2
# ===========================================================================
#
# The modulus-copy wall: at eta = 0 the feature is an EXACT copy of a
# delta-independent reference and carries nothing.  The support floor enters
# the feature linearly,
#       F_t = z_t + eta * delta * z_{t-1},
# with z a fixed AR(1).  Then
#       Sigma(delta) = (1 + eta delta)^2 L_z,
#       Gamma        = 2 eta (1 + eta delta) L_z,
#       p            = 1/2 (Gamma/Sigma)^2 = 2 eta^2 / (1 + eta delta)^2,
# so p vanishes QUADRATICALLY -- and the alternative "linear" reading would
# have p ~ eta.  Over the eta range swept the two differ by the square of the
# range, which is printed, so the reader can see the exponents are separated
# by far more than the error bars.

PHI_Z = 0.5


def seal_sigma(eta, delta, n=None):
    """Long-run variance of F_t = z_t + eta delta z_{t-1}, z ~ AR(1, PHI_Z)
    with innovation variance 1 - PHI_Z^2 (so Var z = 1)."""
    if n is None:
        Lz = (1.0 - PHI_Z ** 2) / (1.0 - PHI_Z) ** 2
    else:
        k = np.arange(1, n)
        Lz = 1.0 + 2.0 * float(np.sum((1.0 - k / float(n)) * PHI_Z ** k))
    return (1.0 + eta * delta) ** 2 * Lz


def seal_p(eta, delta, n=None):
    S = seal_sigma(eta, delta, n)
    h = 1e-6
    G = (seal_sigma(eta, delta + h, n) - seal_sigma(eta, delta - h, n)) / (2 * h)
    return 0.5 * (G / S) ** 2


def sim_seal_means(eta, delta, n, M, rng, chunk=400000):
    """Sample mean of F over n steps, per cohort. AR(1) from stationarity."""
    out = np.empty(M)
    sdi = math.sqrt(1.0 - PHI_Z ** 2)
    for lo in range(0, M, chunk):
        hi = min(lo + chunk, M)
        z = rng.standard_normal(hi - lo)
        acc = np.zeros(hi - lo)
        for _ in range(n):
            zp = z
            z = PHI_Z * z + sdi * rng.standard_normal(hi - lo)
            acc += z + eta * delta * zp
        out[lo:hi] = acc / float(n)
    return out


def c3(rng, out):
    print("")
    print("=" * 78)
    print("C3  THE SEALING LAW:  p(delta) ~ eta^2 as eta -> 0")
    print("=" * 78)
    DELTA0 = 1.0
    NP = C3_NP
    etas = tuple(C3_ETAS)
    print("  F_t = z_t + eta * delta * z_{t-1}, z ~ AR(1) phi = %.2f, "
          "delta0 = %.1f, n' = %d (mixing time %.1f)"
          % (PHI_Z, DELTA0, NP, 1.0 / (1 - PHI_Z)))
    print("  P3: eta sweeps %.4gx. Exponent 2 predicts p to fall %.1fx; "
          "exponent 1 predicts %.1fx. The arms are far apart."
          % (etas[0] / etas[-1], (etas[0] / etas[-1]) ** 2,
             etas[0] / etas[-1]))
    M = C3_M
    R = C3_R
    rows = []
    print("")
    print("  %-9s %-13s %-13s %-13s %-11s"
          % ("eta", "p closed form", "p measured", "RMSE meas", "ratio"))
    for eta in etas:
        pth = seal_p(eta, DELTA0, NP)
        tot = M * R
        mm = sim_seal_means(eta, DELTA0, NP, tot, rng)
        U2 = (NP * mm ** 2).reshape(R, M).mean(axis=1)
        # Sigma_hat -> delta_hat by inverting (1+eta delta)^2 Lz
        Lz = seal_sigma(0.0, 0.0, NP)
        ratio = np.sqrt(np.maximum(U2 / Lz, 1e-12))
        dhat = (ratio - 1.0) / eta
        rmse = float(np.sqrt(np.mean((dhat - DELTA0) ** 2)))
        pmeas = 1.0 / (M * rmse ** 2)
        # The information ratio is a function of an RMSE over R ensembles, so
        # its own uncertainty is the uncertainty of that RMSE: 1/sqrt(2R) in
        # relative terms for the RMSE, hence twice that for p ~ 1/RMSE^2. Below
        # about R = 200 the "measured p / closed form = 1.0 within 20 per cent"
        # tolerance is looser than the error bar it is applied to, which makes
        # the check pass by construction.
        rel_se_p = 2.0 / math.sqrt(2.0 * R)
        rows.append({"eta": eta, "p_closed_form": pth, "p_measured": pmeas,
                     "rmse": rmse, "ratio": pmeas / pth,
                     "ratio_se": (pmeas / pth) * rel_se_p,
                     "ensembles": int(R),
                     "bias": float(dhat.mean() - DELTA0),
                     "bias_se": float(dhat.std(ddof=1) / math.sqrt(R))
                     if R > 1 else None,
                     # One row per ensemble, so the scatter behind the RMSE is
                     # in the file and not only its second moment.
                     "delta_hat": [float(x) for x in dhat]})
        print("  %-9.4f %-13.6f %-13.6f %-13.6f %-11.4f"
              % (eta, pth, pmeas, rmse, pmeas / pth))
    le = np.log([r["eta"] for r in rows])
    sl_th = float(np.polyfit(le, np.log([r["p_closed_form"] for r in rows]),
                             1)[0])
    sl_me = float(np.polyfit(le, np.log([r["p_measured"] for r in rows]), 1)[0])
    print("")
    print("  log-log slope over the SIMULATED range: closed form %+.4f, "
          "MEASURED %+.4f" % (sl_th, sl_me))
    #
    # WHY THE RAW SLOPE IS NOT THE TEST, DIAGNOSED FROM THE FIRST RUN.
    # The first run reported a closed-form slope of +1.7853 and called the
    # exponent test FAILED. But the closed form is EXACTLY
    #     p = 2 eta^2 / (1 + eta delta)^2,
    # so d log p / d log eta = 2 - 2 eta delta/(1 + eta delta), which is 1.54
    # at eta = 0.3 and 1.93 at eta = 0.0375. A secant slope of 1.79 across that
    # range is what the construction MUST give; the claim p ~ eta^2 is a
    # statement about the eta -> 0 limit, and the shortfall is the first-order
    # correction, not a different exponent. Fitting a secant slope over a range
    # where the correction is 23% and comparing it to the asymptotic exponent
    # tests the wrong thing.
    #
    # The claim is therefore split into the two statements it actually makes,
    # and both are tested:
    #   (a) THE EXPONENT. The LOCAL slope of the closed form must converge to
    #       exactly 2 as eta -> 0. Swept over four further decades, which costs
    #       nothing because it is arithmetic.
    #   (b) THE INFORMATION. The closed-form p must be the information actually
    #       attainable, i.e. measured p / closed-form p = 1 at every eta. This
    #       is the part that involves nature, and it is where a wrong 1/2, a
    #       wrong HS norm or a wrong power would show up.
    fine = np.array([10.0 ** (-x) for x in np.linspace(0.5, 4.5, 41)])
    pfine = np.array([seal_p(e, DELTA0, NP) for e in fine])
    loc = np.diff(np.log(pfine)) / np.diff(np.log(fine))
    print("  (a) EXPONENT: local slope of the closed form as eta -> 0:")
    print("      eta = 3.2e-01 -> %+.4f   eta = 1.0e-02 -> %+.4f   "
          "eta = 3.2e-05 -> %+.4f   (claim +2, alternative +1)"
          % (loc[0], loc[len(loc) // 2], loc[-1]))
    exponent_ok = abs(loc[-1] - 2.0) < 0.01
    print("      converges to 2: %s" % ("PASS" if exponent_ok else "FAIL"))
    rat = [r["ratio"] for r in rows]
    rat_z = [((r["ratio"] - 1.0) / r["ratio_se"]) if r["ratio_se"] else None
             for r in rows]
    info_ok = all(abs(x - 1.0) < 0.20 for x in rat)
    print("  (b) INFORMATION: measured p / closed-form p at each eta: %s"
          % ", ".join("%.4f" % x for x in rat))
    print("      standard errors: %s"
          % ", ".join("%.4f" % (r["ratio_se"] or float("nan")) for r in rows))
    print("      deviations from 1.0 in SE: %s"
          % ", ".join("n/a" if z is None else "%+.2f" % z for z in rat_z))
    print("      the closed-form p IS the attainable information: %s"
          % ("PASS" if info_ok else "FAIL"))
    ok = exponent_ok and info_ok
    out["C3"] = {"delta0": DELTA0, "n_prime": NP, "rows": rows,
                 "secant_slope_closed_form": sl_th,
                 "secant_slope_measured": sl_me,
                 "local_slope_at_smallest_eta": float(loc[-1]),
                 "exponent_pass": bool(exponent_ok),
                 "information_ratios": rat,
                 "information_ratio_z": rat_z,
                 "information_pass": bool(info_ok),
                 "pass": bool(ok)}
    return ok


# ===========================================================================
# C4. ADDITIVITY OF THE CLOSING LAW
# ===========================================================================
#
#   AggRisk / eps^2  =  d0/(2n) + sum_i 1/(2 m p_i) + r_perp^2
#
# instantiated exactly: d0 source coordinates estimated from n source draws of
# unit per-draw information; two deployment coordinates estimated THROUGH THE
# ACTUAL CHANNEL (the C3 construction at two different support floors, so the
# p_i are genuinely different and genuinely measured, not assumed); an
# unmodellable residual of size r_perp; quadratic loss with unit Hessian, so
# the curvature kappa is ZERO BY CONSTRUCTION and the (1 + O(kappa .))
# correction is exactly 1.  That correction is therefore NOT exercised here and
# is reported as untested rather than fitted around.
#
# n, m and r_perp vary on a FULL FACTORIAL grid; the fit includes an n*m cross
# term whose coefficient additivity says is zero.  P4 pushes a deliberately
# non-additive synthetic risk through the identical fitter to show the cross
# term is detectable when present.

def c4(rng, out):
    print("")
    print("=" * 78)
    print("C4  ADDITIVITY OF THE CLOSING LAW")
    print("=" * 78)
    D0 = 4
    NP = C4_NP
    ETAS = (0.30, 0.15)
    DELTA0 = 1.0
    ps = [seal_p(e, DELTA0, NP) for e in ETAS]
    print("  d0 = %d source coordinates, per-draw information 1" % D0)
    print("  deployment coordinates: eta = %s -> p = %s"
          % (list(ETAS), ["%.6f" % x for x in ps]))
    print("  loss is exactly quadratic with unit Hessian: kappa = 0 by "
          "construction, so (1 + O(kappa .)) is exactly 1 and IS NOT TESTED "
          "HERE.")
    n_grid = C4_N_GRID
    m_grid = C4_M_GRID
    rp_grid = (0.0, 0.05, 0.10)
    REP = C4_REP
    rows = []
    Lz = seal_sigma(0.0, 0.0, NP)
    print("")
    print("  %-7s %-7s %-7s %-14s %-14s %-9s"
          % ("n", "m", "r_perp", "AggRisk meas", "AggRisk pred", "ratio"))
    # The deployment error depends on m and eta, NOT on the source depth n, so
    # it is measured once per m rather than once per (n, m) cell. Speed only:
    # the same m values, the same REP replicates, the same depth.
    deploy_err = {}
    for m in m_grid:
        derr2 = 0.0
        for eta in ETAS:
            mm = sim_seal_means(eta, DELTA0, NP, m * REP, rng)
            U2 = (NP * mm ** 2).reshape(REP, m).mean(axis=1)
            dhat = (np.sqrt(np.maximum(U2 / Lz, 1e-12)) - 1.0) / eta
            derr2 += float(np.mean((dhat - DELTA0) ** 2))
        deploy_err[m] = derr2
    for n in n_grid:
        for m in m_grid:
            derr2 = deploy_err[m]
            # source block: n draws of unit information per coordinate
            src = rng.standard_normal((REP, D0)) / math.sqrt(float(n))
            serr2 = float(np.mean((src ** 2).sum(axis=1)))
            for rp in rp_grid:
                meas = 0.5 * (serr2 + derr2) + rp * rp
                pred = D0 / (2.0 * n) + sum(1.0 / (2.0 * m * p)
                                            for p in ps) + rp * rp
                rows.append({"n": n, "m": m, "r_perp": rp,
                             "agg_measured": meas, "agg_predicted": pred,
                             "ratio": meas / pred,
                             "source_term": 0.5 * serr2,
                             "deploy_term": 0.5 * derr2})
                print("  %-7d %-7d %-7.2f %-14.7f %-14.7f %-9.4f"
                      % (n, m, rp, meas, pred, meas / pred))

    # joint fit with a cross term additivity says must vanish
    A = np.array([[float(D0) / r["n"], 1.0 / r["m"], r["r_perp"] ** 2,
                   1.0 / (r["n"] * r["m"])] for r in rows])
    y = np.array([r["agg_measured"] for r in rows])
    coef, res, _, _ = np.linalg.lstsq(A, y, rcond=None)
    resid = y - A.dot(coef)
    dof = max(1, len(y) - 4)
    s2 = float(resid.dot(resid) / dof)
    cov = s2 * np.linalg.inv(A.T.dot(A))
    se = np.sqrt(np.diag(cov))
    inv_p = sum(1.0 / p for p in ps)
    print("")
    print("  JOINT FIT  AggRisk = a*(d0/n) + b*(1/m) + c*r_perp^2 + x/(n m)")
    print("    a = %.6f +- %.6f   (claim 0.5)" % (coef[0], se[0]))
    print("    b = %.6f +- %.6f   (claim sum_i 1/(2 p_i) = %.6f)"
          % (coef[1], se[1], 0.5 * inv_p))
    print("    c = %.6f +- %.6f   (claim 1.0)" % (coef[2], se[2]))
    print("    x = %.4g +- %.4g   (ADDITIVITY says 0; that is %.2f sigma)"
          % (coef[3], se[3], abs(coef[3]) / se[3] if se[3] > 0 else 0.0))

    # THE EXCLUSION BOUND, which is what "additivity holds" actually means.
    # The smallest cell has the largest 1/(n m), so a cross term of size
    # x/(n m) contributes most there; with |x| < 3 SE the fit excludes any
    # cross term contributing more than the printed fraction of that cell's
    # risk. Stating the bound is the difference between "we saw nothing" and
    # "nothing larger than this is there".
    smallest = min(r["n"] * r["m"] for r in rows)
    smallest_risk = min(r["agg_measured"] for r in rows
                        if r["n"] * r["m"] == smallest)
    excl = 3.0 * se[3] / smallest / smallest_risk
    print("  EXCLUSION: |x| < 3 SE = %.4g bounds any cross-term contribution "
          "at the smallest cell (n m = %d, risk %.5f) to %.3f%% of that risk"
          % (3 * se[3], smallest, smallest_risk, 100.0 * excl))

    # P4: the fitter must be able to SEE a cross term.
    #
    # THE FIRST RUN'S P4 WAS A BROKEN CONTROL AND IS REPAIRED HERE. It injected
    # 5/(n m), which at the smallest cell is 6e-5 against risks of order 0.05,
    # four orders of magnitude below this fit's own standard error of 18.8 on
    # that coefficient. It came back at 0.4 sigma, and correctly so: the
    # injection was far below the fitter's resolution, so the control
    # demonstrated nothing. A control whose alternative is undetectable by
    # construction is not a control -- it is the exact failure this project
    # keeps catching. The injection is now scaled to TEN standard errors of
    # this fit, so it must be recovered if the fitter works at all, and the
    # recovered value is checked against the INJECTED size and not merely
    # against zero.
    inject = 10.0 * se[3]
    nn = np.array([r["n"] for r in rows], dtype=float)
    mm_ = np.array([r["m"] for r in rows], dtype=float)
    ycross = y + inject / (nn * mm_)
    cc, _, _, _ = np.linalg.lstsq(A, ycross, rcond=None)
    rr = ycross - A.dot(cc)
    s2c = float(rr.dot(rr) / dof)
    sec = math.sqrt(float(s2c * np.linalg.inv(A.T.dot(A))[3, 3]))
    print("  P4 CONTROL: injecting a genuine %.4g/(n m) cross term -- ten "
          "standard errors of this fit -- the same fitter recovers x = %.4g "
          "+- %.4g; the SHIFT from the uninjected fit is %.4g against %.4g "
          "injected (ratio %.4f), at %.1f sigma from zero"
          % (inject, cc[3], sec, cc[3] - coef[3], inject,
             (cc[3] - coef[3]) / inject if inject else 0.0,
             abs(cc[3]) / sec if sec > 0 else 0))
    p4 = bool(sec > 0 and abs(cc[3]) / sec > 5.0
              and abs((cc[3] - coef[3]) / inject - 1.0) < 0.05)
    add_ok = (abs(coef[3]) / se[3] < 3.0) if se[3] > 0 else False
    coef_ok = (abs(coef[0] - 0.5) < 0.08 and abs(coef[2] - 1.0) < 0.15
               and abs(coef[1] / (0.5 * inv_p) - 1.0) < 0.15)
    print("  additivity (cross term consistent with zero): %s ; coefficients "
          "match the stated constants: %s ; P4 fired: %s"
          % (add_ok, coef_ok, p4))
    out["C4"] = {"d0": D0, "n_grid": list(n_grid), "m_grid": list(m_grid),
                 "r_perp_grid": list(rp_grid), "p_i": ps, "rows": rows,
                 "fit_a": float(coef[0]), "fit_a_se": float(se[0]),
                 "fit_b": float(coef[1]), "fit_b_se": float(se[1]),
                 "fit_b_claim": 0.5 * inv_p,
                 "fit_c": float(coef[2]), "fit_c_se": float(se[2]),
                 "fit_cross": float(coef[3]), "fit_cross_se": float(se[3]),
                 "P4_control_cross_recovered": float(cc[3]),
                 "P4_fired": bool(p4), "additive": bool(add_ok),
                 "coefficients_ok": bool(coef_ok),
                 "kappa_correction_tested": False}
    return add_ok and coef_ok and p4


# ===========================================================================
# C5. COUNT AND ORDER
# ===========================================================================
#
# Spectral family: F_t = w_t + h1 w_{t-1} + h2 w_{t-2} + h3 w_{t-3}, so d = 3.
#   gamma(1) = h1 + h1 h2 + h2 h3
#   gamma(2) = h2 + h1 h3
#   gamma(3) = h3
# COMPLETE SCHEME: the three lags {1,2,3}, Jacobian nonsingular.
# NEGATIVE ARM: the two lags {1,2}.  The theorem says d-1 lags must fail by
# leaving a GENUINELY UNIDENTIFIED DIRECTION.  That is tested by following the
# exact level set of (gamma(1), gamma(2)) to a SECOND parameter point h' != h
# with identical two-lag observables, then showing that gamma(3) and the
# deployment risk differ by order one there.  Fitting worse would not be a
# result; two indistinguishable points with different deployment behaviour is.
# DEGENERATE ARM: lags {4,5,6}, where gamma is identically zero for this family
# and the Jacobian is the zero matrix, so the nonsingularity condition bites.

def ma_gam(h, k):
    c = np.concatenate([[1.0], h])
    if k >= len(c):
        return 0.0
    return float(np.dot(c[:len(c) - k], c[k:]))


def ma_jac(h, lags, eps=1e-6):
    J = np.zeros((len(lags), len(h)))
    for j in range(len(h)):
        hp, hm = h.copy(), h.copy()
        hp[j] += eps
        hm[j] -= eps
        for i, k in enumerate(lags):
            J[i, j] = (ma_gam(hp, k) - ma_gam(hm, k)) / (2 * eps)
    return J


def follow_level_set(h0, lags, steps=4000, arclen=0.9):
    """Move along the null direction of the two-lag Jacobian, projecting back
    onto the exact level set at every step. Produces a SECOND point with the
    same observables, not merely a nearby one."""
    h = h0.copy()
    tgt = np.array([ma_gam(h0, k) for k in lags])
    ds = arclen / steps
    prev = None
    for _ in range(steps):
        J = ma_jac(h, lags)
        u, s, vt = np.linalg.svd(J)
        v = vt[-1]
        if prev is not None and np.dot(v, prev) < 0:
            v = -v
        prev = v
        h = h + ds * v
        for _it in range(6):
            r = np.array([ma_gam(h, k) for k in lags]) - tgt
            if np.max(np.abs(r)) < 1e-14:
                break
            J = ma_jac(h, lags)
            h = h - J.T.dot(np.linalg.solve(J.dot(J.T)
                                            + 1e-14 * np.eye(len(lags)), r))
    return h


def sim_ma_autocov(h, n, M, rng, lags, chunk=20000):
    """Per-cohort sample autocovariances at the given lags."""
    c = np.concatenate([[1.0], h])
    K = len(c)
    outv = np.empty((M, len(lags)))
    for lo in range(0, M, chunk):
        hi = min(lo + chunk, M)
        w = rng.standard_normal((hi - lo, n + K - 1))
        F = np.zeros((hi - lo, n))
        for j in range(K):
            F += c[j] * w[:, K - 1 - j: K - 1 - j + n]
        for i, k in enumerate(lags):
            outv[lo:hi, i] = (F[:, :n - k] * F[:, k:]).mean(axis=1)
    return outv


def c5(rng, out):
    print("")
    print("=" * 78)
    print("C5  COUNT AND ORDER:  count = dim W, order = max r*")
    print("=" * 78)
    h0 = np.array([0.60, -0.35, 0.25])
    d = len(h0)
    print("  family F_t = w_t + h1 w_{t-1} + h2 w_{t-2} + h3 w_{t-3}, d = %d"
          % d)
    print("  h0 = %s, gamma(1..3) = %s"
          % (h0.tolist(), ["%.6f" % ma_gam(h0, k) for k in (1, 2, 3)]))
    J3 = ma_jac(h0, [1, 2, 3])
    J2 = ma_jac(h0, [1, 2])
    Jdeg = ma_jac(h0, [4, 5, 6])
    s3 = np.linalg.svd(J3, compute_uv=False)
    print("  COMPLETE   lags {1,2,3}: singular values %s, |det| = %.6f -> "
          "nonsingular" % (np.round(s3, 5).tolist(),
                           abs(float(np.linalg.det(J3)))))
    print("  DEGENERATE lags {4,5,6}: Jacobian is %s (identically zero beyond "
          "the MA order) -> nonsingularity condition BITES"
          % ("all zero" if np.max(np.abs(Jdeg)) < 1e-12 else "nonzero"))
    print("  NEGATIVE   lags {1,2}:   %d x %d, rank %d -> a one-dimensional "
          "null direction" % (J2.shape[0], J2.shape[1],
                              int(np.linalg.matrix_rank(J2))))

    h1 = follow_level_set(h0, [1, 2])
    print("")
    print("  followed the exact (gamma(1),gamma(2)) level set to a SECOND "
          "point:")
    print("    h  = %s" % np.round(h0, 6).tolist())
    print("    h' = %s   (moved %.4f in parameter space)"
          % (np.round(h1, 6).tolist(),
             float(np.linalg.norm(h1 - h0))))
    print("    gamma(1): %.12f vs %.12f     gamma(2): %.12f vs %.12f"
          % (ma_gam(h0, 1), ma_gam(h1, 1), ma_gam(h0, 2), ma_gam(h1, 2)))
    print("    gamma(3): %.6f vs %.6f  -> differs by %.1f%%  (the "
          "unidentified direction is REAL, not a worse fit)"
          % (ma_gam(h0, 3), ma_gam(h1, 3),
             100.0 * abs(ma_gam(h1, 3) - ma_gam(h0, 3))
             / max(abs(ma_gam(h0, 3)), 1e-12)))
    Ldep0 = sum(np.concatenate([[1.0], h0])) ** 2
    Ldep1 = sum(np.concatenate([[1.0], h1])) ** 2
    print("    deployment quantity L = (sum c)^2: %.6f vs %.6f (%.1f%% apart)"
          % (Ldep0, Ldep1, 100.0 * abs(Ldep1 - Ldep0) / Ldep0))

    # measured: do the two-lag observables actually fail to separate?
    NP, M = C5_NP, C5_M
    a0 = sim_ma_autocov(h0, NP, M, rng, [1, 2, 3])
    a1 = sim_ma_autocov(h1, NP, M, rng, [1, 2, 3])
    print("")
    print("  measured, %d cohorts of depth %d, Welch t between the two points:"
          % (M, NP))
    ts = []
    for i, k in enumerate((1, 2, 3)):
        t = ((a0[:, i].mean() - a1[:, i].mean())
             / math.sqrt(a0[:, i].var(ddof=1) / M + a1[:, i].var(ddof=1) / M))
        ts.append(float(t))
        print("    lag %d:  %+.5f vs %+.5f   t = %+9.2f  %s"
              % (k, a0[:, i].mean(), a1[:, i].mean(), t,
                 "INDISTINGUISHABLE" if abs(t) < 4 else "SEPARATES"))
    neg_ok = abs(ts[0]) < 4.0 and abs(ts[1]) < 4.0 and abs(ts[2]) > 20.0
    print("  d-1 = 2 lags leave the pair indistinguishable; adding lag 3 "
          "separates at %.0f sigma -> %s" % (abs(ts[2]),
                                             "PASS" if neg_ok else "FAIL"))

    # positive arm: three lags identify, at rate m^{-1/2}
    print("")
    print("  COMPLETE ARM: recover h from three lags, %d cohorts per ensemble"
          % 2000)
    rowsp = []
    for m in C5_M_GRID:
        nens = M // m
        blk = a0[:nens * m].reshape(nens, m, 3).mean(axis=1)
        tgt = np.array([ma_gam(h0, k) for k in (1, 2, 3)])
        est = np.empty((nens, 3))
        for e in range(nens):
            hh = h0.copy()
            for _it in range(60):
                r = np.array([ma_gam(hh, k) for k in (1, 2, 3)]) - blk[e]
                Jc = ma_jac(hh, [1, 2, 3])
                hh = hh - np.linalg.solve(Jc, r)
                if np.max(np.abs(r)) < 1e-12:
                    break
            est[e] = hh
        rmse = float(np.sqrt(np.mean(np.sum((est - h0) ** 2, axis=1))))
        rowsp.append({"m": m, "ensembles": nens, "rmse_h": rmse})
        print("    m = %-6d ensembles %-4d  RMSE(h) = %.6f" % (m, nens, rmse))
    # THE SLOPE NEEDS ITS OWN ERROR BAR, which the first run did not print.
    # An RMSE built from E ensembles has relative standard error 1/sqrt(2E), so
    # log RMSE carries 1/sqrt(2E) and the fitted slope inherits it. The first
    # run had only 7 ensembles at the top m, giving a slope standard error near
    # 0.10, and then declared FAIL on a fitted -0.5829 that was well inside one
    # sigma of -0.5. The pool is now four times larger, so the top cell has 30
    # ensembles rather than 7, and the slope is reported WITH its standard
    # error and judged against it rather than against a fixed tolerance.
    lm = np.log([r["m"] for r in rowsp])
    ly = np.log([r["rmse_h"] for r in rowsp])
    wsd = np.array([1.0 / math.sqrt(2.0 * r["ensembles"]) for r in rowsp])
    sl = float(np.polyfit(lm, ly, 1)[0])
    sxx = float(np.sum((lm - lm.mean()) ** 2))
    sl_se = float(math.sqrt(np.sum(((lm - lm.mean()) * wsd) ** 2)) / sxx)
    print("    rate d log RMSE / d log m = %+.4f +- %.4f (claim -0.5, that is "
          "%.2f sigma)" % (sl, sl_se, abs(sl + 0.5) / sl_se))
    pos_ok = abs(sl + 0.5) < 3.0 * sl_se

    out["C5"] = {"h0": h0.tolist(), "h_level_set": h1.tolist(),
                 "singular_values_3lag": s3.tolist(),
                 "det_J3": abs(float(np.linalg.det(J3))),
                 "rank_J2": int(np.linalg.matrix_rank(J2)),
                 "J_degenerate_max_abs": float(np.max(np.abs(Jdeg))),
                 "gamma3_h0": ma_gam(h0, 3), "gamma3_h1": ma_gam(h1, 3),
                 "L_h0": Ldep0, "L_h1": Ldep1,
                 "welch_t_by_lag": ts, "negative_arm_pass": bool(neg_ok),
                 "complete_arm": rowsp, "rate_slope": sl, "rate_slope_se": sl_se,
                 "complete_arm_pass": bool(pos_ok)}
    return neg_ok and pos_ok


# ===========================================================================

def c6(out):
    """Independent numerical evaluation of the two-channel Schur-complement law."""
    print("")
    print("=" * 78)
    print("C6  VALUE OF AN ADDED CORRELATED PROBE")
    print("=" * 78)

    first_noise = 2.4
    second_noise = 1.7
    shared_noise = 0.8
    response = np.array([0.6, -0.35])
    noise = np.array([[first_noise, shared_noise],
                      [shared_noise, second_noise]])
    precision = np.linalg.inv(noise)
    total = float(response @ precision @ response)
    base = float(response[0] ** 2 / first_noise)
    conditional_response = float(
        response[1] - shared_noise / first_noise * response[0]
    )
    conditional_noise = float(
        second_noise - shared_noise ** 2 / first_noise
    )
    innovation = float(conditional_response ** 2 / conditional_noise)
    decomposed = base + innovation

    redundant_response = np.array([
        response[0], shared_noise / first_noise * response[0]
    ])
    redundant_total = float(redundant_response @ precision @ redundant_response)
    redundant_base = float(redundant_response[0] ** 2 / first_noise)

    determinant = float(np.linalg.det(noise))
    identity_error = abs(total - decomposed)
    redundancy_error = abs(redundant_total - redundant_base)
    base_cost = 1.0
    worthwhile_added_cost = 0.4
    excessive_added_cost = 2.0
    base_efficiency = base / base_cost
    worthwhile_efficiency = total / (base_cost + worthwhile_added_cost)
    excessive_efficiency = total / (base_cost + excessive_added_cost)
    worthwhile_gain_efficiency = innovation / worthwhile_added_cost
    excessive_gain_efficiency = innovation / excessive_added_cost
    budget = 1000.0
    worthwhile_budget_gain = (
        budget * worthwhile_efficiency - budget * base_efficiency
    )
    passed = bool(
        determinant > 0.0
        and conditional_noise > 0.0
        and innovation > 0.0
        and total > base
        and identity_error < 1e-12
        and redundancy_error < 1e-12
        and worthwhile_efficiency > base_efficiency
        and worthwhile_gain_efficiency > base_efficiency
        and excessive_efficiency < base_efficiency
        and excessive_gain_efficiency < base_efficiency
        and worthwhile_budget_gain > 0.0
    )

    print("  det(noise)                 = %.12f" % determinant)
    print("  total / base / innovation  = %.12f / %.12f / %.12f" %
          (total, base, innovation))
    print("  decomposition abs error    = %.3e" % identity_error)
    print("  redundant-probe abs gain   = %.3e" % redundancy_error)
    print("  base / augmented info/$    = %.12f / %.12f" %
          (base_efficiency, worthwhile_efficiency))
    print("  innovation info/added $    = %.12f" % worthwhile_gain_efficiency)
    print("  excessive-cost augmented $ = %.12f (must be below base)" %
          excessive_efficiency)
    print("  fixed-budget information gain = %.12f" % worthwhile_budget_gain)
    print("  PASS                        = %s" % passed)

    out["C6"] = {
        "noise": noise.tolist(),
        "response": response.tolist(),
        "determinant": determinant,
        "total_information": total,
        "first_information": base,
        "conditional_response": conditional_response,
        "conditional_noise": conditional_noise,
        "innovation_information": innovation,
        "decomposition_abs_error": identity_error,
        "redundant_probe_abs_gain": redundancy_error,
        "base_cost": base_cost,
        "worthwhile_added_cost": worthwhile_added_cost,
        "excessive_added_cost": excessive_added_cost,
        "base_information_per_cost": base_efficiency,
        "worthwhile_augmented_information_per_cost": worthwhile_efficiency,
        "worthwhile_innovation_information_per_added_cost": worthwhile_gain_efficiency,
        "excessive_augmented_information_per_cost": excessive_efficiency,
        "excessive_innovation_information_per_added_cost": excessive_gain_efficiency,
        "fixed_budget": budget,
        "worthwhile_fixed_budget_information_gain": worthwhile_budget_gain,
        "pass": passed,
    }
    return passed


# ===========================================================================

def main(argv=None):
    parser = argparse.ArgumentParser(
        description=__doc__,
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="tunable knobs for --set NAME=VALUE:\n" +
               "\n".join("  %-16s %s" % (k, v) for k, v in TUNABLES.items()))
    parser.add_argument("--profile", choices=("quick", "full", "deep"),
                        default="quick",
                        help="bounded development signal, the registered full "
                             "experiment, or the same experiment with the "
                             "sampling widened (deep)")
    parser.add_argument("--set", dest="settings", action="append", default=[],
                        metavar="NAME=VALUE",
                        help="override one knob after the profile; repeatable")
    parser.add_argument("--seed", type=int, default=SEED,
                        help="master seed (default %d)" % SEED)
    parser.add_argument("--output", default="fam_permeability_results.json")
    parser.add_argument("--innovation-only", action="store_true",
                        help="run only the fast deterministic correlated-probe check")
    args = parser.parse_args(argv)
    if args.innovation_only:
        return 0 if c6({}) else 1
    configure_profile(args.profile)
    overrides = apply_overrides(args.settings)
    t0 = time.time()
    rng = np.random.default_rng(args.seed)
    config = resolved_config()
    print("profile %s, seed %d" % (args.profile, args.seed))
    if overrides:
        print("overrides: %s" % ", ".join("%s=%s" % kv
                                          for kv in overrides.items()))
    # The provenance header is written from the same module the popgen sweeps
    # use, and carries the same field names as `Shared.Results.write` on the
    # Lean side, so a reader can tell a current result from a stale one without
    # trusting whoever quoted it.
    out = {"_provenance": simprov.stamp(
        "differential/cluster/fam_permeability.py", config, args.seed,
        {"C1_ensembles_at_max_m": C1_R_ENS, "C3_ensembles_per_eta": C3_R,
         "C4_reps_per_cell": C4_REP}),
        "profile": args.profile, "seed": args.seed,
        "overrides": overrides, "config": config}
    r1 = c1(rng, out)
    r2 = c2(rng, out)
    r3 = c3(rng, out)
    r4 = c4(rng, out)
    r5 = c5(rng, out)
    r6 = c6(out)

    print("")
    print("=" * 78)
    print("NOT ATTEMPTED")
    print("=" * 78)
    print("  The deconvolution face's (log m)^{-beta} rate with pi/2 in the")
    print("  exponent is NUMERICALLY OUT OF REACH: m = 1e3 -> 1e6 moves log m")
    print("  by 2x, which cannot separate (log m)^{-beta} from a constant at")
    print("  any achievable m, let alone recover pi/2. Recorded as")
    print("  analytically stated and untested. No exponent is fitted here")
    print("  because a fitted exponent would not be believable.")
    out["deconvolution_rate"] = "NOT TESTED -- numerically out of reach"

    print("")
    print("=" * 78)
    print("SUMMARY")
    print("=" * 78)
    checks = (("C1 permeability constant", r1), ("C2 the wall", r2),
              ("C3 sealing law exponent", r3), ("C4 additivity", r4),
              ("C5 count and order", r5), ("C6 correlated-probe value", r6))
    for tag, v in checks:
        print("  %-30s %s" % (tag, v))
    ok = bool(r1 and r2 and r3 and r4 and r5 and r6)
    failed = [tag for tag, v in checks if not v]
    out["READ_THE_TEST"] = ok
    out["failed_checks"] = failed
    out["runtime_sec"] = time.time() - t0
    print("  READ_THE_TEST: %s" % ok)
    print("  runtime %.1f s" % (time.time() - t0))
    fh = open(args.output, "w")
    json.dump(out, fh, indent=1)
    fh.close()
    print("-> %s" % args.output)
    if not ok:
        # A harness that runs twenty scripts and collects stderr saw this one
        # exit 1 with stderr completely empty, and read that as a crash. It was
        # not a crash: exit 1 here means a CHECK FAILED, and the whole report
        # went to stdout. So say on stderr which checks failed and that the
        # results file was still written -- a nonzero exit whose only
        # explanation is on a stream the caller is not reading is a result
        # nobody will find.
        sys.stderr.write(
            "fam_permeability: %d of %d checks FAILED under profile '%s': %s\n"
            % (len(failed), len(checks), args.profile, ", ".join(failed)))
        sys.stderr.write(
            "fam_permeability: this is a measurement, not a crash. The full "
            "report is on stdout and the results file was written to %s\n"
            % args.output)
        if args.profile == "quick":
            sys.stderr.write(
                "fam_permeability: profile 'quick' is the bounded development "
                "run and its ensemble counts are too small for the C1 and C3 "
                "tolerances to be meaningful. Use --profile full before "
                "reading a failure here as a finding.\n")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
