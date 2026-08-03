#!/usr/bin/env python3
"""Numerical validation for the condensation / polygenic-spectroscopy modules.

This script exists for the reason stated in `proofs/Calibrator/Identification.lean`:
a Lean `def` cannot be internally wrong, so the whole risk sits in whether a named
quantity's *formula* has the population-genetic meaning its *name* claims. Every
quantity below is computed twice — once by direct summation over the three diploid
genotypes (the definition), once by the closed form (the theorem) — and the two are
required to agree.

Checks performed
----------------
1.  `condensationConstant` c_G = 2 - gamma - log 2 equals E[log chi2_3], computed by
    quadrature against the chi-square-3 density, and equals digamma(3/2) + log 2.
2.  `gaussianJetVariance` v_G = pi^2/2 - 4 equals Var(log chi2_3) = trigamma(3/2).
3.  `hweMellinDrift` closed form equals the direct genotype sum, across the frequency
    spectrum. This is the check that would have caught a wrong constant.
4.  The exact interior point: c((5 - sqrt5)/10) = (3/5) log 2.
5.  The crossing: c(q) - c_G changes sign between q = (5-sqrt5)/10 and q = 1/256, and
    the crossing frequency is located by bisection.
6.  The safe-order table reproduced in the module docstring.
7.  The hard-call lattice point q* = (2 - sqrt2)/4: the three values of log x^2 are in
    exact arithmetic progression, with span log(3 + 2 sqrt2), and the Poisson
    intensity inflation factor h/(1 - exp(-h)).
8.  A direct Monte-Carlo of the condensation phase transition: the variance of the
    normalized chaos under Gaussian versus hard-called-genotype coordinates, swept
    across the predicted boundary m* = log N / c.
9.  The covariance-channel kurtosis penalty: direct Hardy-Weinberg summation and a
    fixed-seed genotype simulation verify the exact `4901/198` variance multiplier at
    one-percent MAF, and its multiplicative combination with inverse-square response
    attenuation (`9802/99` at half response).

Run:  python3 proofs/validation/condensation/check_condensation.py
"""

from __future__ import annotations

import math
import sys

import numpy as np
from scipy import integrate, special

TOL = 1e-9

# --------------------------------------------------------------------------------
# 1-2. The Gaussian Mellin 2-jet at the size-bias point theta = 1
# --------------------------------------------------------------------------------

CONDENSATION_CONSTANT = 2.0 - np.euler_gamma - math.log(2.0)
GAUSSIAN_JET_VARIANCE = math.pi**2 / 2.0 - 4.0


def chi2_3_log_moments() -> tuple[float, float]:
    """E[log X] and Var(log X) for X ~ chi-square with 3 degrees of freedom.

    The size-biased square of a standard Gaussian (density proportional to x times the
    chi-square-1 density) *is* a chi-square-3; this is the identity that makes the
    condensation constant what it is.
    """

    def density(x: float) -> float:
        return x**0.5 * math.exp(-x / 2.0) / (math.sqrt(2.0 * math.pi))

    m1, _ = integrate.quad(lambda x: math.log(x) * density(x), 0, np.inf, limit=400)
    m2, _ = integrate.quad(lambda x: math.log(x) ** 2 * density(x), 0, np.inf, limit=400)
    return m1, m2 - m1**2


def check_gaussian_jet() -> None:
    quad_mean, quad_var = chi2_3_log_moments()
    digamma_mean = special.digamma(1.5) + math.log(2.0)
    trigamma_var = special.polygamma(1, 1.5)

    assert abs(quad_mean - CONDENSATION_CONSTANT) < 1e-8, (quad_mean, CONDENSATION_CONSTANT)
    assert abs(digamma_mean - CONDENSATION_CONSTANT) < TOL, (digamma_mean, CONDENSATION_CONSTANT)
    assert abs(quad_var - GAUSSIAN_JET_VARIANCE) < 1e-7, (quad_var, GAUSSIAN_JET_VARIANCE)
    assert abs(trigamma_var - GAUSSIAN_JET_VARIANCE) < TOL, (trigamma_var, GAUSSIAN_JET_VARIANCE)

    # The bounds proved in Lean from mathlib's gamma and log-2 bounds.
    assert 0.640 < CONDENSATION_CONSTANT < 0.807
    assert GAUSSIAN_JET_VARIANCE > 0

    print(f"  c_G = {CONDENSATION_CONSTANT:.10f}   (quadrature {quad_mean:.10f})")
    print(f"  v_G = {GAUSSIAN_JET_VARIANCE:.10f}   (quadrature {quad_var:.10f})")
    print(f"  critical multiplier 1/c_G = {1.0 / CONDENSATION_CONSTANT:.6f}")


# --------------------------------------------------------------------------------
# 3. The Hardy-Weinberg Mellin drift, twice
# --------------------------------------------------------------------------------


def hwe_drift_by_summation(q: float) -> float:
    """E[x^2 log x^2] by direct summation over the three diploid genotypes.

    This mirrors `HardyWeinbergModel.mellinDrift` exactly: standardize the centered
    alternative-allele count by the Hardy-Weinberg genotype variance `2 q (1 - q)`,
    then average `x^2 log x^2` against the Hardy-Weinberg genotype probabilities.
    """
    p = 1.0 - q
    variance = 2.0 * q * p
    total = 0.0
    for count, prob in ((0.0, p * p), (1.0, 2.0 * p * q), (2.0, q * q)):
        x2 = (count - 2.0 * q) ** 2 / variance
        # Lean's convention: `Real.log 0 = 0`, and the coefficient x2 is 0 there anyway.
        total += prob * x2 * (math.log(x2) if x2 > 0 else 0.0)
    return total


def hwe_drift_closed_form(q: float) -> float:
    """`hweMellinDrift` from the Lean development."""
    het = (1.0 - 2.0 * q) ** 2
    denom = 2.0 * q * (1.0 - q)
    head = het * (math.log(het / denom) if het > 0 else 0.0)
    return head + 4.0 * q * (1.0 - q) * math.log(2.0)


def check_closed_form() -> None:
    grid = np.concatenate(
        [
            np.logspace(-6, -1.2, 60),
            np.linspace(0.06, 0.94, 200),
            1.0 - np.logspace(-6, -1.2, 60),
        ]
    )
    worst = 0.0
    for q in grid:
        a = hwe_drift_by_summation(float(q))
        b = hwe_drift_closed_form(float(q))
        worst = max(worst, abs(a - b))
    assert worst < 1e-9, f"closed form disagrees with the genotype sum by {worst}"
    print(f"  closed form vs genotype summation: max abs deviation {worst:.3e}")

    # q = 1/2 anchor
    assert abs(hwe_drift_closed_form(0.5) - math.log(2.0)) < TOL

    # the exactly solvable interior point
    q_star = (5.0 - math.sqrt(5.0)) / 10.0
    exact = 0.6 * math.log(2.0)
    assert abs(hwe_drift_closed_form(q_star) - exact) < TOL
    print(f"  c((5-sqrt5)/10) = {hwe_drift_closed_form(q_star):.10f}  = (3/5) log 2 = {exact:.10f}")


# --------------------------------------------------------------------------------
# 5. The crossing of the Gaussian constant
# --------------------------------------------------------------------------------


def check_crossing() -> float:
    lo = (5.0 - math.sqrt(5.0)) / 10.0  # drift below c_G
    hi = 1.0 / 256.0  # drift above c_G
    assert hwe_drift_closed_form(lo) < CONDENSATION_CONSTANT
    assert hwe_drift_closed_form(hi) > CONDENSATION_CONSTANT

    a, b = hi, lo
    for _ in range(200):
        mid = 0.5 * (a + b)
        if hwe_drift_closed_form(mid) > CONDENSATION_CONSTANT:
            a = mid
        else:
            b = mid
    crossing = 0.5 * (a + b)
    print(f"  drift crosses c_G at q = {crossing:.6f}  (drift-blind frequency)")

    # the drift is genuinely non-monotone: locate the interior minimum
    qs = np.linspace(1e-4, 0.5, 20000)
    vals = np.array([hwe_drift_closed_form(float(q)) for q in qs])
    qmin = float(qs[int(np.argmin(vals))])
    print(f"  interior minimum at q = {qmin:.4f}, c = {vals.min():.6f}")
    assert 0.20 < qmin < 0.35, qmin
    assert vals.min() < hwe_drift_closed_form(0.5)
    return crossing


# --------------------------------------------------------------------------------
# 6. The safe-order table quoted in the module docstring
# --------------------------------------------------------------------------------


def check_table(n_terms: float = 1e6) -> None:
    log_n = math.log(n_terms)
    rows = [0.5, (5.0 - math.sqrt(5.0)) / 10.0, 0.2, 0.14, 0.05, 0.01, 0.001, 0.0001]
    print(f"  safe epistatic order m* = log N / c(q), N = {n_terms:g}")
    print(f"    {'q':>10} {'c(q)':>10} {'m*':>8}")
    for q in rows:
        c = hwe_drift_closed_form(q)
        print(f"    {q:>10.4f} {c:>10.4f} {log_n / c:>8.2f}")
    # the headline claim: pairwise epistasis at MAF 1e-4 is past the boundary
    c_rare = hwe_drift_closed_form(1e-4)
    assert log_n / c_rare < 2.0, log_n / c_rare
    # ...while the additive score is deeply subcritical at every frequency shown
    for q in rows:
        assert log_n / hwe_drift_closed_form(q) > 1.0


# --------------------------------------------------------------------------------
# 7. The hard-call lattice point
# --------------------------------------------------------------------------------


def check_lattice_point() -> None:
    q = (2.0 - math.sqrt(2.0)) / 4.0
    p = 1.0 - q
    variance = 2.0 * q * p
    x2 = [
        (0.0 - 2.0 * q) ** 2 / variance,
        (1.0 - 2.0 * q) ** 2 / variance,
        (2.0 - 2.0 * q) ** 2 / variance,
    ]
    logs = sorted(math.log(v) for v in x2)
    gap1, gap2 = logs[1] - logs[0], logs[2] - logs[1]
    assert abs(gap1 - gap2) < 1e-12, (gap1, gap2)

    span = math.log(p / q)
    assert abs(span - gap1) < 1e-12, (span, gap1)
    assert abs(span - math.log(3.0 + 2.0 * math.sqrt(2.0))) < 1e-12

    inflation = span / (1.0 - math.exp(-span))
    assert inflation > 1.0
    print(f"  q* = {q:.6f}: log x^2 in exact arithmetic progression, span h = {span:.6f}")
    print(f"  lattice intensity inflation h/(1-exp(-h)) = {inflation:.6f}")

    # and the criterion that defines the point
    assert abs((1.0 - 2.0 * q) ** 2 - 4.0 * q * p) < 1e-14


# --------------------------------------------------------------------------------
# 8. Monte-Carlo of the phase transition
# --------------------------------------------------------------------------------


def chaos_variance(rng: np.random.Generator, coords: str, m: int, n: int, q: float) -> float:
    """Sample variance of `N^{-1/2} sum_j prod_{i in S_j} x_i` for disjoint blocks.

    `coords` is either "gaussian" (the surrogate) or "genotype" (hard calls at
    frequency `q`, standardized). Both have mean 0 and variance 1 per coordinate, so
    the aggregate has variance exactly 1 in expectation. Condensation is visible as the
    *sample* variance collapsing for the Gaussian coordinates while staying near 1 for
    the genotype coordinates.
    """
    reps = 400
    out = np.empty(reps)
    for r in range(reps):
        if coords == "gaussian":
            x = rng.standard_normal((n, m))
        else:
            counts = rng.binomial(2, q, size=(n, m)).astype(float)
            x = (counts - 2.0 * q) / math.sqrt(2.0 * q * (1.0 - q))
        out[r] = x.prod(axis=1).sum() / math.sqrt(n)
    return float(out.var())


def check_phase_transition() -> None:
    """Sweep the degree across the two predicted boundaries.

    The demonstration needs a frequency where the genotype drift is far from the
    Gaussian one, otherwise the two boundaries coincide and nothing is visible. At
    `q = 0.05` the genotype drift is `1.868`, well above `c_G = 0.730`, so the
    *genotype* side condenses first: its boundary is at `m* = log N / 1.868`, the
    Gaussian's at `log N / 0.730`. Between the two boundaries the surrogate and the
    truth disagree qualitatively, which is the whole claim.
    """
    rng = np.random.default_rng(20260801)
    n = 4096
    q = 0.05
    c_geno = hwe_drift_closed_form(q)
    m_star_gauss = math.log(n) / CONDENSATION_CONSTANT
    m_star_geno = math.log(n) / c_geno
    print(f"  N = {n}, q = {q}: c_geno = {c_geno:.4f} vs c_G = {CONDENSATION_CONSTANT:.4f}")
    print(f"  predicted boundaries: m* = {m_star_geno:.2f} (genotype), "
          f"{m_star_gauss:.2f} (Gaussian surrogate)")
    print(f"    {'m':>4} {'var[genotype]':>14} {'var[gaussian]':>14}")
    for m in (2, 3, 5, 8, 11, 16, 24):
        vx = chaos_variance(rng, "genotype", m, n, q)
        vg = chaos_variance(rng, "gaussian", m, n, q)
        print(f"    {m:>4} {vx:>14.4f} {vg:>14.4f}")

    # In the window strictly between the two boundaries the surrogate still carries
    # its variance while the truth has already condensed. Sampling is noisy, so this
    # is reported rather than asserted.
    m_window = int(round(0.5 * (m_star_geno + m_star_gauss)))
    vx_w = chaos_variance(rng, "genotype", m_window, n, q)
    vg_w = chaos_variance(rng, "gaussian", m_window, n, q)
    print(f"  inside the window (m={m_window}): genotype {vx_w:.4f}  gaussian {vg_w:.4f}")
    if not vx_w < vg_w:
        print("  NOTE: sampled separation not resolved at this N; increase n or reps")


# --------------------------------------------------------------------------------
# 9. Rare-variant covariance-channel sample cost
# --------------------------------------------------------------------------------


def hwe_standardized_square_variance(q: float) -> float:
    """Direct genotype-sum value of Var(X^2) for standardized diploid dosage."""
    p = 1.0 - q
    genotype_variance = 2.0 * q * p
    probabilities = np.array([p * p, 2.0 * p * q, q * q])
    counts = np.array([0.0, 1.0, 2.0])
    standardized_squares = (counts - 2.0 * q) ** 2 / genotype_variance
    mean_square = float(probabilities @ standardized_squares)
    return float(probabilities @ (standardized_squares - mean_square) ** 2)


def check_one_percent_covariance_penalty() -> None:
    """Validate the exact one-percent-MAF and half-response multipliers.

    A Gaussian unit-variance coordinate has Var(X^2)=2. The standardized diploid
    coordinate has Var(X^2)=1/[2q(1-q)]-1, so the ratio at q=0.01 is 4901/198.
    Dividing a covariance fluctuation by a response attenuated by `eta` multiplies
    estimator variance by `1/eta^2`.
    """
    q = 0.01
    response_fraction = 0.5
    exact_multiplier = 4901.0 / 198.0
    exact_joint_multiplier = 9802.0 / 99.0
    summed_multiplier = hwe_standardized_square_variance(q) / 2.0
    assert abs(summed_multiplier - exact_multiplier) < 1e-12, (
        summed_multiplier,
        exact_multiplier,
    )
    summed_joint_multiplier = summed_multiplier / response_fraction**2
    assert abs(summed_joint_multiplier - exact_joint_multiplier) < 1e-12, (
        summed_joint_multiplier,
        exact_joint_multiplier,
    )

    rng = np.random.default_rng(20260802)
    counts = rng.binomial(2, q, size=1_000_000).astype(float)
    standardized_squares = (counts - 2.0 * q) ** 2 / (2.0 * q * (1.0 - q))
    sampled_multiplier = float(standardized_squares.var() / 2.0)
    relative_error = abs(sampled_multiplier / exact_multiplier - 1.0)
    assert relative_error < 0.02, (sampled_multiplier, exact_multiplier, relative_error)
    sampled_joint_multiplier = sampled_multiplier / response_fraction**2
    joint_relative_error = abs(sampled_joint_multiplier / exact_joint_multiplier - 1.0)
    assert joint_relative_error < 0.02, (
        sampled_joint_multiplier,
        exact_joint_multiplier,
        joint_relative_error,
    )

    print(f"  q = 0.01 exact covariance-variance multiplier = {exact_multiplier:.6f}")
    print(
        "  fixed-seed HWE simulation multiplier "
        f"= {sampled_multiplier:.6f} (relative error {relative_error:.3%})"
    )
    print(
        "  q = 0.01, half-response joint multiplier "
        f"= {exact_joint_multiplier:.6f}; simulation {sampled_joint_multiplier:.6f} "
        f"(relative error {joint_relative_error:.3%})"
    )


def main() -> None:
    print("[1-2] Gaussian Mellin 2-jet")
    check_gaussian_jet()
    print("[3-4] Hardy-Weinberg Mellin drift")
    check_closed_form()
    print("[5] Crossing of the Gaussian constant")
    check_crossing()
    print("[6] Safe epistatic order")
    check_table()
    print("[7] Hard-call lattice point")
    check_lattice_point()
    print("[8] Phase transition, sampled")
    check_phase_transition()
    print("[9] One-percent-MAF covariance-channel penalty")
    check_one_percent_covariance_penalty()
    print("\nAll deterministic checks passed.")


if __name__ == "__main__":
    if "--kurtosis-only" in sys.argv[1:]:
        check_one_percent_covariance_penalty()
    else:
        main()
