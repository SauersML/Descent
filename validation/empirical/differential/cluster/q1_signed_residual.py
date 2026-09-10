#!/usr/bin/env python3
"""Exact illustrative Q1 calculations accompanying IndividualLossMoments.lean.

These calculations do not estimate the paper's residual moments. In particular,
bin-level partial R2 is not substituted for conditional individual error variance.
The Gaussian-style formula requires its second/fourth-moment relationship.

The sharp CV bound on [a,b], for 0 < a <= b, is (b-a)/(2*sqrt(a*b)).
It is attained by probabilities b/(a+b) at a and a/(a+b) at b, not equal
endpoint probabilities. Signed-residual R2 alone does not identify the variance
of squared conditional bias: conditional fourth moments are also required.

For general residuals, measure conditional moments from the SAME residualization
and prediction procedure used to calculate individual squared loss. The exact
between-cell numerator is Var(v + m^2), including 2*Cov(v,m^2); its denominator
is E[E[r^4|D] - E[r^2|D]^2] + Var(E[r^2|D]). A fitted spline additionally has
approximation and estimation error. Neither a signed-residual regression nor
outcome-variance heterogeneity alone identifies the empirical explanation.
"""

from fractions import Fraction as F
import json
import math


def cv_squared_bound(a, b):
    """Sharp squared CV; exact when the endpoints are Fractions."""
    if not 0 < a <= b:
        raise ValueError("Require 0 < a <= b")
    return (b - a) ** 2 / (4 * a * b)


def gaussian_style_fraction(cv_squared):
    """Requires E[r^2|D]=v and E[r^4|D]=3v^2; CV refers to v."""
    if cv_squared < 0:
        raise ValueError("Squared CV must be nonnegative")
    return cv_squared / (2 + 3 * cv_squared)


def pure_bias_fraction(second_moment, fourth_moment):
    """Centered conditional bias plus independent unit Gaussian noise.

    Both moments are inputs. No fourth-moment shape is inferred from signed R2.
    """
    if second_moment < 0 or fourth_moment < second_moment ** 2:
        raise ValueError("Bias moments violate moment positivity")
    between = fourth_moment - second_moment ** 2
    return between / (2 + 4 * second_moment + between)


def moments(values, masses):
    if len(values) != len(masses) or sum(masses) != 1 or any(p < 0 for p in masses):
        raise ValueError("Supply a normalized probability law")
    return tuple(sum(p * x ** k for x, p in zip(values, masses)) for k in (1, 2, 4))


def main():
    # Exact attainment and a direct refutation of the old equal-mass CV bound.
    a, b = F(1), F(4)
    mean, second, _ = moments((a, b), (b / (a + b), a / (a + b)))
    cv2 = (second - mean ** 2) / mean ** 2
    assert cv2 == cv_squared_bound(a, b) == F(9, 16)
    assert cv2 > ((b - a) / (a + b)) ** 2

    # Equal signed-bias variance, unequal squared-bias variance.
    first = moments((F(-1), F(1)), (F(1, 2), F(1, 2)))
    sparse = moments((F(-2), F(0), F(2)), (F(1, 8), F(3, 4), F(1, 8)))
    assert first[:2] == sparse[:2] == (0, 1)
    assert pure_bias_fraction(first[1], first[2]) == 0
    assert pure_bias_fraction(sparse[1], sparse[2]) == F(1, 3)

    example = gaussian_style_fraction(F(1, 100))
    assert example == F(1, 203)
    reported_fraction = F(51, 10000)
    required_cv2 = 2 * reported_fraction / (1 - 3 * reported_fraction)
    assert gaussian_style_fraction(required_cv2) == reported_fraction
    print(json.dumps({
        "status": "exact model calculations; not empirical attribution",
        "interval_1_4_max_cv": math.sqrt(cv2),
        "equal_signed_r2": "1/2 under independent unit Gaussian noise",
        "squared_loss_r2": ["0", "1/3"],
        "gaussian_style_r2_at_cv_0_1": float(example),
        "cv_required_for_0_0051_under_stated_moments": math.sqrt(required_cv2),
        "checks": "passed",
    }, indent=2))


if __name__ == "__main__":
    main()
