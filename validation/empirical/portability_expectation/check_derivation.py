"""Deterministic checks of DERIVATION.md; no simulated or fitted accuracy curves."""

from fractions import Fraction as F
import json
from math import atan, pi, sqrt
from pathlib import Path

import numpy as np


ROOT = Path(__file__).resolve().parent


def dot(x, y):
    return sum((a * b for a, b in zip(x, y, strict=True)), F(0))


def center(x):
    mean = sum(x, F(0)) / len(x)
    return [F(a) - mean for a in x]


def centered_columns(rows):
    return list(map(list, zip(*(center(col) for col in zip(*rows)), strict=True)))


def matvec(matrix, vector):
    return [dot(row, vector) for row in matrix]


def geometry(causal, score):
    c = centered_columns(causal)
    s = center(score)
    columns = list(zip(*c))
    return (
        [[dot(x, y) for y in columns] for x in columns],
        [dot(x, s) for x in columns],
        dot(s, s),
    )


def quadratic(matrix, beta):
    return dot(beta, matvec(matrix, beta))


def direct_r2(score, liability):
    s, g = center(score), center(liability)
    return dot(s, g) ** 2 / (dot(s, s) * dot(g, g))


def formula_r2(branch, beta):
    b, a, v = branch
    return dot(a, beta) ** 2 / (v * quadratic(b, beta))


def formula_ratio(source, target, beta):
    bs, a_s, vs = source
    bt, a_t, vt = target
    return (vs / vt * dot(a_t, beta) ** 2 * quadratic(bs, beta)
            / (dot(a_s, beta) ** 2 * quadratic(bt, beta)))


def exact_sample_checks():
    # Different source and target cohort sizes, covariance structures and scores.
    source = [[0, 0, 0], [0, 2, 2], [2, 0, 2], [2, 2, 0], [1, 1, 1]]
    target = [[0, 0, 1], [1, 0, 2], [2, 1, 0], [2, 2, 1], [0, 2, 2], [1, 1, 0]]
    s_score = [F(0), F(1), F(3), F(4), F(2)]
    t_score = [F(1), F(3), F(0), F(2), F(4), F(-1)]
    gs, gt = geometry(source, s_score), geometry(target, t_score)
    count = 0
    for index in range(1, 26):
        beta = [F(index), F(index + 2, 3), F(2 * index + 1, 5)]
        # Deliberately apply different nonzero scales/offsets; correlation cancels them.
        ys = [F(7, 3) * x + 11 for x in matvec(source, beta)]
        yt = [F(-4, 9) * x - 5 for x in matvec(target, beta)]
        rs, rt = direct_r2(s_score, ys), direct_r2(t_score, yt)
        assert rs == formula_r2(gs, beta)
        assert rt == formula_r2(gt, beta)
        assert rt / rs == formula_ratio(gs, gt, beta)
        assert formula_ratio(gs, gs, beta) == 1
        assert 0 <= rs <= 1 and 0 <= rt <= 1
        count += 1
    return count


def integrability_witnesses():
    c2 = [[-1, -1], [-1, 1], [1, -1], [1, 1]]
    source = geometry(c2, [row[0] for row in c2])
    target = geometry(c2, [row[1] for row in c2])
    assert source == ([[4, 0], [0, 4]], [4, 0], 4)
    assert target == ([[4, 0], [0, 4]], [0, 4], 4)
    for n in (2, 10, 100, 1000):
        beta = [F(1, n), F(1)]
        assert formula_ratio(source, target, beta) == n * n
        assert formula_r2(source, beta) == F(1, 1 + n * n)
        assert formula_r2(target, beta) == F(n * n, 1 + n * n)

    # Rank-one source: both causal columns coincide, and its score is exact.
    c1 = [[x, x] for x in (-1, -1, 1, 1)]
    rank_one = geometry(c1, [-1, -1, 1, 1])
    zero_target = geometry(c2, [1, -1, -1, 1])
    assert zero_target[1] == [0, 0]
    for beta in ([F(1), F(2)], [F(2), F(-1)], [F(-3), F(1)]):
        assert formula_r2(rank_one, beta) == 1
        assert formula_ratio(rank_one, target, beta) <= 1
        assert formula_ratio(source, zero_target, beta) == 0

    # Parallel vectors with a rank-two target whose nullspace is not in the
    # source nullspace: Q = (beta1² + beta2² + beta3²)/(beta1² + beta2²).
    c3 = [[x, y, z] for x in (-1, 1) for y in (-1, 1) for z in (-1, 1)]
    source3 = geometry(c3, [row[0] for row in c3])
    target2 = geometry([[x, y, 0] for x, y, _ in c3], [row[0] for row in c3])
    assert source3[1] == target2[1] == [8, 0, 0]
    null_vector = [F(0), F(0), F(1)]
    assert quadratic(target2[0], null_vector) == 0
    assert quadratic(source3[0], null_vector) == 8
    for n in (2, 10, 100):
        beta = [F(1, n), F(1, n), F(1)]
        assert formula_ratio(source3, target2, beta) == 1 + F(n * n, 2)

    # Reverse this geometry: target rank three, parallel vectors, bounded Q.
    # Identical full-rank panels additionally exercise kernel containment.
    for beta in ([F(1), F(2), F(3)], [F(2), F(1), F(-4)]):
        assert 0 <= formula_ratio(target2, source3, beta) <= 1
        assert formula_ratio(source3, source3, beta) == 1
    return {
        "nonparallel_source_rank_two": "Q(1/n,1) = n², exactly",
        "rank_one_source": "source accuracy = 1; ratio bounded by 1",
        "zero_target_vector": "target accuracy and ratio = 0",
        "parallel_rank_two_target": "Q(1/n,1/n,1) = 1 + n²/2, exactly",
        "parallel_rank_three_target": "checked reversed geometry has bounded ratio",
        "kernel_containment": "identical panels give ratio = 1",
    }


def gaussian_quadrature_checks():
    # Uniform Gaussian angle theta gives Q = tan(theta)². Integrate theta
    # directly, independently of the transformed density's antiderivative (6).
    nodes, weights = np.polynomial.legendre.leggauss(512)
    rows = []
    for cap in (1, 4, 25, 100, 10_000):
        stop = atan(sqrt(cap))
        angles = (nodes + 1) * stop / 2
        numerical = float(stop / pi * np.dot(weights, np.tan(angles) ** 2))
        analytical = 2 / pi * (sqrt(cap) - atan(sqrt(cap)))
        assert abs(numerical - analytical) <= 2e-8 * max(1, analytical)
        rows.append({
            "cap": cap,
            "exact_expression": "2/pi * (sqrt(cap) - atan(sqrt(cap)))",
            "expression_evaluated": analytical,
            "angle_quadrature": numerical,
            "absolute_difference": abs(numerical - analytical),
        })
    return rows


def main():
    result = {
        "status": "passed",
        "exact_rational_sample_fixtures": exact_sample_checks(),
        "exact_geometry_checks": integrability_witnesses(),
        "gaussian_witness_truncated_means": gaussian_quadrature_checks(),
        "method": "exact rational identities and deterministic 512-node Gaussian quadrature",
        "scope": "checks analytical consequences; does not certify simulator support or replace proof",
        "numpy_version": np.__version__,
    }
    (ROOT / "verification.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
