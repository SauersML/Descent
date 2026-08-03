#!/usr/bin/env python3.12
"""Tighter check of effectiveSampleSizeFromSE (StatisticalGeneticsMethodology
.lean:180) with a large replicate count, plus the scope probe: the exact
population value is N/(1 - h2_snp), so a SNP explaining a large share of the
phenotype should show a predictable overshoot.

POSITIVE CONTROL: the same harness applied to effectiveSampleSizeSE = 1/se^2
(already falsified) must recover the ratio 2p(1-p) exactly.
"""
import json
import math
import random
from multiprocessing import Pool


def job(a):
    N, p, beta, seed, reps = a
    rng = random.Random(seed)
    vg = beta * beta * 2 * p * (1 - p)
    ve = 1.0 - vg
    bs = []
    for _ in range(reps):
        sx = sxx = sy = syy = sxy = 0.0
        for _ in range(N):
            x = (1 if rng.random() < p else 0) + (1 if rng.random() < p else 0)
            y = beta * x + rng.gauss(0, math.sqrt(ve))
            sx += x; sxx += x * x; sy += y; syy += y * y; sxy += x * y
        cxy = sxy / N - (sx / N) * (sy / N)
        vx = sxx / N - (sx / N) ** 2
        vy = syy / N - (sy / N) ** 2
        bs.append((cxy / vx) / math.sqrt(vy))
    m = sum(bs) / len(bs)
    var = sum((b - m) ** 2 for b in bs) / (len(bs) - 1)
    se = math.sqrt(var)
    rel = 1.0 / math.sqrt(2 * (len(bs) - 1))          # rel. SE of an SD
    n_corr = 1.0 / (se * se * 2 * p * (1 - p))
    return {
        "N_true": N, "p": p, "beta": beta, "h2_snp": vg, "reps": reps,
        "se_empirical": se, "se_rel_uncertainty": rel,
        "effectiveSampleSizeFromSE": n_corr,
        "ratio_to_N": n_corr / N,
        "ratio_to_N_pm": 2 * rel,
        "predicted_ratio_N_over_1_minus_h2": 1.0 / (1.0 - vg),
        "effectiveSampleSizeSE_naive": 1.0 / (se * se),
        "naive_ratio_to_N": (1.0 / (se * se)) / N,
        "naive_predicted_2pq": 2 * p * (1 - p),
    }


if __name__ == "__main__":
    jobs = [
        (2000, 0.5, 0.02, 11, 900),
        (2000, 0.1, 0.02, 12, 900),
        (500, 0.3, 0.02, 13, 900),
        (4000, 0.05, 0.02, 14, 700),
        (2000, 0.5, 0.45, 15, 900),      # h2_snp = 0.10, scope probe
        (2000, 0.5, 0.63, 16, 900),      # h2_snp ~ 0.20, scope probe
    ]
    with Pool(6) as pool:
        print(json.dumps(pool.map(job, jobs), indent=1))
