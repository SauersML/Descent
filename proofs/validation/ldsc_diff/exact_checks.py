#!/usr/bin/env python3.12
"""Exact-rational checks on Calibrator/StatisticalGeneticsMethodology.lean:281
`geneticCorrelationLDSC`.  No floats decide anything here: every comparison is
between Fractions (squared cosines, so no sqrt is needed).

Q1. Is the body the right ESTIMAND on true effects under the corpus's own
    per-allele effect convention?  Conventions.additiveVariance and
    VarianceComponents.additiveVariance both weight alpha_i^2 by 2p_i(1-p_i),
    i.e. effects in this corpus are per-allele.  Genetic correlation on the
    per-allele scale is sum w_i b_s b_t / sqrt(sum w_i b_s^2 * sum w_i b_t^2)
    with w_i = 2p_i(1-p_i).  The Lean body sets all w_i = 1.

Q2. Under LD, does the cosine of MARGINAL effects (what summary stats give)
    equal the cosine of JOINT effects (what rho_g is about)?
"""
from fractions import Fraction as F
import json


def cos2(u, v, w=None):
    """Exact squared cosine, optionally in the metric diag(w)."""
    if w is None:
        w = [F(1)] * len(u)
    num = sum(wi * a * b for wi, a, b in zip(w, u, v))
    du = sum(wi * a * a for wi, a in zip(w, u))
    dv = sum(wi * b * b for wi, b in zip(w, v))
    return F(num * num, du * dv), (num >= 0)


def matvec(R, x):
    return [sum(rij * xj for rij, xj in zip(row, x)) for row in R]


out = {}

# ---------------------------------------------------------------- Q1
# Three SNPs, per-allele effects, frequencies differing between populations.
p_s = [F(1, 2), F(1, 10), F(1, 4)]
p_t = [F(1, 2), F(2, 5), F(1, 20)]
b_s = [F(1), F(2), F(-1)]
b_t = [F(1), F(1), F(1)]
w_s = [2 * p * (1 - p) for p in p_s]
w_t = [2 * p * (1 - p) for p in p_t]
# cross-population weight: sqrt of the product would be irrational, so use the
# single-population case (p_s = p_t) to make the comparison exact and decisive.
lean, lean_sign = cos2(b_s, b_t)
weighted, w_sign = cos2(b_s, b_t, w_s)      # both effect vectors in pop s
out["Q1_per_allele_weighting"] = {
    "note": "same population, so the weight w=2p(1-p) is unambiguous",
    "p": [str(p) for p in p_s],
    "beta_s": [str(x) for x in b_s],
    "beta_t": [str(x) for x in b_t],
    "lean_cos2": str(lean),
    "lean_cos": float(lean) ** 0.5 * (1 if lean_sign else -1),
    "hwe_weighted_cos2": str(weighted),
    "hwe_weighted_cos": float(weighted) ** 0.5 * (1 if w_sign else -1),
    "equal_exactly": lean == weighted and lean_sign == w_sign,
}

# frequency-difference version: the estimand a cross-population rho_g needs
out["Q1b_frequencies_differ"] = {
    "cos2_in_pop_s_metric": str(cos2(b_s, b_t, w_s)[0]),
    "cos2_in_pop_t_metric": str(cos2(b_s, b_t, w_t)[0]),
    "metrics_disagree": cos2(b_s, b_t, w_s)[0] != cos2(b_s, b_t, w_t)[0],
    "note": "the Lean body has no frequency argument, so it cannot express "
            "either; LDSCModel carries no allele frequencies at all",
}

# ---------------------------------------------------------------- Q2
# Two SNPs in LD, r = 1/2.  Marginal effects are R b.
R = [[F(1), F(1, 2)], [F(1, 2), F(1)]]
jb_s = [F(1), F(0)]
jb_t = [F(0), F(1)]        # truly orthogonal joint effects: rho_g = 0
mb_s, mb_t = matvec(R, jb_s), matvec(R, jb_t)
c_joint, s_joint = cos2(jb_s, jb_t)
c_marg, s_marg = cos2(mb_s, mb_t)
out["Q2_LD_marginal_vs_joint"] = {
    "R": [[str(x) for x in row] for row in R],
    "joint_beta_s": [str(x) for x in jb_s],
    "joint_beta_t": [str(x) for x in jb_t],
    "cos_joint": 0.0 if c_joint == 0 else float(c_joint) ** 0.5,
    "cos2_joint": str(c_joint),
    "marginal_beta_s": [str(x) for x in mb_s],
    "marginal_beta_t": [str(x) for x in mb_t],
    "cos2_marginal": str(c_marg),
    "cos_marginal": float(c_marg) ** 0.5 * (1 if s_marg else -1),
    "equal_exactly": c_joint == c_marg,
    "verdict": "orthogonal joint effects (rho_g = 0) give a strictly nonzero "
               "cosine of marginal effects under LD",
}

# Q2b: the reverse -- identical joint effects still give cos = 1 under LD
jb = [F(3), F(-1)]
c_j, _ = cos2(jb, jb)
c_m, _ = cos2(matvec(R, jb), matvec(R, jb))
out["Q2b_identical_effects_are_safe"] = {
    "cos2_joint": str(c_j), "cos2_marginal": str(c_m),
    "equal_exactly": c_j == c_m,
}

# ---------------------------------------------------------------- Q3
# Does the Lean body ever exceed 1?  (the Lean theorem says no; verify the
# Cauchy-Schwarz bound is what it rests on, exactly, on a random rational set)
import random
rng = random.Random(7)
worst = F(0)
for _ in range(2000):
    n = rng.randint(2, 6)
    u = [F(rng.randint(-9, 9), rng.randint(1, 7)) for _ in range(n)]
    v = [F(rng.randint(-9, 9), rng.randint(1, 7)) for _ in range(n)]
    if sum(x * x for x in u) == 0 or sum(x * x for x in v) == 0:
        continue
    c, _ = cos2(u, v)
    worst = max(worst, c)
out["Q3_bounded_by_one"] = {"max_cos2_over_2000_rational_draws": str(worst),
                            "exceeds_one": worst > 1}

print(json.dumps(out, indent=1))
