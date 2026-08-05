#!/usr/bin/env python3.12
"""Secondary targets.

(A) VarianceComponents.lean:137 additiveVariance  =  sum_i 2 p_i (1-p_i) a_i^2
    Standard quantitative genetics: V_A = Var(sum_i a_i X_i) = a' Sigma a,
    which equals the Lean sum ONLY under linkage equilibrium.  With LD the
    cross terms 2 a_i a_j Cov(X_i,X_j) = 4 a_i a_j D_ij are dropped.
    Decided exactly with Fractions; confirmed by direct genotype simulation.

(B) StatisticalGeneticsMethodology.lean:180 effectiveSampleSizeFromSE
    = 1/(se^2 * 2p(1-p)).  Checked by simulating a GWAS at known N and MAF.
    POSITIVE CONTROL: the same harness is run on effectiveSampleSizeSE
    = 1/se^2, already falsified by a previous sweep, and must flag it.

(C) VarianceComponents.lean:55 snpH2 = V_A_tagged / V_P, checked against a
    direct simulation of tagged vs untagged additive variance.
"""
from fractions import Fraction as F
import json
import math
import random

out = {}

# ------------------------------------------------------------------ (A) exact
def lean_VA(ps, al):
    return sum(2 * p * (1 - p) * a * a for p, a in zip(ps, al))


def true_VA(ps, al, D):
    """Two loci, LD coefficient D.  Cov(X1,X2) = 2D for diploid allele counts."""
    return lean_VA(ps, al) + 2 * al[0] * al[1] * 2 * D


cases = []
for p1, p2, D, a1, a2 in [
    (F(1, 2), F(1, 2), F(1, 8), F(1), F(1)),     # r = 1/2, same-sign effects
    (F(1, 2), F(1, 2), F(1, 8), F(1), F(-1)),    # opposite-sign effects
    (F(1, 5), F(1, 5), F(1, 25), F(1), F(1)),    # rarer variants
    (F(1, 2), F(1, 2), F(0), F(1), F(1)),        # linkage equilibrium
]:
    ps, al = [p1, p2], [a1, a2]
    lv, tv = lean_VA(ps, al), true_VA(ps, al, D)
    r = F(1) if D == 0 else D / (p1 * (1 - p1) * p2 * (1 - p2)) ** 1  # D/(pq pq)
    cases.append({
        "p": [str(p1), str(p2)], "alpha": [str(a1), str(a2)], "D": str(D),
        "lean_VA": str(lv), "true_VA": str(tv),
        "exactly_equal": lv == tv,
        "lean_over_true": str(F(lv, tv)) if tv != 0 else None,
        "lean_over_true_float": float(lv) / float(tv) if tv != 0 else None,
    })
out["A_additiveVariance_exact"] = {
    "claim": "Lean drops the LD cross term 4 a_i a_j D_ij",
    "cases": cases,
}


# ------------------------------------------------- (A2) simulate to ground it
def sim_two_locus(p1, p2, D, a1, a2, n, seed):
    rng = random.Random(seed)
    h = [(p1 * p2 + D, 1, 1), (p1 * (1 - p2) - D, 1, 0),
         ((1 - p1) * p2 - D, 0, 1), ((1 - p1) * (1 - p2) + D, 0, 0)]
    assert all(f > 0 for f, _, _ in h), "invalid D"
    cum, acc = [], 0.0
    for f, x, y in h:
        acc += f
        cum.append((acc, x, y))

    def draw():
        u = rng.random()
        for c, x, y in cum:
            if u <= c:
                return x, y
        return cum[-1][1], cum[-1][2]

    s = ss = 0.0
    for _ in range(n):
        x1a, x2a = draw()
        x1b, x2b = draw()
        g = a1 * (x1a + x1b) + a2 * (x2a + x2b)
        s += g
        ss += g * g
    return ss / n - (s / n) ** 2


p1 = p2 = 0.5
D = 0.125
a1 = a2 = 1.0
vsim = sim_two_locus(p1, p2, D, a1, a2, 400000, 11)
out["A2_additiveVariance_simulated"] = {
    "n_individuals": 400000,
    "V_A_simulated": vsim,
    "V_A_lean_formula": float(lean_VA([F(1, 2), F(1, 2)], [F(1), F(1)])),
    "V_A_with_LD_term": float(true_VA([F(1, 2), F(1, 2)], [F(1), F(1)], F(1, 8))),
    "sim_matches_LD_formula_within_1pct":
        abs(vsim - 1.5) / 1.5 < 0.01,
    "lean_understates_by_pct": 100 * (1.5 - 1.0) / 1.5,
}
# LE control: the Lean formula must be exact when D = 0
vsim0 = sim_two_locus(p1, p2, 0.0, a1, a2, 400000, 12)
out["A2_LE_control"] = {"V_A_simulated": vsim0, "V_A_lean_formula": 1.0,
                        "matches_within_1pct": abs(vsim0 - 1.0) < 0.01}


# ------------------------------------------------------- (B) effective N
def gwas_se(N, p, beta, h2_other, seed, reps=200):
    """Empirical SE of the per-allele OLS slope, phenotype standardized."""
    rng = random.Random(seed)
    vg = beta * beta * 2 * p * (1 - p)
    ve = 1.0 - vg - h2_other
    bs = []
    for _ in range(reps):
        sx = sxx = sy = syy = sxy = 0.0
        for _ in range(N):
            x = (1 if rng.random() < p else 0) + (1 if rng.random() < p else 0)
            y = beta * x + rng.gauss(0, math.sqrt(ve)) + \
                rng.gauss(0, math.sqrt(h2_other))
            sx += x; sxx += x * x; sy += y; syy += y * y; sxy += x * y
        cxy = sxy / N - (sx / N) * (sy / N)
        vx = sxx / N - (sx / N) ** 2
        vy = syy / N - (sy / N) ** 2
        bs.append((cxy / vx) / math.sqrt(vy))     # slope, y standardized
    m = sum(bs) / len(bs)
    var = sum((b - m) ** 2 for b in bs) / (len(bs) - 1)
    return math.sqrt(var)


rows = []
for N, p in [(2000, 0.5), (2000, 0.1), (500, 0.3), (4000, 0.05)]:
    se = gwas_se(N, p, 0.05, 0.3, seed=1000 + N + int(100 * p), reps=150)
    n_corr = 1.0 / (se * se * 2 * p * (1 - p))
    n_naive = 1.0 / (se * se)                      # effectiveSampleSizeSE
    rows.append({"N_true": N, "p": p, "se_empirical": se,
                 "effectiveSampleSizeFromSE": n_corr,
                 "ratio_corrected_to_N": n_corr / N,
                 "effectiveSampleSizeSE": n_naive,
                 "ratio_naive_to_N": n_naive / N})
out["B_effectiveSampleSize"] = {
    "note": "phenotype standardized; predicted exact value is N/(1-h2_snp), "
            "and h2_snp is ~0.4% here so the target ratio is ~1.00",
    "rows": rows,
}

# ------------------------------------------------------------------ (C) snpH2
rng = random.Random(5)
M_tag, M_untag, N = 40, 40, 20000
b_tag = [rng.gauss(0, math.sqrt(0.3 / M_tag)) for _ in range(M_tag)]
b_un = [rng.gauss(0, math.sqrt(0.2 / M_untag)) for _ in range(M_untag)]
ps = [rng.uniform(0.05, 0.95) for _ in range(M_tag + M_untag)]
sg = sgg = sy = syy = 0.0
for _ in range(N):
    gt = gu = 0.0
    for j, b in enumerate(b_tag):
        p = ps[j]
        gt += b * ((1 if rng.random() < p else 0) + (1 if rng.random() < p else 0))
    for j, b in enumerate(b_un):
        p = ps[M_tag + j]
        gu += b * ((1 if rng.random() < p else 0) + (1 if rng.random() < p else 0))
    e = rng.gauss(0, math.sqrt(0.5))
    y = gt + gu + e
    sg += gt; sgg += gt * gt; sy += y; syy += y * y
VA_tag = sgg / N - (sg / N) ** 2
VP = syy / N - (sy / N) ** 2
out["C_snpH2"] = {
    "VA_tagged_sim": VA_tag, "VP_sim": VP, "snpH2_lean": VA_tag / VP,
    "VA_tagged_from_lean_formula":
        sum(2 * ps[j] * (1 - ps[j]) * b * b for j, b in enumerate(b_tag)),
    "note": "tagged and untagged loci are in linkage equilibrium here, so the "
            "per-locus formula and the simulated variance must agree",
}

print(json.dumps(out, indent=1))
