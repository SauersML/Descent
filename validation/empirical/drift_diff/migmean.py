#!/usr/bin/env /usr/bin/python3.12
"""Does ANY scalar symmetric summary of (m12, m21) determine two-deme equilibrium F_ST?

Two independent instruments:
  (1) EXACT identity-by-descent recursion, solved in fractions.Fraction.  Two demes of
      2N gene copies, backward migration m1 (fraction of deme-1 gametes drawn from deme
      2) and m2, infinite-alleles mutation rate u.  States: Q1, Q2 (probability of
      identity for two distinct genes both in deme 1 / deme 2) and Q12 (one in each).
      This is a linear fixed point; no approximation, no float.
  (2) DIRECT Wright-Fisher forward simulation with the same migration convention and
      symmetric two-way biallelic mutation; F_ST measured with Hudson's estimator from
      exact integer allele counts (frequencies are exact rationals c/(2N)).

Decisive design: hold a candidate mean FIXED and vary m1/m2 over >= 1 order of
magnitude.  If measured F_ST moves while the candidate is constant, that candidate is
not the argument F_ST depends on, and no recalibration of it can help.
"""
import json, random, sys
from fractions import Fraction as F


# ------------------------------------------------- (1) exact IBD recursion
def solve3(A, c):
    """Solve (I - A) Q = c exactly for 3 unknowns.  A is 3x3, c is len-3, Fractions."""
    M = [[(F(1) if i == j else F(0)) - A[i][j] for j in range(3)] + [c[i]]
         for i in range(3)]
    for col in range(3):
        piv = next(r for r in range(col, 3) if M[r][col] != 0)
        M[col], M[piv] = M[piv], M[col]
        pv = M[col][col]
        M[col] = [x / pv for x in M[col]]
        for r in range(3):
            if r != col and M[r][col] != 0:
                f = M[r][col]
                M[r] = [x - f * y for x, y in zip(M[r], M[col])]
    return [M[i][3] for i in range(3)]


def fst_exact(twoN, m1, m2, u):
    """Exact equilibrium F_ST = (Qbar_within - Q_between)/(1 - Q_between)."""
    m1 = F(m1); m2 = F(m2); u = F(u)
    a = F(1, twoN); b = 1 - a
    g = (1 - u) ** 2
    A = [[g * (1 - m1) ** 2 * b, g * m1 ** 2 * b,          g * 2 * m1 * (1 - m1)],
         [g * m2 ** 2 * b,       g * (1 - m2) ** 2 * b,    g * 2 * m2 * (1 - m2)],
         [g * (1 - m1) * m2 * b, g * m1 * (1 - m2) * b,
          g * ((1 - m1) * (1 - m2) + m1 * m2)]]
    c = [g * a * ((1 - m1) ** 2 + m1 ** 2),
         g * a * ((1 - m2) ** 2 + m2 ** 2),
         g * a * ((1 - m1) * m2 + m1 * (1 - m2))]
    Q1, Q2, Q12 = solve3(A, c)
    within = (Q1 + Q2) / 2
    return (within - Q12) / (1 - Q12), Q1, Q2, Q12


# ------------------------------------------------- (2) forward WF simulation
def sim_fst(L, twoN, m1, m2, u, t, reps, seed, burn_frac=0.5, samples=10):
    """Two demes, backward migration (m1 into deme 1, m2 into deme 2), symmetric two-way
    mutation u.  Returns per-replicate Hudson F_ST averaged over post-burn-in samples."""
    random.seed(seed)
    out = []
    burn = int(t * burn_frac)
    stride = max(1, (t - burn) // samples)
    for r in range(reps):
        p1 = [random.randrange(1, twoN) for _ in range(L)]
        p2 = list(p1)
        acc = []
        for gen in range(t):
            f1 = [c / twoN for c in p1]
            f2 = [c / twoN for c in p2]
            n1 = []; n2 = []
            for j in range(L):
                x1 = (1 - m1) * f1[j] + m1 * f2[j]
                x2 = (1 - m2) * f2[j] + m2 * f1[j]
                x1 = x1 * (1 - u) + (1 - x1) * u
                x2 = x2 * (1 - u) + (1 - x2) * u
                n1.append(random.binomialvariate(twoN, min(1.0, max(0.0, x1))))
                n2.append(random.binomialvariate(twoN, min(1.0, max(0.0, x2))))
            p1, p2 = n1, n2
            if gen >= burn and (gen - burn) % stride == 0:
                num = F(0); den = F(0)
                for c1, c2 in zip(p1, p2):
                    q1 = F(c1, twoN); q2 = F(c2, twoN)
                    num += (q1 - q2) ** 2
                    den += q1 * (1 - q2) + q2 * (1 - q1)
                if den:
                    acc.append(num / den)
        if acc:
            out.append(float(sum(acc) / len(acc)))
    return out


# ------------------------------------------------- means
def means(m1, m2):
    m1 = F(m1); m2 = F(m2)
    am = (m1 + m2) / 2
    hm = 2 * m1 * m2 / (m1 + m2) if (m1 + m2) else F(0)
    gm2 = m1 * m2                      # squared geometric mean, exact
    return dict(AM=float(am), HM=float(hm), GM=float(gm2) ** 0.5)


if __name__ == "__main__":
    mode = sys.argv[1]
    cfg = json.loads(sys.argv[2])

    if mode == "exact":
        # dense exact sweep: for each held-fixed candidate mean, vary the ratio
        twoN = cfg["twoN"]; u = cfg["u"]
        rows = []
        for fam, target, ratios in cfg["families"]:
            for R in ratios:
                R = F(R)
                t = F(target)
                if fam == "AM":       # (m1+m2)/2 = t, m1 = R m2
                    m2 = 2 * t / (1 + R); m1 = R * m2
                elif fam == "HM":     # 2 m1 m2/(m1+m2) = t
                    m2 = t * (1 + R) / (2 * R); m1 = R * m2
                elif fam == "GM":     # m1 m2 = t^2
                    # m2 = t/sqrt(R): keep exact by choosing R a perfect square
                    s = F(int(R ** F(1, 2))) if int(R ** 0.5) ** 2 == R else None
                    if s is None:
                        continue
                    m2 = t / s; m1 = R * m2
                fst, Q1, Q2, Q12 = fst_exact(twoN, m1, m2, u)
                rows.append(dict(family=fam, target=float(t), ratio=float(R),
                                 m1=float(m1), m2=float(m2),
                                 fst_exact=float(fst), **means(m1, m2)))
        print(json.dumps(dict(mode="exact", cfg=cfg, rows=rows)))

    elif mode == "sim":
        pts = cfg.pop("points")
        rows = []
        for label, m1, m2 in pts:
            m1 = F(m1); m2 = F(m2)
            v = sim_fst(m1=float(m1), m2=float(m2), u=float(F(cfg["u"])),
                        **{k: w for k, w in cfg.items() if k != "u"})
            n = len(v); mu = sum(v) / n
            sd = (sum((x - mu) ** 2 for x in v) / max(1, n - 1)) ** 0.5
            fe, _, _, _ = fst_exact(cfg["twoN"], F(m1), F(m2), F(cfg["u"]))
            rows.append(dict(label=label, m1=float(m1), m2=float(m2),
                             fst_sim=mu, se=sd / n ** 0.5, reps=n,
                             fst_exact_ibd=float(fe), **means(F(m1), F(m2))))
        print(json.dumps(dict(mode="sim", cfg=cfg, rows=rows)))
