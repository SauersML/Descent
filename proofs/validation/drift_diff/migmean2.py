#!/usr/bin/env /usr/bin/python3.12
"""Two follow-ups, both by exact identity-by-descent recursion in fractions.Fraction.

A) DEMES: d-deme symmetric island model, exact 2-state recursion (by symmetry the only
   states are "two lineages in the same deme" and "in different demes").  Two migration
   conventions are simulated separately, because the corpus's factor-of-two hinges on
   which one `m` denotes:
     PAIRWISE : each deme replaces fraction m by migrants drawn from the OTHER d-1 demes
     POOLED   : each deme replaces fraction m by migrants drawn from the pooled
                population INCLUDING its own deme (so m_pairwise = m*(d-1)/d)
   Compared against the corpus's two forms:
     fstMigrationDriftEquilibrium Ne m = 1/(1+4*Ne*m)              (d -> infinity limit)
     islandFstFiniteDemes Ne m d       = 1/(1+4*Ne*m*(d/(d-1))^2)  (finite-deme)

B) UNEQUAL DEME SIZES: 3-state recursion (Q1, Q2, Q12) with a_i = 1/(2*N_i) allowed to
   differ.  Tests whether the arithmetic-mean invariance established for N1 = N2 survives.
"""
import json, sys
from fractions import Fraction as F


def solve(M, c):
    """Solve (I - M) Q = c exactly.  n x n, Fractions."""
    n = len(c)
    A = [[(F(1) if i == j else F(0)) - M[i][j] for j in range(n)] + [c[i]]
         for i in range(n)]
    for col in range(n):
        piv = next(r for r in range(col, n) if A[r][col] != 0)
        A[col], A[piv] = A[piv], A[col]
        pv = A[col][col]
        A[col] = [x / pv for x in A[col]]
        for r in range(n):
            if r != col and A[r][col] != 0:
                f = A[r][col]
                A[r] = [x - f * y for x, y in zip(A[r], A[col])]
    return [A[i][n] for i in range(n)]


# ------------------------------------------------------------ A) d demes
def fst_ddeme(twoN, m, d, u, convention="PAIRWISE"):
    """Exact F_ST for d equal demes of twoN gene copies under symmetric migration."""
    m = F(m); u = F(u); d = int(d)
    if convention == "POOLED":
        m = m * F(d - 1, d)          # fraction actually leaving for another deme
    a = F(1, twoN); b = 1 - a
    g = (1 - u) ** 2
    if d == 1:
        return None
    # P(both parents in the same deme | lineages started in the same deme)
    Ps = (1 - m) ** 2 + m ** 2 / F(d - 1)
    # P(both parents in the same deme | lineages started in different demes)
    Pd = 2 * m * (1 - m) / F(d - 1) + F(d - 2) * m ** 2 / F(d - 1) ** 2
    M = [[g * Ps * b, g * (1 - Ps)],
         [g * Pd * b, g * (1 - Pd)]]
    c = [g * Ps * a, g * Pd * a]
    Qs, Qd = solve(M, c)
    return (Qs - Qd) / (1 - Qd)


# ------------------------------------------ B) two demes, unequal sizes
def fst_unequal(twoN1, twoN2, m1, m2, u):
    """Exact F_ST, two demes of twoN1 / twoN2 gene copies, backward rates m1 / m2.
    m1 = fraction of deme-1 gametes drawn from deme 2."""
    m1 = F(m1); m2 = F(m2); u = F(u)
    a1 = F(1, twoN1); b1 = 1 - a1
    a2 = F(1, twoN2); b2 = 1 - a2
    g = (1 - u) ** 2
    # Q1 (both in deme 1), Q2 (both in deme 2), Q12
    M = [[g * (1 - m1) ** 2 * b1, g * m1 ** 2 * b2,        g * 2 * m1 * (1 - m1)],
         [g * m2 ** 2 * b1,       g * (1 - m2) ** 2 * b2,  g * 2 * m2 * (1 - m2)],
         [g * (1 - m1) * m2 * b1, g * m1 * (1 - m2) * b2,
          g * ((1 - m1) * (1 - m2) + m1 * m2)]]
    c = [g * a1 * (1 - m1) ** 2 + g * a2 * m1 ** 2,
         g * a1 * m2 ** 2 + g * a2 * (1 - m2) ** 2,
         g * a1 * (1 - m1) * m2 + g * a2 * m1 * (1 - m2)]
    Q1, Q2, Q12 = solve(M, c)
    within = (Q1 + Q2) / 2            # Hudson, equal sample sizes from each deme
    return (within - Q12) / (1 - Q12)


if __name__ == "__main__":
    mode = sys.argv[1]

    if mode == "control":
        # POSITIVE CONTROL: both generalisations must reproduce the already-validated
        # equal-size two-deme numbers exactly.
        print("POSITIVE CONTROL 1: fst_unequal at N1 = N2 vs the validated equal-size run")
        print("  expect F_ST = 1/(1+8*N*AM) to within the discrete-generation correction")
        for twoN, s in [(200, '1/100'), (200, '1/200'), (1000, '1/200')]:
            S = F(s)
            for k in ['1/2', '3/4', '99/100']:
                m1 = S * F(k); m2 = S - m1
                v = fst_unequal(twoN, twoN, m1, m2, F(1, 10000))
                print("    2N1=2N2=%-5d sum=%-7s split=%-7s  F_ST=%.9f" % (twoN, s, k, float(v)))
        print()
        print("POSITIVE CONTROL 2: fst_ddeme at d=2 PAIRWISE vs closed form 1/(1+8*N*m)")
        for twoN, m in [(200, '1/100'), (200, '1/200'), (1000, '1/500')]:
            N = twoN // 2
            v = fst_ddeme(twoN, F(m), 2, F(1, 10000), "PAIRWISE")
            cf = 1 / (1 + 8 * N * float(F(m)))
            print("    2N=%-5d m=%-8s exact=%.6f  1/(1+8Nm)=%.6f  %+.2f%%"
                  % (twoN, m, float(v), cf, (float(v) / cf - 1) * 100))

    elif mode == "demes":
        twoN = 200; N = twoN // 2; u = F(1, 100000)
        rows = []
        for conv in ["PAIRWISE", "POOLED"]:
            for m in ['1/200', '1/500', '1/1000']:
                for d in [2, 5, 10, 40]:
                    v = fst_ddeme(twoN, F(m), d, u, conv)
                    mm = float(F(m))
                    limit = 1 / (1 + 4 * N * mm)
                    finite = 1 / (1 + 4 * N * mm * (d / (d - 1.0)) ** 2)
                    rows.append(dict(conv=conv, m=m, d=d, twoN=twoN,
                                     fst_exact=float(v),
                                     corpus_limit=limit,
                                     corpus_limit_err_pct=(limit / float(v) - 1) * 100,
                                     corpus_finite=finite,
                                     corpus_finite_err_pct=(finite / float(v) - 1) * 100))
        print(json.dumps(rows))

    elif mode == "unequal":
        u = F(1, 10000)
        rows = []
        for (n1, n2) in [(200, 200), (200, 400), (200, 1000), (200, 2000), (100, 2000)]:
            for s in ['1/100', '1/200', '1/1000']:
                S = F(s)
                vals = []
                for k in ['1/2', '3/5', '3/4', '9/10', '99/100', '999/1000']:
                    m1 = S * F(k); m2 = S - m1
                    v = fst_unequal(n1, n2, m1, m2, u)
                    vals.append((k, float(m1), float(m2), v))
                fl = [float(x[3]) for x in vals]
                rows.append(dict(twoN1=n1, twoN2=n2, sum_m=s,
                                 all_identical=(len(set(x[3] for x in vals)) == 1),
                                 fst_min=min(fl), fst_max=max(fl),
                                 swing_pct=(max(fl) / min(fl) - 1) * 100,
                                 detail=[(k, f1, f2, float(v)) for k, f1, f2, v in vals]))
        print(json.dumps(rows))

    elif mode == "weights":
        # If AM fails at unequal sizes, is there ANY fixed linear summary w1*m1+w2*m2?
        # Level-curve slope = -(dF/dm1)/(dF/dm2), computed by exact central differences.
        u = F(1, 10000); h = F(1, 10 ** 7)
        out = []
        for (n1, n2) in [(200, 200), (200, 400), (200, 1000), (200, 2000), (100, 2000)]:
            pts = []
            for (m1s, m2s) in [('1/400', '1/400'), ('1/200', '1/600'),
                               ('1/1000', '1/1000'), ('3/1000', '1/3000')]:
                m1 = F(m1s); m2 = F(m2s)
                d1 = (fst_unequal(n1, n2, m1 + h, m2, u) -
                      fst_unequal(n1, n2, m1 - h, m2, u)) / (2 * h)
                d2 = (fst_unequal(n1, n2, m1, m2 + h, u) -
                      fst_unequal(n1, n2, m1, m2 - h, u)) / (2 * h)
                pts.append(dict(m1=m1s, m2=m2s, ratio_dF1_over_dF2=float(d1 / d2)))
            out.append(dict(twoN1=n1, twoN2=n2, points=pts,
                            const_across_points=(len(set(round(p['ratio_dF1_over_dF2'], 9)
                                                         for p in pts)) == 1)))
        print(json.dumps(out))

    elif mode == "asymfst":
        # Direct test of PortabilityDrift.asymmetricFst Ne m_into = 1/(1+4*Ne*m_into).
        # Exact recursion gives Q1, Q2, Q12, hence BOTH:
        #   pairwise (Hudson) F_ST  = ((Q1+Q2)/2 - Q12)/(1-Q12)   -- one number for the pair
        #   population-specific F_i = (Q_i - Q12)/(1-Q12)          -- direction-dependent
        u = F(1, 10000)
        out = []
        for twoN in [200, 1000]:
            N = twoN // 2
            for (m12s, m21s) in [('1/200', '1/200'), ('3/400', '1/400'),
                                 ('9/1000', '1/1000'), ('99/10000', '1/10000')]:
                m12 = F(m12s); m21 = F(m21s)
                m1 = m12; m2 = m21          # m1 = rate INTO deme 1 from deme 2
                a1 = F(1, twoN); b1 = 1 - a1
                a2 = F(1, twoN); b2 = 1 - a2
                g = (1 - u) ** 2
                M = [[g*(1-m1)**2*b1, g*m1**2*b2,       g*2*m1*(1-m1)],
                     [g*m2**2*b1,     g*(1-m2)**2*b2,   g*2*m2*(1-m2)],
                     [g*(1-m1)*m2*b1, g*m1*(1-m2)*b2,
                      g*((1-m1)*(1-m2)+m1*m2)]]
                c = [g*a1*(1-m1)**2 + g*a2*m1**2,
                     g*a1*m2**2 + g*a2*(1-m2)**2,
                     g*a1*(1-m1)*m2 + g*a2*m1*(1-m2)]
                Q1, Q2, Q12 = solve(M, c)
                F1 = (Q1 - Q12) / (1 - Q12)
                F2 = (Q2 - Q12) / (1 - Q12)
                pair = ((Q1 + Q2) / 2 - Q12) / (1 - Q12)
                out.append(dict(
                    twoN=twoN, m12=m12s, m21=m21s,
                    pairwise_fst=float(pair),
                    popspecific_F1=float(F1), popspecific_F2=float(F2),
                    asymmetricFst_at_m12=1/(1+4*N*float(m12)),
                    asymmetricFst_at_m21=1/(1+4*N*float(m21)),
                    err_F1_vs_asymFst_pct=(1/(1+4*N*float(m12))/float(F1)-1)*100,
                    err_F2_vs_asymFst_pct=(1/(1+4*N*float(m21))/float(F2)-1)*100,
                    direction_ordering_F1_lt_F2=bool(F1 < F2)))
        print(json.dumps(out))
