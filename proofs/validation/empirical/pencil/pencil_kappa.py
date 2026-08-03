#!/usr/bin/env /usr/bin/python3.12
"""TARGET 2: the whitening-gain trichotomy.

kappa_m = (1/m) Tr(A_m^{-1}) = (1/m)( 1 + sum_k (1+eps_k^2)/(1-eps_k^2) )

Controls first:
  (C1) the sum formula equals an explicit matrix-inverse trace at small m;
  (C2) at constant eps=rho the summand equals ldWhiteningGain(rho)=(1+r^2)/(1-r^2)
       and kappa_m equals the exact finite-m form [1+(m-1)g]/m.
Then the scaling of centred fluctuations vs the predicted 1/b-1 and -1/2.

Pure stdlib.
"""
import json, math, random, sys
from multiprocessing import Pool

def g(e):
    return (1.0 + e * e) / (1.0 - e * e)

def kappa_from_sum(eps):
    return (1.0 + sum(g(e) for e in eps)) / (len(eps) + 1)

# --------------------------------------------------- explicit matrix control
def corr_matrix(eps):
    """Stationary unit-variance Gaussian Markov chain correlation matrix:
    Sigma_ij = prod_{k=i}^{j-1} eps_k for i<j."""
    m = len(eps) + 1
    S = [[0.0] * m for _ in range(m)]
    for i in range(m):
        S[i][i] = 1.0
        p = 1.0
        for j in range(i + 1, m):
            p *= eps[j - 1]
            S[i][j] = p
            S[j][i] = p
    return S

def inv_trace(S):
    """Trace of the inverse by Gauss-Jordan with partial pivoting."""
    m = len(S)
    A = [row[:] + [1.0 if i == j else 0.0 for j in range(m)] for i, row in enumerate(S)]
    for c in range(m):
        p = max(range(c, m), key=lambda r: abs(A[r][c]))
        if abs(A[p][c]) < 1e-300:
            raise ZeroDivisionError
        A[c], A[p] = A[p], A[c]
        pv = A[c][c]
        A[c] = [x / pv for x in A[c]]
        Ac = A[c]
        for r in range(m):
            if r == c:
                continue
            f = A[r][c]
            if f:
                Ar = A[r]
                for k in range(c, 2 * m):
                    Ar[k] -= f * Ac[k]
    return sum(A[i][m + i] for i in range(m))

# ---------------------------------------------------------------- sampling
def sample_eps(b, m, rnd):
    """1-eps = U^{1/b} so P(1-eps < r) = r^b exactly: boundary tail index b."""
    ib = 1.0 / b
    return [1.0 - rnd.random() ** ib for _ in range(m)]

def work(args):
    b, m, reps, seed = args
    rnd = random.Random(seed)
    ib = 1.0 / b
    out = []
    for _ in range(reps):
        s = 1.0
        for _ in range(m):
            e = 1.0 - rnd.random() ** ib
            s += (1.0 + e * e) / (1.0 - e * e)
        out.append(s / (m + 1))
    return (b, m, out)

def quantile(v, q):
    v = sorted(v)
    n = len(v)
    x = q * (n - 1)
    lo = int(math.floor(x))
    hi = min(lo + 1, n - 1)
    return v[lo] + (x - lo) * (v[hi] - v[lo])

def loglog_slope(xs, ys):
    """least-squares slope of log y vs log x, plus its standard error."""
    lx = [math.log(x) for x in xs]
    ly = [math.log(y) for y in ys]
    n = len(lx)
    mx = sum(lx) / n
    my = sum(ly) / n
    sxx = sum((x - mx) ** 2 for x in lx)
    sxy = sum((x - mx) * (y - my) for x, y in zip(lx, ly))
    slope = sxy / sxx
    inter = my - slope * mx
    if n > 2:
        rss = sum((y - inter - slope * x) ** 2 for x, y in zip(lx, ly))
        se = math.sqrt(rss / (n - 2) / sxx)
    else:
        se = float("nan")
    return slope, se

def main():
    out = {}
    NPROC = 14

    # ---- C1: sum formula vs explicit Tr(Sigma^{-1})
    rnd = random.Random(7)
    c1 = []
    for m in (4, 8, 16, 32, 64):
        for trial in range(3):
            eps = [rnd.uniform(-0.9, 0.95) for _ in range(m - 1)]
            direct = inv_trace(corr_matrix(eps)) / m
            formula = kappa_from_sum(eps)
            c1.append(dict(m=m, trial=trial, matrix_inverse=direct, sum_formula=formula,
                           absdiff=abs(direct - formula),
                           reldiff=abs(direct - formula) / abs(formula)))
    out["control_sum_vs_matrix_inverse"] = c1

    # ---- C2: constant environment vs ldWhiteningGain
    c2 = []
    for rho in (0.0, 0.1, 0.5, 0.9, 0.99, -0.7):
        gain = (1.0 + rho * rho) / (1.0 - rho * rho)
        for m in (10, 100, 10000, 1000000):
            eps = None
            kap = (1.0 + (m - 1) * gain) / m           # exact closed form of the sum
            if m <= 100:                                # verify the closed form itself
                eps = [rho] * (m - 1)
                kap_s = kappa_from_sum(eps)
            else:
                kap_s = kap
            row = dict(rho=rho, m=m, ldWhiteningGain=gain, kappa_m=kap,
                       kappa_m_from_explicit_sum=kap_s,
                       summand_equals_gain_exactly=(g(rho) == gain),
                       kappa_minus_gain=kap - gain,
                       exact_gap_formula=(1.0 - gain) / m)
            if m <= 64:
                row["matrix_inverse_kappa"] = inv_trace(corr_matrix([rho] * (m - 1))) / m
            c2.append(row)
    out["control_constant_env_vs_ldWhiteningGain"] = c2

    # ---- empirical boundary tail index of the summand
    tail = []
    rnd2 = random.Random(99)
    for b in (0.5, 1.5, 2.5, 4.0):
        vals = [g(e) for e in sample_eps(b, 400000, rnd2)]
        vals.sort()
        n = len(vals)
        pts = []
        for frac in (0.01, 0.003, 0.001, 0.0003):
            k = int(n * frac)
            pts.append((vals[n - k], frac))
        sl, se = loglog_slope([p[0] for p in pts], [p[1] for p in pts])
        tail.append(dict(b=b, fitted_tail_exponent=-sl, se=se, points=pts))
    out["summand_tail_index"] = tail

    # ---- scaling of kappa_m
    plan = [(100, 4000), (1000, 2500), (10000, 800), (100000, 160)]
    bs = [0.5, 1.5, 2.5, 4.0]
    jobs = []
    sd = 20000
    NCH = 8
    for b in bs:
        for m, reps in plan:
            per = max(1, reps // NCH)
            for k in range(NCH):
                sd += 1
                jobs.append((b, m, per, sd))
    with Pool(NPROC) as p:
        res = p.map(work, jobs)
    coll = {}
    for b, m, vals in res:
        coll.setdefault((b, m), []).extend(vals)

    stats = []
    for (b, m), vals in sorted(coll.items()):
        stats.append(dict(b=b, m=m, reps=len(vals), median=quantile(vals, 0.5),
                          iqr=quantile(vals, 0.75) - quantile(vals, 0.25),
                          q10=quantile(vals, 0.10), q90=quantile(vals, 0.90),
                          mean=sum(vals) / len(vals), minv=min(vals), maxv=max(vals)))
    out["kappa_stats"] = stats

    scal = []
    for b in bs:
        rows = [s for s in stats if s["b"] == b]
        ms = [s["m"] for s in rows]
        sl_iqr, se_iqr = loglog_slope(ms, [s["iqr"] for s in rows])
        sl_med, se_med = loglog_slope(ms, [s["median"] for s in rows])
        sl_sp, se_sp = loglog_slope(ms, [s["q90"] - s["q10"] for s in rows])
        pred_fluc = (1.0 / b - 1.0) if b < 2.0 else -0.5
        scal.append(dict(b=b, predicted_fluctuation_exponent=pred_fluc,
                         iqr_slope=sl_iqr, iqr_slope_se=se_iqr,
                         q90_q10_slope=sl_sp, q90_q10_slope_se=se_sp,
                         median_slope=sl_med, median_slope_se=se_med,
                         predicted_median_slope=(1.0 / b - 1.0) if b < 1.0 else 0.0))
    out["scaling_fits"] = scal

    json.dump(out, sys.stdout, indent=1)

if __name__ == "__main__":
    main()
