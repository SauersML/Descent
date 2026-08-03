#!/usr/bin/env /usr/bin/python3.12
"""TARGET 1: is phi(abab) = 2 E[a^2]E[b^2] + 4 (Ea)^2(Eb)^2 for independent
tridiagonal pairs, and does the same harness return the FREE value when the
pair is genuinely free (one side Haar-rotated)?

Pure stdlib. No numpy/sympy on the cluster.
"""
import json, math, random, sys, os
from multiprocessing import Pool

# ---------------------------------------------------------------- structures
def tridiag(m, vals):
    """rows[i] = {j: value}; zero diagonal, symmetric off-diagonal vals[k]."""
    rows = [dict() for _ in range(m)]
    for k in range(m - 1):
        rows[k][k + 1] = vals[k]
        rows[k + 1][k] = vals[k]
    return rows

def add_diag(rows, s):
    if s == 0.0:
        return rows
    for i, r in enumerate(rows):
        r[i] = r.get(i, 0.0) + s
    return rows

def spmul(X, Y, m):
    R = [dict() for _ in range(m)]
    for i in range(m):
        Ri = R[i]
        for j, v in X[i].items():
            for k, w in Y[j].items():
                Ri[k] = Ri.get(k, 0.0) + v * w
    return R

def sp_tr_sq(C, m):
    """Tr(C C) = sum_ij C_ij C_ji."""
    t = 0.0
    for i in range(m):
        for j, v in C[i].items():
            w = C[j].get(i)
            if w is not None:
                t += v * w
    return t

def sp_trace(X, m):
    return sum(X[i].get(i, 0.0) for i in range(m))

def phi_abab_sparse(m, av, bv, s=0.0, t=0.0):
    A = add_diag(tridiag(m, av), s)
    B = add_diag(tridiag(m, bv), t)
    C = spmul(A, B, m)
    return sp_tr_sq(C, m) / m

# ------------------------------------------------------- dense cross-check
def to_dense(rows, m):
    D = [[0.0] * m for _ in range(m)]
    for i in range(m):
        for j, v in rows[i].items():
            D[i][j] = v
    return D

def dmul(X, Y, m):
    Yt = [[Y[i][j] for i in range(m)] for j in range(m)]
    return [[sum(x * y for x, y in zip(X[i], Yt[j])) for j in range(m)] for i in range(m)]

def phi_abab_dense(m, av, bv, s=0.0, t=0.0):
    A = to_dense(add_diag(tridiag(m, av), s), m)
    B = to_dense(add_diag(tridiag(m, bv), t), m)
    M = dmul(dmul(dmul(A, B, m), A, m), B, m)
    return sum(M[i][i] for i in range(m)) / m

# ------------------------------------------------------------ distributions
def make_dist(spec):
    kind = spec[0]
    if kind == "const":
        c = spec[1]
        return (lambda: c), c, c * c, f"const({c:g})"
    if kind == "unif":
        u = spec[1]
        return (lambda: random.uniform(0.0, u)), u / 2.0, u * u / 3.0, f"unif(0,{u:g})"
    if kind == "expo":
        mu = spec[1]
        return (lambda: random.expovariate(1.0 / mu)), mu, 2.0 * mu * mu, f"expo({mu:g})"
    if kind == "two":
        p, x, y = spec[1], spec[2], spec[3]
        def g():
            return x if random.random() < p else y
        return g, p * x + (1 - p) * y, p * x * x + (1 - p) * y * y, f"two({p:g},{x:g},{y:g})"
    raise ValueError(spec)

# ----------------------------------------------------------- Haar orthogonal
def haar_rows(m, rng):
    """Orthonormal rows via Gram-Schmidt on a Gaussian matrix (Haar up to signs;
    sign convention is irrelevant for U B U^T)."""
    U = []
    for _ in range(m):
        v = [rng.gauss(0.0, 1.0) for _ in range(m)]
        for u in U:
            d = 0.0
            for a, b in zip(u, v):
                d += a * b
            for i in range(m):
                v[i] -= d * u[i]
        n = math.sqrt(sum(x * x for x in v))
        U.append([x / n for x in v])
    return U

def phi_abab_rotated(m, av, bv, s, t, rng):
    """phi( (A+sI) (U B U^T + tI) (A+sI) (U B U^T + tI) ) with Haar U."""
    U = haar_rows(m, rng)
    # W = U B  (B tridiagonal)  -> W[i][j] = U[i][j-1]*bv[j-1] + U[i][j+1]*bv[j]
    W = [[0.0] * m for _ in range(m)]
    for i in range(m):
        Ui, Wi = U[i], W[i]
        for j in range(m):
            x = 0.0
            if j >= 1:
                x += Ui[j - 1] * bv[j - 1]
            if j + 1 < m:
                x += Ui[j + 1] * bv[j]
            Wi[j] = x
    # Bp = W U^T   (the only O(m^3) step)
    Bp = [[0.0] * m for _ in range(m)]
    for i in range(m):
        Wi, Bpi = W[i], Bp[i]
        for j in range(m):
            Uj = U[j]
            ssum = 0.0
            for a, b in zip(Wi, Uj):
                ssum += a * b
            Bpi[j] = ssum
        if t:
            Bpi[i] += t
    # C = (A + sI) Bp ; A tridiagonal
    C = [[0.0] * m for _ in range(m)]
    for i in range(m):
        Ci = C[i]
        lo = Bp[i - 1] if i >= 1 else None
        hi = Bp[i + 1] if i + 1 < m else None
        al = av[i - 1] if i >= 1 else 0.0
        ah = av[i] if i + 1 < m else 0.0
        Bpi = Bp[i]
        for j in range(m):
            x = s * Bpi[j]
            if lo is not None:
                x += al * lo[j]
            if hi is not None:
                x += ah * hi[j]
            Ci[j] = x
    tr = 0.0
    for i in range(m):
        Ci = C[i]
        for j in range(m):
            tr += Ci[j] * C[j][i]
    return tr / m

# ------------------------------------------------------------------- workers
def work_pair(args):
    m, specA, specB, reps, seed, s, t = args
    random.seed(seed)
    gA, EA, EA2, nA = make_dist(specA)
    gB, EB, EB2, nB = make_dist(specB)
    vals = []
    for _ in range(reps):
        av = [gA() for _ in range(m - 1)]
        bv = [gB() for _ in range(m - 1)]
        vals.append(phi_abab_sparse(m, av, bv, s, t))
    n = len(vals)
    mu = sum(vals) / n
    var = sum((v - mu) ** 2 for v in vals) / (n - 1) if n > 1 else 0.0
    return dict(m=m, distA=nA, distB=nB, EA=EA, EA2=EA2, EB=EB, EB2=EB2,
                reps=n, mean=mu, sem=math.sqrt(var / n), s=s, t=t)

def work_free(args):
    m, reps, seed, s, t = args
    rng = random.Random(seed)
    av = [1.0] * (m - 1)
    bv = [1.0] * (m - 1)
    vals = [phi_abab_rotated(m, av, bv, s, t, rng) for _ in range(reps)]
    n = len(vals)
    mu = sum(vals) / n
    var = sum((v - mu) ** 2 for v in vals) / (n - 1) if n > 1 else 0.0
    return dict(m=m, reps=n, mean=mu, sem=math.sqrt(var / n), s=s, t=t)

# ----------------------------------------------------------- weighted 2-fit
def wls2(rows):
    """fit y = c1*x1 + c2*x2 with weights 1/sem^2; returns (c1,c2,se1,se2)."""
    s11 = s12 = s22 = b1 = b2 = 0.0
    for x1, x2, y, se in rows:
        w = 1.0 / (se * se)
        s11 += w * x1 * x1; s12 += w * x1 * x2; s22 += w * x2 * x2
        b1 += w * x1 * y;   b2 += w * x2 * y
    det = s11 * s22 - s12 * s12
    c1 = (s22 * b1 - s12 * b2) / det
    c2 = (s11 * b2 - s12 * b1) / det
    return c1, c2, math.sqrt(s22 / det), math.sqrt(s11 / det)

# ------------------------------------------------------------------ main
def main():
    out = {}
    NPROC = 14

    # ---- CONTROL 0: sparse harness == dense O(m^3) matmul, exactly
    random.seed(11)
    ctl = []
    for m in (12, 25, 40):
        for (s, t) in ((0.0, 0.0), (1.0, -0.5)):
            av = [random.uniform(0.2, 2.0) for _ in range(m - 1)]
            bv = [random.uniform(0.2, 2.0) for _ in range(m - 1)]
            a = phi_abab_sparse(m, av, bv, s, t)
            d = phi_abab_dense(m, av, bv, s, t)
            ctl.append(dict(m=m, s=s, t=t, sparse=a, dense=d, absdiff=abs(a - d),
                            reldiff=abs(a - d) / abs(d)))
    out["control_sparse_vs_dense"] = ctl

    # ---- CONTROL 1: exact finite-m expectation for a deterministic pair
    # alpha=beta=1 => Tr(ABAB) is deterministic; predicted 2(m-1)+4(m-2)
    det = []
    for m in (10, 50, 200):
        v = phi_abab_sparse(m, [1.0] * (m - 1), [1.0] * (m - 1))
        pred = (2.0 * (m - 1) + 4.0 * (m - 2)) / m
        det.append(dict(m=m, observed=v, predicted_finite_m=pred, absdiff=abs(v - pred)))
    out["control_deterministic_exact_count"] = det

    # ---- MAIN: random ensembles, several distributions, several m
    specs = [("const", 1.0), ("unif", 2.0), ("expo", 1.0), ("two", 0.5, 0.5, 1.5),
             ("const", math.sqrt(2.0)), ("two", 0.5, 0.1, 1.9), ("unif", 3.0),
             ("expo", 0.5), ("two", 0.25, 0.4, 2.4), ("const", 0.7)]
    pairs = [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7),
             (2, 4), (4, 2), (0, 2), (6, 7), (8, 3), (9, 6), (5, 8), (1, 4)]
    jobs, meta = [], []
    seed = 1000
    for m, reps in ((200, 2000), (1000, 800), (4000, 300)):
        for (ia, ib) in pairs:
            seed += 1
            jobs.append((m, specs[ia], specs[ib], reps, seed, 0.0, 0.0))
    with Pool(NPROC) as p:
        res = p.map(work_pair, jobs)
    out["ensembles"] = res

    # ---- fit coefficients, per m, against both the asymptotic and the
    #      exact finite-m design (which carries the (1-1/m),(1-2/m) factors)
    fits = {}
    for m in sorted(set(r["m"] for r in res)):
        rows_as, rows_fm = [], []
        for r in res:
            if r["m"] != m:
                continue
            if r["sem"] <= 0.0:
                continue      # deterministic pair: zero variance, handled exactly above
            se = r["sem"]
            x1 = r["EA2"] * r["EB2"]
            x2 = (r["EA"] ** 2) * (r["EB"] ** 2)
            rows_as.append((x1, x2, r["mean"], se))
            rows_fm.append((x1 * (1 - 1.0 / m), x2 * (1 - 2.0 / m), r["mean"], se))
        c1, c2, e1, e2 = wls2(rows_as)
        d1, d2, f1, f2 = wls2(rows_fm)
        fits[str(m)] = dict(asymptotic_design=dict(c1=c1, c2=c2, se_c1=e1, se_c2=e2),
                            finite_m_design=dict(c1=d1, c2=d2, se_c1=f1, se_c2=f2))
    out["coefficient_fits"] = fits

    # ---- residuals of each ensemble against the exact finite-m prediction
    resid = []
    for r in res:
        m = r["m"]
        pred = 2.0 * (1 - 1.0 / m) * r["EA2"] * r["EB2"] + \
               4.0 * (1 - 2.0 / m) * (r["EA"] ** 2) * (r["EB"] ** 2)
        z = (r["mean"] - pred) / r["sem"] if r["sem"] > 0 else None
        resid.append(dict(m=m, distA=r["distA"], distB=r["distB"], mean=r["mean"],
                          sem=r["sem"], predicted=pred, absdiff=abs(r["mean"] - pred), z=z))
    out["residuals_vs_exact"] = resid
    zs = [abs(x["z"]) for x in resid if x["z"] is not None]
    out["residual_z_summary"] = dict(n=len(zs), max_abs_z=max(zs),
                                     mean_abs_z=sum(zs) / len(zs))

    # ---- POSITIVE CONTROL: genuinely free pair (Haar-rotated B)
    # (i)  s=t=0: freeness predicts 0 ; tensor/banded pair predicts ~6
    # (ii) s=t=1: freeness predicts a NONZERO value, so the harness is shown
    #      to track the free formula rather than merely returning zero.
    freejobs = []
    sd = 5000
    for m, reps in ((100, 36), (200, 24), (400, 12), (800, 6)):
        for (s, t) in ((0.0, 0.0), (1.0, 1.0)):
            for k in range(6):
                sd += 1
                freejobs.append((m, max(1, reps // 6), sd, s, t))
    with Pool(NPROC) as p:
        fres = p.map(work_free, freejobs)
    # merge chunks with the same (m,s,t)
    agg = {}
    for r in fres:
        key = (r["m"], r["s"], r["t"])
        agg.setdefault(key, []).append(r)
    free_rows = []
    for (m, s, t), rs in sorted(agg.items()):
        n = sum(r["reps"] for r in rs)
        mu = sum(r["mean"] * r["reps"] for r in rs) / n
        # pooled sem from chunk means (conservative)
        sem = math.sqrt(sum((r["sem"] ** 2) * (r["reps"] ** 2) for r in rs)) / n
        phi_a = s
        phi_b = t
        phi_a2 = 2.0 * (m - 1) / m + s * s
        phi_b2 = 2.0 * (m - 1) / m + t * t
        free_pred = phi_a2 * phi_b ** 2 + phi_a ** 2 * phi_b2 - phi_a ** 2 * phi_b ** 2
        unrot = phi_abab_sparse(m, [1.0] * (m - 1), [1.0] * (m - 1), s, t)
        free_rows.append(dict(m=m, s=s, t=t, reps=n, rotated_mean=mu, rotated_sem=sem,
                              free_prediction=free_pred,
                              z_vs_free=(mu - free_pred) / max(sem, 1e-12),
                              unrotated_same_seed_value=unrot,
                              z_unrotated_vs_free=(unrot - free_pred) / max(sem, 1e-12)))
    out["free_positive_control"] = free_rows

    json.dump(out, sys.stdout, indent=1)

if __name__ == "__main__":
    main()
