"""GATE PREDICTOR v3.2 -- the selection-conditioned winner-location integral.
PURE; pinned for the third blind gate (seeds 117-124, never generated at pin time).

THE LAW (SELFTAG_DERIVATION.md section 8; every predecessor recovered as a limit):
    ratio(t->j) = [ SUM_x P_win(x; z) * a_tj(x) ]^2
  P_win: winner-location distribution of the correlated Gaussian significance field
      (single-causal decomposition Z(x) = r(x) Z_c + eta(x), Cov(eta) = R - r r^T
      with R from the DD rho-profile; threshold-limited conditioning max in
      [z, z+0.5); effect-size prior chi-square-1 at scales 0.7/1.0/1.4 pooled --
      robustness across scales is part of the record).  Evaluated by fixed-seed
      Monte Carlo (rng seed 20260812, 4000 draws per scale) -- a deterministic
      numerical evaluation of a defined expectation with stated convergence, like
      quadrature; not data simulation.
  a_tj(x) = sqrt(R_self(t,j)) * [DD_tj(rho(x))/DD_tt(rho(x))] / [DD_tj(0)/DD_tt(0)]
      -- the regression-conditional amplitude, continuous to the self channel at
      x = 0; R_self from the exact ascertained fourth moments.
  AUC via the Gaussian liability chart with the v1 variance law (this chain PASSED
  gate 2 at -0.009 +/- 0.012 and is unchanged).

DEVELOPMENT DISCLOSURE (spent seeds 101-116, direction only, never evidence):
  v1 +0.261, v3 -0.264, v3.1 -0.127, THIS LAW -0.102 +/- 0.057.

BARS pre-filed: P1 seed-level mean transport-ratio residual within 3 seed-sems
(phenoC primary); P2 same for AUC.  Interpretations fixed: negative beyond bars
indicts the amplitude normalization (the reg0 reference) or the effect-size prior;
positive indicts the winner density's tail mass; AUC-only indicts the variance law.
"""
import json, math, bisect
import numpy as np
from statistics import NormalDist

ND = NormalDist()
PREV = 0.15
N_TRAIN = 5000
N_OTHER = 250
NREF = 1e4
C0 = 1e-8
TO = "/projects/standard/hsiehph/sauer354/theory-out"


def load_all():
    sw = json.load(open(f"{TO}/grid2d_rho_sweep.json"))
    rhog = sorted((float(k[3:]) for k in sw["production"]), key=float)
    tabs = {r: {} for r in rhog}
    for r in rhog:
        for row in sw["production"]["rho%g" % r]["DD_canonical_table"]:
            tabs[r][(int(row[0]), int(row[1]))] = float(row[2])
    return {"gt": json.load(open(f"{TO}/gate_tables.json")),
            "asc": json.load(open(f"{TO}/fourth_moment_ascertained.json")),
            "rhog": rhog, "tabs": tabs}


def _interp(rhog, vals, rho):
    if rho <= rhog[0]:
        return vals[0]
    if rho >= rhog[-1]:
        return vals[-1]
    k = bisect.bisect_right(rhog, rho) - 1
    f = (rho - rhog[k]) / (rhog[k + 1] - rhog[k])
    a, b = vals[k], vals[k + 1]
    if a > 0 and b > 0:
        return math.exp((1 - f) * math.log(a) + f * math.log(b))
    return (1 - f) * a + f * b


def _win_density(tables, z):
    rhog, tabs = tables["rhog"], tables["tabs"]
    r2p = [tabs[r][(0, 0)] / tabs[rhog[0]][(0, 0)] for r in rhog]
    rho_of = lambda x: 4 * NREF * C0 * abs(x)

    def rprof(x):
        return 1.0 if x == 0 else math.sqrt(max(_interp(rhog, r2p, rho_of(x)), 1e-12))
    xs = np.concatenate([-np.geomspace(500, 250000, 60)[::-1], [0],
                         np.geomspace(500, 250000, 60)])
    rv = np.array([rprof(x) for x in xs])
    n = len(xs)
    R = np.eye(n)
    for i in range(n):
        for j in range(i + 1, n):
            R[i, j] = R[j, i] = rprof(abs(xs[i] - xs[j]))
    C = R - np.outer(rv, rv)
    L = np.linalg.cholesky(C + 1e-9 * np.eye(n))
    rng = np.random.default_rng(20260812)
    locs = np.zeros(n)
    acc = 0
    for scale in (0.7, 1.0, 1.4):
        for _ in range(4000):
            zc = rng.normal() * math.sqrt(scale) * z
            Z = rv * zc + L @ rng.normal(size=n)
            X = Z * Z
            mx = X.max()
            if z * z <= mx < (z + 0.5) ** 2:
                locs[np.argmax(X)] += 1
                acc += 1
    return xs, locs / max(acc, 1)


def chart_auc(rr, prevalence):
    rr = max(min(abs(rr), 0.999), 0.0)
    xs = np.linspace(-8, 8, 2001)
    ph = np.exp(-xs ** 2 / 2) / math.sqrt(2 * math.pi)
    sig = math.sqrt(max(1 - rr ** 2, 1e-12))
    T = ND.inv_cdf(1 - prevalence)
    pc = np.array([ND.cdf((rr * x - T) / sig) for x in xs])
    Kh = float(np.trapezoid(ph * pc, xs))
    fc = ph * pc / Kh
    f0 = ph * (1 - pc) / (1 - Kh)
    F0 = np.cumsum(f0) * (xs[1] - xs[0])
    return float(np.trapezoid(fc * F0, xs))


def _g(tab, i, j):
    return tab.get(f"{i}_{j}", tab.get(f"{j}_{i}"))


def predict(tables, train_deme, r2_train, p_threshold):
    from scipy.stats import chi2
    gt, asc = tables["gt"], tables["asc"]
    rhog, tabs = tables["rhog"], tables["tabs"]
    H = gt["H"]
    D = gt["D"]
    m1 = lambda i: asc["m1"][str(i)]
    cra = lambda i, j: asc["cross"][f"{min(i, j)}_{max(i, j)}"]
    z = round(math.sqrt(chi2.isf(p_threshold, 1)), 1)
    xs, Pw = _win_density(tables, z)
    rho_of = lambda x: 4 * NREF * C0 * abs(x)
    w = {j: (N_TRAIN if j == train_deme else N_OTHER) for j in range(D)}
    wtot = sum(w.values())
    for j in w:
        w[j] /= wtot
    t = train_deme
    T_pool = sum(w[a] * w[b] * _g(H, a, b) for a in range(D) for b in range(D))
    T_within = sum(w[a] * _g(H, a, a) for a in range(D))
    Fbar = 1 - T_within / T_pool
    cv2t = cra(t, t) / m1(t) ** 2 - 1
    out = {"z": z}
    for j in range(D):
        if j == t:
            continue
        r_self = (1 + (cra(t, j) / (m1(t) * m1(j)) - 1)) / (1 + cv2t)
        regv = [tabs[r][(min(t, j), max(t, j))] / tabs[r][(t, t)] for r in rhog]
        reg0 = regv[0]
        amp = np.array([math.sqrt(max(r_self, 0.0)) *
                        (_interp(rhog, regv, rho_of(x)) / reg0) for x in xs])
        ratio = float((Pw * amp).sum()) ** 2
        Tjp = sum(w[k] * _g(H, j, k) for k in range(D))
        v = (_g(H, j, j) / Tjp) / (1 + Fbar)
        rr = math.sqrt(max(min(ratio * r2_train, 0.999), 0.0)) * math.sqrt(v / (v + 1.0))
        out[j] = {"ratio": ratio, "r2": ratio * r2_train, "auc": chart_auc(rr, PREV)}
    return out
