"""GATE PREDICTOR v3.1 -- the phi-weighted channel mixture.  PURE; pinned for the
second blind gate (seeds 109-116, never generated anywhere at pin time).

THE LAW (all derived; the only inputs beyond analytic tables are the training deme,
the anchor r2_train, and the per-seed selection threshold, each a design/reported
input declared below):

  Channel mixture at amplitude level:
    ratio(t->j) = [ phi * sqrt(R_self) + (1 - phi) * sqrt(R_lam) ]^2

  R_self = (1 + rho_tj) / (1 + CV2_t)     -- the self-tagged channel law: selection
      tilt proportional to significance cancels the mean factors, leaving the
      ascertained fourth-moment scatter statistics (fourth_moment_ascertained.json;
      exact incomplete-Beta conditioning of the degree-4 hierarchy).

  R_lam  = (sum_w DD_tj / sum_w DD_tt)^2 * (H_tt/H_jj)^2  -- the tagged channel law
      (panelTransportRatio over the three production separations; gate_tables.json).

  phi = P(clump index is the causal itself | region survives) -- the winner's-curse
      flip probability: with tag Z-scores decomposing as r Z_c + sqrt(1-r^2) eps, a
      tag at LD r beats the causal w.p. Phi(-z sqrt((1-r)/(1+r))); phi(z) is the
      product over effective-independent tags on both sides, with the r-profile read
      from the train-deme DD(rho) sweep (grid2d_rho_sweep.json) and the DECLARED
      discretization: tag spacing = the separation at which the r^2 profile halves
      (computed from the same tables, = 4.6 kb here; 54 effective tags per side).
      z = sqrt(chi2_1 quantile of the seed's selected p-threshold), a reported
      design output of the pipeline (sidecar pt.best_p_threshold).

  AUC via the Gaussian liability chart at prevalence 0.15 with the v1 variance law
  (declared secondary; the ratio bar is primary).

DEVELOPMENT DISCLOSURE (spent gate seeds 101-108, direction checks, never gate
evidence): pure-lambda +0.261 +/- 0.101; pure self-tag -0.264 +/- 0.098; this
mixture -0.127 +/- 0.096.  The derivation chain is sections 1-6 of
SELFTAG_DERIVATION.md.

BARS for the second gate, pre-filed: P1 seed-level mean transport-ratio residual
within 3 seed-sems of zero (phenoC primary, phenoA secondary); P2 same for AUC
(secondary; its variance law is declared unrepaired).  Interpretation fixed now:
a residual beyond bars that is NEGATIVE indicts the phi derivation's independence
discretization (too much self weight); POSITIVE indicts the tagged-channel panel
representation; AUC-only failure indicts the variance law, already the named next
object.
"""
import json
import math
import bisect
from statistics import NormalDist

ND = NormalDist()
PREV = 0.15
N_TRAIN = 5000
N_OTHER = 250
NREF = 10000.0
C0 = 1e-8
WINDOW_BP = 250000.0
TO = "/projects/standard/hsiehph/sauer354/theory-out"


def load_all():
    return {
        "gt": json.load(open(f"{TO}/gate_tables.json")),
        "asc": json.load(open(f"{TO}/fourth_moment_ascertained.json")),
        "sweep": json.load(open(f"{TO}/grid2d_rho_sweep.json")),
    }


def _g(tab, i, j):
    return tab.get(f"{i}_{j}", tab.get(f"{j}_{i}"))


def _profile(sweep):
    rhog = sorted((float(k[3:]) for k in sweep["production"]), key=float)
    dd0 = {}
    for r in rhog:
        for row in sweep["production"]["rho%g" % r]["DD_canonical_table"]:
            if int(row[0]) == 0 and int(row[1]) == 0:
                dd0[r] = float(row[2])
                break

    def r2prof(rho):
        if rho <= rhog[0]:
            return 1.0
        if rho >= rhog[-1]:
            return max(dd0[rhog[-1]] / dd0[rhog[0]], 1e-12)
        k = bisect.bisect_right(rhog, rho) - 1
        r0, r1 = rhog[k], rhog[k + 1]
        f = (rho - r0) / (r1 - r0)
        a, b = dd0[r0] / dd0[rhog[0]], dd0[r1] / dd0[rhog[0]]
        return math.exp((1 - f) * math.log(max(a, 1e-12)) + f * math.log(max(b, 1e-12)))
    return r2prof


def derive_phi(tables, p_threshold):
    from scipy.stats import chi2
    r2prof = _profile(tables["sweep"])
    rho_of = lambda x: 4 * NREF * C0 * x
    half = None
    x = 100.0
    while x <= WINDOW_BP:
        if r2prof(rho_of(x)) < 0.5:
            half = x
            break
        x += 100.0
    step = half if half else 25000.0
    xs = []
    x = step / 2
    while x <= WINDOW_BP:
        xs.append(x)
        x += step
    z = math.sqrt(chi2.isf(p_threshold, 1))
    p = 1.0
    for x in xs:
        r = math.sqrt(max(r2prof(rho_of(x)), 0.0))
        gq = math.sqrt(max((1 - r) / (1 + r), 1e-12))
        p *= (1 - ND.cdf(-z * gq)) ** 2
    return p


def chart_auc(rr, prevalence):
    import numpy as np
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


def predict(tables, train_deme, r2_train, p_threshold):
    gt, asc = tables["gt"], tables["asc"]
    H = gt["H"]
    DDs = list(gt["DD"].values())
    D = gt["D"]
    m1 = lambda i: asc["m1"][str(i)]
    cr = lambda i, j: asc["cross"][f"{min(i, j)}_{max(i, j)}"]
    phi = derive_phi(tables, p_threshold)
    w = {j: (N_TRAIN if j == train_deme else N_OTHER) for j in range(D)}
    wtot = sum(w.values())
    for j in w:
        w[j] /= wtot
    t = train_deme
    sum_tt = sum(_g(dd, t, t) for dd in DDs)
    T_pool = sum(w[a] * w[b] * _g(H, a, b) for a in range(D) for b in range(D))
    T_within = sum(w[a] * _g(H, a, a) for a in range(D))
    Fbar = 1 - T_within / T_pool
    out = {"phi": phi}
    cv2t = cr(t, t) / m1(t) ** 2 - 1
    for j in range(D):
        if j == t:
            continue
        r_self = (1 + (cr(t, j) / (m1(t) * m1(j)) - 1)) / (1 + cv2t)
        sum_tj = sum(_g(dd, t, j) for dd in DDs)
        r_lam = (sum_tj / sum_tt) ** 2 * (_g(H, t, t) / _g(H, j, j)) ** 2
        ratio = (phi * math.sqrt(max(r_self, 0.0))
                 + (1 - phi) * math.sqrt(max(r_lam, 0.0))) ** 2
        Tjp = sum(w[k] * _g(H, j, k) for k in range(D))
        v = (_g(H, j, j) / Tjp) / (1 + Fbar)
        rr = math.sqrt(max(min(ratio * r2_train, 0.999), 0.0)) * math.sqrt(v / (v + 1.0))
        out[j] = {"ratio": ratio, "r_self": r_self, "r_lam": r_lam,
                  "r2": ratio * r2_train, "auc": chart_auc(rr, PREV)}
    return out
