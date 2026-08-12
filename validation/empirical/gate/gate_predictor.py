"""BLIND GATE, stage 2: the pinned analytic predictor.  PURE -- no simulation input.

Inputs: gate_tables.json (analytic moment tables, produced before any gate seed
exists), the training deme index (a design input: the pipeline draws it from the seed
before any genetics is generated), and the single declared anchor r2_train (the
training deme's own realized r2, disclosed exactly as the bounds papers disclose r0^2).

Outputs, per target deme: the transport ratio, the absolute r2, and the AUC.

LAWS (all landed in Descent before this file was pinned; no fitted constants):
  ratio(t->j)  = (sum_w DD_w[t,j] / sum_w DD_w[t,t])^2 * (H[t,t]/H[j,j])^2
                 (Coalescent.DemographicTwoLocusMoments.panelTransportRatio; the panel
                  is the three production separations rho = 0, 1, 10)
  v_j          = (1 - Fstar_j) / (1 + Fbar)   with the divergences read from H as
                 coalescence times: Fstar_j = 1 - H[j,j]/T_{j,pool},
                 T_{j,pool} = sum_k w_k H[j,k], Fbar = 1 - T_within/T_pool,
                 weights w = realized sample fractions (5000 train, 250 others)
  AUC chart    = Gaussian liability threshold model at prevalence 0.15 (phenoC's
                 global-intercept probit with unit environmental sd and unit slope on
                 the demeaned genetic liability), with score-latent correlation
                 rr = sqrt(ratio * r2_train) * sqrt(v_j/(v_j + 1)).

BARS (pre-filed here, before any gate outcome exists):
  P1  seed-level mean residual of measured-minus-predicted transport ratio within
      3 seed-sems of zero, per phenotype graded (phenoC primary).
  P2  same for AUC.
  Interpretation is fixed in advance: a uniform ratio miss indicts the ascertained
  variance factor (the named open sub-law); a pair-structured miss indicts the
  transport composition; an AUC-only miss indicts the variance law or chart inputs.
"""
import json
import math
from statistics import NormalDist

ND = NormalDist()
PREV = 0.15
N_TRAIN = 5000
N_OTHER = 250


def load_tables(path):
    return json.load(open(path))


def _g(tab, i, j):
    return tab.get(f"{i}_{j}", tab.get(f"{j}_{i}"))


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


def predict(tables, train_deme, r2_train):
    H = tables["H"]
    DDs = list(tables["DD"].values())
    D = tables["D"]
    w = {j: (N_TRAIN if j == train_deme else N_OTHER) for j in range(D)}
    wtot = sum(w.values())
    for j in w:
        w[j] /= wtot
    t = train_deme
    sum_tt = sum(_g(dd, t, t) for dd in DDs)
    T_pool = sum(w[a] * w[b] * _g(H, a, b) for a in range(D) for b in range(D))
    T_within = sum(w[a] * _g(H, a, a) for a in range(D))
    Fbar = 1 - T_within / T_pool
    out = {}
    for j in range(D):
        if j == t:
            continue
        sum_tj = sum(_g(dd, t, j) for dd in DDs)
        ratio = (sum_tj / sum_tt) ** 2 * (_g(H, t, t) / _g(H, j, j)) ** 2
        Tjp = sum(w[k] * _g(H, j, k) for k in range(D))
        v = (_g(H, j, j) / Tjp) / (1 + Fbar)
        rr = math.sqrt(max(min(ratio * r2_train, 0.999), 0.0)) * math.sqrt(v / (v + 1.0))
        out[j] = {"ratio": ratio, "r2": ratio * r2_train,
                  "v": v, "auc": chart_auc(rr, PREV)}
    return out
