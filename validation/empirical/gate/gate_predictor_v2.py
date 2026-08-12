"""GATE PREDICTOR v2 -- the derived continuum panel, replacing the pinned three-atom
panel that the first gate run indicted (verdict at gate_verdict_seeds101-108.json:
every residual positive, ratio +0.261, AUC +0.077/+0.086 -- the pinned panel
under-weighted the tight pairs the real clumped panel concentrates on).

THE DERIVED PANEL LAW (leading-order ascertainment, no fitted constants):
  A clump index tag at tag--causal separation x is selected in proportion to its
  expected GWAS signal, whose noncentrality scales with E[D^2] at that separation in
  the TRAINING deme -- the within-source DD curve itself.  Tag--causal candidate
  pairs are uniform in x under uniform marker density, truncated by the clump window
  W = 250 kb.  So the panel's separation density is
      w(x) dx  proportional to  DD_tt(rho(x)) dx,   x in (0, W],
  and the transport ratio's panel sums become window integrals:
      S_tj = INT_0^W  w(x) DD_tj(rho(x)) dx,
      ratio(t->j) = (S_tj / S_tt)^2 * (H_tt / H_jj)^2.
  Equivalently: the numerator weight is DD_tt * DD_tj and the denominator weight is
  DD_tt^2 -- selection enters both sides once, alignment enters the numerator once.
  This is the panelTransportRatio law with the panel supplied by the ascertainment
  physics instead of by fiat.  The selection-conditioning correction beyond leading
  order (E[D_t D_j | D_t^2 large] deviating from DD_tj) is an order-6/8 moment and is
  NOT included; if a re-gate residual survives, that term is the pre-declared next
  suspect, ahead of any variance refinement.

Numerics: DD(rho) is supplied on a rho grid from the validated sparse operator
pipeline; integrals are trapezoid in x with rho(x) = 4 N c0 x, N = 3000,
c0 = 1e-8 per bp, interpolating DD log-linearly in rho between grid points.

Variance law and AUC chart are unchanged from v1 (gate_predictor.py).

DEVELOPMENT-REFUTED AS A GATE CANDIDATE (spent gate seeds 101-108, direction check
only, never a validation): this panel law moves BOTH bars the wrong way -- ratio
residual +0.467 +/- 0.098 versus v1's +0.261, AUC +0.120 versus +0.077.  Reality
behaves like a panel concentrated even TIGHTER than DD^2-weighting, which is exactly
the pre-declared next-order term above: selection-conditioning on realized D^2
(winner's curse toward high-D pairs) tilts the surviving panel beyond the
expected-signal density.  Two consequences filed before any further attempt: the
next candidate must carry the selection-conditioning correction (an order-6/8 moment
object) rather than any reweighting of expected DD; and the v1 three-atom panel's
better grade is understood -- its sums are dominated by the rho = 0 atom, an
accidental proxy for a maximally tight panel.  This file is retained as the graded
record of the refuted intermediate, not offered for pinning.
"""
import json
import math
import bisect
from statistics import NormalDist

ND = NormalDist()
PREV = 0.15
N_TRAIN = 5000
N_OTHER = 250
WINDOW_BP = 250000.0
N_DEME = 3000.0
C0 = 1e-8


def load_tables(path):
    return json.load(open(path))


def _g(tab, i, j):
    return tab.get(f"{i}_{j}", tab.get(f"{j}_{i}"))


def _interp_dd(rho_grid, dd_vals, rho):
    """log-linear in rho between grid points; flat extrapolation at the ends."""
    if rho <= rho_grid[0]:
        return dd_vals[0]
    if rho >= rho_grid[-1]:
        return dd_vals[-1]
    k = bisect.bisect_right(rho_grid, rho) - 1
    r0, r1 = rho_grid[k], rho_grid[k + 1]
    f = (rho - r0) / (r1 - r0)
    a, b = dd_vals[k], dd_vals[k + 1]
    if a > 0 and b > 0:
        return math.exp((1 - f) * math.log(a) + f * math.log(b))
    return (1 - f) * a + f * b


def panel_sums(tables, t, j, nx=400):
    grid = tables["rho_grid"]
    DDg = tables["DD_by_rho"]
    tt = [_g(DDg[str(r)], t, t) for r in grid]
    tj = [_g(DDg[str(r)], t, j) for r in grid]
    s_tj = s_tt = 0.0
    dx = WINDOW_BP / nx
    for k in range(nx):
        x = (k + 0.5) * dx
        rho = 4 * N_DEME * C0 * x
        w = _interp_dd(grid, tt, rho)
        s_tt += w * w * dx
        s_tj += w * _interp_dd(grid, tj, rho) * dx
    return s_tj, s_tt


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
    D = tables["D"]
    w = {j: (N_TRAIN if j == train_deme else N_OTHER) for j in range(D)}
    wtot = sum(w.values())
    for j in w:
        w[j] /= wtot
    t = train_deme
    T_pool = sum(w[a] * w[b] * _g(H, a, b) for a in range(D) for b in range(D))
    T_within = sum(w[a] * _g(H, a, a) for a in range(D))
    Fbar = 1 - T_within / T_pool
    out = {}
    for j in range(D):
        if j == t:
            continue
        s_tj, s_tt = panel_sums(tables, t, j)
        ratio = (s_tj / s_tt) ** 2 * (_g(H, t, t) / _g(H, j, j)) ** 2
        Tjp = sum(w[k] * _g(H, j, k) for k in range(D))
        v = (_g(H, j, j) / Tjp) / (1 + Fbar)
        rr = math.sqrt(max(min(ratio * r2_train, 0.999), 0.0)) * math.sqrt(v / (v + 1.0))
        out[j] = {"ratio": ratio, "r2": ratio * r2_train,
                  "v": v, "auc": chart_auc(rr, PREV)}
    return out
