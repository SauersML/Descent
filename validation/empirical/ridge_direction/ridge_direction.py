#!/usr/bin/env python3
"""Settle the effective-ridge direction for the robust objective

    J(phi) = (||(phi - 1) S|| + r)^2 + tau^2 ||phi||^2 .

Two candidates for the effective ridge eta in the filter phi = S^2/(S^2 + eta):

    DEFLATED (Descent/Decision/TransportedMinimax.lean):  eta = tau^2 a/(a+r)
    INFLATED (upstream manuscript):                        eta = tau^2 (1 + r/a)

with a = ||(phi-1)S|| at the optimum.  They are reciprocal about tau^2.

Three independent instruments, in increasing generality:

  A. EXACT rational arithmetic, scalar case.  The interior stationary point is a
     rational function of (S, tau, r), so the whole comparison is done in
     fractions.Fraction with no tolerance anywhere.
  B. Direct numerical minimisation, scalar case.
  C. Direct numerical minimisation, genuine multi-mode vector case with a
     spectrum of S values.  The ridge-filter FORM is itself tested here: the
     per-mode backed-out eta_i must agree across modes, which is not automatic.

POSITIVE CONTROL: r = 0 is run first in every instrument.  Both candidates must
collapse to exactly tau^2 there; if they do not the harness is wrong.
"""

import json
import math
from fractions import Fraction as F

import numpy as np
from scipy.optimize import minimize

OUT = {}

# ----------------------------------------------------------------------------
# A. exact rational arithmetic, scalar case
# ----------------------------------------------------------------------------
# For scalar S > 0, tau, r >= 0 and an interior optimum (phi < 1, so a > 0):
#     J(phi) = (S(1-phi) + r)^2 + tau^2 phi^2
#     J'(phi) = -2 S (S(1-phi)+r) + 2 tau^2 phi = 0
#  => phi* = S(S+r) / (S^2 + tau^2)                       [exact rational]
#     a*   = S(1-phi*) = S(tau^2 - S r)/(S^2 + tau^2)
# The interior branch is valid iff a* > 0, i.e. tau^2 > S r.
# Backing out the ridge from the filter form phi = S^2/(S^2+eta):
#     eta_measured = S^2 (1 - phi*)/phi*                  [exact rational]


def exact_scalar(S: F, tau2: F, r: F):
    denom = S * S + tau2
    phi = S * (S + r) / denom
    a = S * (1 - phi)
    interior = a > 0
    eta_meas = S * S * (1 - phi) / phi if phi != 0 else None
    eta_defl = tau2 * a / (a + r) if (a + r) != 0 else None
    eta_infl = tau2 * (1 + r / a) if a != 0 else None
    return dict(
        S=S, tau2=tau2, r=r, phi=phi, a=a, interior=interior,
        eta_meas=eta_meas, eta_defl=eta_defl, eta_infl=eta_infl,
        matches_deflated=(eta_meas == eta_defl),
        matches_inflated=(eta_meas == eta_infl),
    )


def run_exact():
    rows = []
    Ss = [F(1), F(1, 2), F(2), F(3, 7)]
    tau2s = [F(1, 100), F(1, 10), F(1), F(4), F(9, 5)]
    # r = 0 FIRST: the positive control.
    rs = [F(0), F(1, 1000), F(1, 100), F(1, 10), F(1, 2), F(1), F(3)]
    n_interior = 0
    n_defl = 0
    n_infl = 0
    control_ok = True
    for S in Ss:
        for tau2 in tau2s:
            for r in rs:
                res = exact_scalar(S, tau2, r)
                if not res["interior"]:
                    continue
                n_interior += 1
                n_defl += bool(res["matches_deflated"])
                n_infl += bool(res["matches_inflated"])
                if r == 0:
                    # positive control: both candidates must be exactly tau^2
                    if not (res["eta_defl"] == tau2 and res["eta_infl"] == tau2
                            and res["eta_meas"] == tau2):
                        control_ok = False
                rows.append(dict(
                    S=str(S), tau2=str(tau2), r=str(r),
                    phi=str(res["phi"]), a=str(res["a"]),
                    eta_meas=str(res["eta_meas"]),
                    eta_defl=str(res["eta_defl"]),
                    eta_infl=str(res["eta_infl"]),
                    matches_deflated=res["matches_deflated"],
                    matches_inflated=res["matches_inflated"],
                ))
    return dict(
        method="exact rational arithmetic (fractions.Fraction), no tolerance",
        positive_control_r0_both_candidates_equal_tau2=control_ok,
        n_interior_cases=n_interior,
        n_matching_deflated=n_defl,
        n_matching_inflated=n_infl,
        rows=rows,
    )


# ----------------------------------------------------------------------------
# B/C. direct numerical minimisation
# ----------------------------------------------------------------------------

def J(phi, S, tau, r):
    a = float(np.linalg.norm((phi - 1.0) * S))
    return (a + r) ** 2 + tau ** 2 * float(phi @ phi)


def gradJ(phi, S, tau, r):
    d = (phi - 1.0) * S
    a = float(np.linalg.norm(d))
    if a == 0.0:
        return 2.0 * tau ** 2 * phi  # subgradient representative
    return 2.0 * (a + r) * (d * S) / a + 2.0 * tau ** 2 * phi


def minimise(S, tau, r, seed=0):
    rng = np.random.default_rng(seed)
    best = None
    starts = [np.ones_like(S), 0.5 * np.ones_like(S), np.zeros_like(S),
              S ** 2 / (S ** 2 + tau ** 2)]
    starts += [rng.uniform(0, 1, size=S.shape) for _ in range(8)]
    for x0 in starts:
        for meth in ("L-BFGS-B", "BFGS"):
            try:
                res = minimize(J, x0, args=(S, tau, r), jac=gradJ, method=meth,
                               options=dict(maxiter=20000, gtol=1e-14,
                                            ftol=1e-16) if meth == "L-BFGS-B"
                               else dict(maxiter=20000, gtol=1e-14))
            except Exception:
                continue
            if best is None or res.fun < best.fun:
                best = res
    return best


def analyse(S, tau, r, label, seed=0):
    res = minimise(S, tau, r, seed)
    phi = res.x
    a = float(np.linalg.norm((phi - 1.0) * S))
    eta_defl = tau ** 2 * a / (a + r) if (a + r) > 0 else float("nan")
    eta_infl = tau ** 2 * (1 + r / a) if a > 0 else float("inf")
    # back out the ridge per mode from phi_i = S_i^2/(S_i^2 + eta_i)
    with np.errstate(divide="ignore", invalid="ignore"):
        eta_i = S ** 2 * (1.0 - phi) / phi
    eta_i = eta_i[np.isfinite(eta_i)]
    eta_hat = float(np.median(eta_i))
    spread = float(np.max(eta_i) - np.min(eta_i)) if eta_i.size else float("nan")
    rel_spread = spread / abs(eta_hat) if eta_hat != 0 else float("nan")

    def rel(x):
        return abs(eta_hat - x) / abs(x) if x not in (0.0,) and np.isfinite(x) else float("nan")

    return dict(
        label=label, n_modes=int(S.size), tau=tau, r=r,
        S_min=float(S.min()), S_max=float(S.max()),
        J_opt=float(res.fun), a_opt=a,
        eta_measured=eta_hat,
        eta_per_mode_rel_spread=rel_spread,
        eta_deflated=eta_defl, eta_inflated=eta_infl,
        rel_err_vs_deflated=rel(eta_defl),
        rel_err_vs_inflated=rel(eta_infl),
        verdict=("DEFLATED" if rel(eta_defl) < rel(eta_infl) else "INFLATED")
        if np.isfinite(rel(eta_defl)) and np.isfinite(rel(eta_infl)) else "boundary",
        interior=bool(a > 1e-9),
    )


SPECTRA = {
    "scalar": np.array([1.0]),
    "scalar_S0.5": np.array([0.5]),
    "vector_powerlaw_d20": np.array([k ** -0.5 for k in range(1, 21)]),
    "vector_geometric_d12": np.array([0.85 ** k for k in range(12)]),
    "vector_wide_d8": np.array([0.05, 0.1, 0.2, 0.4, 0.8, 1.6, 3.2, 6.4]),
    "vector_flat_d30": np.ones(30),
}


def run_numeric():
    rows = []
    control = []
    taus = [0.1, 0.3, 1.0, 2.0]
    rs = [0.0, 0.001, 0.01, 0.05, 0.2, 0.5]
    for name, S in SPECTRA.items():
        for tau in taus:
            # POSITIVE CONTROL FIRST: r = 0
            c = analyse(S, tau, 0.0, f"{name}|control", seed=1)
            control.append(c)
            for r in rs[1:]:
                rows.append(analyse(S, tau, r, name, seed=1))
    interior = [x for x in rows if x["interior"]]
    return dict(
        method="direct minimisation of J by L-BFGS-B/BFGS with analytic gradient, multistart",
        positive_control_r0=dict(
            n=len(control),
            max_rel_err_vs_tau2=max(
                abs(c["eta_measured"] - c["tau"] ** 2) / c["tau"] ** 2 for c in control),
            note="at r=0 both candidates equal tau^2; the measured ridge must too",
            rows=control,
        ),
        n_interior=len(interior),
        n_verdict_deflated=sum(1 for x in interior if x["verdict"] == "DEFLATED"),
        n_verdict_inflated=sum(1 for x in interior if x["verdict"] == "INFLATED"),
        max_rel_err_vs_deflated=max(x["rel_err_vs_deflated"] for x in interior),
        max_eta_per_mode_rel_spread=max(x["eta_per_mode_rel_spread"] for x in interior),
        median_rel_err_vs_inflated=float(np.median(
            [x["rel_err_vs_inflated"] for x in interior])),
        rows=rows,
    )


if __name__ == "__main__":
    OUT["exact_scalar"] = run_exact()
    OUT["numeric"] = run_numeric()
    print(json.dumps(OUT, indent=1, default=str))
