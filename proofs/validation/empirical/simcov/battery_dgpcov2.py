"""battery_dgpcov2: extensions.  FRESHNESS GUARD: DGPCOV2-2026-08-04-B

D2: the marker-vs-direction kappa mismatch at kappa != 1/2 and at two panel
    sizes, to rule out a coincidence at one half and a finite-n artefact.
B2: group B re-read against (d/I)/n at the INTEGER n actually simulated, so
    the rounding of n_req is not charged to the body.
"""
import json
import numpy as np
from scipy.linalg import toeplitz

GUARD = "DGPCOV2-2026-08-04-B"
out = {}


def band_share(rho, kappa):
    t = np.linspace(-np.pi, np.pi, 4_000_001)
    recip = (1 - 2 * rho * np.cos(t) + rho ** 2) / (1 + rho ** 2)
    return np.trapezoid(recip * (np.abs(t) <= np.pi * kappa), t) / np.trapezoid(recip, t)


rows = []
rng = np.random.default_rng(11)
for n in (512, 2048):
    for rho in (0.5, 0.8):
        sig = toeplitz(rho ** np.arange(n))
        w_full = np.trace(np.linalg.inv(sig))
        for step in (2, 3, 4):
            kappa = 1.0 / step
            idx = np.arange(0, n, step)
            thin = np.trace(np.linalg.inv(sig[np.ix_(idx, idx)])) / w_full
            k = len(idx) / n
            body = k - 2 * rho * np.sin(np.pi * k) / (np.pi * (1 + rho ** 2))
            r2 = rho ** step
            thin_cf = k * (1 + r2 ** 2) / (1 + r2 ** 2 * 0 + 1) / 1  # placeholder
            thin_cf = k * ((1 + r2 ** 2) / (1 - r2 ** 2)) / ((1 + rho ** 2) / (1 - rho ** 2))
            ridx = np.sort(rng.choice(n, len(idx), replace=False))
            rand = np.trace(np.linalg.inv(sig[np.ix_(ridx, ridx)])) / w_full
            rows.append(dict(n=n, rho=rho, kappa=k, body=body,
                             band_control=band_share(rho, k),
                             thinned_panel=thin, thinned_closed_form=thin_cf,
                             random_panel=rand,
                             ratio_thin_over_body=thin / body))
out["group_d2_kappa_is_markers_not_directions"] = rows

b2 = []
for fam, d, tau in (("gaussian", 5, 0.10), ("bernoulli", 5, 0.10)):
    info = 1 / 4.0 if fam == "gaussian" else 1 / (0.3 * 0.7)
    nreq = (d / info) / tau
    n = int(round(nreq))
    reps = 40000
    if fam == "gaussian":
        est = rng.normal(0, np.sqrt(4.0 / n), size=(reps, d))
    else:
        est = rng.binomial(n, 0.3, size=(reps, d)) / n - 0.3
    tmse = float((est ** 2).sum(axis=1).mean())
    se = float((est ** 2).sum(axis=1).std(ddof=1) / np.sqrt(reps))
    b2.append(dict(family=fam, d=d, tau=tau, n_req_exact=nreq, n_used=n,
                   trace_mse=tmse, se=se,
                   predicted_at_integer_n=(d / info) / n,
                   sems_vs_integer_n=abs(tmse - (d / info) / n) / se,
                   sems_vs_tau=abs(tmse - tau) / se))
out["group_b2_integer_n"] = b2
out["_guard"] = GUARD
json.dump(out, open("battery_dgpcov2_results.json", "w"), indent=1, default=float)
print("FRESHNESS=%s" % GUARD)
print(json.dumps(out, indent=1, default=float))
