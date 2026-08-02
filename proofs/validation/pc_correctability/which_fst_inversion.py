#!/usr/bin/env python3
"""Recover the spike constant under BOTH F_ST conventions, from one simulation.

`which_fst.py` established that under the Balding-Nichols panel
`bn_independent.py` draws, aggregated as a ratio of averages,

    Hudson / Nei  ->  2      (1.999 at F=0.001, 1.990 at 0.01, 1.950 at 0.05)

and that this is independent of whether the ancestral spectrum is symmetric
about 1/2 -- the asymmetric and rare-spectrum controls give the same ratio.  So
the two functionals never coincide here, and the question "did the 3.9920
validation run where the distinction is invisible" is answered NO.

That leaves an inference to close by measurement rather than by argument.
`demographicSpike n F m = 4 F m(n-m)/n` was validated at `3.9920 +/- 0.0045`
with F "measured as Hudson F_ST on the same simulated data".  If that is so and
Hudson = 2 Nei, then the same spike expressed in the Nei quantity the Lean body
actually computes needs a constant near 8, not 4.

This script does not infer it.  It runs the BBP inversion once and reports the
recovered constant against BOTH estimators from the identical genotypes, so the
two numbers come from one simulation and cannot differ by anything but the
definition.

    kappa_hudson = spike_recovered / (F_hudson * m(n-m)/n)
    kappa_nei    = spike_recovered / (F_nei    * m(n-m)/n)

The spike is recovered by inverting the BBP eigenvalue law
`lam1 = (1+s)(1+c/s)`, `c = n/M`, exactly as `analyze.py` does.

CONTROL: the aspect ratio `c = n/M` is reported alongside, because the inversion
is only meaningful above the BBP edge `s > sqrt(c)`.  Replicates below the edge
are reported and excluded rather than silently averaged in -- an inversion
attempted below the edge returns a spike that is an artifact of the bulk.
"""

from __future__ import annotations

import numpy as np

try:
    from scipy.linalg.blas import ssyrk
except Exception:  # pragma: no cover
    ssyrk = None


def hudson_fst_parametric(p1, p2):
    num = (p1 - p2) ** 2
    den = p1 * (1 - p2) + p2 * (1 - p1)
    return float(num.sum() / den.sum())


def nei_gst_parametric(p1, p2):
    pbar = 0.5 * (p1 + p2)
    within = p1 * (1 - p1) + p2 * (1 - p2)
    total = 2.0 * pbar * (1 - pbar)
    return float(1.0 - within.sum() / total.sum())


def spike_from_eigenvalue(lam, c):
    """Invert lam = (1+s)(1+c/s) for the larger root; nan below the edge."""
    b = lam - 1 - c
    disc = b * b - 4 * c
    if disc <= 0:
        return np.nan
    return (b + np.sqrt(disc)) / 2


def one_rep(n, m, M, F, seed):
    rng = np.random.default_rng(seed)
    p = rng.uniform(0.05, 0.95, size=M)
    a = p * (1 - F) / F
    b = (1 - p) * (1 - F) / F
    p1 = rng.beta(a, b)
    p2 = rng.beta(a, b)

    f_hud = hudson_fst_parametric(p1, p2)
    f_nei = nei_gst_parametric(p1, p2)

    X = np.empty((n, M), dtype=np.float32)
    for lo, hi, pr in ((0, m, p1), (m, n, p2)):
        rows = hi - lo
        u = rng.random((rows, M), dtype=np.float32)
        X[lo:hi] = (u < pr.astype(np.float32))
        u = rng.random((rows, M), dtype=np.float32)
        X[lo:hi] += (u < pr.astype(np.float32))

    c1 = X[:m].sum(axis=0, dtype=np.float64)
    c2 = X[m:].sum(axis=0, dtype=np.float64)
    phat = ((c1 + c2) / (2.0 * n)).astype(np.float32)
    keep = (phat > 0) & (phat < 1)
    if not keep.all():
        X = np.ascontiguousarray(X[:, keep])
        phat = phat[keep]
    Mk = int(keep.sum())
    X -= 2 * phat
    X *= (1.0 / np.sqrt(2 * phat * (1 - phat))).astype(np.float32)

    if ssyrk is not None:
        psi = np.asarray(ssyrk(alpha=1.0 / Mk, a=X, lower=0), dtype=np.float64)
        evals = np.linalg.eigvalsh(psi, UPLO="U")
    else:
        psi = (X @ X.T) / Mk
        evals = np.linalg.eigvalsh(psi)
    lam1 = float(evals[-1])

    cc = n / Mk
    s = spike_from_eigenvalue(lam1, cc)
    eff = m * (n - m) / n
    return dict(f_hud=f_hud, f_nei=f_nei, s=s, eff=eff, c=cc, lam1=lam1, M=Mk)


def main() -> int:
    n, m, M = 1200, 600, 60_000
    reps = 12
    print(f"n={n} m={m} M={M} reps={reps}")
    print()
    for F in (0.01, 0.02, 0.05):
        rows = [one_rep(n, m, M, F, seed=int(1000 + F * 1e5 + i)) for i in range(reps)]
        edge = np.sqrt(rows[0]["c"])
        usable = [r for r in rows if np.isfinite(r["s"]) and r["s"] > edge]
        dropped = len(rows) - len(usable)
        if not usable:
            print(f"F={F}: all {len(rows)} replicates at or below the BBP edge; no inversion.")
            continue
        kh = np.array([r["s"] / (r["f_hud"] * r["eff"]) for r in usable])
        kn = np.array([r["s"] / (r["f_nei"] * r["eff"]) for r in usable])
        fh = np.mean([r["f_hud"] for r in usable])
        fn = np.mean([r["f_nei"] for r in usable])
        se = lambda v: v.std(ddof=1) / np.sqrt(len(v))
        print(
            f"F_target={F}: c={rows[0]['c']:.4f} edge={edge:.4f} "
            f"used {len(usable)}/{len(rows)} (dropped {dropped} below edge)"
        )
        print(f"    F_hudson={fh:.5f}  F_nei={fn:.5f}  ratio={fh/fn:.4f}")
        print(f"    kappa vs HUDSON = {kh.mean():.4f} +/- {se(kh):.4f}")
        print(f"    kappa vs NEI    = {kn.mean():.4f} +/- {se(kn):.4f}")
        print()
    print("The corpus asserts kappa = 4. Whichever column lands on 4 is the")
    print("estimator demographicSpike's constant was calibrated against.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
