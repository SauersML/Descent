"""
Empirical test of the m_eff prohibition.

Claim under test (Descent.PCCorrectability.ImitationCapacity):
  a participation-ratio effective-marker count is a weakly continuous
  functional of the LD spectrum and CANNOT determine a detection threshold;
  the inverse-trace certificate tr(K^-1)/m is edge-sensitive and DOES.

Witness: on m = n + n^2 markers push the n smallest eigenvalues to 1/(n+1),
a vanishing 1/(n+1) fraction of the spectrum.

Key structural fact used for speed: the whitened certificate statistic
tr(K^-1 S)/m with S = Z'Z/N and rows Z ~ N(0,K) equals the mean of N*m iid
chi-square(1) variates, so its NULL law does not depend on the spectrum at all.
Only the alternative's mean shift does, and that shift is t * v'K^-1 v, whose
isotropic expectation is t * tr(K^-1)/m -- the spike load.
"""
import numpy as np

rng = np.random.default_rng(20260802)


def li_ji_meff(lam):
    """Li & Ji (2005) / Cheverud-Nyholt: a functional of the eigenvalue
    variance, hence of normalized moments 1 and 2 only."""
    m = len(lam)
    return 1.0 + (m - 1.0) * (1.0 - np.var(lam) / m)


def certificate(lam):
    return float(np.mean(1.0 / lam))


def spectra(n):
    eps = 1.0 / (n + 1.0)
    return np.ones(n + n * n), np.concatenate([np.full(n, eps), np.ones(n * n)])


def measured_threshold(lam, N, reps=400, alpha=0.05, seed=0):
    """Simulate the certificate statistic directly and bisect for 50% power."""
    r = np.random.default_rng(seed)
    m = len(lam)
    sq, inv = np.sqrt(lam), 1.0 / lam

    def stats(t, R):
        out = np.empty(R)
        for i in range(R):
            Z = r.standard_normal((N, m)) * sq
            if t > 0:
                v = r.standard_normal(m); v /= np.linalg.norm(v)
                Z += np.sqrt(t) * np.outer(r.standard_normal(N), v)
            out[i] = np.einsum('ij,j,ij->', Z, inv, Z) / (N * m)
        return out

    crit = np.quantile(stats(0.0, reps), 1 - alpha)
    lo, hi = 1e-5, 8.0
    for _ in range(14):
        mid = np.sqrt(lo * hi)
        if np.mean(stats(mid, reps) > crit) < 0.5:
            lo = mid
        else:
            hi = mid
    return np.sqrt(lo * hi)


print(f"{'n':>3} {'m':>6} {'meff_ratio':>10} {'cert_ratio':>10} "
      f"{'measured':>10} {'max_moment_gap':>15} {'bound':>8}")
print("-" * 68)

rows = []
for n in (4, 8, 16):
    flat, pert = spectra(n)
    m = len(flat)
    meff_r = li_ji_meff(pert) / li_ji_meff(flat)
    cert_r = certificate(pert) / certificate(flat)
    gap = max(abs(np.mean(pert ** p) - np.mean(flat ** p)) for p in (1, 2, 3, 4))

    N = 3 * m
    t_flat = measured_threshold(flat, N, seed=1)
    t_pert = measured_threshold(pert, N, seed=1)
    meas = t_flat / t_pert
    rows.append((n, m, meff_r, cert_r, meas, gap))
    print(f"{n:>3} {m:>6} {meff_r:>10.4f} {cert_r:>10.4f} {meas:>10.4f} "
          f"{gap:>15.5f} {1/(n+1):>8.5f}")

print()
print("m_eff       predicts measured = meff_ratio (-> 1.0)")
print("certificate predicts measured = cert_ratio (-> 2.0)")
print()
for n, m, meff_r, cert_r, meas, gap in rows:
    e_meff = abs(meas - meff_r)
    e_cert = abs(meas - cert_r)
    print(f"n={n:<3} |measured-meff|={e_meff:.4f}   "
          f"|measured-cert|={e_cert:.4f}   "
          f"-> {'CERTIFICATE' if e_cert < e_meff else 'M_EFF'} wins")
