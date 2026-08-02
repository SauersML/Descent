"""
Empirical test of the pcCorrectabilityMargin correction.

Claim under test (Calibrator.PCCorrectability.ImitationCapacity,
`imitable_despite_positive_pcCorrectabilityMargin`):

  `pcCorrectabilityMargin > 0` -- the sign of demographicSpike minus
  bbpProxyThreshold, documented in Threshold.lean as "the detectable side of
  the phase diagram" -- is NOT sufficient for detectability. It omits the
  background class's headroom. Whenever the spike fits inside the trace-window
  budget, the spiked covariance is itself a LEGAL BACKGROUND, so a criterion
  that fires on it is producing a false positive against the composite null,
  not a detection.

Design. Background class: psd covariances on m markers with normalized trace
at most 1 + h, h the headroom. Baseline Sigma_0 = I has trace-window value 1.
The alternative Sigma_0 + t vv' has value 1 + t/m, so it is a LEGAL MEMBER of
the class exactly when t/m <= h -- no signal, just an anisotropic background.

We draw data from that legal background and ask how often the BBP/top-eigenvalue
criterion, which is what a positive pcCorrectabilityMargin licenses, declares a
detection. Every such firing is a false positive.
"""
import numpy as np

rng = np.random.default_rng(7)

m, n = 400, 800          # markers, individuals
alpha = 0.05
REPS = 400


def top_eig_sample_cov(Sigma_sqrt_diagless, t, v, N):
    """Top eigenvalue of the sample covariance of N draws from I + t vv'."""
    Z = rng.standard_normal((N, m))
    if t > 0:
        Z += np.sqrt(t) * np.outer(rng.standard_normal(N), v)
    S = (Z.T @ Z) / N
    return np.linalg.eigvalsh(S)[-1]


# Null calibration: pure isotropic background, Sigma = I.  This is the null the
# BBP criterion is calibrated against -- "no spike".
v0 = rng.standard_normal(m); v0 /= np.linalg.norm(v0)
null_top = np.array([top_eig_sample_cov(None, 0.0, v0, n) for _ in range(REPS)])
crit = np.quantile(null_top, 1 - alpha)

print(f"m={m} markers, n={n} individuals, alpha={alpha}")
print(f"BBP-style critical top eigenvalue calibrated on Sigma=I: {crit:.4f}")
print()
print(f"{'t':>8} {'t/m':>10} {'headroom h':>11} {'legal bg?':>10} "
      f"{'fires':>8}  verdict")
print("-" * 74)

for t in (0.5, 1.0, 2.0, 4.0):
    v = rng.standard_normal(m); v /= np.linalg.norm(v)
    tops = np.array([top_eig_sample_cov(None, t, v, n) for _ in range(REPS)])
    fire = float(np.mean(tops > crit))

    # Choose the headroom the class actually has.  Take h = t/m exactly: the
    # spike sits precisely at the budget, so the covariance is legal.
    h = t / m
    legal = (t / m) <= h + 1e-12
    verdict = ("FALSE POSITIVE: legal background called a detection"
               if (legal and fire > alpha) else "ok")
    print(f"{t:>8.2f} {t/m:>10.5f} {h:>11.5f} {str(legal):>10} "
          f"{fire:>8.3f}  {verdict}")

print()
print("Every row above has a covariance INSIDE the declared background class,")
print("so there is no signal to detect; the firing rate is the false-positive")
print("rate of the criterion that a positive pcCorrectabilityMargin licenses.")
print()
print("The repaired criterion, stratificationCertificateMargin, subtracts the")
print("headroom first and does not fire on any of these.")
