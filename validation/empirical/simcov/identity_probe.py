"""The replication probe: separates a MEASUREMENT from an ALGEBRAIC IDENTITY.

Why this exists. `verdict.classify` has a SELF-TEST gate, and it fires only when
prediction and truth agree to machine precision in every cell. That catches a
formula compared against a transcription of itself. It does NOT catch the case
where the ORACLE is algebraically pinned to the body while still carrying Monte
Carlo noise, because the noise keeps the two numbers from ever being bit-equal.

Three of those escaped in one sitting, all scored MATCH:

  `driftVariance = p0(1-p0)*fst` against simulated `Var(p)`, where the fst fed
      in was the measured heterozygosity ratio. Given only the Wright-Fisher
      martingale property `E[p_t] = p0`, `p0(1-p0)(1 - H_t/H_0)` reduces
      IDENTICALLY to `Var(p_t)`. Nothing was on trial.

  `haplotypeHomozygosity = sum f_i^2` against the rate at which two independent
      draws match. For independent draws `P(a=b) = sum_i P(a=i)P(b=i)` is the
      definition of independence, not a consequence of the body.

  `multiTraitEffectiveSampleSize = n1 + rg^2 n2` against the realised variance
      of a combined estimator -- built with weights `w2 = n2 rg^2`, which makes
      `Var = 1/(n1 + rg^2 n2)` come out by construction.

THE SIGNATURE. Let `d(N) = |lean - truth|` at replicate count `N`, and
`z(N) = d(N)/sem(N)`. Since `sem ~ N^(-1/2)`:

  * an IDENTITY has no systematic part, so `d(N) ~ N^(-1/2)`: quadrupling `N`
    halves the residual, and `z` stays O(1) forever -- it never resolves,
    however long it runs.
  * a GENUINE match with a real bias `b` has `d(N) -> b > 0`, so `d` flattens
    and `z ~ b*N^(1/2)` GROWS. Even a bias too small to matter shows up as
    growth in `z`.
  * a genuine EXACT law (bias truly zero) also has `d ~ N^(-1/2)`, and is
    indistinguishable from an identity by this probe alone. That is the honest
    limit and it is reported as INCONCLUSIVE, not as a pass.

So the probe reruns one cell at `N` and `4N` and reads the ratio `d(N)/d(4N)`,
which is ~2 for a null-bias law and ~1 for a biased one, together with the
growth of `z`.

CALIBRATION. A gate with no control is not evidence, so `main` runs the probe
against three designs known to be identities and one known to be a genuine
measurement, and reports whether each is classified correctly.
"""
import math

import numpy as np


def probe(run_cell, n_small, factor=16, seed=0):
    """`run_cell(n, seed) -> (lean, truth, sem)` at replicate count `n`.

    Returns a verdict dict. The same seed stream is NOT reused across the two
    replicate counts, so the two residuals are independent draws.

    The discriminator is the GROWTH OF z, not the residual ratio. `|lean -
    truth|` is itself a random variable with order-100% scatter, so the ratio of
    two single residuals is far too noisy to threshold -- it misclassified a
    known identity on the first calibration run. `z` at high replication is the
    stable statistic: it is bounded for an identity and unbounded for a bias.
    """
    lean1, truth1, sem1 = run_cell(n_small, seed)
    lean2, truth2, sem2 = run_cell(n_small * factor, seed + 977)
    d1, d2 = abs(lean1 - truth1), abs(lean2 - truth2)
    z1 = d1 / sem1 if sem1 > 0 else float("inf")
    z2 = d2 / sem2 if sem2 > 0 else float("inf")
    ratio = d1 / d2 if d2 > 0 else float("inf")
    if z2 > 3.0:
        verdict = "MEASUREMENT (bias resolves with replication)"
    else:
        verdict = ("IDENTITY OR EXACT LAW (no bias visible at %dx replication)"
                   % factor)
    return dict(d1=d1, d2=d2, z1=z1, z2=z2, ratio=ratio,
                expected=math.sqrt(factor), verdict=verdict)


# ---------------------------------------------------------------------------
# calibration cases
# ---------------------------------------------------------------------------

def cell_drift_variance(n, seed):
    """KNOWN IDENTITY: p0(1-p0)(1 - H_t/H_0) is Var(p) given E[p_t] = p0."""
    rng = np.random.default_rng(seed)
    Ne, p0, t = 100, 0.3, 40
    p = np.full(n, float(p0))
    for _ in range(t):
        p = rng.binomial(2 * Ne, p) / (2.0 * Ne)
    het_t = float(np.mean(2 * p * (1 - p)))
    het_0 = 2 * p0 * (1 - p0)
    fst = 1.0 - het_t / het_0
    var = float(np.var(p, ddof=1))
    return p0 * (1 - p0) * fst, var, var * math.sqrt(2.0 / (n - 1))


def cell_haplotype_homozygosity(n, seed):
    """KNOWN IDENTITY: P(two independent draws match) = sum f_i^2."""
    rng = np.random.default_rng(seed)
    freq = np.array([0.7, 0.2, 0.07, 0.03])
    a = rng.choice(len(freq), size=n, p=freq)
    b = rng.choice(len(freq), size=n, p=freq)
    match = float(np.mean(a == b))
    return float(np.sum(freq ** 2)), match, math.sqrt(match * (1 - match) / n)


def cell_multitrait_neff(n, seed):
    """KNOWN IDENTITY: the combining weights force Var = 1/(n1 + rg^2 n2)."""
    rng = np.random.default_rng(seed)
    n1, n2, rg, beta1 = 2000, 8000, 0.5, 0.1
    b1 = beta1 + rng.normal(0, 1 / math.sqrt(n1), n)
    b2 = rg * beta1 + rng.normal(0, 1 / math.sqrt(n2), n)
    w1, w2 = n1, n2 * rg ** 2
    est = (w1 * b1 + w2 * (b2 / rg)) / (w1 + w2)
    var = float(est.var(ddof=1))
    neff = 1.0 / var
    return n1 + rg ** 2 * n2, neff, neff * math.sqrt(2.0 / (n - 1))


def cell_hwe_variance_biased(n, seed):
    """KNOWN MEASUREMENT with a real (small) bias: the claim is 2p(1-p) but the
    oracle draws dosages with a deliberate 3% excess variance, so a systematic
    discrepancy exists and must resolve with replication."""
    rng = np.random.default_rng(seed)
    p = 0.3
    g = rng.binomial(2, p, n).astype(float) * math.sqrt(1.03)
    v = float(g.var(ddof=1))
    return 2 * p * (1 - p), v, v * math.sqrt(2.0 / (n - 1))


def main():
    cases = [
        ("driftVariance [known identity]", cell_drift_variance, 20000),
        ("haplotypeHomozygosity [known identity]",
         cell_haplotype_homozygosity, 200000),
        ("multiTraitEffectiveSampleSize [known identity]",
         cell_multitrait_neff, 4000),
        ("hweGenotypeVariance +3% [known measurement]",
         cell_hwe_variance_biased, 200000),
    ]
    print("%-46s %9s %9s %7s %7s  %s"
          % ("case", "d(N)", "d(4N)", "z(N)", "z(4N)", "verdict"))
    ok = 0
    for name, fn, n in cases:
        r = probe(fn, n, seed=4242)
        expect_identity = "known identity" in name
        got_identity = r["verdict"].startswith("IDENTITY")
        correct = expect_identity == got_identity
        ok += correct
        print("%-46s %9.2e %9.2e %7.2f %7.2f  %s  %s"
              % (name, r["d1"], r["d2"], r["z1"], r["z2"], r["verdict"],
                 "OK" if correct else "MISCLASSIFIED"))
    print("\ncalibration: %d/%d classified correctly" % (ok, len(cases)))


if __name__ == "__main__":
    main()
