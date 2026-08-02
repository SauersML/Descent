"""Measure the sign-bias coupling channel of a sliding-window design.

WHAT THIS TESTS

A sliding-window interaction statistic shares loci between adjacent windows. The
corpus records such designs as tempered when their hub energy is bounded, which is
a statement about the HUB channel. There is a second channel, the COUPLING channel,
which is dead only when the coordinate law is symmetric. A standardized
Hardy-Weinberg genotype is symmetric at exactly one allele frequency, q = 1/2.

The coupling channel's strength is the conditional sign bias

    b = E[x |x|] / E[x^2],

the mean sign under the x^2-tilted law. For a standardized HWE coordinate this has a
closed form, proved in Calibrator.EpistaticChaos.hweSignBias_eq:

    b = (1 - 2q)^2    for q <= 1/2.

In the tuned sector the covariance of two window products at separation j is
b^(2 min(j, w)): the min(j, w) shared loci contribute s^2 = 1 and the 2 min(j, w)
unshared ones contribute a mean sign b each. Summing gives a variance inflation
relative to a disjoint design of

    2 b^2 / (1 - b^2)    in the many-window, wide-window limit,

which is Calibrator.EpistaticChaos.couplingVarianceInflation. That is 0 at MAF 0.5,
13122/3439 = 3.8156 at MAF 0.05, and 11529602/485199 = 23.7626 at MAF 0.01.

WHAT IS MEASURED, AND WHAT IS PREDICTED

Stage 1 measures b from simulated genotypes and checks it against the closed form.
Nothing about b is assumed: the tilted law is derived from the Hardy-Weinberg
probabilities and the standardization.

Stage 2 samples loci from that derived tilted law, forms sliding-window and disjoint
window products, and measures the ratio of their variances. Two predictions are
printed:

  * EXACT, the finite-design value for these m and w, computed from b alone. This is
    the number the simulation should hit, and it is the pass/fail target.
  * ASYMPTOTIC, 1 + 2b^2/(1 - b^2), the wide-window limit. At rare MAF the two differ
    substantially because b^(2w) is not small -- at MAF 0.01 with w = 8, b^(2w) = 0.53
    -- so a gap between EXACT and ASYMPTOTIC is expected and is not a failure.

CONTROLS PINNED BY THEORY, NOT BY SIMULATION

  1. MAF 0.5: b = 0 exactly, because the coordinate is symmetric there and the
     x^2-tilted law puts equal mass on the two homozygotes. The variance ratio must
     be exactly 1. If the arms separate at 0.5, the harness is wrong, not the theory.
  2. b measured against (1 - 2q)^2 at every frequency. This is a proved identity, so
     a mismatch localizes the fault to the sampler rather than to the mechanism.
  3. The disjoint arm's variance has the closed form 1 - b^(2w) and is checked
     against it, so a failure distinguishes "coupling is wrong" from "both arms are
     wrong".

Python 3.6.8, numpy only. No scipy, no 3.7+ syntax.
"""

from __future__ import print_function

import numpy as np

# ---------------------------------------------------------------- design constants

MAFS = [0.5, 0.35, 0.211324865, 0.10, 0.05, 0.01]
WINDOWS = 200          # m, number of windows in each arm
WIDTH = 8              # w, loci per window
INDIVIDUALS = 400000   # N, total samples
CHUNK = 50000          # samples per chunk, bounds peak memory
SEED = 20260802

# Tolerance for the theory-pinned checks. The Monte Carlo error on a variance from
# N samples is about sqrt(2/N) relative, which is 0.2 percent here; 1.5 percent
# leaves room for the heavier tails at rare MAF without being vacuous.
RELATIVE_TOLERANCE = 0.015


def genotype_law(q):
    """Standardized genotype law at alternative-allele frequency q.

    Returns (probabilities, standardized values) over homRef, het, homAlt.
    """
    p = 1.0 - q
    probs = np.array([p * p, 2.0 * p * q, q * q])
    dosage = np.array([0.0, 1.0, 2.0])
    variance = 2.0 * q * p
    centered = dosage - 2.0 * q
    values = centered / np.sqrt(variance)
    return probs, values


def sign_bias(probs, values):
    """b = E[x |x|] / E[x^2]; the denominator is 1 for a standardized coordinate."""
    return float(np.sum(probs * values * np.abs(values)) / np.sum(probs * values ** 2))


def tilted_sign_law(probs, values):
    """The x^2-tilted law's sign distribution: P(s = +1), and its mean sign.

    The tilt is derived, not assumed: weight w_g = P(g) x_g^2, normalized. Under it
    every genotype with x != 0 contributes its own sign, and the mean sign is b.
    """
    weights = probs * values ** 2
    weights = weights / np.sum(weights)
    positive = float(np.sum(weights[values > 0.0]))
    negative = float(np.sum(weights[values < 0.0]))
    return positive, positive - negative


def exact_ratio(b, m, w):
    """Finite-design variance ratio, from b alone.

    Sliding: Var = (1/m) sum_{k,l} b^(2 min(|k-l|, w)) - m b^(2w).
    Disjoint: Var = 1 - b^(2w).
    """
    separations = np.arange(1, m)
    exponents = 2.0 * np.minimum(separations, w)
    off_diagonal = 2.0 * np.sum((m - separations) * np.power(b, exponents))
    sliding = (m + off_diagonal) / float(m) - m * b ** (2 * w)
    disjoint = 1.0 - b ** (2 * w)
    return sliding, disjoint, sliding / disjoint


def asymptotic_ratio(b):
    """1 + 2 b^2 / (1 - b^2), the wide-window limit."""
    return 1.0 + 2.0 * b * b / (1.0 - b * b)


def window_products(negative_flags, m, w):
    """Products of signs over m consecutive windows of width w.

    Signs are +-1, so a window product is determined by the parity of the number of
    negative signs in it, which a cumulative sum gives in one pass.
    """
    running = np.zeros((negative_flags.shape[0], negative_flags.shape[1] + 1),
                       dtype=np.int32)
    np.cumsum(negative_flags, axis=1, out=running[:, 1:])
    parity = (running[:, w:w + m] - running[:, 0:m]) & 1
    return 1 - 2 * parity


def simulate(q, rng):
    """Measure the sliding-vs-disjoint variance ratio in the tuned sector."""
    probs, values = genotype_law(q)
    positive, b_tilt = tilted_sign_law(probs, values)

    sliding_loci = WINDOWS + WIDTH - 1
    disjoint_loci = WINDOWS * WIDTH

    totals = {"slide_sum": 0.0, "slide_sq": 0.0, "disj_sum": 0.0, "disj_sq": 0.0}
    remaining = INDIVIDUALS
    while remaining > 0:
        n = min(CHUNK, remaining)
        remaining -= n

        draws = rng.random_sample((n, sliding_loci))
        flags = (draws >= positive).astype(np.int32)
        slide = window_products(flags, WINDOWS, WIDTH)
        slide_stat = slide.sum(axis=1) / np.sqrt(float(WINDOWS))

        draws = rng.random_sample((n, disjoint_loci))
        flags = (draws >= positive).astype(np.int32).reshape(n, WINDOWS, WIDTH)
        parity = flags.sum(axis=2) & 1
        disj_stat = (1 - 2 * parity).sum(axis=1) / np.sqrt(float(WINDOWS))

        totals["slide_sum"] += float(slide_stat.sum())
        totals["slide_sq"] += float((slide_stat ** 2).sum())
        totals["disj_sum"] += float(disj_stat.sum())
        totals["disj_sq"] += float((disj_stat ** 2).sum())

    n_total = float(INDIVIDUALS)
    slide_var = totals["slide_sq"] / n_total - (totals["slide_sum"] / n_total) ** 2
    disj_var = totals["disj_sq"] / n_total - (totals["disj_sum"] / n_total) ** 2
    return b_tilt, slide_var, disj_var


def main():
    rng = np.random.RandomState(SEED)
    failures = []

    print("sliding-window sign-bias coupling")
    print("m = {0} windows, w = {1} loci, N = {2}, seed = {3}".format(
        WINDOWS, WIDTH, INDIVIDUALS, SEED))
    print("")
    header = "{0:>8} {1:>9} {2:>9} {3:>10} {4:>10} {5:>11} {6:>10}".format(
        "MAF", "b closed", "b tilted", "ratio obs", "ratio exact", "ratio asympt",
        "verdict")
    print(header)
    print("-" * len(header))

    for q in MAFS:
        probs, values = genotype_law(q)
        b_closed = (1.0 - 2.0 * q) ** 2
        b_moment = sign_bias(probs, values)

        # Control 2: the closed form is a proved identity.
        if abs(b_moment - b_closed) > 1e-10:
            failures.append(
                "MAF {0}: measured sign bias {1:.10f} against closed form {2:.10f}; "
                "the standardization or the law is wrong".format(
                    q, b_moment, b_closed))

        b_tilt, slide_var, disj_var = simulate(q, rng)
        slide_exact, disj_exact, ratio_exact = exact_ratio(b_closed, WINDOWS, WIDTH)
        ratio_obs = slide_var / disj_var
        ratio_asym = asymptotic_ratio(b_closed)

        ok = abs(ratio_obs - ratio_exact) <= RELATIVE_TOLERANCE * ratio_exact

        # Control 3: the disjoint arm alone.
        if abs(disj_var - disj_exact) > RELATIVE_TOLERANCE * max(disj_exact, 1e-12):
            failures.append(
                "MAF {0}: disjoint arm variance {1:.6f} against closed form "
                "{2:.6f}; both arms are suspect, not just the coupling".format(
                    q, disj_var, disj_exact))

        # Control 1: the symmetric frequency forces the ratio to exactly 1.
        if abs(q - 0.5) < 1e-12:
            if abs(b_tilt) > 1e-12:
                failures.append(
                    "MAF 0.5: tilted mean sign is {0:.3e}, must be 0 by "
                    "symmetry".format(b_tilt))
            if abs(ratio_obs - 1.0) > RELATIVE_TOLERANCE:
                failures.append(
                    "MAF 0.5 control: ratio {0:.4f} against a theory-forced 1.0; "
                    "the harness is wrong, not the theory".format(ratio_obs))

        print("{0:>8.4f} {1:>9.5f} {2:>9.5f} {3:>10.4f} {4:>11.4f} {5:>11.4f} "
              "{6:>10}".format(q, b_closed, b_tilt, ratio_obs, ratio_exact,
                               ratio_asym, "ok" if ok else "MISS"))

        if not ok:
            failures.append(
                "MAF {0}: ratio {1:.4f} against exact prediction {2:.4f}".format(
                    q, ratio_obs, ratio_exact))

    print("")
    print("EXACT is the pass/fail target. ASYMPT is the wide-window limit and differs")
    print("from EXACT when b^(2w) is not small, which at MAF 0.01 with w = 8 is 0.53.")
    print("")

    if failures:
        print("FAILURES ({0}):".format(len(failures)))
        for line in failures:
            print("  " + line)
    else:
        print("all checks passed, including the three theory-pinned controls")


if __name__ == "__main__":
    main()
