"""Check the genotype sign bias against its closed form.

SCOPE, AND A RETRACTION

An earlier version of this script measured the variance ratio of a sliding-window
design against a disjoint one, to test a predicted coupling inflation
2 b^2 / (1 - b^2). That prediction has been retracted upstream: the argument behind
it used a theta = 1/2 weight where the level-one computation needs another, and at
the correct weights the first-order cross term exposes E[x^4], which the hub channel
already exposes. The term is hub-redundant rather than a separate channel, so there
is no separate inflation to measure and that arm of the script has been removed.

Do not resurrect it from git history without checking whether a replacement mechanism
has been supplied. As of this writing none has.

WHAT REMAINS, AND WHY IT IS WORTH RUNNING

The sign bias itself is untouched by the retraction. It is a property of the genotype
law, and Descent.EpistaticChaos.hweSignBias_eq proves

    b = E[x |x|] = (1 - 2q)^2    for q <= 1/2,

where x is the standardized genotype. This script draws Hardy-Weinberg genotypes,
standardizes them, and checks the measured b against that closed form across an
allele-frequency sweep. It tests the corpus's arithmetic against sampled data, which
is the one thing here a simulation can still falsify.

CONTROLS PINNED BY THEORY, NOT BY SIMULATION

  1. MAF 0.5 forces b = 0, because the standardized coordinate is symmetric there
     (Descent.EpistaticChaos.standardizedGenotype_symmetric_iff) and b vanishes
     exactly on symmetric laws. A nonzero reading there is a harness fault.
  2. The exact three-point law's b is computed from the probabilities directly, with
     no sampling, and must equal (1 - 2q)^2 to machine precision. If that fails, the
     closed form or the standardization is wrong rather than the sampler.
  3. E[x] = 0 and E[x^2] = 1 are checked on the same samples. Both are proved
     (standardizedGenotype_expectation_zero, standardizedGenotype_second_moment_one),
     so they separate "the sampler is wrong" from "the sign bias is wrong".

Python 3.6.8, numpy only. No scipy, no 3.7+ syntax.
"""

from __future__ import print_function

import numpy as np

MAFS = [0.5, 0.35, 0.211324865, 0.10, 0.05, 0.01]
INDIVIDUALS = 2000000
CHUNK = 250000
SEED = 20260802

# Monte Carlo error on a mean from N samples is about 1/sqrt(N), which is 7e-4 here.
# Five times that leaves headroom at rare MAF, where the coordinate is heavy tailed,
# without being vacuous.
SAMPLING_TOLERANCE = 0.0035
EXACT_TOLERANCE = 1e-12


def genotype_law(q):
    """Standardized genotype law at alternative-allele frequency q."""
    p = 1.0 - q
    probs = np.array([p * p, 2.0 * p * q, q * q])
    dosage = np.array([0.0, 1.0, 2.0])
    variance = 2.0 * q * p
    values = (dosage - 2.0 * q) / np.sqrt(variance)
    return probs, values


def exact_sign_bias(probs, values):
    """b = E[x |x|] over the three-point law, with no sampling."""
    return float(np.sum(probs * values * np.abs(values)))


def sampled_moments(q, rng):
    """Measure E[x], E[x^2] and E[x |x|] from drawn genotypes."""
    probs, values = genotype_law(q)
    thresholds = np.cumsum(probs)

    total_first = 0.0
    total_second = 0.0
    total_signed = 0.0
    remaining = INDIVIDUALS
    while remaining > 0:
        n = min(CHUNK, remaining)
        remaining -= n
        draws = rng.random_sample(n)
        codes = np.searchsorted(thresholds, draws, side="right")
        np.clip(codes, 0, 2, out=codes)
        x = values[codes]
        total_first += float(x.sum())
        total_second += float((x * x).sum())
        total_signed += float((x * np.abs(x)).sum())

    n_total = float(INDIVIDUALS)
    return total_first / n_total, total_second / n_total, total_signed / n_total


def main():
    rng = np.random.RandomState(SEED)
    failures = []

    print("genotype sign bias against its closed form")
    print("N = {0}, seed = {1}".format(INDIVIDUALS, SEED))
    print("")
    header = "{0:>10} {1:>11} {2:>11} {3:>11} {4:>10} {5:>10} {6:>8}".format(
        "MAF", "b closed", "b exact", "b sampled", "E[x]", "E[x^2]", "verdict")
    print(header)
    print("-" * len(header))

    for q in MAFS:
        probs, values = genotype_law(q)
        b_closed = (1.0 - 2.0 * q) ** 2
        b_exact = exact_sign_bias(probs, values)
        first, second, b_sampled = sampled_moments(q, rng)

        # Control 2: no sampling involved, so this is the corpus's arithmetic.
        if abs(b_exact - b_closed) > EXACT_TOLERANCE:
            failures.append(
                "MAF {0}: exact three-point b is {1:.15f} against closed form "
                "{2:.15f}; the closed form or the standardization is wrong".format(
                    q, b_exact, b_closed))

        # Control 3: the sampler itself.
        if abs(first) > SAMPLING_TOLERANCE:
            failures.append(
                "MAF {0}: sampled E[x] = {1:.5f}, must be 0; the sampler is wrong "
                "rather than the sign bias".format(q, first))
        if abs(second - 1.0) > SAMPLING_TOLERANCE:
            failures.append(
                "MAF {0}: sampled E[x^2] = {1:.5f}, must be 1; the sampler is wrong "
                "rather than the sign bias".format(q, second))

        ok = abs(b_sampled - b_closed) <= SAMPLING_TOLERANCE
        if not ok:
            failures.append(
                "MAF {0}: sampled b = {1:.5f} against closed form {2:.5f}".format(
                    q, b_sampled, b_closed))

        # Control 1: symmetry at the balanced locus forces b = 0.
        if abs(q - 0.5) < 1e-12 and abs(b_sampled) > SAMPLING_TOLERANCE:
            failures.append(
                "MAF 0.5 control: sampled b = {0:.5f} where symmetry forces 0; "
                "the harness is wrong, not the theory".format(b_sampled))

        print("{0:>10.6f} {1:>11.6f} {2:>11.6f} {3:>11.6f} {4:>10.5f} {5:>10.5f} "
              "{6:>8}".format(q, b_closed, b_exact, b_sampled, first, second,
                              "ok" if ok else "MISS"))

    print("")
    if failures:
        print("FAILURES ({0}):".format(len(failures)))
        for line in failures:
            print("  " + line)
    else:
        print("all checks passed, including the three theory-pinned controls")


if __name__ == "__main__":
    main()
