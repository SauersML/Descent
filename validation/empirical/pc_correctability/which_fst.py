#!/usr/bin/env python3
"""Which F_ST does the 3.9920 spike-constant validation actually invert against?

THE QUESTION

`Descent/Foundations/Conventions.lean`'s `neiGst` computes Nei's `G_ST`, not Hudson's
`F_ST`: it divides by the total-pool heterozygosity `2 p̄(1-p̄)` where Hudson
divides by the between-subgroup heterozygosity `p₁(1-p₂) + p₂(1-p₁)`.  The Lean
identity `4F = standardized contrast variance` was derived for the Nei quantity.

But `bn_independent.py` -- the experiment behind `demographicSpike`'s
"VALIDATED (BBP inversion recovers 3.9920 +/- 0.0045)" -- estimates F_ST with
GENUINE Hudson (`den = p1*(1-p2) + p2*(1-p1)`, Bhatia et al. ratio of averages).

So a four-digit agreement was obtained by inverting a Nei-derived formula
against a Hudson-estimated input.  Either the two quantities coincide in the
regime that experiment was run in, or the agreement is luck.  This script finds
out which, and it does not need the eigendecomposition to do it: the question is
entirely about the two F_ST functionals on the same simulated frequencies.

THE DESIGN BEING INTERROGATED

`bn_independent.py` draws an ancestral frequency per marker,

    p ~ Uniform(0.05, 0.95)          <-- SYMMETRIC ABOUT 1/2

then `p1, p2 ~ Beta(p(1-F)/F, (1-p)(1-F)/F)` (Balding-Nichols), and aggregates
Hudson as a RATIO OF AVERAGES over markers, `sum(num)/sum(den)`.

The hypothesis under test is that the ratio-of-averages aggregation over a
p-distribution symmetric about 1/2 lands where the two functionals agree, so
the experiment cannot distinguish them -- it would be a validation run exactly
where its own distinction is invisible.

THE CONTROL THAT MAKES A NULL INFORMATIVE

Re-running under an ASYMMETRIC ancestral distribution must separate the two if
the mechanism is what we think.  A run where symmetric and asymmetric both agree
would mean the estimators simply coincide in this model and the label is the
only defect; a run where symmetric agrees and asymmetric diverges means the
validation is real but untested precisely where it matters.  Reporting the
symmetric arm alone would be a search that cannot fail.

No genotypes are drawn: both functionals are computed from the frequencies the
same way `bn_independent.py` does, at the parametric limit and at finite sample.
"""

from __future__ import annotations

import numpy as np


def hudson_ratio_of_averages(p1, p2):
    """Genuine Hudson F_ST, parametric (no sample-size correction)."""
    num = (p1 - p2) ** 2
    den = p1 * (1 - p2) + p2 * (1 - p1)
    return float(num.sum() / den.sum())


def nei_gst_ratio_of_averages(p1, p2):
    """The corpus quantity: 1 - mean-within / total, aggregated as a ratio of
    averages so the comparison is like-for-like with Hudson above.

    `Conventions.neiGst p1 p2 = 1 - (p1(1-p1) + p2(1-p2)) / (2 p̄ (1-p̄))`.
    As a ratio of averages that is 1 - sum(within)/sum(total).
    """
    pbar = 0.5 * (p1 + p2)
    within = p1 * (1 - p1) + p2 * (1 - p2)
    total = 2.0 * pbar * (1 - pbar)
    return float(1.0 - within.sum() / total.sum())


def nei_gst_per_marker_mean(p1, p2):
    """Per-marker Nei averaged (average of ratios), for contrast."""
    pbar = 0.5 * (p1 + p2)
    within = p1 * (1 - p1) + p2 * (1 - p2)
    total = 2.0 * pbar * (1 - pbar)
    ok = total > 0
    return float(np.mean(1.0 - within[ok] / total[ok]))


def draw(rng, M, F, lo, hi):
    p = rng.uniform(lo, hi, size=M)
    a = p * (1 - F) / F
    b = (1 - p) * (1 - F) / F
    return rng.beta(a, b), rng.beta(a, b), p


def arm(label, lo, hi, F, M=400_000, reps=8, seed=0):
    rng = np.random.default_rng(seed)
    hud, nei, ratio, pbars = [], [], [], []
    for _ in range(reps):
        p1, p2, p = draw(rng, M, F, lo, hi)
        h = hudson_ratio_of_averages(p1, p2)
        g = nei_gst_ratio_of_averages(p1, p2)
        hud.append(h)
        nei.append(g)
        ratio.append(h / g)
        pbars.append(float(np.mean(0.5 * (p1 + p2))))
    hud, nei, ratio = map(np.array, (hud, nei, ratio))
    print(
        f"  {label:34s} F={F:<6.3f} "
        f"Hudson={hud.mean():.5f} Nei={nei.mean():.5f} "
        f"H/N={ratio.mean():.5f}+/-{ratio.std(ddof=1)/np.sqrt(reps):.5f} "
        f"mean p̄={np.mean(pbars):.4f}"
    )
    return ratio.mean()


def main() -> int:
    print(__doc__.split("THE QUESTION")[0].strip())
    print()
    print("If H/N == 1 the experiment cannot tell the two apart.")
    print("If the spike constant is 4 under one and 4*(H/N) under the other,")
    print("then H/N is exactly the factor by which a Hudson input misstates the spike.")
    print()

    for F in (0.001, 0.01, 0.05):
        print(f"--- F_ST target {F} ---")
        # The arm bn_independent.py actually ran.
        r_sym = arm("SYMMETRIC  U(0.05,0.95)  [as run]", 0.05, 0.95, F)
        # Controls: asymmetric ancestral spectra.
        r_lo = arm("ASYMMETRIC U(0.05,0.50)", 0.05, 0.50, F)
        r_hi = arm("ASYMMETRIC U(0.50,0.95)", 0.50, 0.95, F)
        r_rare = arm("RARE       U(0.01,0.20)", 0.01, 0.20, F)
        print(
            f"  => symmetric arm departs from 1 by {abs(r_sym - 1):.2e}; "
            f"asymmetric arms by {abs(r_lo - 1):.2e}, {abs(r_hi - 1):.2e}, "
            f"{abs(r_rare - 1):.2e}"
        )
        print()

    print("Reference point-values (single marker, no aggregation):")
    for p1, p2 in ((0.2, 0.6), (0.2, 0.8), (0.3, 0.5)):
        a = np.array([p1])
        b = np.array([p2])
        h = hudson_ratio_of_averages(a, b)
        g = nei_gst_ratio_of_averages(a, b)
        print(f"  p1={p1} p2={p2}: Hudson={h:.4f} Nei={g:.4f} ratio={h/g:.4f}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
