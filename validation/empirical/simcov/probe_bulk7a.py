"""Does battery_bulk7's drift simulator implement the process selectedDriftFactor
describes?  A positive control that CAN fail, and that fails for the reason the
row would fail.

selectedDriftFactor is `(1 - 1/(2Ne) + s)^t`: a CONSTANT per-generation multiplier
on heterozygosity.  The battery's `s_corr` branch instead applies, after each
Wright-Fisher generation, the map

    p <- 0.5 - (0.5 - p) * sqrt(1 - s)

which contracts the deviation from one half.  Writing `H = 2p(1-p) = 0.5 - 2d^2`
with `d = p - 0.5`, that map sends `H -> H + s(0.5 - H)`: AFFINE toward a fixed
point, not a multiplication.  Composed with drift the recurrence is

    H_{t+1} = (1 - 1/(2Ne)) (1 - s) H_t + 0.5 s

whose solution is `H* + (H_0 - H*) a^t` with `a = (1-1/(2Ne))(1-s)` and
`H* = 0.5 s / (1 - a)`.  That is a different function of t from the body's, and
it agrees with it only at `s = 0`.

So this script predicts the SIMULATOR from its own code, independently of the
body, and prints three columns: what the simulator does, what the body says, and
what the affine model says.  If the measurement tracks the affine model and not
the body, the row's disagreement is a property of the design and not of the
definition, and the gate that refused to call it FALSIFIED was right.

The error bar is also recomputed. The battery asserts `sem = obs * 0.006` -- a
flat 0.6 percent of the value, written rather than measured -- while it has 400
replicates in hand. The block sem over those replicates is printed beside it.
"""
import math

import numpy as np

DESIGNS = ((200, 0.0, 60), (200, 0.001, 60), (500, 0.0005, 100))
N_LOCI, REPS = 3000, 400


def run_cell(Ne, s_corr, t, seed):
    """The battery's loop, transcribed, with per-replicate retention kept."""
    rng = np.random.default_rng(seed)
    two_n = int(2 * Ne)
    p = np.full((REPS, N_LOCI), 0.5)
    H0 = float((2 * p * (1 - p)).mean())
    for _ in range(t):
        p = rng.binomial(two_n, p) / two_n
        if s_corr:
            p = p + s_corr * (0.5 - p) * 0.0 + 0.0     # the battery's no-op
            het = 2 * p * (1 - p)                      # the battery's dead line
            boost = s_corr
            p = 0.5 - (0.5 - p) * math.sqrt(max(1.0 - boost, 0.0))
    per_rep = (2 * p * (1 - p)).mean(axis=1) / H0
    return float(per_rep.mean()), float(per_rep.std(ddof=1) / math.sqrt(REPS))


def affine(Ne, s, t):
    """What the battery's own map does to E[H]/H0, derived from its code."""
    a = (1.0 - 1.0 / (2.0 * Ne)) * (1.0 - s)
    if s == 0.0:
        return a ** t
    Hstar = 0.5 * s / (1.0 - a)
    H0 = 0.5
    return (Hstar + (H0 - Hstar) * a ** t) / H0


print("%-22s %12s %12s %12s %12s %12s"
      % ("cell", "simulated", "body", "affine", "sem(reps)", "sem(asserted)"))
for Ne, s, t in DESIGNS:
    obs, sem = run_cell(Ne, s, t, 16101)
    body = (1 - 1 / (2 * Ne) + s) ** t
    aff = affine(Ne, s, t)
    print("%-22s %12.6f %12.6f %12.6f %12.6f %12.6f"
          % ("Ne=%d s=%.4f t=%d" % (Ne, s, t), obs, body, aff, sem, obs * 0.006))
    print("%-22s %12s %12.2f %12.2f"
          % ("", "sems off:", abs(obs - body) / sem, abs(obs - aff) / sem))
