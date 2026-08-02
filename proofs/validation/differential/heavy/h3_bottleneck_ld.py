#!/usr/bin/env python3
"""HEAVY 3 -- LD excess after a bottleneck, the quantity with no closed form.

DECIDES: `LDDecayTheory.excessLDAfterBottleneck` (LDDecayTheory.lean:660) and
`DemographicHistory.bottleneckExcessLD` (DemographicHistory.lean:685).  These
replaced `bottleneckLDAmplification`, which was falsified at up to 3.3x.  Both
replacements are marked UNTESTED.

WHY THIS IS IN THE STOCHASTIC TIER AND NOT THE ANALYTIC ONE
    Under a size change there is no closed-form sigma_d^2.  The analytic tier
    can only supply the two equilibria the trajectory travels between, and a
    check whose tolerance is wide enough to hold between them cannot fail.
    That is why no analytic check for these two definitions was written; a
    toothless check that reports AGREE is worse than an acknowledged gap.

WHAT TO SIMULATE
    Neutral two-locus Wright-Fisher (the h2 engine) with a piecewise-constant
    size history: N_r for a long burn-in, then N_b for t_b generations, then
    N_r again for t_r generations.

WHAT TO MEASURE
    sigma_d^2 at the end, and the ratio to the pre-bottleneck stationary value,
    as a function of (N_b, t_b, t_r, c).

WHAT THE DEFINITIONS PREDICT
    Iterating `driftLDStep` at N_b for t_b generations from the N_r (or N_b)
    equilibrium, then at N_r for t_r generations.  The script computes both
    corpus predictions alongside the measurement.

THE CAN-FAIL CLAUSE
    Three asymmetries are mandatory.
    1.  N_b must be far below N_r -- use N_b/N_r = 1/20.  With N_b ~ N_r the
        bottleneck equilibrium and the recovery equilibrium coincide, the
        trajectory is flat, and every candidate recursion reproduces a
        constant.  This is the exact shape of the earlier false validation.
    2.  t_b must be comparable to N_b, not to N_r.  If t_b << N_b nothing
        happens and the answer is the starting value; if t_b >> N_b the answer
        is the bottleneck equilibrium and the check degenerates into the
        equilibrium check already done analytically.  The informative window
        is t_b in [0.2 N_b, 3 N_b] and the grid must straddle it.
    3.  The c grid must span rho = 4 N_b c from below 1 to above 20.  The
        predicted amplification saturates at 1/(1+4Nc); a tightly-linked-only
        grid sits on the saturated plateau where all candidates agree.
    A run in which the measured ratio never departs from 1 by more than the
    replicate noise means the design failed condition 1 or 2 and must be
    rerun, NOT that the definitions are validated.

EXPECTED RUNTIME
    ~90 min on 16 cores.  4 c x 3 t_b x 3 t_r x 400 replicates, burn-in
    20*N_r generations at N_r = 5000.  This is the most expensive item in the
    queue; run it after h1 and h2.

REQUIREMENTS
    numpy only.
"""

import json

import numpy as np

import h2_ld_equilibrium as h2   # reuse the validated two-locus engine

N_R = 5000
N_B = 250
T_BS = [50, 250, 750]
T_RS = [0, 100, 1000]
RHOS_AT_NB = [0.5, 2.0, 8.0, 30.0]
REPS = 400


def sigma_d2(x):
    pA = x[:, 0] + x[:, 1]
    pB = x[:, 0] + x[:, 2]
    D = x[:, 0] * x[:, 3] - x[:, 1] * x[:, 2]
    return float((D ** 2).mean() / (pA * (1 - pA) * pB * (1 - pB)).mean())


def step_block(x, ne, c, gens, rng):
    n = 2 * ne
    m = h2.MU
    M = np.array([
        [(1 - m) ** 2, m * (1 - m), m * (1 - m), m * m],
        [m * (1 - m), (1 - m) ** 2, m * m, m * (1 - m)],
        [m * (1 - m), m * m, (1 - m) ** 2, m * (1 - m)],
        [m * m, m * (1 - m), m * (1 - m), (1 - m) ** 2],
    ])
    for _ in range(gens):
        D = x[:, 0] * x[:, 3] - x[:, 1] * x[:, 2]
        x = x + c * np.stack([-D, D, D, -D], axis=1)
        x = np.clip(x @ M.T, 0, None)
        x /= x.sum(axis=1, keepdims=True)
        x = np.stack([rng.multinomial(n, xi) for xi in x]).astype(np.float64) / n
    return x


def lean_prediction(n_b, n_r, c, t_b, t_r):
    """driftLDStep iterated: the corpus's own prediction, computed here."""
    def eq(ne):
        a = (1 - c) ** 2
        return a / (2 * ne) / (1 - a * (1 - 1 / (2 * ne)))

    def run(q, ne, t):
        a = (1 - c) ** 2
        for _ in range(t):
            q = a * (1 / (2 * ne) + (1 - 1 / (2 * ne)) * q)
        return q

    return run(run(eq(n_r), n_b, t_b), n_r, t_r)


def main():
    rng = np.random.default_rng(20260802)
    out = []
    for rho in RHOS_AT_NB:
        c = rho / (4.0 * N_B)
        x = rng.multinomial(2 * N_R, [0.25] * 4, size=REPS).astype(np.float64) / (2 * N_R)
        x = step_block(x, N_R, c, 20 * N_R, rng)
        base = sigma_d2(x)
        for t_b in T_BS:
            xb = step_block(x.copy(), N_B, c, t_b, rng)
            for t_r in T_RS:
                xr = step_block(xb.copy(), N_R, c, t_r, rng) if t_r else xb
                rec = dict(
                    rho_at_Nb=rho, c=c, t_b=t_b, t_r=t_r,
                    sigma_d2_pre=base,
                    sigma_d2_post=sigma_d2(xr),
                    ratio_measured=sigma_d2(xr) / base,
                    lean_excessLDAfterBottleneck=lean_prediction(N_B, N_R, c, t_b, t_r),
                    lean_ratio=lean_prediction(N_B, N_R, c, t_b, t_r) / base,
                )
                out.append(rec)
                print(json.dumps(rec), flush=True)
    json.dump(out, open("h3_results.json", "w"), indent=1)


if __name__ == "__main__":
    main()
