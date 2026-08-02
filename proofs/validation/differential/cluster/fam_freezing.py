#!/usr/bin/env python3
"""Freezing transition: the lattice ghost of mass e^{-1/kappa}. numpy only.

WHAT THIS IS ABOUT, AND WHAT IT IS NOT ABOUT
    The model is DEPENDENCE IN THE PARAMETER along the marker sequence: the
    per-marker effect follows a correlated chain with correlation length ell,
    and genotypes are CONDITIONALLY INDEPENDENT GIVEN THE PARAMETERS.

    THIS IS NOT LINKAGE DISEQUILIBRIUM. LD is correlation between GENOTYPES at
    FIXED frequencies; this is correlation between PARAMETERS with genotypes
    independent given them. Different objects, and a result here must not be
    read as an LD result. Testing whether the same coefficient survives genuine
    genotype-level dependence is a separate experiment and a discrepancy there
    would be a finding rather than a bug.

THE PREDICTION, WHICH HAS NO FREE PARAMETER
    The score converges to a mixture of a smooth body and a LATTICE GHOST whose
    mass is the probability of no regeneration in n steps. With n/ell -> 1/kappa
    that mass is e^{-1/kappa} = e^{-n/ell}.

    The renewal here is discrete, so the EXACT finite-n mass is (1-1/ell)^(n-1)
    -- marker 1 opens a block and each of the remaining n-1 markers regenerates
    independently with probability 1/ell. e^{-n/ell} is its continuum limit.
    Both are reported. Reporting only the asymptotic form would let a finite-n
    discrepancy read as a failure of the theorem.

WHY A LATTICE GHOST EXISTS AT ALL
    Score S = sum_i beta_i g_i with g_i in {0,1,2}. If every marker shares ONE
    beta -- no regeneration anywhere -- then S = beta * sum_i g_i and sum_i g_i
    is an integer, so S lives on a lattice of span beta. If the betas differ the
    spans are incommensurate and the sum smooths out. So the ghost is exactly
    the event "no regeneration", and its mass is what the theorem predicts.

THE STATISTIC, AND THE TRAP IN IT
    For each realised parameter path, generate many genotype draws and evaluate
    the empirical characteristic function at the lattice frequency the path
    would have if it were frozen, t* = 2*pi/beta_1. A frozen path gives
    |phi| = 1; a regenerated path gives |phi| near 0. Averaging over paths
    estimates the ghost mass directly.

    THE TRAP: |phi_hat| from M draws is BIASED UPWARD and tends to 1/sqrt(M)
    even when the true |phi| is zero, so a naive version reports discreteness
    everywhere and would fit e^{-n/ell} for the wrong reason -- which is
    precisely the failure mode flagged when this was assigned. The estimator
    used is the debiased one:

        E|phi_hat|^2 = |phi|^2 + (1 - |phi|^2)/M
        =>  |phi|^2_hat = (M*|phi_hat|^2 - 1) / (M - 1),  clipped at 0

    which is unbiased for |phi|^2 and CAN REPORT ZERO. Stated before running:
    at ell = 1 it must come out at 0 within noise, and at ell >> n at 1.

TWO CONTROLS, EACH ISOLATING ONE ENDPOINT, BOTH GIVEN BY THE THEOREM
    C1  ell = 1, every marker regenerates. Ghost mass must be 0. This is the
        control the debiasing exists for: a biased statistic fails here and
        nowhere else.
    C2  ell >> n, frozen. Ghost mass must be 1, and the score must be visibly
        lattice.
    They isolate different things: C1 tests the STATISTIC (can it report
    absence), C2 tests the SIMULATOR (does a frozen chain actually freeze).
    A combined endpoint check would pass while either was broken.

CAN-FAIL CLAUSE
    The ell sweep must straddle n. For ell << n the ghost is exp(-large) and
    indistinguishable from zero; for ell >> n it saturates at 1. Only near
    ell ~ n does the predicted curve have any shape to match, and a sweep
    confined to either tail fits a constant and confirms nothing.

A THIRD CONTROL WITH A PREDICTED FAILURE
    The theory reduces the dependent case to the independent one over
    excursions between regeneration events, and it fails where there is no
    genuine renewal. A DETERMINISTIC PERIODIC chain of period ell has the same
    correlation length and NO renewal structure. The prediction is that
    e^{-n/ell} does NOT describe it. A predicted failure that fails is worth
    more than another predicted success, so it is run as a labelled arm.

numpy only. Single-threaded by environment.
"""

import json
import math
import sys

import numpy as np

Q = 0.3                # genotype frequency, fixed; the chain is in the EFFECT
N_MARKERS = 40
N_PATHS = 400
N_DRAWS = 600          # genotype draws per path, for the characteristic function
SEED = 20260802


def beta_path(n, ell, rng, mode="renewal"):
    """Effect chain with correlation length ell.

    renewal: marker 1 opens a block; each later marker regenerates with
             probability 1/ell, else copies its predecessor. This is the
             model the theorem describes.
    periodic: deterministic blocks of length ell. Same correlation length,
             NO renewal structure -- the predicted-failure arm.
    """
    b = np.empty(n)
    if mode == "renewal":
        b[0] = rng.uniform(0.5, 1.5)
        regen = rng.random(n - 1) < (1.0 / ell)
        for i in range(1, n):
            b[i] = rng.uniform(0.5, 1.5) if regen[i - 1] else b[i - 1]
        return b, bool(not regen.any())
    vals = rng.uniform(0.5, 1.5, size=int(math.ceil(n / ell)) + 1)
    for i in range(n):
        b[i] = vals[i // int(round(ell))]
    return b, bool(int(round(ell)) >= n)


def ghost_mass(n, ell, rng, mode="renewal", paths=N_PATHS, draws=N_DRAWS):
    """Debiased estimate of the lattice-component mass, plus the true frozen rate."""
    est, frozen_flags = [], []
    for _ in range(paths):
        b, frozen = beta_path(n, ell, rng, mode)
        frozen_flags.append(frozen)
        g = rng.binomial(2, Q, size=(draws, n))
        s = g @ b
        t = 2.0 * math.pi / b[0]              # lattice frequency IF frozen
        phi = np.exp(1j * t * s).mean()
        raw = float(abs(phi) ** 2)
        # debias: unbiased for |phi|^2, can report zero
        deb = (draws * raw - 1.0) / (draws - 1.0)
        est.append(max(deb, 0.0))
    return float(np.mean(est)), float(np.std(est) / math.sqrt(paths)), \
        float(np.mean(frozen_flags))


def main():
    rng = np.random.default_rng(SEED)
    out = {"model": "parameter-chain (NOT linkage disequilibrium)",
           "n_markers": N_MARKERS, "q": Q, "paths": N_PATHS, "draws": N_DRAWS}

    print("CONTROLS (C1 tests the STATISTIC, C2 tests the SIMULATOR)")
    m1, s1, f1 = ghost_mass(N_MARKERS, 1.0, rng)
    c1 = m1 < 0.02
    print("  C1 ell=1, every marker regenerates: ghost %.4f +-%.4f, must be 0 -> %s"
          % (m1, s1, "PASS" if c1 else "FAIL"))
    m2, s2, f2 = ghost_mass(N_MARKERS, 1e6, rng)
    c2 = m2 > 0.98
    print("  C2 ell>>n, frozen: ghost %.4f +-%.4f (frozen paths %.3f), must be 1 -> %s"
          % (m2, s2, f2, "PASS" if c2 else "FAIL"))
    out["controls"] = {"C1_ghost": m1, "C1_pass": bool(c1),
                       "C2_ghost": m2, "C2_pass": bool(c2)}

    print("")
    print("SWEEP: ell straddles n = %d" % N_MARKERS)
    print("  %-8s %-10s %-18s %-14s %-14s" % ("ell", "n/ell", "measured ghost",
                                              "exact (1-1/l)^(n-1)", "asymptotic e^-n/l"))
    rows = []
    for ell in (5.0, 10.0, 20.0, 40.0, 80.0, 160.0, 320.0):
        m, s, frac = ghost_mass(N_MARKERS, ell, rng)
        exact = (1.0 - 1.0 / ell) ** (N_MARKERS - 1)
        asym = math.exp(-N_MARKERS / ell)
        rows.append({"ell": ell, "n_over_ell": N_MARKERS / ell,
                     "ghost_measured": m, "ghost_sem": s,
                     "frozen_path_fraction": frac,
                     "exact_finite_n": exact, "asymptotic": asym})
        print("  %-8.0f %-10.3f %-18s %-14.5f %-14.5f"
              % (ell, N_MARKERS / ell, "%.5f +-%.5f" % (m, s), exact, asym))
    out["sweep"] = rows

    dev_exact = max(abs(r["ghost_measured"] - r["exact_finite_n"]) for r in rows)
    dev_asym = max(abs(r["ghost_measured"] - r["asymptotic"]) for r in rows)
    print("  max |measured - exact|      = %.5f" % dev_exact)
    print("  max |measured - asymptotic| = %.5f" % dev_asym)
    out["max_dev_exact"] = dev_exact
    out["max_dev_asymptotic"] = dev_asym

    print("")
    print("C3 PREDICTED-FAILURE ARM: deterministic periodic chain, no renewal")
    prows = []
    for ell in (10.0, 20.0, 40.0):
        m, s, frac = ghost_mass(N_MARKERS, ell, rng, mode="periodic")
        exact = (1.0 - 1.0 / ell) ** (N_MARKERS - 1)
        prows.append({"ell": ell, "ghost_measured": m, "ghost_sem": s,
                      "renewal_prediction": exact})
        print("  ell=%-6.0f ghost %.5f +-%.5f   renewal formula would say %.5f"
              % (ell, m, s, exact))
    out["C3_periodic"] = prows
    c3_differs = any(abs(r["ghost_measured"] - r["renewal_prediction"]) > 0.05
                     for r in prows)
    print("  periodic chain departs from the renewal formula: %s"
          % ("YES, as predicted" if c3_differs else "NO -- unexpected, investigate"))
    out["C3_departs_as_predicted"] = bool(c3_differs)

    out["READ_THE_TEST"] = bool(c1 and c2)
    print("")
    print("READ_THE_TEST: %s" % out["READ_THE_TEST"])
    fh = open("fam_freezing_results.json", "w")
    json.dump(out, fh, indent=1)
    fh.close()
    print("-> fam_freezing_results.json")
    return 0 if out["READ_THE_TEST"] else 1


if __name__ == "__main__":
    sys.exit(main())
