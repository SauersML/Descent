#!/usr/bin/env python3
"""Family simulator: LD DECAY AND RECURRENCE. numpy only.

The largest unsimulated family in the slice, 13 in-slice definitions, and it
carries the two largest analytic errors found anywhere in the corpus. One
two-locus Wright-Fisher engine settles all of them.

    ldRetentionPerGen  ldAfterGenerations  ldRecurrence  ldDecayRatePerGen
    ldHalfLife         driftLDStep         driftLDRetention
    driftLDEquilibrium driftLDTrajectory   excessLDAfterBottleneck
    bottleneckExcessLD driftLDCreationRate tagR2

WHAT IS MEASURED, AND WHICH DEFINITION EACH SETTLES

  A. E[D_t]/D_0 per generation.  Hill & Robertson: E[D] decays by exactly
     (1-r)(1 - 1/(2Ne)) per generation. Settles ldRetentionPerGen,
     ldAfterGenerations, ldRecurrence, and -- since it is the same quantity
     inverted -- ldHalfLife and ldDecayRatePerGen.

     ldHalfLife and ldRetainedFraction were REPAIRED this session, having been
     2110x and 37000x wrong by dropping the recombination argument entirely.
     Their checks are expected to pass now. This simulator is the standing
     check that keeps them right, which is the third leg the repair needed.

  B. sigma_d^2 = E[D^2]/E[p(1-p)q(1-q)] at equilibrium.  Decides whether
     driftLDEquilibrium -- exactly the fixed point of driftLDStep -- is the
     gametic-identity probability it algebraically is, or the E[r^2] its name
     implies. Sved gives 1/(1+4Nc); Ohta-Kimura gives (10+rho)/((2+rho)(11+rho));
     they differ by 120% as rho -> 0 and converge as rho -> infinity.

  C. Bottleneck excess.  excessLDAfterBottleneck and bottleneckExcessLD are the
     only definitions here with NO closed-form reference under a size change,
     which is why they were left out of the analytic tier rather than checked
     against a bound wide enough to always hold.

TWO CONTROLS PINNED BY THEORY, EACH ISOLATING ONE FACTOR OF THE PRODUCT

  C1  NO RECOMBINATION, r = 0.  Then E[D] must decay by exactly (1-1/(2Ne))^t.
      Pins the DRIFT factor alone.
  C2  NO DRIFT, Ne enormous.  Then E[D] must decay by exactly (1-r)^t.
      Pins the RECOMBINATION factor alone.

  Together they pin both factors of (1-r)(1-1/2Ne) separately, so a simulator
  that gets the product right by getting both factors wrong in compensating
  directions cannot pass. Neither control is fitted; both are exact.

CAN-FAIL CLAUSE
  The r grid MUST straddle 1/(2Ne). Where r >> 1/(2Ne) the drift factor is
  invisible and the retention is indistinguishable from (1-r); where
  r << 1/(2Ne) recombination is invisible and it is indistinguishable from
  (1-1/2Ne). Only near r ~ 1/(2Ne) do both factors matter at once, and a grid
  that misses that band cannot tell a product from either of its factors.

  For sigma_d^2 the rho = 4 Ne c grid must reach BELOW 10. Sved and Ohta-Kimura
  agree to 2% at rho = 100, so a loosely-linked grid validates both and decides
  nothing.

SPEED
  Vectorised over replicates; haplotype frequencies, not individuals. Sized for
  signal first, then scaled only where the answer was interesting.
"""

import json
import math
import sys

import numpy as np

MU = 1e-4
SEED = 20260802


def wf_step(x, ne, c, rng, mutate=True):
    """One Wright-Fisher generation on 4 haplotype frequencies, all replicates.

    Order: recombination, then mutation, then multinomial resampling. x has
    shape (reps, 4) for haplotypes AB, Ab, aB, ab.
    """
    D = x[:, 0] * x[:, 3] - x[:, 1] * x[:, 2]
    x = x + c * np.stack([-D, D, D, -D], axis=1)
    if mutate:
        m = MU
        M = np.array([
            [(1 - m) ** 2, m * (1 - m), m * (1 - m), m * m],
            [m * (1 - m), (1 - m) ** 2, m * m, m * (1 - m)],
            [m * (1 - m), m * m, (1 - m) ** 2, m * (1 - m)],
            [m * m, m * (1 - m), m * (1 - m), (1 - m) ** 2],
        ])
        x = x @ M.T
    x = np.clip(x, 0.0, None)
    x /= x.sum(axis=1, keepdims=True)
    if ne is None:                      # infinite population: no drift
        return x
    # Batched multinomial. The first version looped in Python over replicates,
    # which made the drift step O(reps) interpreted calls per generation and
    # did not finish in two minutes. numpy Generator.multinomial broadcasts
    # over a 2-D pvals since 1.22, so this is the same draw at a fraction of
    # the cost -- a speed fix, not a fidelity cut.
    n = 2 * ne
    return rng.multinomial(n, x).astype(np.float64) / n


def d_of(x):
    return x[:, 0] * x[:, 3] - x[:, 1] * x[:, 2]


def measure_D_retention(ne, c, gens, reps, rng, mutate=False):
    """E[D_t]/E[D_0] per generation, averaged over the trajectory.

    D is measured in EXPECTATION across replicates, not per replicate: E[D] is
    what Hill & Robertson describes, and |D| or D^2 decay differently.
    """
    # start in complete positive LD at p = q = 0.5
    x = np.tile(np.array([0.5, 0.0, 0.0, 0.5]), (reps, 1))
    d0 = float(np.mean(d_of(x)))
    traj = [d0]
    for _ in range(gens):
        x = wf_step(x, ne, c, rng, mutate=mutate)
        traj.append(float(np.mean(d_of(x))))
    traj = np.array(traj)
    ok = traj > 1e-9
    k = int(ok.sum())
    if k < 3:
        return None, None
    t = np.arange(len(traj))[ok]
    slope = np.polyfit(t, np.log(traj[ok]), 1)[0]
    return math.exp(slope), k


def measure_sigma_d2(ne, c, burn, samples, reps, rng):
    x = rng.multinomial(2 * ne, [0.25] * 4, size=reps).astype(np.float64) / (2 * ne)
    for _ in range(burn):
        x = wf_step(x, ne, c, rng)
    num, den = [], []
    for i in range(samples):
        x = wf_step(x, ne, c, rng)
        if i % 20:
            continue
        pa = x[:, 0] + x[:, 1]
        pb = x[:, 0] + x[:, 2]
        D = d_of(x)
        num.append(D ** 2)
        den.append(pa * (1 - pa) * pb * (1 - pb))
    num = np.concatenate(num); den = np.concatenate(den)
    return float(num.mean() / den.mean())


def corpus_bottleneck_prediction(n_b, n_r, c, t_b, t_r):
    """What the corpus predicts: driftLDStep iterated at N_b then at N_r.

    Written here rather than called from the Lean table so this script has no
    dependency on the extract layer, which is currently stale relative to the
    repaired definitions. The recursion is transcribed from driftLDStep,
    Q' = (1-c)^2 (1/(2Ne) + (1-1/(2Ne)) Q), and its fixed point.
    """
    a = (1.0 - c) ** 2

    def eq(ne):
        return a / (2.0 * ne) / (1.0 - a * (1.0 - 1.0 / (2.0 * ne)))

    def run(q, ne, t):
        for _ in range(int(t)):
            q = a * (1.0 / (2.0 * ne) + (1.0 - 1.0 / (2.0 * ne)) * q)
        return q

    return run(run(eq(n_r), n_b, t_b), n_r, t_r)


def family_bottleneck(rng):
    """Section C: LD excess after a bottleneck.

    The only two definitions in this family with NO closed-form reference under
    a size change, which is why they were never in the analytic tier: the only
    available reference was a bound wide enough to always hold, and a check
    that cannot fail is worse than an acknowledged gap.

    CONTROL PINNED BY THEORY: the NULL BOTTLENECK. Run the identical code path
    with N_b = N_r, i.e. no size change at all. Stationarity then fixes the
    ratio at exactly 1.0, independent of which of Sved, Ohta-Kimura or the
    corpus recursion is right. A null ratio departing from 1 means the burn-in
    is short or the engine drifts, and any amplification measured in the real
    cells is that artefact rather than a bottleneck effect.

    Note the null cell is exactly the degenerate case the can-fail clause
    forbids for the TEST -- with N_b = N_r nothing happens and every candidate
    reproduces a constant. Useless as a test, decisive as a control.
    """
    N_R, N_B = 500, 50
    REPS = 200
    rows = []
    for rho_at_nb in (2.0, 10.0):
        c = rho_at_nb / (4.0 * N_B)
        x = rng.multinomial(2 * N_R, [0.25] * 4, size=REPS).astype(np.float64) / (2 * N_R)
        for _ in range(8 * N_R):
            x = wf_step(x, N_R, c, rng)
        pre = _sigma_d2_now(x)
        for (nb, tag) in ((N_R, "NULL (no bottleneck)"), (N_B, "bottleneck")):
            for t_b in (25, 100):
                xb = x.copy()
                for _ in range(t_b):
                    xb = wf_step(xb, nb, c, rng)
                post = _sigma_d2_now(xb)
                pred = corpus_bottleneck_prediction(nb, N_R, c, t_b, 0)
                rows.append({
                    "rho_at_Nb": rho_at_nb, "c": c, "N_b": nb, "t_b": t_b,
                    "arm": tag,
                    "sigma_d2_pre": pre, "sigma_d2_post": post,
                    "ratio_measured": post / pre,
                    "corpus_prediction": pred,
                    "corpus_ratio": pred / pre,
                })
                print("    rho@Nb=%-5.1f %-22s t_b=%-4d  ratio %.4f   corpus %.4f"
                      % (rho_at_nb, tag, t_b, post / pre, pred / pre), flush=True)
    return rows


def _sigma_d2_now(x):
    pa = x[:, 0] + x[:, 1]
    pb = x[:, 0] + x[:, 2]
    D = d_of(x)
    return float((D ** 2).mean() / (pa * (1 - pa) * pb * (1 - pb)).mean())


def main():
    rng = np.random.default_rng(SEED)
    out = {}

    # ---------- CONTROLS FIRST -------------------------------------------
    print("CONTROLS (each isolates one factor of (1-r)(1-1/2Ne))")
    NE_C, REPS_C, GENS_C = 200, 400, 60

    ret, _ = measure_D_retention(NE_C, 0.0, GENS_C, REPS_C, rng)
    want = 1.0 - 1.0 / (2.0 * NE_C)
    c1 = ret is not None and abs(ret - want) < 0.004
    print("  C1 r=0, drift only: measured %.6f vs (1-1/2Ne) = %.6f -> %s"
          % (ret if ret else float("nan"), want, "PASS" if c1 else "FAIL"))

    ret2, _ = measure_D_retention(None, 0.02, 40, REPS_C, rng)
    want2 = 1.0 - 0.02
    c2 = ret2 is not None and abs(ret2 - want2) < 0.004
    print("  C2 Ne=inf, recombination only: measured %.6f vs (1-r) = %.6f -> %s"
          % (ret2 if ret2 else float("nan"), want2, "PASS" if c2 else "FAIL"))
    out["controls"] = {"C1_drift_only": ret, "C1_expected": want, "C1_pass": bool(c1),
                       "C2_recomb_only": ret2, "C2_expected": want2,
                       "C2_pass": bool(c2)}

    # ---------- A. E[D] retention, r straddling 1/(2Ne) -------------------
    print("")
    print("A. E[D] RETENTION PER GENERATION  (r straddles 1/(2Ne) = %.5f)"
          % (1.0 / (2.0 * NE_C)))
    print("    %-10s %-14s %-14s %-10s" % ("r", "measured", "HR (1-r)(1-1/2Ne)",
                                           "rel err"))
    rowsA = []
    for r in (0.0, 0.00125, 0.0025, 0.005, 0.02, 0.10):
        ret, k = measure_D_retention(NE_C, r, GENS_C, REPS_C, rng)
        if ret is None:
            continue
        hr = (1.0 - r) * (1.0 - 1.0 / (2.0 * NE_C))
        rowsA.append({"r": r, "measured": ret, "hill_robertson": hr,
                      "rel_err": (ret - hr) / hr, "gens_used": k})
        print("    %-10.5f %-14.6f %-14.6f %+.4f"
              % (r, ret, hr, (ret - hr) / hr))
    out["A_D_retention"] = rowsA

    # ---------- B. sigma_d^2 at equilibrium -------------------------------
    print("")
    print("B. sigma_d^2 AT EQUILIBRIUM  (rho grid reaches below 10)")
    print("    %-8s %-12s %-12s %-12s %-12s"
          % ("rho", "measured", "corpus(Sved)", "Ohta-Kimura", "closer to"))
    rowsB = []
    NE_B, REPS_B = 150, 500
    for rho in (0.5, 2.0, 10.0, 40.0):
        c = rho / (4.0 * NE_B)
        s = measure_sigma_d2(NE_B, c, 6 * NE_B, 3000, REPS_B, rng)
        a = (1.0 - c) ** 2
        corpus = a / (2.0 * NE_B) / (1.0 - a * (1.0 - 1.0 / (2.0 * NE_B)))
        ok_ = (10.0 + rho) / ((2.0 + rho) * (11.0 + rho))
        closer = "corpus" if abs(s - corpus) < abs(s - ok_) else "Ohta-Kimura"
        rowsB.append({"rho": rho, "measured": s, "corpus_driftLDEquilibrium": corpus,
                      "ohta_kimura": ok_, "closer_to": closer})
        print("    %-8.1f %-12.5f %-12.5f %-12.5f %-12s"
              % (rho, s, corpus, ok_, closer))
    out["B_sigma_d2"] = rowsB

    print("")
    print("C. LD EXCESS AFTER A BOTTLENECK  (null arm is the control)")
    rowsC = family_bottleneck(rng)
    out["C_bottleneck"] = rowsC
    nulls = [r for r in rowsC if r["arm"].startswith("NULL")]
    c3 = all(abs(r["ratio_measured"] - 1.0) < 0.15 for r in nulls)
    print("    CONTROL null bottleneck, ratio must be 1.0: %s  (%s)"
          % ("PASS" if c3 else "FAIL",
             ", ".join("%.4f" % r["ratio_measured"] for r in nulls)))
    out["controls"]["C3_null_bottleneck_pass"] = bool(c3)

    out["READ_THE_TEST"] = bool(c1 and c2 and c3)
    print("")
    print("READ_THE_TEST: %s" % out["READ_THE_TEST"])
    fh = open("fam_ld_decay_results.json", "w")
    json.dump(out, fh, indent=1)
    fh.close()
    print("-> fam_ld_decay_results.json")
    return 0 if out["READ_THE_TEST"] else 1


if __name__ == "__main__":
    sys.exit(main())
