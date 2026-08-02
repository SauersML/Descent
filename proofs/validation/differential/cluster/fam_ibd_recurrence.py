#!/usr/bin/env python3
"""FAMILY identity_by_descent_recurrence -- the two readings of `rate`, decided.

THE CLAIM UNDER TEST
    One body appears in the corpus under nine names:

        ibdRecurrenceStep Ne rate x = (1-rate)^2 (1/(2Ne) + (1-1/(2Ne)) x)
        ibdRecurrenceFixedPoint Ne rate
            = (1-rate)^2 / ((1-rate)^2 + 2 Ne rate (2-rate))
        islandFstMultiplicativeStep Ne m F      := ibdRecurrenceStep Ne m F
        fstIslandMultiplicativeEquilibrium Ne m := ibdRecurrenceFixedPoint Ne m

    and a linearised companion,

        ibdFlowStep Ne rate F = F + (1-F)/(2Ne) - 2 rate F, fixed point
        1/(1 + 4 Ne rate)
        fstMigDriftNext Ne m Fst = (1 - 2m - 1/(2Ne)) Fst + 1/(2Ne), same
        fstDriftFlowStep / fstEquilibrium = 1/(1 + theta + bigM)
        scaledIdentityStep scaledRate F = 1 - scaledRate F, fixed point
        1/(1 + scaledRate)

    `rate` is instantiated as a MUTATION rate in some members and a MIGRATION
    rate in others, from one body, and no member takes an argument saying which.
    Every one of these is marked `Empirical status: UNTESTED` in the Lean.

WHY THEY CANNOT BOTH BE RIGHT
    A mutation destroys identity on the lineage it hits and the lineage is gone
    for good, so `(1-mu)^2` -- neither of two lineages mutating -- is an exact
    factor. A migration event MOVES one lineage to another deme; the lineage is
    still there and can migrate back, so `(1-m)^2` is an ABSORBING
    approximation to a recurrent process. That is a statement about a model, and
    it is decided here by computing the model exactly.

WHAT IS COMPUTED
    (1) EXACT.  The discrete-generation ancestral process for two gene copies in
        a d-deme island model of Ne diploids per deme, per generation:
        migration (each lineage moves to a uniformly chosen OTHER deme with
        probability m), then mutation (infinite alleles, rate mu per lineage),
        then coalescence (probability 1/(2Ne) if co-resident).  The probability
        of identity in state from each of the two states -- co-resident (f_S)
        and separated (f_B) -- solves a 2x2 linear system, solved exactly.
        F_ST = (f_S - f_B) / (1 - f_B).
    (2) INDEPENDENT MONTE CARLO of the same process, on ACTUAL deme labels, one
        vectorised generation at a time over R replicate lineage pairs.  It
        shares no code with (1) and exists so that (1) is not the only witness.
    (3) THE CORPUS CLOSED FORMS, evaluated at the same parameters.

SPLIT CONTROLS -- WHAT EACH ISOLATES, AND HOW EACH CAN FAIL
    J1  rate = 0 under BOTH readings.  f_S must be exactly 1: with no mutation
        and no migration the two lineages certainly coalesce and are certainly
        identical.  ISOLATES the drift arm and proves the linear solve and the
        Monte Carlo both converge.  FAILS if the solve is singular, if the MC
        censors before absorption, or if the corpus fixed point does not attain
        its boundary.
    J2  Ne -> 1e9 at fixed positive rate.  Identity must go to 0: drift never
        coalesces anything, so a mutation always arrives first.  ISOLATES the
        flow arm with drift switched off.  FAILS if the 1/(2Ne) term is
        mis-scaled -- a wrong 1/(2Ne) with a compensating wrong (1-rate)^2 lands
        on the right answer at one scaled rate and fails BOTH J1 and J2, which
        is why neither is redundant and why the pair is run before J3.
    J3  THE DISCRIMINATING RUN, which neither control performs.  At MATCHED
        scaled rate 4*Ne*rate, evaluate the ONE corpus body against the exact
        model under each reading in turn.  Mutation reading: single panmictic
        deme, infinite alleles.  Migration reading: d-deme island F_ST.
    J4  THE MISSING ARGUMENT.  The migration arm is run at d = 2, 10 and 100
        demes at otherwise identical parameters.  The corpus body has no d, so
        it returns ONE number for all three; if the exact model does not, the
        defect is a MISSING REGIME DECLARATION and not wrong arithmetic.

CAN-FAIL CLAUSE ON THE GRID
    The scaled rate must go BELOW 1.  Above scaled rate ~10 every candidate
    gives F ~ 0 and a grid confined there validates all of them at once; the
    grid therefore runs 0.25 to 20 so that BOTH the discriminating regime and
    the degenerate one are visible in the same table, and the degenerate rows
    are labelled as such rather than counted as agreement.
    The mutation floor of the migration arm is likewise swept: F_ST is only
    defined relative to some mutation, so theta is halved in a companion cell
    and the F_ST must not move.  If it does, the migration arm is measuring the
    mutation rate.

VECTORISATION
    The Monte Carlo advances every replicate by one generation in one numpy
    call per event.  Each element of rng.random(size=k) is an independent
    uniform, which is exactly the draw a per-replicate loop would make; no
    variate is reused across replicates, so trajectories never share state.
    Nothing here was made cheaper: the exact arm is a closed-form linear solve
    and carries no replicate count at all, and the MC replicate count,
    generation cap and grids are set for signal.
"""

import json
import os
import sys

for _v in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS",
           "NUMEXPR_NUM_THREADS", "VECLIB_MAXIMUM_THREADS"):
    os.environ.setdefault(_v, "1")

import numpy as np

SEED = 20260802
HERE = os.path.dirname(os.path.abspath(__file__))
N_REPS = 300000
GEN_CAP = 400000


# ---------------------------------------------------------------------------
# CORPUS CLOSED FORMS, transcribed from Lean.  Named for the Lean name.
# ---------------------------------------------------------------------------
def ibd_recurrence_step(ne, rate, x):
    """PortabilityDrift.ibdRecurrenceStep (= islandFstMultiplicativeStep)."""
    return (1 - rate) ** 2 * (1.0 / (2 * ne) + (1 - 1.0 / (2 * ne)) * x)


def ibd_recurrence_fixed_point(ne, rate):
    """PortabilityDrift.ibdRecurrenceFixedPoint
    (= fstIslandMultiplicativeEquilibrium)."""
    return (1 - rate) ** 2 / ((1 - rate) ** 2 + 2 * ne * rate * (2 - rate))


def ibd_flow_step(ne, rate, f):
    """PortabilityDrift.ibdFlowStep -- the linearised companion."""
    return f + (1 - f) / (2 * ne) - 2 * rate * f


def fst_mig_drift_next(ne, m, fst):
    """PortabilityDrift.fstMigDriftNext."""
    return (1 - 2 * m - 1.0 / (2 * ne)) * fst + 1.0 / (2 * ne)


def linear_fixed_point(ne, rate):
    """Common fixed point of ibdFlowStep and fstMigDriftNext, and the value
    scaledIdentityStep / fstEquilibrium give at scaledRate = 4*Ne*rate."""
    return 1.0 / (1.0 + 4.0 * ne * rate)


def scaled_identity_step(scaled_rate, f):
    """PopulationGeneticsFoundations.scaledIdentityStep."""
    return 1.0 - scaled_rate * f


def iterate(step, x0, n):
    x = x0
    for _ in range(n):
        x = step(x)
    return x


# ---------------------------------------------------------------------------
# (1) EXACT: the 2x2 identity system for the d-deme island model.
# ---------------------------------------------------------------------------
def exact_identity(ne, m, mu, d):
    """(f_S, f_B) : probability two lineages are identical in state, starting
    co-resident and starting separated.

    Migration, then mutation, then coalescence, each generation.  With uniform
    migration to one of the d-1 other demes the only thing that matters is
    whether the two lineages are co-resident, so the backward chain is exactly
    two states:

        S -> S : neither moves (1-m)^2, or both move and land together,
                 m^2 / (d-1)
        B -> S : exactly one moves and lands on the other, 2m(1-m)/(d-1), or
                 both move and land together, m^2 (d-2)/(d-1)^2
    """
    if d == 1:
        m = 0.0
    q = 1.0 if d == 1 else 1.0 / (d - 1.0)
    m_ss = (1 - m) ** 2 + (m ** 2) * q
    m_sb = 1.0 - m_ss
    m_bs = 2 * m * (1 - m) * q + (m ** 2) * (d - 2.0) * q * q if d > 1 else 0.0
    m_bb = 1.0 - m_bs
    surv = (1 - mu) ** 2
    c = 1.0 / (2.0 * ne)

    # f_S = surv [ M_SS (c + (1-c) f_S) + M_SB f_B ]
    # f_B = surv [ M_BS (c + (1-c) f_S) + M_BB f_B ]
    a = np.array([[1.0 - surv * m_ss * (1 - c), -surv * m_sb],
                  [-surv * m_bs * (1 - c), 1.0 - surv * m_bb]])
    b = np.array([surv * m_ss * c, surv * m_bs * c])
    f_s, f_b = np.linalg.solve(a, b)
    return float(f_s), float(f_b)


def exact_fst(ne, m, mu, d):
    f_s, f_b = exact_identity(ne, m, mu, d)
    return (f_s - f_b) / (1.0 - f_b), f_s, f_b


# ---------------------------------------------------------------------------
# (2) INDEPENDENT MONTE CARLO on actual deme labels.
# ---------------------------------------------------------------------------
def mc_identity(rng, ne, m, mu, d, start_same, reps=N_REPS, cap=GEN_CAP):
    """P(identical in state) by direct backward simulation of two lineages.

    Shares no code with exact_identity: this one carries deme LABELS and never
    forms a transition matrix.  Returns (probability, standard error,
    unresolved fraction).  An unresolved fraction above 0 is reported, not
    silently dropped -- a censored replicate is not a non-identical one.
    """
    d1 = np.zeros(reps, dtype=np.int64)
    d2 = np.zeros(reps, dtype=np.int64) if start_same else np.ones(reps,
                                                                  dtype=np.int64)
    if d == 1:
        d2 = np.zeros(reps, dtype=np.int64)
    idx = np.arange(reps)
    out = np.full(reps, -1, dtype=np.int8)
    c = 1.0 / (2.0 * ne)
    surv = (1 - mu) ** 2

    for _ in range(cap):
        k = idx.size
        if k == 0:
            break
        if d > 1 and m > 0:
            for arr in (d1, d2):
                mov = rng.random(k) < m
                nm = int(mov.sum())
                if nm:
                    off = rng.integers(0, d - 1, size=nm)
                    cur = arr[mov]
                    arr[mov] = off + (off >= cur)
        # mutation on either lineage this generation ends identity
        mut = rng.random(k) >= surv
        if mut.any():
            out[idx[mut]] = 0
        keep = ~mut
        # coalescence, only for co-resident pairs
        same = (d1 == d2) & keep
        coal = same & (rng.random(k) < c)
        if coal.any():
            out[idx[coal]] = 1
        keep &= ~coal
        idx = idx[keep]
        d1 = d1[keep]
        d2 = d2[keep]

    resolved = out >= 0
    n_res = int(resolved.sum())
    unresolved = 1.0 - n_res / float(reps)
    if n_res == 0:
        return float("nan"), float("nan"), unresolved
    p = float(out[resolved].mean())
    se = float(np.sqrt(max(p * (1 - p), 0.0) / n_res))
    return p, se, unresolved


def main():
    rng = np.random.default_rng(SEED)
    rows = []
    NE = 100

    # ---- J1 : rate = 0 under BOTH readings.  f_S must be exactly 1. --------
    f_s, f_b = exact_identity(NE, 0.0, 0.0, 2)
    mc, se, unres = mc_identity(rng, NE, 0.0, 0.0, 1, True, reps=20000)
    corpus_fp = ibd_recurrence_fixed_point(NE, 0.0)
    corpus_iter = iterate(lambda x: ibd_recurrence_step(NE, 0.0, x), 0.0, 20000)
    lin_iter = iterate(lambda x: ibd_flow_step(NE, 0.0, x), 0.0, 20000)
    rows.append({
        "cell": "J1 control rate=0, both readings",
        "exact_f_S": f_s, "mc_f_S": mc, "mc_se": se, "mc_unresolved": unres,
        "ibdRecurrenceFixedPoint": corpus_fp,
        "ibdRecurrenceStep_iterated": corpus_iter,
        "ibdFlowStep_iterated": lin_iter,
        "predicted": 1.0,
        "isolates": "the drift arm; also proves the solve and the MC converge",
        "ok": (abs(f_s - 1) < 1e-12 and abs(mc - 1) < 1e-12
               and abs(corpus_fp - 1) < 1e-12 and abs(corpus_iter - 1) < 1e-3
               and abs(lin_iter - 1) < 1e-3 and unres == 0.0),
    })

    # ---- J2 : Ne enormous.  Identity must vanish. --------------------------
    for rate in (0.01, 0.001):
        f_s, _ = exact_identity(1e9, 0.0, rate, 1)
        rows.append({
            "cell": "J2 control Ne=1e9, drift off",
            "rate": rate,
            "exact_f_S": f_s,
            "ibdRecurrenceFixedPoint": ibd_recurrence_fixed_point(1e9, rate),
            "linear_fixed_point_1_over_1_plus_4Nerate":
                linear_fixed_point(1e9, rate),
            "predicted": 0.0,
            "isolates": "the flow arm with drift switched off",
            "ok": abs(f_s) < 1e-6,
        })

    # ---- J3 : THE DISCRIMINATING RUN.  Matched scaled rate. ---------------
    # CAN-FAIL: 0.25 and 0.5 are below the regime where the readings collapse;
    # 20 is inside it, and is labelled degenerate rather than counted.
    for scaled in (0.25, 0.5, 1.0, 2.0, 8.0, 20.0):
        rate = scaled / (4.0 * NE)
        corpus_fp = ibd_recurrence_fixed_point(NE, rate)
        lin_fp = linear_fixed_point(NE, rate)

        # -- MUTATION reading: one panmictic deme, infinite alleles. --
        mut_exact, _ = exact_identity(NE, 0.0, rate, 1)
        mut_mc, mut_se, mut_un = mc_identity(rng, NE, 0.0, rate, 1, True)

        # -- MIGRATION reading: d-deme island F_ST at a mutation floor. --
        # theta held at 1e-3, three orders below the migration scale at the
        # smallest M on the grid, and halved in the companion cell below.
        theta = 1e-3
        mu_floor = theta / (4.0 * NE)
        mig = {}
        for d in (2, 10, 100):
            fst_ex, fs, fb = exact_fst(NE, rate, mu_floor, d)
            mig["exact_Fst_d%d" % d] = fst_ex
            mig["exact_f_S_d%d" % d] = fs
            mig["exact_f_B_d%d" % d] = fb
        fst_half, _, _ = exact_fst(NE, rate, mu_floor / 2.0, 2)

        rows.append({
            "cell": "J3 discriminating run, matched scaled rate",
            "scaled_rate_4Ne": scaled, "rate": rate,
            "CORPUS_ibdRecurrenceFixedPoint": corpus_fp,
            "CORPUS_linear_1_over_1_plus_scaled": lin_fp,
            "MUTATION_reading_exact": mut_exact,
            "MUTATION_reading_mc": mut_mc, "MUTATION_reading_mc_se": mut_se,
            "MUTATION_mc_unresolved": mut_un,
            "MUTATION_relerr_vs_corpus":
                abs(mut_exact - corpus_fp) / max(abs(mut_exact), 1e-12),
            "MIGRATION_relerr_vs_corpus_d2":
                abs(mig["exact_Fst_d2"] - corpus_fp)
                / max(abs(mig["exact_Fst_d2"]), 1e-12),
            "MIGRATION_Fst_d2_theta_halved": fst_half,
            "mutation_floor_shift":
                abs(fst_half - mig["exact_Fst_d2"])
                / max(abs(mig["exact_Fst_d2"]), 1e-12),
            "degenerate_regime": scaled >= 10.0,
            "isolates": ("nothing -- this IS the test.  J1 and J2 have already "
                         "pinned the drift and flow arms separately, so a gap "
                         "here is about the READING of `rate`"),
            # The assertion is only that the MC confirms the exact arm; the
            # corpus comparison is the measurement, not the pass condition.
            "ok": (abs(mut_mc - mut_exact) < 5 * max(mut_se, 1e-9) + 2e-3
                   and mut_un == 0.0),
            **mig,
        })

    # ---- J4 : the missing d argument, isolated. ---------------------------
    for scaled in (0.5, 2.0):
        rate = scaled / (4.0 * NE)
        mu_floor = 1e-3 / (4.0 * NE)
        vals = {}
        for d in (2, 10, 100):
            vals["exact_Fst_d%d" % d] = exact_fst(NE, rate, mu_floor, d)[0]
        mc2, se2, un2 = mc_identity(rng, NE, rate, mu_floor, 2, True,
                                    reps=100000, cap=200000)
        mcb, seb, unb = mc_identity(rng, NE, rate, mu_floor, 2, False,
                                    reps=100000, cap=200000)
        mc_fst = (mc2 - mcb) / (1.0 - mcb)
        rows.append({
            "cell": "J4 MISSING ARGUMENT: F_ST depends on d, the body does not",
            "scaled_rate_4Ne": scaled,
            "CORPUS_ibdRecurrenceFixedPoint_no_d_argument":
                ibd_recurrence_fixed_point(NE, rate),
            "mc_Fst_d2": mc_fst, "mc_f_S": mc2, "mc_f_B": mcb,
            "mc_unresolved": max(un2, unb),
            "mc_vs_exact_d2_relerr":
                abs(mc_fst - vals["exact_Fst_d2"])
                / max(abs(vals["exact_Fst_d2"]), 1e-12),
            "spread_d2_to_d100":
                abs(vals["exact_Fst_d100"] - vals["exact_Fst_d2"])
                / max(abs(vals["exact_Fst_d2"]), 1e-12),
            "isolates": ("the number of demes alone -- every other parameter "
                         "is held fixed across the three columns"),
            "ok": (abs(mc_fst - vals["exact_Fst_d2"])
                   < 6 * max(se2 + seb, 1e-9) + 5e-3),
            **vals,
        })

    n_bad = 0
    print("=" * 78)
    print("IDENTITY-BY-DESCENT RECURRENCE")
    print("=" * 78)
    for r in rows:
        if not r.get("ok"):
            n_bad += 1
        bits = []
        for k in sorted(r):
            if k in ("cell", "ok", "isolates"):
                continue
            v = r[k]
            bits.append("%s=%.6g" % (k, v) if isinstance(v, float)
                        else "%s=%s" % (k, v))
        print("  [%s] %-52s %s" % ("ok " if r.get("ok") else "RED",
                                   r["cell"], "  ".join(bits)))

    j3 = [r for r in rows if r["cell"].startswith("J3")
          and not r["degenerate_regime"]]
    mut_ok = all(r["MUTATION_relerr_vs_corpus"] < 1e-9 for r in j3)
    mig_off = max(r["MIGRATION_relerr_vs_corpus_d2"] for r in j3)
    print("")
    print("J3 VERDICT: under the MUTATION reading the corpus body is %s"
          % ("EXACT at every non-degenerate scaled rate"
             if mut_ok else "NOT exact -- see the relerr column"))
    print("            under the MIGRATION reading it is off by up to %.1f%%"
          % (100.0 * mig_off))
    j4 = [r for r in rows if r["cell"].startswith("J4")]
    print("J4 VERDICT: exact F_ST moves by up to %.1f%% between d=2 and d=100 "
          "at fixed 4*Ne*m, and the corpus body has no d argument."
          % (100.0 * max(r["spread_d2_to_d100"] for r in j4)))

    out = {"seed": SEED, "n_reps": N_REPS, "rows": rows, "cells_red": n_bad,
           "mutation_reading_exact": bool(mut_ok),
           "migration_reading_max_relerr": float(mig_off)}
    fh = open(os.path.join(HERE, "fam_ibd_recurrence_results.json"), "w")
    json.dump(out, fh, indent=1)
    fh.close()
    print("-> fam_ibd_recurrence_results.json  (%d cells red)" % n_bad)
    return 0


if __name__ == "__main__":
    sys.exit(main())
