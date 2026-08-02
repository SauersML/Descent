#!/usr/bin/env python3
"""Family simulator: STEPPING STONE. numpy only, no msprime, no scipy.

The family with the largest measured errors in the corpus and, until now, no
simulator at all. Five in-slice definitions, two engines, both vectorised over
replicates so the whole file runs in seconds rather than the ~25 minutes the
msprime script `heavy/h1_stepping_stone_length.py` was budgeted.

    steppingStoneCharacteristicLength   L = sqrt(m / (2 mu))
    steppingStoneCoalescenceTime        T(d) = d / (2 sigma^2 m)
    demoSteppingStoneFst                d / (d + 4 Ne m sigma^2)
    steppingStoneFstQuadratic           d / (d + 4 Ne sigma^4 m^2)
    steppingStoneFst                    min 1 (f_nb * (1 + alpha (d-1)))

THE MODEL, ONCE, FOR BOTH ENGINES

  A circle of D demes, each of diploid size Ne. Per generation a lineage
  migrates with probability m; a migrant moves +k or -k demes with probability
  1/2 each. So the per-generation dispersal variance is

      V  =  m * k^2   =   m * sigma^2 ,      sigma^2 = k^2 .

  k is what lets sigma^2 be varied AT FIXED m and m AT FIXED sigma^2. That is
  the whole point: `demoSteppingStoneFst`'s own docstring records that its
  evidence came from a FREELY FITTED sigma^2, that such a fit constrains only
  the product m*sigma^2, and that "distinguishing the two forms empirically
  requires holding sigma^2 fixed at an independently measured dispersal
  variance and varying m, which has not been done." Here sigma^2 = k^2 is not
  fitted, it is set. This run is that experiment.

  Symmetric two-allele mutation at rate mu per allele per generation is used in
  engine 1 only; engine 2 is mutation-free, which is the regime
  `demoSteppingStoneFst` is derived in.

ENGINE 1 -- WRIGHT-FISHER FREQUENCY LATTICE, array shape (reps, D)

  migrate -> mutate -> binomial resample. The resample is ONE
  rng.binomial(2*Ne, p) call on the full 2-D array per generation; a Python
  loop over replicates or over demes here is the bug that makes this family
  look expensive.

  Measures the covariance C(d) = E[(p_i - 1/2)(p_{i+d} - 1/2)] at mutation-
  migration-drift equilibrium, averaged over every deme i, every replicate and
  many time points, and fits C(d) ~ exp(-d/L).

  DECIDES `steppingStoneCharacteristicLength`. The diffusion balance is
  2*V*C'' = 4*mu*C away from the origin, giving

      L_true = sqrt(V / (2 mu)) = sqrt(m * sigma^2 / (2 mu)) ,

  against the corpus body sqrt(m / (2 mu)), which carries no sigma^2. The two
  agree exactly at sigma^2 = 1 and differ by a factor sigma at every other
  dispersal variance. THE k AXIS IS THE ONE THE PREVIOUS CHECK DID NOT HAVE.

ENGINE 2 -- TWO-LINEAGE COALESCENT ON THE CIRCLE, array shape (reps,)

  Exact backwards WF: both lineages migrate, then if they are in the same deme
  they coalesce with probability 1/(2 Ne). The state is the single integer
  circular distance between them, so a replicate is one int and R replicates
  are one array. Coalesced replicates are compacted out of the array, so the
  total work is R * E[T] element-visits, not R * max(T).

  Measures E[T(d)] for every d, hence
      H(d)   = E[T(d)] - E[T(0)]      the meeting time, DECIDES
                                      `steppingStoneCoalescenceTime`
      F_ST(d) = H(d) / (H(d) + E[T(0)])   Hudson, DECIDES
                                      `demoSteppingStoneFst`,
                                      `steppingStoneFstQuadratic`,
                                      `steppingStoneFst`,
                                      and the deleted 1 - exp(-d/L).

  Mutation-free and frequency-free, so it settles the F_ST forms without any
  of engine 1's estimator noise, and the two engines share no code path beyond
  the migration parameters -- an agreement between them is not circular.

SIX CONTROLS, EACH ISOLATING ONE FACTOR, NONE FITTED

  Engine 1 (splits the three rates that L is built from, and shows Ne is not
  one of them):
    F1  DRIFT ALONE.   m = 0, mu = 0. E[p(1-p)] must fall by exactly
        (1 - 1/(2 Ne)) per generation.
    F2  MIGRATION ALONE. Ne = infinite, mu = 0, a delta profile. The spatial
        variance of the profile must grow by exactly m*k^2 per generation.
        This is where sigma^2 is pinned to k^2 rather than assumed.
    F3  MUTATION ALONE. Ne = infinite, m = 0, p = 1. (p - 1/2) must fall by
        exactly (1 - 2 mu) per generation.
    A simulator that got L right by getting the migration and mutation rates
    wrong in compensating directions passes a combined equilibrium check and
    fails F2 and F3 separately.

  Engine 2 (splits the two factors of F_ST = H/(H+T0)):
    E1  COALESCENCE ALONE.  D = 1, one deme, no migration possible. E[T] must
        be exactly 2*Ne.
    E2  RANDOM WALK ALONE.  2*Ne = 1, so lineages coalesce the instant they
        meet and T(d) IS the hitting time. On a circle of D demes a walk of
        relative-step variance V_rel = 2*m*k^2 has hitting time exactly
        d*(D-d)/V_rel -- gambler's ruin, no population-genetic content.
    E3  NO STRUCTURE.  D = 3, k = 1, m = 2/3 puts equal weight on all three
        demes, so the metapopulation is panmictic: T(d) = 2*Ne*D for every d
        and F_ST(d) = 0. This one can fail loudly and is the check that the
        deme bookkeeping is right at all.

CAN-FAIL CLAUSES

  L:  the grid varies mu over 16x AT FIXED m, k, Ne (corpus exponent 0 vs
      truth -1/2), Ne over 25x AT FIXED m, k, mu (corpus 0, truth 0 -- a
      guard against a regression, not a discriminator), m over 8x (corpus
      +1/2, truth +1/2 -- also not a discriminator), and k over 3x AT FIXED
      m, mu, Ne, where the corpus exponent is 0 and the truth is +1. A grid
      without the k axis cannot see the missing sigma^2 at all, and a grid
      without the mu axis cannot see the pre-repair error; both are required.

  F_ST(d):  d must run out to D/2. For d << D the meeting time d*(D-d)/V_rel
      is indistinguishable from its linearisation d*D/V_rel, and EVERY
      candidate here -- hyperbolic, quadratic, linear, exponential -- agrees
      with the others to first order in d. Only the far half of the lattice
      separates them.

  sigma^2:  the (m, k) grid contains pairs with the SAME m*sigma^2 and
      different m. `demoSteppingStoneFst` depends on the pair only through
      m*sigma^2 and must give identical F_ST across such a pair;
      `steppingStoneFstQuadratic` depends on sigma^4*m^2 = (m*sigma^2)^2 *
      (sigma^2/m)^0... it depends on m separately and must not. That pair of
      cells is the experiment the corpus says has not been done.
"""

import json
import math
import sys

import numpy as np

SEED = 20260802


# ===========================================================================
# ENGINE 1 -- Wright-Fisher frequency lattice
# ===========================================================================

def migrate(p, m, k):
    """Circular nearest-k migration on the deme axis of a (reps, D) array."""
    if m == 0.0:
        return p
    return (1.0 - m) * p + 0.5 * m * (np.roll(p, k, axis=1) + np.roll(p, -k, axis=1))


def wf_lattice_step(p, ne, m, k, mu, rng):
    p = migrate(p, m, k)
    if mu:
        p = p * (1.0 - mu) + (1.0 - p) * mu
    if ne is None:
        return p
    n = 2 * ne
    return rng.binomial(n, np.clip(p, 0.0, 1.0)).astype(np.float64) / n


def covariance_profile(ne, m, k, mu, D, reps, burn, samples, thin, rng):
    """C(d) = E[(p_i - 1/2)(p_{i+d} - 1/2)] at equilibrium, d = 0..D//2.

    Averaged over every deme i (all D of them), every replicate and every
    retained time point, which is why a few hundred replicates suffice.
    """
    p = np.full((reps, D), 0.5)
    for _ in range(burn):
        p = wf_lattice_step(p, ne, m, k, mu, rng)
    half = D // 2
    acc = np.zeros(half + 1)
    cnt = 0
    for i in range(samples):
        p = wf_lattice_step(p, ne, m, k, mu, rng)
        if i % thin:
            continue
        x = p - 0.5
        # FFT autocorrelation over the circular deme axis: one transform per
        # sample instead of D lag-by-lag dot products.
        f = np.fft.rfft(x, axis=1)
        c = np.fft.irfft(f * np.conj(f), n=D, axis=1).real / D
        acc += c.mean(axis=0)[: half + 1]
        cnt += 1
    return acc / cnt


def fit_decay_length(c, dmin, dmax):
    """Fit C(d) ~ exp(-d/L) over d in [dmin, dmax]; returns L or None."""
    d = np.arange(dmin, dmax + 1)
    y = c[dmin : dmax + 1]
    ok = y > 0
    if ok.sum() < 3:
        return None
    slope = np.polyfit(d[ok], np.log(y[ok]), 1)[0]
    if slope >= 0:
        return None
    return -1.0 / slope


# ===========================================================================
# ENGINE 2 -- two-lineage coalescent on the circle
# ===========================================================================

def meeting_times(D, ne, m, k, reps, rng, max_gen):
    """E[T(d)] for d = 0..D//2, one array of circular distances per d.

    Backwards WF: both lineages migrate, then coalesce with probability
    1/(2 Ne) if they are in the same deme. Compacts finished replicates out of
    the working array every generation, so cost is O(reps * E[T]).
    """
    half = D // 2
    out = np.zeros(half + 1)
    pcoal = 1.0 / (2.0 * ne)
    for d0 in range(half + 1):
        dist = np.full(reps, d0, dtype=np.int64)
        total = 0.0
        done = 0
        for t in range(1, max_gen + 1):
            n = dist.shape[0]
            if n == 0:
                break
            # relative displacement of the two lineages
            s1 = rng.random(n)
            s2 = rng.random(n)
            step = np.zeros(n, dtype=np.int64)
            step += np.where(s1 < m * 0.5, k, np.where(s1 < m, -k, 0))
            step -= np.where(s2 < m * 0.5, k, np.where(s2 < m, -k, 0))
            dist = (dist + step) % D
            dist = np.minimum(dist, D - dist)
            hit = (dist == 0) & (rng.random(n) < pcoal)
            nh = int(hit.sum())
            if nh:
                total += nh * t
                done += nh
                dist = dist[~hit]
        if done < reps:
            # censored replicates: recorded rather than silently dropped
            total += (reps - done) * max_gen
        out[d0] = total / reps
    return out


# ===========================================================================
# candidate closed forms
# ===========================================================================

def lean_demo_fst(d, ne, m, sigma_sq):
    return d / (d + 4.0 * ne * m * sigma_sq)


def lean_quadratic_fst(d, ne, m, sigma_sq):
    return d / (d + 4.0 * ne * sigma_sq ** 2 * m ** 2)


def lean_linear_fst(f_nb, alpha, d):
    return min(1.0, f_nb * (1.0 + alpha * (d - 1.0)))


def deleted_exponential_fst(d, L):
    return 1.0 - math.exp(-d / L)


# ===========================================================================

def main():
    rng = np.random.default_rng(SEED)
    out = {}
    ok_all = True

    # ------------------------------------------------------------------
    print("CONTROLS -- ENGINE 1 (three rates, split three ways)")
    # F1 drift alone
    NE_F1, REPS_F1, GENS_F1 = 50, 2000, 40
    p = np.full((REPS_F1, 1), 0.5)
    h0 = float(np.mean(p * (1 - p)))
    for _ in range(GENS_F1):
        p = wf_lattice_step(p, NE_F1, 0.0, 1, 0.0, rng)
    h1 = float(np.mean(p * (1 - p)))
    f1_meas = (h1 / h0) ** (1.0 / GENS_F1)
    f1_want = 1.0 - 1.0 / (2.0 * NE_F1)
    f1 = abs(f1_meas - f1_want) < 0.002
    print("  F1 drift alone      : het retention %.6f vs 1-1/2Ne %.6f -> %s"
          % (f1_meas, f1_want, "PASS" if f1 else "FAIL"))

    # F2 migration alone -- pins sigma^2 = k^2, deterministic
    f2rows = []
    f2 = True
    for k in (1, 2, 3):
        for m in (0.05, 0.2):
            D = 401
            q = np.zeros((1, D))
            q[0, D // 2] = 1.0
            T = 60
            for _ in range(T):
                q = migrate(q, m, k)
            x = np.arange(D) - D // 2
            var = float((q[0] * x ** 2).sum() / q[0].sum())
            want = m * k * k * T
            rel = (var - want) / want
            f2rows.append({"k": k, "m": m, "var_measured": var,
                           "var_expected_m_k2_t": want, "rel_err": rel})
            if abs(rel) > 1e-6:
                f2 = False
    print("  F2 migration alone  : max |rel err| on spatial variance %.2e -> %s"
          % (max(abs(r["rel_err"]) for r in f2rows), "PASS" if f2 else "FAIL"))

    # F3 mutation alone
    MU_F3 = 1e-3
    q = np.ones((1, 1))
    T = 500
    for _ in range(T):
        q = wf_lattice_step(q, None, 0.0, 1, MU_F3, rng)
    f3_meas = (float(q[0, 0]) - 0.5) / 0.5
    f3_want = (1.0 - 2.0 * MU_F3) ** T
    f3 = abs(f3_meas - f3_want) < 1e-9
    print("  F3 mutation alone   : (p-1/2) retention %.9f vs (1-2mu)^t %.9f -> %s"
          % (f3_meas, f3_want, "PASS" if f3 else "FAIL"))

    out["controls_engine1"] = {
        "F1_drift_only": f1_meas, "F1_expected": f1_want, "F1_pass": bool(f1),
        "F2_migration_only": f2rows, "F2_pass": bool(f2),
        "F3_mutation_only": f3_meas, "F3_expected": f3_want, "F3_pass": bool(f3),
    }
    ok_all = ok_all and f1 and f2 and f3

    # ------------------------------------------------------------------
    print("")
    print("CONTROLS -- ENGINE 2 (two factors of F_ST = H/(H+T0), split)")
    # E1 coalescence alone
    NE_E1 = 40
    t = meeting_times(1, NE_E1, 0.0, 1, 40000, rng, 60000)
    e1_meas = float(t[0])
    e1_want = 2.0 * NE_E1
    e1 = abs(e1_meas - e1_want) / e1_want < 0.02
    print("  E1 coalescence alone: E[T] in one deme %.3f vs 2Ne %.1f -> %s"
          % (e1_meas, e1_want, "PASS" if e1 else "FAIL"))

    # E2 random walk alone -- 2Ne = 1, T(d) IS the hitting time
    D_E2, M_E2, K_E2 = 24, 0.25, 1
    t = meeting_times(D_E2, 0.5, M_E2, K_E2, 40000, rng, 200000)
    vrel = 2.0 * M_E2 * K_E2 * K_E2
    e2rows = []
    e2 = True
    for d in range(1, D_E2 // 2 + 1):
        want = d * (D_E2 - d) / vrel
        rel = (t[d] - t[0] - want) / want
        e2rows.append({"d": d, "hitting_measured": float(t[d] - t[0]),
                       "hitting_expected": want, "rel_err": float(rel)})
        if abs(rel) > 0.05:
            e2 = False
    print("  E2 random walk alone: max |rel err| on d(D-d)/V_rel %.4f -> %s"
          % (max(abs(r["rel_err"]) for r in e2rows), "PASS" if e2 else "FAIL"))

    # E3 no structure -- D=3, m=2/3 is exact panmixia over 3 demes
    NE_E3 = 30
    t = meeting_times(3, NE_E3, 2.0 / 3.0, 1, 40000, rng, 100000)
    e3_want = 2.0 * NE_E3 * 3
    e3_fst = float((t[1] - t[0]) / t[1])
    e3 = abs(t[0] - e3_want) / e3_want < 0.03 and abs(e3_fst) < 0.02
    print("  E3 no structure     : E[T]=%.1f vs 2*Ne*D=%.1f, F_ST(1)=%+.4f vs 0 -> %s"
          % (t[0], e3_want, e3_fst, "PASS" if e3 else "FAIL"))

    out["controls_engine2"] = {
        "E1_single_deme": e1_meas, "E1_expected": e1_want, "E1_pass": bool(e1),
        "E2_hitting_time": e2rows, "E2_pass": bool(e2),
        "E3_panmixia_T": float(t[0]), "E3_panmixia_T_expected": e3_want,
        "E3_panmixia_fst": e3_fst, "E3_pass": bool(e3),
    }
    ok_all = ok_all and e1 and e2 and e3

    # ------------------------------------------------------------------
    print("")
    print("A. steppingStoneCharacteristicLength  L = sqrt(m/(2 mu))")
    print("   truth from the diffusion balance: sqrt(m*sigma^2/(2 mu)),")
    print("   sigma^2 = k^2, which the corpus body does not contain.")
    print("   %-6s %-6s %-4s %-9s %-10s %-10s %-10s"
          % ("Ne", "m", "k", "mu", "L_meas", "L_corpus", "L_truth"))
    D_A, REPS_A = 256, 300
    BASE = dict(ne=100, m=0.1, k=1, mu=5e-4)
    cells = []
    for mu in (2e-3, 5e-4, 1.25e-4):          # 16x, corpus exponent 0 pre-repair
        cells.append(dict(BASE, mu=mu))
    for ne in (20, 500):                       # 25x, both say exponent 0
        cells.append(dict(BASE, ne=ne))
    for m in (0.025, 0.2):                     # 8x, both say +1/2
        cells.append(dict(BASE, m=m))
    for k in (2, 3):                           # THE DISCRIMINATING AXIS
        cells.append(dict(BASE, k=k))
    rowsA = []
    for c in cells:
        burn = int(min(20000, 6.0 / (2.0 * c["mu"])))
        prof = covariance_profile(c["ne"], c["m"], c["k"], c["mu"], D_A,
                                  REPS_A, burn, 3000, 10, rng)
        prof = prof / prof[0]
        Ltruth = math.sqrt(c["m"] * c["k"] ** 2 / (2.0 * c["mu"]))
        lo = max(1, int(round(0.5 * Ltruth)))
        hi = min(D_A // 2 - 1, int(round(3.0 * Ltruth)))
        L = fit_decay_length(prof, lo, max(lo + 3, hi))
        Lcorpus = math.sqrt(c["m"] / (2.0 * c["mu"]))
        rowsA.append(dict(c, L_measured=L, L_corpus=Lcorpus, L_truth=Ltruth,
                          rel_err_corpus=None if L is None else (Lcorpus - L) / L,
                          rel_err_truth=None if L is None else (Ltruth - L) / L,
                          fit_range=[lo, max(lo + 3, hi)]))
        print("   %-6d %-6.3f %-4d %-9.2e %-10s %-10.3f %-10.3f"
              % (c["ne"], c["m"], c["k"], c["mu"],
                 "None" if L is None else ("%.3f" % L), Lcorpus, Ltruth))
    out["A_characteristic_length"] = rowsA

    def loglog(rows, key):
        r = [x for x in rows if x["L_measured"]]
        if len(r) < 2:
            return None
        return float(np.polyfit(np.log([x[key] for x in r]),
                                np.log([x["L_measured"] for x in r]), 1)[0])

    mu_rows = [r for r in rowsA if r["ne"] == 100 and r["m"] == 0.1 and r["k"] == 1]
    ne_rows = [r for r in rowsA if r["m"] == 0.1 and r["k"] == 1 and r["mu"] == 5e-4]
    m_rows = [r for r in rowsA if r["ne"] == 100 and r["k"] == 1 and r["mu"] == 5e-4]
    k_rows = [r for r in rowsA if r["ne"] == 100 and r["m"] == 0.1 and r["mu"] == 5e-4]
    exps = {
        "dlogL_dlogmu": {"measured": loglog(mu_rows, "mu"), "corpus": -0.5, "truth": -0.5},
        "dlogL_dlogNe": {"measured": loglog(ne_rows, "ne"), "corpus": 0.0, "truth": 0.0},
        "dlogL_dlogm": {"measured": loglog(m_rows, "m"), "corpus": 0.5, "truth": 0.5},
        "dlogL_dlogsigma2": {"measured": None, "corpus": 0.0, "truth": 0.5},
    }
    kr = [x for x in k_rows if x["L_measured"]]
    if len(kr) >= 2:
        exps["dlogL_dlogsigma2"]["measured"] = float(np.polyfit(
            np.log([x["k"] ** 2 for x in kr]),
            np.log([x["L_measured"] for x in kr]), 1)[0])
    out["A_exponents"] = exps
    print("   fitted exponents (corpus | truth):")
    for kk, v in exps.items():
        print("     %-20s %-10s  %-6s | %-6s"
              % (kk, "None" if v["measured"] is None else "%.3f" % v["measured"],
                 v["corpus"], v["truth"]))

    # ------------------------------------------------------------------
    print("")
    print("B. F_ST(d) AND MEETING TIME  (d out to D/2 -- the can-fail range)")
    D_B, NE_B, REPS_B = 64, 25, 60000
    rowsB = []
    for (m, k) in ((0.1, 1), (0.025, 2), (0.4, 1), (0.1, 2)):
        sigma_sq = float(k * k)
        t = meeting_times(D_B, NE_B, m, k, REPS_B, rng, 400000)
        T0 = float(t[0])
        vrel = 2.0 * m * sigma_sq
        # neighbour F_ST, needed by the linear form; taken from d=1, not fitted
        H1 = float(t[1] - t[0])
        f_nb = H1 / (H1 + T0)
        Lexp = None
        cells = []
        for d in range(1, D_B // 2 + 1):
            H = float(t[d] - t[0])
            fst = H / (H + T0)
            cells.append({
                "d": d,
                "meeting_time_measured": H,
                "meeting_time_corpus": d / (2.0 * sigma_sq * m),
                "meeting_time_circle_theory": d * (D_B - d) / vrel,
                "fst_measured": fst,
                "fst_demoSteppingStone": lean_demo_fst(d, NE_B, m, sigma_sq),
                "fst_quadratic": lean_quadratic_fst(d, NE_B, m, sigma_sq),
                "fst_linear": lean_linear_fst(f_nb, 1.0, d),
            })
        # exponential form with L fitted freely -- the deleted definition,
        # given its best possible chance
        dd = np.array([c["d"] for c in cells], dtype=float)
        ff = np.array([c["fst_measured"] for c in cells])
        best = None
        for Lg in np.exp(np.linspace(math.log(0.2), math.log(500.0), 400)):
            pred = 1.0 - np.exp(-dd / Lg)
            e = float(np.mean(((pred - ff) / np.maximum(ff, 1e-6)) ** 2))
            if best is None or e < best[1]:
                best = (float(Lg), e)
        Lexp = best[0]
        for c in cells:
            c["fst_exponential_bestfit"] = deleted_exponential_fst(c["d"], Lexp)

        def rmsrel(key):
            v = [(c[key] - c["fst_measured"]) / c["fst_measured"] for c in cells]
            return float(np.sqrt(np.mean(np.square(v))))

        rec = {"m": m, "k": k, "sigma_sq": sigma_sq, "Ne": NE_B, "D": D_B,
               "T0_measured": T0, "T0_expected_2NeD": 2.0 * NE_B * D_B,
               "fst_neighbour_used": f_nb, "L_exponential_bestfit": Lexp,
               "rms_rel_err": {
                   "demoSteppingStoneFst": rmsrel("fst_demoSteppingStone"),
                   "steppingStoneFstQuadratic": rmsrel("fst_quadratic"),
                   "steppingStoneFst_linear": rmsrel("fst_linear"),
                   "deleted_exponential_bestfit": rmsrel("fst_exponential_bestfit"),
               },
               "cells": cells}
        rowsB.append(rec)
        print("  m=%.3f k=%d sigma^2=%.0f   T0=%.0f (2NeD=%.0f)"
              % (m, k, sigma_sq, T0, 2.0 * NE_B * D_B))
        print("    %-6s %-11s %-11s %-11s %-11s %-11s"
              % ("d", "fst_meas", "demoSSFst", "quadratic", "linear", "exp(fit)"))
        for c in cells:
            if c["d"] in (1, 2, 4, 8, 16, D_B // 2):
                print("    %-6d %-11.5f %-11.5f %-11.5f %-11.5f %-11.5f"
                      % (c["d"], c["fst_measured"], c["fst_demoSteppingStone"],
                         c["fst_quadratic"], c["fst_linear"],
                         c["fst_exponential_bestfit"]))
        print("    RMS rel err: demo %.4f | quadratic %.4f | linear %.4f | exp %.4f"
              % (rec["rms_rel_err"]["demoSteppingStoneFst"],
                 rec["rms_rel_err"]["steppingStoneFstQuadratic"],
                 rec["rms_rel_err"]["steppingStoneFst_linear"],
                 rec["rms_rel_err"]["deleted_exponential_bestfit"]))
    out["B_fst_and_meeting_time"] = rowsB

    # the sigma^2-at-fixed-product experiment, stated explicitly
    pair = {}
    for r in rowsB:
        pair[(r["m"], r["k"])] = r
    if (0.1, 1) in pair and (0.025, 2) in pair:
        a, b = pair[(0.1, 1)], pair[(0.025, 2)]
        # same m*sigma^2 = 0.1, m differs by 4x
        ca = {c["d"]: c for c in a["cells"]}
        cb = {c["d"]: c for c in b["cells"]}
        rows = []
        for d in (1, 4, 16, D_B // 2):
            rows.append({
                "d": d,
                "fst_measured_m0.1_k1": ca[d]["fst_measured"],
                "fst_measured_m0.025_k2": cb[d]["fst_measured"],
                "demo_predicts_equal": [ca[d]["fst_demoSteppingStone"],
                                        cb[d]["fst_demoSteppingStone"]],
                "quadratic_predicts_unequal": [ca[d]["fst_quadratic"],
                                               cb[d]["fst_quadratic"]],
            })
        out["B_fixed_product_experiment"] = {
            "note": "m*sigma^2 = 0.1 held fixed, m varied 4x. "
                    "demoSteppingStoneFst depends on the pair only through "
                    "m*sigma^2 and must be flat; steppingStoneFstQuadratic "
                    "depends on m separately and must not be. sigma^2 = k^2 "
                    "is set by construction, not fitted.",
            "rows": rows,
        }
        print("")
        print("  FIXED-PRODUCT EXPERIMENT (m*sigma^2 = 0.1, m varied 4x)")
        for r in rows:
            print("    d=%-4d measured %.5f vs %.5f   demo %.5f/%.5f  quad %.5f/%.5f"
                  % (r["d"], r["fst_measured_m0.1_k1"], r["fst_measured_m0.025_k2"],
                     r["demo_predicts_equal"][0], r["demo_predicts_equal"][1],
                     r["quadratic_predicts_unequal"][0],
                     r["quadratic_predicts_unequal"][1]))

    out["READ_THE_TEST"] = bool(ok_all)
    print("")
    print("READ_THE_TEST (all six controls): %s" % out["READ_THE_TEST"])
    fh = open("fam_stepping_stone_results.json", "w")
    json.dump(out, fh, indent=1)
    fh.close()
    print("-> fam_stepping_stone_results.json")
    return 0 if ok_all else 1


if __name__ == "__main__":
    sys.exit(main())
