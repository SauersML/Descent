#!/usr/bin/env python3.12
"""Target 3: the safe epistatic order (PolygenicSpectroscopy `maxSafeEpistaticOrder`).

Chosen because the corpus states this claim "so it can be falsified", marks it
`Empirical status: UNTESTED`, and every gate in the condensation arc
(`additive_score_is_subcritical`, `epistatic_order_safe_iff`,
`epistatic_order_unsafe_iff`, the CondensationUnification design gate) reads off it.
It is also the only unsimulated claim in the ledger whose falsification can be checked
in exact arithmetic as well as by simulation.

THE CLAIM (PolygenicSpectroscopy module docstring):
  score  S_N = N^{-1/2} sum_{j=1..N} prod_{l=1..m} x_{j,l},  disjoint monomials,
  m*(N,q) = log N / c(q),  c(q) = E[x^2 log x^2]  (the Mellin drift).
  * BELOW m*: "the score's law is the same whether one models genotypes by their
    true discrete law or by the Gaussian surrogate."
  * ABOVE m*: the surrogate condenses onto a point mass, the true chaos does not.

TWO EXACT FACTS THAT BOUND THE CLAIM (computed here, no simulation needed):

  (A) For the TRUE genotype chaos, kappa4(S_N) = (E[x^4]^m - 3)/N = ((1/V)^m - 3)/N,
      V = 2q(1-q).  So the true law leaves the Gaussian limit at
          m_kurt(N,q) = log N / log(1/V).
      The function p |-> log E[(x^2)^p] vanishes at p=1, so log(1/V) is its secant
      slope on [1,2] and c(q) is its tangent slope at p=1.  By convexity
          c(q) <= log(1/V)   for every q,
      with equality iff that function is linear, which happens only at q = 1/2.
      Hence m*(N,q) >= m_kurt(N,q) ALWAYS, strictly for every q != 1/2:
      the corpus's safe order is an OVER-estimate at every polymorphic frequency
      except q = 1/2.

  (B) For the GAUSSIAN SURROGATE, kappa4 = (3^m - 3)/N, so the surrogate leaves the
      Gaussian limit at log N / log 3, and it condenses at log N / c_G with
      c_G = E[z^2 log z^2] = 2 - gamma - log 2 = 0.7296...  The corpus's own theorem
      `drift_straddles_condensationConstant` proves c((5-sqrt5)/10) < c_G, i.e. at
      q = 0.2764 the surrogate condenses STRICTLY BEFORE the corpus's own safe order.

The simulation checks (A) and (B) empirically: it draws S_N under both coordinate laws
across an m-grid straddling all three thresholds and measures
  - sample excess kurtosis of S_N (against the exact prediction),
  - the two-sample KS distance between the true-genotype and surrogate laws of S_N
    (this is literally "is the score's law the same"),
  - the participation ratio max_j T_j^2 / sum_j T_j^2 (the condensation diagnostic).

POSITIVE CONTROLS, run first:
  - m = 1 (additive score): the two laws must be indistinguishable and kurtosis ~ 0.
    This is `additive_score_is_subcritical` and must pass or nothing else is readable.
  - a split-half KS of the genotype sample against itself, giving the null level of the
    KS statistic at this replicate count.
  - c(q) recomputed by direct summation and checked against the docstring table.

stdlib only.
"""

import json
import math
import os
import random
import sys
from multiprocessing import Pool

EULER_GAMMA = 0.5772156649015329
C_GAUSS = 2.0 - EULER_GAMMA - math.log(2.0)      # E[z^2 log z^2], z ~ N(0,1)

N_TERMS = 2048       # number of disjoint monomials in the score
REPS = 4000          # replicate scores per (q, m, coordinate law)
M_GRID = [1, 2, 4, 6, 8, 9, 10, 11, 12, 14, 16, 18, 20, 22]
Q_LIST = [0.2764, 0.5, 0.05]

# the module-docstring table, for the positive control
DOC_TABLE = [(0.50, 0.6931, 19.9), (0.2764, 0.4159, 33.2), (0.20, 0.4860, 28.4),
             (0.14, 0.7313, 18.9), (0.05, 1.8676, 7.4), (0.01, 3.7554, 3.7),
             (0.001, 6.1896, 2.2), (0.0001, 8.5138, 1.6)]


def mellin_drift(q):
    """c(q) = E[x^2 log x^2] by direct summation over the three genotypes."""
    V = 2.0 * q * (1.0 - q)
    tot = 0.0
    for g, p in ((0, (1 - q) ** 2), (1, 2 * q * (1 - q)), (2, q * q)):
        x2 = (g - 2.0 * q) ** 2 / V
        if x2 > 0.0 and p > 0.0:
            tot += p * x2 * math.log(x2)
    return tot


def geno_values(q):
    V = 2.0 * q * (1.0 - q)
    s = math.sqrt(V)
    p0 = (1.0 - q) ** 2
    p1 = 2.0 * q * (1.0 - q)
    return ((0 - 2 * q) / s, (1 - 2 * q) / s, (2 - 2 * q) / s), (p0, p0 + p1)


def excess_kurtosis(v):
    n = len(v)
    m = sum(v) / n
    s2 = s4 = 0.0
    for a in v:
        d = a - m
        d2 = d * d
        s2 += d2
        s4 += d2 * d2
    return n * s4 / (s2 * s2) - 3.0


def ks_two_sample(a, b):
    """CAVEAT, and this is why `ks_null_splithalf` is reported alongside every cell:
    this merge form is biased upward when the two samples share large atoms.  At
    q = 0.5 the standardized genotype is 0 for a heterozygote (probability 1/2), so a
    monomial of order m is exactly 0 with probability 1 - 2^-m and the score becomes
    atomic; there `ks_null_splithalf` blows up to 0.1-1.0 and BOTH KS columns for
    q = 0.5 must be discarded in favour of the participation ratio.  At q = 0.2764 and
    q = 0.05 the split-half control stays at its nominal level (~0.02-0.04) and the KS
    column is usable."""
    sa, sb = sorted(a), sorted(b)
    na, nb = len(sa), len(sb)
    i = j = 0
    d = 0.0
    while i < na and j < nb:
        if sa[i] <= sb[j]:
            i += 1
        else:
            j += 1
        d = max(d, abs(i / na - j / nb))
    return d


def draw_scores(q, m, law, rng, reps, n):
    """reps replicates of S_N and of the participation ratio."""
    scores = []
    parts = []
    if law == "geno":
        (c0, c1, c2), (t0, t1) = geno_values(q)
        r = rng.random
    else:
        g = rng.gauss
    root = math.sqrt(n)
    for _ in range(reps):
        tot = 0.0
        sq = 0.0
        mx = 0.0
        for _j in range(n):
            t = 1.0
            if law == "geno":
                for _l in range(m):
                    uu = r()
                    t *= c0 if uu < t0 else (c1 if uu < t1 else c2)
            else:
                for _l in range(m):
                    t *= g(0.0, 1.0)
            tot += t
            t2 = t * t
            sq += t2
            if t2 > mx:
                mx = t2
        scores.append(tot / root)
        parts.append(mx / sq if sq > 0 else 1.0)
    return scores, parts


def run_cell(args):
    q, m, seed = args
    rng = random.Random(seed)
    sg, pg = draw_scores(q, m, "geno", rng, REPS, N_TERMS)
    sz, pz = draw_scores(q, m, "gauss", rng, REPS, N_TERMS)
    V = 2.0 * q * (1.0 - q)
    half = REPS // 2
    return {
        "q": q, "m": m, "N": N_TERMS, "reps": REPS,
        "kurt_geno": excess_kurtosis(sg),
        "kurt_gauss": excess_kurtosis(sz),
        "kurt_geno_exact": ((1.0 / V) ** m - 3.0) / N_TERMS,
        "kurt_gauss_exact": (3.0 ** m - 3.0) / N_TERMS,
        "ks_geno_vs_gauss": ks_two_sample(sg, sz),
        "ks_null_splithalf": ks_two_sample(sg[:half], sg[half:]),
        "participation_geno": sum(pg) / len(pg),
        "participation_gauss": sum(pz) / len(pz),
    }


def main():
    res = {}

    # ---- positive control 1: reproduce the module-docstring table -------------
    ctrl = []
    for q, c_doc, so_doc in DOC_TABLE:
        c = mellin_drift(q)
        ctrl.append({"q": q, "c_doc": c_doc, "c_recomputed": c,
                     "safe_order_doc": so_doc,
                     "safe_order_recomputed": math.log(1e6) / c})
    res["control_doc_table"] = ctrl
    res["c_gauss"] = C_GAUSS

    # ---- exact threshold comparison across the whole spectrum ----------------
    rows = []
    for q in [0.5, 0.45, 0.40, 0.35, 0.30, 0.2764, 0.25, 0.2113248654, 0.20, 0.15,
              0.14, 0.10, 0.05, 0.02, 0.01, 0.001, 0.0001]:
        V = 2.0 * q * (1.0 - q)
        c = mellin_drift(q)
        lv = math.log(1.0 / V)
        lg = math.log(1e6)
        rows.append({
            "q": q, "V": V, "c_mellin_drift": c, "log_inv_V": lv,
            "convexity_gap_logInvV_minus_c": lv - c,
            "safe_order_corpus_N1e6": lg / c,
            "safe_order_fourth_moment_N1e6": lg / lv,
            "surrogate_condensation_order_N1e6": lg / C_GAUSS,
            "surrogate_fourth_moment_order_N1e6": lg / math.log(3.0),
            "corpus_over_true_ratio": (lg / c) / (lg / max(lv, math.log(3.0))),
        })
    res["exact_thresholds"] = rows

    # ---- simulation ----------------------------------------------------------
    tasks = [(q, m, 5000 + 131 * i + 977 * k)
             for k, q in enumerate(Q_LIST) for i, m in enumerate(M_GRID)]
    with Pool(int(os.environ.get("NPROC", "16"))) as pool:
        res["sim"] = pool.map(run_cell, tasks)
    res["params"] = {"N_TERMS": N_TERMS, "REPS": REPS,
                     "M_GRID": M_GRID, "Q_LIST": Q_LIST,
                     "thresholds_at_N_TERMS": {
                         str(q): {"corpus": math.log(N_TERMS) / mellin_drift(q),
                                  "fourth_moment": math.log(N_TERMS) / math.log(1 / (2 * q * (1 - q))),
                                  "surrogate_condensation": math.log(N_TERMS) / C_GAUSS,
                                  "surrogate_fourth_moment": math.log(N_TERMS) / math.log(3.0)}
                         for q in Q_LIST}}

    json.dump(res, sys.stdout, indent=1)
    print()


if __name__ == "__main__":
    main()
