"""Ascertained degree-2 moments through the exact stress histories.

Same construction as fourth_moments_ascertained.py / serial1d_tables.py, degree 2:
conditional moments given ancestral p0 are polynomials in p0 of degree <= |s|
(this survives splits exactly -- copy pullback maps monomials to monomials), so
three basis columns k=0,1,2 propagate through each case's stage sequence
(splits then expm of the stage generator, matching compose_operator), and the
ascertainment window p0 in [0.01, 0.99] finishes with incomplete-Beta integrals
over the Beta(theta,theta) stationary ancestral law -- the identical convention
the grid2d and serial1d gates passed blind with.

Outputs per case: m1[j] = E[p_j q_j | asc]  (per-locus within-deme dosage
variance / 2 per unit beta^2), pp[i_j] = E[p_i p_j | asc]  (for the between-deme
dosage-mean variance in the pooled-standardization denominator), P_asc.
"""
import itertools
import json

import numpy as np
from scipy.linalg import expm
from scipy.special import betainc, beta as beta_fn

TO = "/projects/standard/hsiehph/sauer354/theory-out"
spec = json.load(open(f"{TO}/stress_spec.json"))
THETA = spec["THETA"]
U = THETA / 2.0
KMAX = 2


def multisets(d, kmax):
    out = []
    for k in range(1, kmax + 1):
        out += [tuple(sorted(c)) for c in
                itertools.combinations_with_replacement(range(d), k)]
    return out


def deg_build(d, mig, nus):
    """Generator for E[prod p_z], z in multiset s, |s| <= KMAX; last row/col = const."""
    states = multisets(d, KMAX)
    idx = {s: i for i, s in enumerate(states)}
    n = len(states)
    A = np.zeros((n + 1, n + 1))

    def add(r, s, v):
        if len(s) == 0:
            A[r, n] += v
        else:
            A[r, idx[tuple(sorted(s))]] += v

    for s, r in idx.items():
        counts = {}
        for z in s:
            counts[z] = counts.get(z, 0) + 1
        for i, a in counts.items():
            rest = list(s)
            for _ in range(a):
                rest.remove(i)
            c = 1.0 / nus[i]
            if a >= 2:
                coef = c / 2.0 * a * (a - 1)
                add(r, rest + [i] * (a - 1), coef)
                add(r, list(s), -coef)
            add(r, rest + [i] * (a - 1), U * a)
            add(r, list(s), -2.0 * U * a)
            for t2 in range(d):
                m = mig[i][t2]
                if m > 0:
                    add(r, rest + [i] * (a - 1) + [t2], m * a)
                    add(r, list(s), -m * a)
    return states, idx, A


def deg_split(V, states_old, idx_old, states_new):
    """New deme = copy of parent encoded in states_new construction caller-side."""
    raise NotImplementedError  # replaced by explicit pullback below


def pullback(V, idx_old, states_new, child, parent):
    out = np.zeros((len(states_new) + 1, V.shape[1]))
    for i, s in enumerate(states_new):
        src = tuple(sorted(parent if z == child else z for z in s))
        out[i] = V[idx_old[src]]
    out[-1] = V[-1]
    return out


def case_tables(stages):
    d = 1
    states, idx, _ = deg_build(1, [[0.0]], [1.0])
    n = len(states)
    V = np.zeros((n + 1, KMAX + 1))
    for s, i in idx.items():
        V[i, len(s)] = 1.0
    V[n, 0] = 1.0
    for stg in stages:
        for parent in stg["splits"]:
            child = d
            d += 1
            states_new = multisets(d, KMAX)
            V = pullback(V, idx, states_new, child, parent)
            states = states_new
            idx = {s: i for i, s in enumerate(states)}
        _, _, A = deg_build(d, stg["M"], stg["nu"])
        V = expm(A * stg["T"]) @ V

    B0 = beta_fn(THETA, THETA)

    def Iwin(k, a=0.01, b=0.99):
        return (betainc(THETA + k, THETA, b)
                - betainc(THETA + k, THETA, a)) * beta_fn(THETA + k, THETA) / B0

    Pasc = Iwin(0)

    def asc_E(coeffs):
        return sum(float(coeffs[k]) * Iwin(k) for k in range(KMAX + 1)) / Pasc

    def cp(s):
        return V[idx[tuple(sorted(s))]]

    tabs = {"P_asc": Pasc, "m1": {}, "pp": {}}
    for i in range(d):
        tabs["m1"][str(i)] = asc_E(cp([i]) - cp([i, i]))
        for j in range(i, d):
            tabs["pp"][f"{i}_{j}"] = asc_E(cp([i, j]))
    return tabs, d


def main():
    out = {}
    for case in ("S1", "S2", "anchor"):
        stages = spec["cases"][case]["stages"]
        tabs, d = case_tables(stages)
        out[case] = tabs
        m1 = tabs["m1"]
        print(case, "d =", d, "P_asc %.6f" % tabs["P_asc"])
        for j in sorted(m1, key=int):
            pj2 = tabs["pp"][f"{j}_{j}"]
            print("  deme", j, "E[pq|asc] %.5f" % m1[j], "E[p^2|asc] %.5f" % pj2)
    # anchor sanity: symmetric two-deme case must give equal m1 across demes
    a = out["anchor"]["m1"]
    assert abs(a["0"] - a["1"]) < 1e-10, ("anchor asymmetry", a)
    json.dump(out, open(f"{TO}/stress_asc2.json", "w"), indent=1, sort_keys=True)
    print("wrote stress_asc2.json")


if __name__ == "__main__":
    main()
