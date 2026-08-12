"""BLIND GATE, stage 1: analytic moment tables for the gnomon grid2d demography.

Runs on the compute node. Emits gate_tables.json BEFORE any gate seed is generated.

The H block of the low-order system is closed (H rows reference only H), so the full
36x36 pairwise-H matrix integrates as a 666-dimensional augmented linear system using
the arbiter-validated rate law verbatim (theory-out/serial1d_compose_check.py, BAR E5
green vs moments.LD). The DD tables at rho = 0, 1, 10 are read from the sparse-operator
production run (theory-out/grid2d_lambda_ladder.json, bars V1-V3 green vs moments.LD).

Conventions (identical to the validated runs): N_ref = 10000, nu_anc = 1,
nu_deme = 0.3, time in 2*N_ref generations, M = 2*N_ref*m, theta = 0.001. The gate
predictor consumes only RATIOS of these tables, which are invariant to theta and to
the time-unit convention.

grid2d (gnomon gen_real_pt.py::dem_grid2d): 6x6 = 36 demes, N = 3000, ANC 10000,
simultaneous split at 4*N = 12000 generations, rook migration m = 3e-4.
"""
import json
import hashlib
import numpy as np
from scipy.linalg import expm

THETA = 0.001
NREF = 10000.0
NU_D = 3000.0 / NREF
T_UNIT = 2 * NREF
SIDE = 6
D = SIDE * SIDE
T_SPLIT_GEN = 4 * 3000.0
MIG_M = 2 * NREF * 3e-4

TO = "/projects/standard/hsiehph/sauer354/theory-out"


def h_pairs():
    return [(i, j) for i in range(D) for j in range(i, D)]


def build_h_system():
    pairs = h_pairs()
    idx = {p: k for k, p in enumerate(pairs)}

    def key(i, j):
        return idx[(i, j) if i <= j else (j, i)]

    mig = np.zeros((D, D))
    for r in range(SIDE):
        for c in range(SIDE):
            for dr, dc in ((1, 0), (0, 1)):
                r2, c2 = r + dr, c + dc
                if r2 < SIDE and c2 < SIDE:
                    a, b = r * SIDE + c, r2 * SIDE + c2
                    mig[a][b] = mig[b][a] = MIG_M
    n = len(pairs)
    A = np.zeros((n + 1, n + 1))
    cc = 1.0 / NU_D
    for (i, j), row in idx.items():
        if i == j:
            A[row, key(i, i)] += -cc
        for t in range(D):
            if mig[i][t] > 0:
                A[row, key(t, j)] += mig[i][t]
                A[row, key(i, j)] += -mig[i][t]
            if mig[j][t] > 0:
                A[row, key(i, t)] += mig[j][t]
                A[row, key(i, j)] += -mig[j][t]
        A[row, n] = THETA  # (u_i + u_j)/2 with equal u
    return A, pairs, idx


def main():
    # ancestral one-deme stationary H: -1*H + theta = 0 -> H_anc = theta (nu_anc = 1)
    h_anc = THETA
    A, pairs, idx = build_h_system()
    n = len(pairs)
    state = np.concatenate([np.full(n, h_anc), [1.0]])
    state = expm(A * (T_SPLIT_GEN / T_UNIT)) @ state
    H = {}
    for (i, j), k in idx.items():
        H[f"{i}_{j}"] = float(state[k])

    lad = json.load(open(f"{TO}/grid2d_lambda_ladder.json"))
    DD = {}
    for rho_key, blk in lad["production"].items():
        tab = {}
        for row in blk["DD_canonical_table"]:
            # rows are [i, j, value]
            i, j, v = int(row[0]), int(row[1]), float(row[2])
            tab[f"{i}_{j}"] = v
        DD[rho_key] = tab

    out = {"H": H, "DD": DD, "D": D, "side": SIDE,
           "conventions": {"NREF": NREF, "NU_D": NU_D, "THETA": THETA,
                           "T_SPLIT_GEN": T_SPLIT_GEN, "MIG_M": MIG_M},
           "sources": {"H": "gate_tables.py 666-dim augmented expm, arbiter-validated rate law",
                       "DD": "grid2d_lambda_ladder.json production tables, bars V1-V3 green"}}
    path = f"{TO}/gate_tables.json"
    json.dump(out, open(path, "w"), indent=1, sort_keys=True)
    sha = hashlib.sha256(open(path, "rb").read()).hexdigest()
    print("wrote", path, "sha256", sha)
    print("H00", H["0_0"], "H(0,35)", H.get("0_35"), "Hmax-diag",
          max(H[f"{i}_{i}"] for i in range(D)), "Hmin-diag",
          min(H[f"{i}_{i}"] for i in range(D)))


if __name__ == "__main__":
    main()
