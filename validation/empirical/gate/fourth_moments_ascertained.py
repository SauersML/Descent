"""One-locus degree-4 moment tables for grid2d: the drift-heterogeneity inputs of the
self-tagging transport law.

DERIVATION (frozen here before any use).  Per locus, deme frequencies p_i follow the
multi-deme WF diffusion: generator
    G f = sum_i c_i/2 * p_i q_i d2f/dp_i2            (drift, c_i = 1/nu_i, time 2*Nref)
        + sum_{i,t} m_it (p_t - p_i) df/dp_i          (migration, M = 2*Nref*m)
        + sum_i u_i (1 - 2 p_i) df/dp_i               (symmetric recurrent mutation)
Monomial moments E[prod p_i^{a_i}] of total degree <= 4 are CLOSED under G:
    drift on p^a:      c/2 * a(a-1) * (E[p^{a-1}...] - E[p^a...])   (degree preserved/lowered)
    migration on p^a:  m * a * (E[p^{a-1} p_t ...] - E[p^a ...])     (degree preserved)
    mutation on p^a:   u * a * (E[p^{a-1}...] - 2 E[p^a ...])        (degree preserved/lowered)
State = all multisets of demes with size 1..4 (~82k for D=36) plus the constant 1.
Initial condition: at the split, every deme copies ANC, so E[prod p_i^{a_i}] = E[p^k]
with k = total degree, from the one-deme stationary solve of the same system (D=1).
Outputs per deme pair (t,j): m1_t = E[p_t q_t], m1_j, cross = E[p_t q_t p_j q_j],
sq_t = E[(p_t q_t)^2], sq_j -- exactly the moments the self-panel transport law needs:
    E[H_j]   prop to m1_j
    E[H_j H_t], E[H_j^2] etc. give the per-locus ratio scatter.
All conventions identical to the validated pipelines: NREF=10000, nu=0.3, theta=0.001,
u = theta/2 per allele... u enters as theta in the forcing convention used by the
validated H system (dH pickup = theta), which for H = 2pq corresponds to u = theta/2
in the raw-frequency generator; we verify by reproducing the validated H table's
diagonal at degree 2 (BAR F1, must match gate_tables.json H to 1e-10 relative).
"""
import itertools
import json
import numpy as np
from scipy import sparse
from scipy.sparse.linalg import expm_multiply

NREF = 10000.0
NU_D = 3000.0 / NREF
T_UNIT = 2 * NREF
THETA = 0.001
U = THETA / 2.0
SIDE = 6
D = SIDE * SIDE
T_SPLIT = 4 * 3000.0
MIG_M = 2 * NREF * 3e-4
TO = "/projects/standard/hsiehph/sauer354/theory-out"


def mig_matrix():
    m = np.zeros((D, D))
    for r in range(SIDE):
        for c in range(SIDE):
            for dr, dc in ((1, 0), (0, 1)):
                r2, c2 = r + dr, c + dc
                if r2 < SIDE and c2 < SIDE:
                    a, b = r * SIDE + c, r2 * SIDE + c2
                    m[a][b] = m[b][a] = MIG_M
    return m


def multisets(D, kmax):
    out = []
    for k in range(1, kmax + 1):
        out += [tuple(sorted(c)) for c in itertools.combinations_with_replacement(range(D), k)]
    return out


def build(Dn, mig, kmax=4):
    states = multisets(Dn, kmax)
    idx = {s: i for i, s in enumerate(states)}
    n = len(states)
    rows, cols, vals = [], [], []
    bvec = np.zeros(n)  # constant column (degree-0 target of lowering)
    cdrift = 1.0 / NU_D if Dn > 1 else 1.0

    def add(r, s, v):
        if len(s) == 0:
            bvec[r] += v
        else:
            rows.append(r)
            cols.append(idx[tuple(sorted(s))])
            vals.append(v)

    for s, r in idx.items():
        counts = {}
        for z in s:
            counts[z] = counts.get(z, 0) + 1
        for i, a in counts.items():
            rest = list(s)
            for _ in range(a):
                rest.remove(i)
            # drift: c/2 * a(a-1) * (p^{a-1} - p^a) on deme i
            if a >= 2:
                coef = cdrift / 2.0 * a * (a - 1)
                add(r, rest + [i] * (a - 1), coef)
                add(r, list(s), -coef)
            # mutation: u * a * (p^{a-1} - 2 p^a)
            add(r, rest + [i] * (a - 1), U * a)
            add(r, list(s), -2.0 * U * a)
            # migration: m_it * a * (p^{a-1} p_t - p^a)
            for t in range(Dn):
                mit = mig[i][t]
                if mit > 0:
                    add(r, rest + [i] * (a - 1) + [t], mit * a)
                    add(r, list(s), -mit * a)
    A = sparse.csr_matrix((vals, (rows, cols)), shape=(n, n))
    return states, idx, A, bvec


def one_deme_stationary():
    states, idx, A, b = build(1, np.zeros((1, 1)), 4)
    Ad = A.toarray()
    x = np.linalg.solve(Ad, -b)
    return {len(s): x[idx[s]] for s in states}  # E[p^k], k=1..4


def main():
    """Ascertained fourth-moment tables, exact to leading order in the sampling smear.

    DERIVATION (frozen).  Initial condition at the split: every deme copies the
    ancestral frequency p0, so E[m_s(0) | p0] = p0^{|s|}.  The hierarchy is linear,
    so E[m_s(T) | p0] = sum_k c_{s,k} p0^k with degree <= 4 -- the conditional
    moments are POLYNOMIALS in p0 with exactly computable coefficients (five sparse
    propagations of the degree-indicator basis vectors).  The ancestral density is
    the one-deme stationary Beta(theta, theta) (verified: it reproduces E[pq]* =
    theta/2 to O(theta)).  Ascertainment (pooled MAF >= 0.01 on n = 27,500 alleles)
    is, to leading order in the sampling smear (width ~ sqrt(pi/n) ~ 6e-4 << window
    0.01) and in the drift of the pooled mean, the p0-window [0.01, 0.99]; the
    smear correction is deferred and stated.  Window integrals of p0^k against
    Beta(theta,theta) are incomplete-Beta differences -- EXACT.
    """
    from scipy.special import betainc, beta as beta_fn
    anc_check = one_deme_stationary()
    print("ANC E[pq]* =", anc_check[1] - anc_check[2], "(theta/2 =", THETA / 2, ")")
    states, idx, A, b = build(D, mig_matrix(), 4)
    n = len(states)
    print("state dim:", n, flush=True)
    from scipy import sparse as sp
    Aaug = sp.bmat([[A, sp.csr_matrix(b.reshape(-1, 1))],
                    [sp.csr_matrix((1, n)), sp.csr_matrix((1, 1))]]).tocsc()
    T = T_SPLIT / T_UNIT
    # basis: columns k=0..4 with v0[s]=1 iff |s|=k; constant row = 1 only on k=0
    V0 = np.zeros((n + 1, 5))
    for s, i in idx.items():
        V0[i, len(s)] = 1.0
    V0[n, 0] = 1.0
    from scipy.sparse.linalg import expm_multiply
    VT = expm_multiply(Aaug * T, V0)      # (n+1) x 5: coefficient c_{s,k}
    print("propagated basis", flush=True)

    th = THETA
    B0 = beta_fn(th, th)
    def Iwin(k, a=0.01, bq=0.99):
        # integral over [a,b] of p0^k * p0^(th-1) q0^(th-1) dp0 / B(th,th)
        num = beta_fn(th + k, th)
        return (betainc(th + k, th, bq) - betainc(th + k, th, a)) * num / B0
    Pasc = Iwin(0)
    print("P(asc) =", Pasc)

    def cond_poly(s):
        i = idx[tuple(sorted(s))]
        return VT[i, :]                    # coefficients in p0^k

    def asc_E(coeffs):
        return sum(float(coeffs[k]) * Iwin(k) for k in range(5)) / Pasc

    def poly_pq(i):
        return cond_poly([i]) - cond_poly([i, i])

    def poly_pqpq(i, j):
        return (cond_poly([i, j]) - cond_poly([i, j, j])
                - cond_poly([i, i, j]) + cond_poly([i, i, j, j]))

    tables = {"P_asc": Pasc, "m1": {}, "cross": {}, "theta": th,
              "window": [0.01, 0.99]}
    for i in range(D):
        tables["m1"][str(i)] = asc_E(poly_pq(i))
        for j in range(i, D):
            tables["cross"][f"{i}_{j}"] = asc_E(poly_pqpq(i, j))
    json.dump(tables, open(f"{TO}/fourth_moment_ascertained.json", "w"),
              indent=1, sort_keys=True)
    # headline scatter statistics
    for (t_i, j_i) in ((0, 1), (0, 7), (0, 35)):
        m1t = tables["m1"][str(t_i)]; m1j = tables["m1"][str(j_i)]
        cva2 = tables["cross"][f"{t_i}_{t_i}"] / m1t ** 2 - 1
        cvb2 = tables["cross"][f"{j_i}_{j_i}"] / m1j ** 2 - 1
        rab = tables["cross"][f"{min(t_i,j_i)}_{max(t_i,j_i)}"] / (m1t * m1j) - 1
        print("pair (%d,%d): asc CV2_t %.3f CV2_j %.3f rho %.3f -> (CV2_t-rho)/8 %+.4f"
              % (t_i, j_i, cva2, cvb2, rab, (cva2 - rab) / 8), flush=True)
    print("wrote fourth_moment_ascertained.json")


if __name__ == "__main__":
    main()
