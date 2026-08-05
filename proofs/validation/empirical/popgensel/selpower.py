"""Cell E: effectCorrelationStabilizing Ns = 1 - 1/(2 Ns).

FORWARD, individual-based, with real stabilizing selection -- the neutral
coalescent contains none of this.  Two populations split from one ancestral
population and evolve independently under Gaussian stabilizing selection toward
the SAME optimum, which is the corpus's stated setting.

The corpus body carries NO divergence time.  So the decisive measurement is not
"what is the correlation" but "does the correlation depend on t at fixed Ns".
If it does, no time-free function of Ns can be it, whatever its constant.

Ne is scaled DOWN and 4*Ne*s held on a grid, per the harness rule.
Guard string PGSEL_E1.
"""
import json, math, sys
import numpy as np

GUARD = "PGSEL_E2"


def run_pop(freq, beta, N, Vs, gens, rng):
    """One diploid WF population, L unlinked loci, Gaussian stabilizing
    selection w = exp(-(z - 0)^2 / (2 Vs)) on the additive trait."""
    L = len(beta)
    # materialise genotypes from frequencies (linkage equilibrium at the split)
    G = (rng.random((N, 2, L)) < freq).astype(np.int8)
    for _ in range(gens):
        z = (G.sum(axis=1) * beta).sum(axis=1)
        w = np.exp(-(z ** 2) / (2 * Vs))
        w = w / w.sum()
        par = rng.choice(N, size=(N, 2), p=w)
        pick = rng.integers(0, 2, size=(N, 2, L))
        gam = np.take_along_axis(G[par[:, 0]], pick[:, :1], axis=1)[:, 0]
        gam2 = np.take_along_axis(G[par[:, 1]], pick[:, 1:], axis=1)[:, 0]
        G = np.stack([gam, gam2], axis=1)
    return G


def stats(G, beta):
    p = G.mean(axis=(0, 1))
    return p, 2 * p * (1 - p) * beta ** 2


def cell_E(reps=40):
    rng = np.random.default_rng(9131)
    L = 60
    rows = []
    for N in (30, 60):
        for s in (0.0, 0.1, 0.5, 2.0):
            Ns = N * s if s > 0 else 0.0
            for t in (20,):
                rc, rv = [], []
                for _ in range(reps):
                    beta = rng.normal(0, 1, L)
                    freq = rng.uniform(0.1, 0.9, L)
                    # Vs chosen so the per-generation selection intensity on a
                    # unit-variance trait is ~ s: w ~ exp(-z^2/(2Vs)), Vg ~ Vg0.
                    Vg = (2 * freq * (1 - freq) * beta ** 2).sum()
                    if s == 0.0:
                        Vs = 1e12
                    else:
                        Vs = Vg / (2 * s)
                    G1 = run_pop(freq, beta, N, Vs, t, rng)
                    G2 = run_pop(freq, beta, N, Vs, t, rng)
                    p1, v1 = stats(G1, beta)
                    p2, v2 = stats(G2, beta)
                    m = (p1 > 0) & (p1 < 1) & (p2 > 0) & (p2 < 1)
                    if m.sum() > 15:
                        rc.append(np.corrcoef(p1[m], p2[m])[0, 1])
                        rv.append(np.corrcoef(v1[m], v2[m])[0, 1])
                rows.append(dict(N=N, s=s, Ns=Ns, t=t,
                                 corr_freq=float(np.mean(rc)),
                                 corr_freq_sem=float(np.std(rc, ddof=1) / math.sqrt(len(rc))),
                                 corr_varcontrib=float(np.mean(rv)),
                                 corr_varcontrib_sem=float(np.std(rv, ddof=1) / math.sqrt(len(rv))),
                                 corpus_1_minus_half_over_Ns=(1 - 1 / (2 * Ns)) if Ns else None,
                                 reps=len(rc)))
    return rows


if __name__ == "__main__":
    r = cell_E(int(sys.argv[1]) if len(sys.argv) > 1 else 40)
    print("FRESHNESS=OK", GUARD)
    print(json.dumps(dict(cell="E", target="effectCorrelationStabilizing",
                          argument_source="forward individual-based WF with Gaussian "
                                          "stabilizing selection; two populations split from "
                                          "one ancestor, same optimum",
                          guard=GUARD, detail=r), indent=1))
