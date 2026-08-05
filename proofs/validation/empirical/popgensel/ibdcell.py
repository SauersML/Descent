"""Cell H: AssortativeMatingPGS.ibdFst = d / (4*N*sigma_sq + d)

Rousset's continuous isolation-by-distance law, rearranged: the body is
equivalent to `F / (1 - F) = d / (4*N*sigma^2)`, i.e. Rousset's regression
statistic is LINEAR in distance with slope `1 / (4*N*sigma^2)`.

The measurement is deliberately convention-free on two counts, because this
corpus has shipped a factor-of-four F_ST error before.

  1. The observable is Rousset's own `a_r = (pi_between(d) - pi_within) /
     pi_within`, built from probabilities of identity, NOT from any named F_ST
     estimator.  Nei's G_ST between two demes is a quarter of the corpus's
     pairwise F_ST, so any cell reporting a factor of four here would be
     reporting an estimator choice.
  2. The discrimination is the SLOPE of `a_r` against `d`.  A slope test is
     immune to an additive convention offset, and it separates the constant `4`
     from `2` and `8` directly.

The habitat is a RING of demes, so every deme is equivalent and there are no
edge effects; distances are kept well below the ring size so the law's
unbounded-habitat regime applies.  Under a stepping-stone reparametrisation the
density reading the docstring insists on is the deme size per unit spacing and
`sigma^2 = 2*m` for nearest-neighbour migration at rate `m` in each direction.

Positive control: the intercept.  Rousset's `a_r` must extrapolate to 0 at
`d = 0`, and a fitted intercept far from zero means the linear regime was left.

Guard PGSEL_H1.
"""
import json, math, sys
import numpy as np
import msprime

GUARD = "PGSEL_H1"


def ring_ar(D, Nd, m, dists, nsamp, seqlen, mu, r, seed):
    """Mean a_r = (pi_between(d) - pi_within)/pi_within on a ring of D demes."""
    dem = msprime.Demography.stepping_stone_model([Nd] * D, migration_rate=m,
                                                  boundaries=False)
    samples = {f"pop_{i}": nsamp for i in range(D)}
    ts = msprime.sim_ancestry(samples=samples, demography=dem,
                              sequence_length=seqlen, recombination_rate=r,
                              random_seed=seed)
    ts = msprime.sim_mutations(ts, rate=mu, random_seed=seed + 1)
    sets = [ts.samples(population=i) for i in range(D)]
    pw = ts.divergence(sets, indexes=[(i, j) for i in range(D) for j in range(D)],
                       mode="site")
    pw = np.array(pw).reshape(D, D)
    piw = np.mean([pw[i, i] for i in range(D)])
    out = {}
    for d in dists:
        vals = [pw[i, (i + d) % D] for i in range(D)]
        out[d] = (np.mean(vals) - piw) / piw
    return out, piw


def cell_H(seeds=6):
    rows = []
    for (D, Nd, m) in ((40, 20, 0.05), (40, 40, 0.10)):
        sigma_sq = 2 * m                      # nearest-neighbour, spacing 1
        dists = [1, 2, 3, 4, 5, 6]
        per = {d: [] for d in dists}
        for s in range(seeds):
            ar, _ = ring_ar(D, Nd, m, dists, 4, 5e5, 1e-6, 1e-8, 1000 + 7 * s)
            for d in dists:
                per[d].append(ar[d])
        mean = np.array([np.mean(per[d]) for d in dists])
        sem = np.array([np.std(per[d], ddof=1) / math.sqrt(seeds) for d in dists])
        x = np.array(dists, dtype=float)
        # weighted straight-line fit; the intercept is the positive control
        w = 1.0 / sem ** 2
        A = np.vstack([x, np.ones_like(x)]).T
        W = np.diag(w)
        cov = np.linalg.inv(A.T @ W @ A)
        beta = cov @ (A.T @ W @ mean)
        slope, intercept = beta[0], beta[1]
        slope_sem = math.sqrt(cov[0, 0])
        int_sem = math.sqrt(cov[1, 1])
        cands = {
            "corpus 1/(4 N sigma^2)": 1 / (4 * Nd * sigma_sq),
            "COMP 1/(2 N sigma^2)": 1 / (2 * Nd * sigma_sq),
            "COMP 1/(8 N sigma^2)": 1 / (8 * Nd * sigma_sq),
            "PLANTED 1.4x corpus": 1.4 / (4 * Nd * sigma_sq),
        }
        rows.append(dict(D=D, Nd=Nd, m=m, sigma_sq=sigma_sq, seeds=seeds,
                         a_r_mean=dict(zip(map(str, dists), mean)),
                         a_r_sem=dict(zip(map(str, dists), sem)),
                         slope=slope, slope_sem=slope_sem,
                         positive_control_intercept=intercept,
                         positive_control_intercept_sem=int_sem,
                         pred=cands,
                         sems={k: (v - slope) / slope_sem for k, v in cands.items()}))
    return rows


if __name__ == "__main__":
    r = cell_H(int(sys.argv[1]) if len(sys.argv) > 1 else 6)
    print("FRESHNESS=OK", GUARD)
    print(json.dumps(dict(cell="H", target="ibdFst", guard=GUARD,
                          argument_source="msprime ring stepping-stone; observable is "
                                          "Rousset's a_r from identity probabilities, "
                                          "discriminated by its SLOPE in distance, so no "
                                          "F_ST estimator convention enters",
                          detail=r), indent=1, default=float))
