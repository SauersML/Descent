"""Battery 26: does stepping-stone F_ST grow linearly in distance?

`steppingStoneFst = min 1 (fst_neighbor * (1 + alpha * (d - 1)))` says F_ST is
LINEAR in the separation `d`, capped at one. The sibling
`demoSteppingStoneFst = d / (d + 4 Ne m sigma_sq)` says it SATURATES, approaching
one only as `d` grows without bound. Those are different functions of `d` and the
disagreement is largest exactly where a linear form must eventually fail.

The two are separated here without committing to any constant. Measure `F_ST` at
several separations on one lattice, then ask which functional form the sequence
follows:

  linear      F(d) / F(1) = 1 + alpha (d - 1)     -- a straight line in d
  saturating  d (1 - F(d)) / F(d) = K             -- a CONSTANT, independent of d

The second is the sharper test, because it predicts a constant rather than a
slope: any drift in `K` across `d` refutes the saturating form, and a straight
line through `F(d)/F(1)` refutes nothing on its own since two points always lie
on one.

Interior demes only, so no boundary reflection enters, and recombining so each
replicate carries many independent genealogies. F_ST is read from coalescence
times, which needs no estimator convention.
"""
import json
import math

import numpy as np

import simlib
from battery_core import RESULTS, record


def stepping_fst(n_demes, Ne, m, i, j, reps=26, seed=1):
    import msprime
    dem = msprime.Demography.stepping_stone_model(
        [Ne] * n_demes, migration_rate=m / 2.0, boundaries=True)
    vals = []
    for r in range(reps):
        ts = msprime.sim_ancestry(
            samples={"pop_%d" % i: 30, "pop_%d" % j: 30}, demography=dem,
            sequence_length=6e6, recombination_rate=1e-8, random_seed=seed + r)
        A, B = ts.samples(population=i), ts.samples(population=j)
        da = ts.diversity([A], mode="branch")[0]
        db = ts.diversity([B], mode="branch")[0]
        dab = ts.divergence([A, B], indexes=[(0, 1)], mode="branch")[0]
        vals.append(1.0 - ((da + db) / 2.0) / dab)
    return simlib.summarize(vals)


def main():
    n_demes, Ne, m = 20, 500, 0.01
    base = 4                      # interior anchor deme
    ds = [1, 2, 3, 5, 8]
    F, S = {}, {}
    for d in ds:
        s = stepping_fst(n_demes, Ne, m, base, base + d, seed=21001)
        F[d], S[d] = s["mean"], s["sem"]
        print("  d=%d  F_ST = %.5f ± %.5f" % (d, F[d], S[d]))

    # --- saturating form: K = d(1-F)/F must be CONSTANT in d ----------------
    cells_sat = []
    K1 = 1 * (1 - F[1]) / F[1]
    for d in ds[1:]:
        K = d * (1 - F[d]) / F[d]
        rel = S[d] / F[d] / (1 - F[d])
        cells_sat.append(dict(design="K at d=%d (vs d=1)" % d, lean=K1,
                              truth=K, sem=K * rel))
    record("demoSteppingStoneFst [saturating: K constant in d]",
           "DemographicHistory.lean", "d / (d + K)", cells_sat,
           regime="K = d(1-F)/F fitted at d=1 and compared at every other "
                  "separation; the saturating form predicts it is constant",
           control=dict(design="K at d=1 reproduces itself by construction",
                        lean=K1, truth=K1 * 1.0000001, sem=K1 * 0.02))

    # --- linear form: F(d)/F(1) = 1 + alpha (d-1) ---------------------------
    alpha = (F[2] / F[1] - 1) / 1.0        # fit alpha at d=2 only
    cells_lin = []
    for d in ds[2:]:
        cells_lin.append(dict(design="d=%d (alpha from d=2)" % d,
                              lean=F[1] * (1 + alpha * (d - 1)), truth=F[d],
                              sem=S[d]))
    record("steppingStoneFst [linear in d]", "PortabilityDrift.lean",
           "min 1 (fst_neighbor * (1 + alpha * (d - 1)))", cells_lin,
           regime="alpha fitted at d=2 and used to predict d=3, 5 and 8; a "
                  "form fitted to all points would agree with anything monotone",
           control=dict(design="the fitted point d=2 reproduces itself",
                        lean=F[2], truth=F[2] * 1.0000001, sem=S[2]))

    json.dump(RESULTS, open("battery_bulk11_results.json", "w"), indent=1,
              default=str)
    print("\n\n================ SUMMARY ================")
    for r in RESULTS:
        w = r.get("worst", {})
        print("%-20s %-48s worst %9.2f sems, %7.2f%% rel"
              % (r["verdict"], r["name"], w.get("sems_off", float("nan")),
                 100 * w.get("rel_err", float("nan"))))


if __name__ == "__main__":
    main()
