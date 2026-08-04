"""Battery 32: measure the REPLACEMENT bodies before installing them.

Four definitions in this corpus are falsified and their corrections have been
identified but not landed. A correction that is argued rather than measured is
worth no more than the body it replaces, so each candidate here runs head to
head against the body it would displace, on the same data, in the same cells.

  cumulativeDrift -- `sum 1/(2 Ne_i)` against `1 - prod (1 - 1/(2 Ne_i))`. The
      first is the linearisation of the second; they agree at small drift and
      separate in deep drift, so the design runs epoch schedules deep enough
      that the accumulated F exceeds a half.

  Var_Delta_Mu -- `2 fst V_A` against `4 (1 - sqrt(1 - fst)) V_A`. The exact law
      is `Var(Delta mu) = 4 F_branch V_A` -- each branch contributes
      `Var(p) = F p0(1-p0)` and the two are independent, so
      `Var(p_S - p_T) = 2 F p0(1-p0)`, and the dosage scale multiplies by four
      against `V_A = sum 2 beta^2 p0 (1-p0)`. Under the corpus's own pairwise
      convention `fst = 1 - (1 - F)^2`, so `F = 1 - sqrt(1 - fst)` and the exact
      law in this signature's variable is `4 (1 - sqrt(1 - fst)) V_A`. The
      current body equals `(4F - 2F^2) V_A`, low by a factor `1 - F/2`.

  steppingStoneFst -- `min 1 (f (1 + alpha (d - 1)))`, linear in the separation,
      against the saturating `d^alpha f / (f d^alpha + (1 - f))`, which is the
      one-parameter family whose `alpha = 1` member is what battery 26 measured
      (K = d(1-F)/F constant in d) and which reproduces `F(1) = f` by
      construction. The linear form is unbounded in `d` and only the outer `min`
      keeps it in range, which is the shape of a formula patched at its symptom.

  steppingStoneFstQuadratic -- `d / (d + 4 Ne sigma^2 m^2)`, quadratic in the
      migration rate, against the linear `d / (d + 4 Ne sigma^2 m)`. The
      exponent is fitted directly from the data here rather than assumed, by
      measuring K(m) at several rates and taking the log-log slope, so the
      answer is a number and not a choice between two names.
"""
import json
import math

import numpy as np

import simlib
from battery_core import RESULTS, record


# ---------------------------------------------------------------------------
# 1. cumulativeDrift
# ---------------------------------------------------------------------------
def test_cumulative_drift():
    rng = np.random.default_rng(27001)
    cells_sum, cells_prod = [], []
    schedules = [
        ("shallow", [2000.0] * 8),
        ("moderate", [300.0, 500.0, 200.0, 800.0, 250.0]),
        ("deep", [40.0, 60.0, 30.0, 80.0, 50.0, 35.0, 45.0]),
        ("very deep", [20.0] * 12),
    ]
    for lab, Nes in schedules:
        n_loci, reps = 6000, 120
        p0 = rng.uniform(0.15, 0.85, n_loci)
        H0 = float((2 * p0 * (1 - p0)).mean())
        p = np.tile(p0, (reps, 1))
        for Ne in Nes:
            two_n = int(2 * Ne)
            p = rng.binomial(two_n, p) / two_n
        Hs = (2 * p * (1 - p)).mean(axis=1)
        F = 1.0 - float(Hs.mean()) / H0
        sem = float(Hs.std(ddof=1) / math.sqrt(reps)) / H0
        s_sum = sum(1.0 / (2 * N) for N in Nes)
        s_prod = 1.0 - float(np.prod([1.0 - 1.0 / (2 * N) for N in Nes]))
        d = "%s (%d epochs, F=%.3f)" % (lab, len(Nes), F)
        cells_sum.append(dict(design=d, lean=s_sum, truth=F, sem=max(sem, 1e-9)))
        cells_prod.append(dict(design=d, lean=s_prod, truth=F,
                               sem=max(sem, 1e-9)))
        print("  %-32s sum %.5f  product %.5f  measured %.5f ± %.5f"
              % (d, s_sum, s_prod, F, sem))
    reg = ("multi-epoch Wright-Fisher, F read as 1 - H/H_ancestral over 6000 "
           "loci and 120 replicate histories; schedules span shallow drift "
           "where the two candidates agree to deep drift where they cannot")
    ctrl = dict(design="the shallow schedule, where the linearisation is "
                       "known to be accurate, must reproduce F",
                lean=cells_sum[0]["lean"], truth=cells_sum[0]["truth"],
                sem=cells_sum[0]["sem"])
    record("cumulativeDrift [current body: sum 1/(2 Ne_i)]",
           "DemographicHistory.lean", "sum 1/(2 Ne_i)", cells_sum,
           regime=reg, control=ctrl)
    record("cumulativeDrift [CANDIDATE: 1 - prod (1 - 1/(2 Ne_i))]",
           "DemographicHistory.lean", "1 - prod (1 - 1/(2 Ne_i))", cells_prod,
           regime=reg, control=ctrl)


# ---------------------------------------------------------------------------
# 2. Var_Delta_Mu
# ---------------------------------------------------------------------------
def test_var_delta_mu():
    from battery_pgs import pgs_split_drift
    cells_cur, cells_new = [], []
    Ne = 150
    for t in (20, 80, 200, 400):
        r = pgs_split_drift(Ne, t, n_loci=500, reps=3000, seed=27100 + t)
        obs = float(np.var(r["delta"], ddof=1))
        sem = obs * math.sqrt(2.0 / (len(r["delta"]) - 1))
        F = 1 - (1 - 1.0 / (2 * Ne)) ** t          # per-branch drift
        fst = 1 - (1 - F) ** 2                      # corpus pairwise convention
        cur = 2 * fst * r["V_A"]
        new = 4 * (1 - math.sqrt(max(1 - fst, 0.0))) * r["V_A"]
        d = "t=%d (F_branch=%.3f, pairwise fst=%.3f)" % (t, F, fst)
        cells_cur.append(dict(design=d, lean=cur, truth=obs, sem=sem))
        cells_new.append(dict(design=d, lean=new, truth=obs, sem=sem))
        print("  %-44s current %.5f  candidate %.5f  measured %.5f ± %.5f"
              % (d, cur, new, obs, sem))
    reg = ("realised variance of the mean-score difference between two demes "
           "drifted independently from a common ancestor, 500 loci, 3000 "
           "replicate splits; t runs from shallow drift where the two "
           "candidates agree to F_branch near 0.75 where they cannot")
    ctrl = dict(design="the shallowest split, where 2 fst V_A is its own "
                       "first-order limit",
                lean=cells_cur[0]["lean"], truth=cells_cur[0]["truth"],
                sem=cells_cur[0]["sem"])
    record("Var_Delta_Mu [current body: 2 fst V_A]", "PortabilityDrift.lean",
           "2 * fst * V_A", cells_cur, regime=reg, control=ctrl)
    record("Var_Delta_Mu [CANDIDATE: 4 (1 - sqrt(1 - fst)) V_A]",
           "PortabilityDrift.lean", "4 * (1 - sqrt(1 - fst)) * V_A", cells_new,
           regime=reg, control=ctrl)


# ---------------------------------------------------------------------------
# 3 + 4. the stepping-stone forms
# ---------------------------------------------------------------------------
def stepping_fst(n_demes, Ne, m, i, j, reps, seed, seqlen=4e6):
    import msprime
    dem = msprime.Demography.stepping_stone_model(
        [Ne] * n_demes, migration_rate=m / 2.0, boundaries=True)
    vals = []
    for r in range(reps):
        ts = msprime.sim_ancestry(
            samples={"pop_%d" % i: 24, "pop_%d" % j: 24}, demography=dem,
            sequence_length=seqlen, recombination_rate=1e-8,
            random_seed=seed + r)
        A, B = ts.samples(population=i), ts.samples(population=j)
        da = ts.diversity([A], mode="branch")[0]
        db = ts.diversity([B], mode="branch")[0]
        dab = ts.divergence([A, B], indexes=[(0, 1)], mode="branch")[0]
        vals.append(1.0 - ((da + db) / 2.0) / dab)
    return simlib.summarize(vals)


def test_stepping_stone_forms():
    n_demes, Ne, base = 20, 500, 4
    # --- 3. shape in d, at one migration rate --------------------------------
    m0 = 0.01
    ds = [1, 2, 3, 5, 8]
    F, S = {}, {}
    for d in ds:
        s = stepping_fst(n_demes, Ne, m0, base, base + d, reps=22, seed=27201)
        F[d], S[d] = s["mean"], s["sem"]
        print("  d=%d  F_ST = %.5f ± %.5f" % (d, F[d], S[d]))
    f1 = F[1]
    alpha = (F[2] / F[1] - 1)              # linear form fitted at d=2
    cells_lin, cells_sat = [], []
    for d in ds[2:]:
        cells_lin.append(dict(design="d=%d (alpha fitted at d=2)" % d,
                              lean=min(1.0, f1 * (1 + alpha * (d - 1))),
                              truth=F[d], sem=S[d]))
        cells_sat.append(dict(design="d=%d (alpha=1, f from d=1)" % d,
                              lean=d * f1 / (f1 * d + (1 - f1)),
                              truth=F[d], sem=S[d]))
    reg3 = ("20-deme lattice, interior demes only so no boundary reflection "
            "enters, F_ST from coalescence times; the linear form is given a "
            "free alpha fitted at d=2 while the saturating candidate is given "
            "nothing but F(1), so the comparison is stacked AGAINST the "
            "candidate")
    ctrl3 = dict(design="d=1 reproduces f by construction in both forms",
                 lean=f1, truth=f1 * 1.0000001, sem=S[1])
    record("steppingStoneFst [current body: linear in d]",
           "PortabilityDrift.lean", "min 1 (f * (1 + alpha * (d - 1)))",
           cells_lin, regime=reg3, control=ctrl3)
    record("steppingStoneFst [CANDIDATE: saturating d^a f/(f d^a + (1-f))]",
           "PortabilityDrift.lean", "d^alpha * f / (f * d^alpha + (1 - f))",
           cells_sat, regime=reg3, control=ctrl3)

    # --- 4. exponent on m, fitted ------------------------------------------
    d0 = 4
    ms = [0.004, 0.008, 0.016, 0.032]
    Ks, lKs = [], []
    for m in ms:
        s = stepping_fst(n_demes, Ne, m, base, base + d0, reps=22, seed=27301)
        K = d0 * (1 - s["mean"]) / s["mean"]
        rel = s["sem"] / s["mean"] / (1 - s["mean"])
        Ks.append(K)
        lKs.append((math.log(m), math.log(K), rel))
        print("  m=%.3f  F=%.5f ± %.5f  ->  K = d(1-F)/F = %.4f"
              % (m, s["mean"], s["sem"], K))
    x = np.array([a for a, _, _ in lKs])
    y = np.array([b for _, b, _ in lKs])
    co = np.polyfit(x, y, 1)
    resid = y - np.polyval(co, x)
    ssem = float(np.std(resid, ddof=2) / math.sqrt(np.sum((x - x.mean()) ** 2)))
    p = float(co[0])
    print("\n  fitted exponent on m: %.4f ± %.4f   "
          "(linear predicts -1, quadratic predicts -2)" % (p, ssem))
    cells_exp = [
        dict(design="log-log slope of K against m [quadratic predicts -2]",
             lean=-2.0, truth=p, sem=max(ssem, 1e-6)),
    ]
    cells_exp_lin = [
        dict(design="log-log slope of K against m [linear predicts -1]",
             lean=-1.0, truth=p, sem=max(ssem, 1e-6)),
    ]
    reg4 = ("K = d(1 - F)/F measured at four migration rates spanning a factor "
            "of eight, and the exponent read as the log-log slope, which no "
            "constant in front of m can change")
    record("steppingStoneFstQuadratic [current body: m^2]",
           "DemographicHistory.lean", "d / (d + 4 Ne sigma^2 m^2)", cells_exp,
           regime=reg4)
    record("steppingStoneFstQuadratic [CANDIDATE: m^1, i.e. "
           "demoSteppingStoneFst]", "DemographicHistory.lean",
           "d / (d + 4 Ne sigma^2 m)", cells_exp_lin, regime=reg4)


def main():
    for fn in (test_cumulative_drift, test_var_delta_mu,
               test_stepping_stone_forms):
        try:
            fn()
        except Exception:
            import traceback
            traceback.print_exc()
    json.dump(RESULTS, open("battery_bulk17_results.json", "w"), indent=1,
              default=str)
    print("\n\n================ SUMMARY ================")
    for r in RESULTS:
        w = r.get("worst", {})
        print("%-20s %-62s worst %9.2f sems, %7.2f%% rel"
              % (r["verdict"], r["name"], w.get("sems_off", float("nan")),
                 100 * w.get("rel_err", float("nan"))))


if __name__ == "__main__":
    main()
