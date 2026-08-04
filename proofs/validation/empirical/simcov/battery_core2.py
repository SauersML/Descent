"""Battery 1b: the three designs from battery 1 that were testing the wrong thing.

Battery 1 reported three falsifications that were artefacts of the test, not
defects in the corpus.  Each is rebuilt here so that it measures the quantity
the definition actually names:

  driftLDRetention  -- battery 1 compared it against the ratio of raw `E[D^2]`
      between generations and found the ratio EXCEEDS one at `c = 0`.  That is
      correct population genetics and not a defect: drift destroys `E[D]` but
      GENERATES variance in `D`, so `E[D^2]` grows.  The retention factor is a
      coefficient inside the `driftLDStep` recurrence on the normalised
      `sigma_d^2 = E[D^2] / E[p(1-p)q(1-q)]`, which is what is tested here, as a
      one-step map measured at many starting values.

  steppingStoneFst  -- battery 1 had to invent a value for `sigma_sq`, and the
      answer moved by two orders of magnitude with the convention chosen.  A
      test whose verdict is set by an unstated convention measures the
      convention.  Rebuilt CONVENTION-FREE: hold everything fixed and vary only
      `d`, then only `m`, and ask what FUNCTIONAL FORM the simulation follows.
      `d/(d+K)` versus `d/(d+K')` cannot be told apart by any `sigma_sq`, but
      `K ∝ m` versus `K ∝ m^2` can, and that is exactly the difference between
      the validated sibling and the quadratic form under test.

  neiGst -- battery 1 compared a per-site parametric formula against a
      ratio-of-averages estimator.  Those differ by Jensen's inequality for any
      correct formula, so the comparison could only ever "falsify".  Rebuilt as
      a per-site identity check, with the aggregation gap reported separately as
      a convention observation rather than a defect.
"""
import json
import math

import numpy as np

import simlib
from battery_core import RESULTS, record


# ---------------------------------------------------------------------------
# driftLDStep as a one-step map on sigma_d^2
# ---------------------------------------------------------------------------
def sigma_d2_trajectory(Ne, c, gens, reps, seed):
    """Track normalised sigma_d^2 = E[D^2] / E[p(1-p)q(1-q)] generation by generation."""
    rng = np.random.default_rng(seed)
    two_n = int(2 * Ne)
    p0 = q0 = 0.5
    D0 = 0.15
    f = np.empty((reps, 4))
    f[:, 0] = p0 * q0 + D0
    f[:, 1] = p0 * (1 - q0) - D0
    f[:, 2] = (1 - p0) * q0 - D0
    f[:, 3] = (1 - p0) * (1 - q0) + D0
    out = []
    for _ in range(gens + 1):
        p = f[:, 0] + f[:, 1]
        q = f[:, 0] + f[:, 2]
        D = f[:, 0] - p * q
        denom = float(np.mean(p * (1 - p) * q * (1 - q)))
        out.append(float(np.mean(D ** 2) / denom) if denom > 0 else float("nan"))
        Dr = D * (1 - c)
        g = np.empty_like(f)
        g[:, 0] = p * q + Dr
        g[:, 1] = p * (1 - q) - Dr
        g[:, 2] = (1 - p) * q - Dr
        g[:, 3] = (1 - p) * (1 - q) + Dr
        g = np.clip(g, 0.0, None)
        g /= g.sum(axis=1, keepdims=True)
        for i in range(reps):
            f[i] = rng.multinomial(two_n, g[i]) / two_n
    return np.array(out)


def test_drift_ld_step():
    """One-step map: does Q_{t+1} = (1-c)^2 (1/(2Ne) + (1 - 1/(2Ne)) Q_t)?"""
    lean_step = lambda Ne, c, Q: (1 - c) ** 2 * (1 / (2 * Ne) + (1 - 1 / (2 * Ne)) * Q)
    cells = []
    for Ne, c in ((100, 0.0), (100, 0.05), (500, 0.01), (500, 0.05)):
        traj = sigma_d2_trajectory(Ne, c, gens=25, reps=6000, seed=61)
        # compare prediction from Q_t against measured Q_{t+1}, over the run
        preds, obs = [], []
        for t in range(5, 24):        # skip the transient from the fixed start
            if not (np.isfinite(traj[t]) and np.isfinite(traj[t + 1])):
                continue
            preds.append(lean_step(Ne, c, traj[t]))
            obs.append(traj[t + 1])
        preds, obs = np.array(preds), np.array(obs)
        rel = (preds - obs) / obs
        cells.append(dict(design="Ne=%d c=%.2f" % (Ne, c),
                          lean=float(preds.mean()), truth=float(obs.mean()),
                          sem=float(obs.std(ddof=1) / math.sqrt(len(obs)))))
    record("driftLDStep (one-step map on sigma_d^2)", "LDDecayTheory.lean",
           "(1-c)^2 * (1/(2*Ne) + (1 - 1/(2*Ne)) * Q)", cells,
           regime="WF two-locus, sigma_d^2 = E[D^2]/E[p(1-p)q(1-q)]")


# ---------------------------------------------------------------------------
# stepping stone: convention-free functional-form discrimination
# ---------------------------------------------------------------------------
def stepping_fst(n_demes, Ne, m, i, j, reps=14, seed=71):
    import msprime
    # migration_rate is per ordered neighbour pair; m/2 each way makes the
    # TOTAL emigration rate of an interior deme equal m.
    dem = msprime.Demography.stepping_stone_model(
        [Ne] * n_demes, migration_rate=m / 2.0, boundaries=True)
    hud = []
    for r in range(reps):
        ts = msprime.sim_ancestry(
            samples={"pop_%d" % i: 40, "pop_%d" % j: 40}, demography=dem,
            sequence_length=4e6, random_seed=seed + r)
        ts = msprime.sim_mutations(ts, rate=1e-8, random_seed=seed + 500 + r)
        if ts.num_sites == 0:
            continue
        gm = ts.genotype_matrix()
        a, b = ts.samples(population=i), ts.samples(population=j)
        hud.append(simlib.hudson_fst(gm[:, a].sum(1).astype(float), len(a),
                                     gm[:, b].sum(1).astype(float), len(b)))
    return simlib.summarize(hud)


def test_stepping_stone_form():
    """Which power of m does the stepping-stone F_ST scale factor follow?

    Both candidate definitions have the shape `d / (d + K)`.  Fit K from the
    simulation at each m -- K = d (1 - F) / F -- and ask how K scales with m.
    The validated sibling says K ∝ m; the quadratic form under test says K ∝ m^2.
    No value of sigma_sq can change an exponent, so this is convention-free.
    """
    n_demes, Ne = 16, 500
    i, j, d = 5, 8, 3            # interior demes only: no boundary reflection
    ms = [0.005, 0.01, 0.02, 0.04]
    Ks, rows = [], []
    for m in ms:
        s = stepping_fst(n_demes, Ne, m, i, j)
        F = s["mean"]
        K = d * (1 - F) / F
        Ks.append(K)
        rows.append((m, F, s["sem"], K))
    lm, lK = np.log(np.array(ms)), np.log(np.array(Ks))
    slope = float(np.polyfit(lm, lK, 1)[0])
    print("\nstepping-stone scale factor K = d(1-F)/F, fitted against m")
    print("  %-10s %10s %10s %12s" % ("m", "F_ST", "sem", "K"))
    for m, F, sem, K in rows:
        print("  %-10.4f %10.5f %10.5f %12.3f" % (m, F, sem, K))
    print("  log-log slope d(log K)/d(log m) = %.3f" % slope)
    print("    linear form  d/(d + 4*Ne*m*sigma_sq)   predicts slope  1")
    print("    quadratic    d/(d + 4*Ne*sigma_sq^2*m^2) predicts slope 2")
    verdict = ("supports the LINEAR sibling" if abs(slope - 1) < abs(slope - 2)
               else "supports the QUADRATIC form")
    print("  --> %s" % verdict)

    # And the d-dependence at fixed m, which both forms share.
    m = 0.01
    print("\n  d-dependence at m=%.3f (both forms predict K constant in d)" % m)
    Kd = []
    for dd in (1, 2, 3, 5):
        s = stepping_fst(n_demes, Ne, m, 5, 5 + dd)
        F = s["mean"]
        K = dd * (1 - F) / F
        Kd.append(K)
        print("    d=%d  F_ST=%.5f (sem %.5f)  K=%.2f" % (dd, F, s["sem"], K))
    spread = (max(Kd) - min(Kd)) / np.mean(Kd)
    print("    K spread across d: %.0f%%  (a d-independent K is the shape "
          "d/(d+K); a drifting K is not)" % (100 * spread))
    RESULTS.append(dict(name="steppingStoneFstQuadratic (form discrimination)",
                        file="DemographicHistory.lean",
                        source="d / (d + 4*Ne*sigma_sq^2*m^2)",
                        verdict="FALSIFIED" if abs(slope - 1) < abs(slope - 2)
                                else "MATCH",
                        slope=slope, K_by_d=Kd, K_spread=float(spread),
                        rows=[list(map(float, r)) for r in rows],
                        note="convention-free: exponent of m cannot be changed "
                             "by any sigma_sq convention",
                        worst=dict(sems_off=float("nan"), rel_err=float("nan"))))


# ---------------------------------------------------------------------------
# neiGst: per-site identity, plus the aggregation gap as a convention note
# ---------------------------------------------------------------------------
def test_nei_gst_identity():
    def nei(p1, p2):
        pbar = (p1 + p2) / 2
        return 1 - (p1 * (1 - p1) + p2 * (1 - p2)) / (2 * pbar * (1 - pbar))

    rng = np.random.default_rng(4)
    p1 = rng.uniform(0.02, 0.98, 200000)
    p2 = rng.uniform(0.02, 0.98, 200000)
    # per-site truth: (H_T - H_S)/H_T evaluated at the same site
    hs = p1 * (1 - p1) + p2 * (1 - p2)
    pbar = (p1 + p2) / 2
    ht = 2 * pbar * (1 - pbar)
    per_site_truth = (ht - hs) / ht
    lean_vals = nei(p1, p2)
    max_abs = float(np.max(np.abs(lean_vals - per_site_truth)))
    print("\nneiGst per-site identity vs (H_T - H_S)/H_T")
    print("  max |lean - truth| over 200k draws: %.3e  -> %s"
          % (max_abs, "IDENTITY HOLDS" if max_abs < 1e-9 else "MISMATCH"))
    ratio_of_avgs = float((ht.mean() - hs.mean()) / ht.mean())
    mean_of_ratios = float(per_site_truth.mean())
    print("  aggregation gap (a CONVENTION issue, not a defect):")
    print("    ratio of averages %.5f vs mean of per-site ratios %.5f  (%.1f%%)"
          % (ratio_of_avgs, mean_of_ratios,
             100 * abs(ratio_of_avgs - mean_of_ratios) / ratio_of_avgs))
    RESULTS.append(dict(name="neiGst (per-site identity)",
                        file="Conventions.lean",
                        source="1 - (p1(1-p1)+p2(1-p2)) / (ploidy*pbar*(1-pbar))",
                        verdict="MATCH" if max_abs < 1e-9 else "FALSIFIED",
                        max_abs_err=max_abs,
                        aggregation_gap_pct=100 * abs(ratio_of_avgs - mean_of_ratios)
                        / ratio_of_avgs,
                        note="per-site identity holds; the ratio-of-averages vs "
                             "mean-of-ratios gap is a declared-convention question",
                        worst=dict(sems_off=0.0, rel_err=max_abs)))


# ---------------------------------------------------------------------------
# coalFst, with error bars tight enough to be worth quoting
# ---------------------------------------------------------------------------
def test_coalFst_tight():
    lean = lambda t, Ne: t / (t + 2 * Ne)
    Ne = 1000
    cells = []
    for t in (200, 500, 1000, 2000, 4000):
        r = simlib.split_fst(Ne, t, n_dip=60, seq_len=2e7, reps=40, seed=81)
        cells.append(dict(design="t=%d Ne=%d" % (t, Ne), lean=lean(t, Ne),
                          truth=r["hudson"]["mean"], sem=r["hudson"]["sem"]))
    record("coalFst [tight]", "PopulationGeneticsFoundations.lean",
           "t / (t + 2 * Ne)", cells,
           regime="clean split, Hudson ratio-of-averages, 40 reps x 20Mb")


def main():
    for fn in (test_drift_ld_step, test_stepping_stone_form,
               test_nei_gst_identity, test_coalFst_tight):
        try:
            fn()
        except Exception:
            import traceback
            traceback.print_exc()
    json.dump(RESULTS, open("battery_core2_results.json", "w"), indent=1, default=str)


if __name__ == "__main__":
    main()
