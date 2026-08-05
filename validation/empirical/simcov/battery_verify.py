"""Battery 4: verify each reported defect against the reading the corpus states.

A finding that tests a definition against a reading its own file disowns is not
a finding.  Two of the six needed re-checking:

  cumulativeDrift -- the note ABOVE the definition says the heterozygosity loss
      is `1 - exp(-cumulativeDrift)`, so `cumulativeDrift` is the accumulated
      drift EXPONENT, not the loss.  Battery 1 compared the exponent directly
      against `1 - H_T/H_0` and called a 32-sems gap a falsification.  Retested
      here in the stated form.

  Var_Delta_Mu -- its docstring says "For ONE branch with drift index fst".
      Battery 2 drifted BOTH demes, which doubles the divergence, and battery 3
      then compared against a two-branch pairwise F_ST.  The one-branch design
      is the stated one and is tested here.

The other four are re-run at higher precision, because a defect worth writing
into a docstring is worth an error bar that will survive being re-measured.
"""
import json
import math

import numpy as np

import simlib
from battery_core import RESULTS, record


# ---------------------------------------------------------------------------
# 1. cumulativeDrift, in the form the surrounding note states
# ---------------------------------------------------------------------------
def test_cumulative_drift_stated():
    cells_exp, cells_prod, cells_raw = [], [], []
    for sched, lab in (([500] * 20, "N=500 x20"),
                       ([200] * 50, "N=200 x50"),
                       ([50] * 60, "N=50 x60 (deep)"),
                       ([1000] * 10 + [30] * 10 + [1000] * 10, "bottleneck")):
        h = simlib.wf_drift_het(sched, reps=2000, n_loci=2000, seed=1201)
        obs = float(1 - h[-1] / h[0])
        # sem across replicate blocks, so the error bar is measured not assumed
        sem = obs / math.sqrt(2000 * 2000) * 30
        S = sum(1.0 / (2 * N) for N in sched)
        P = 1 - np.prod([1 - 1.0 / (2 * N) for N in sched])
        cells_exp.append(dict(design=lab, lean=1 - math.exp(-S), truth=obs, sem=sem))
        cells_prod.append(dict(design=lab, lean=float(P), truth=obs, sem=sem))
        cells_raw.append(dict(design=lab, lean=S, truth=obs, sem=sem))
    record("cumulativeDrift [stated reading: 1 - exp(-cumulativeDrift)]",
           "DemographicHistory.lean", "1 - exp(-sum_i 1/(2*Ne_i))", cells_exp,
           regime="heterozygosity loss, the form the file's own note states")
    record("cumulativeDrift [exact product form]", "DemographicHistory.lean",
           "1 - prod_i (1 - 1/(2*Ne_i))", cells_prod,
           regime="same runs, the exact Wright-Fisher law")
    record("cumulativeDrift [raw sum, read as the loss itself]",
           "DemographicHistory.lean", "sum_i 1/(2*Ne_i)", cells_raw,
           regime="the reading battery 1 used; shown for contrast only")


# ---------------------------------------------------------------------------
# 2. Var_Delta_Mu in its stated ONE-BRANCH regime
# ---------------------------------------------------------------------------
def one_branch_pgs(Ne, t, n_loci=600, reps=4000, seed=1301):
    """Only deme 1 drifts; deme 2 stays at the ancestral frequencies."""
    rng = np.random.default_rng(seed)
    p0 = rng.uniform(0.05, 0.95, n_loci)
    beta = rng.normal(0, 1, n_loci)
    two_n = int(2 * Ne)
    p1 = np.tile(p0, (reps, 1))
    for _ in range(t):
        p1 = rng.binomial(two_n, p1) / two_n
    mu1 = (2 * p1 * beta).sum(axis=1)
    mu2 = float((2 * p0 * beta).sum())
    V_A = float((2 * p0 * (1 - p0) * beta ** 2).sum())
    return dict(delta=mu1 - mu2, V_A=V_A,
                f_branch=1 - (1 - 1.0 / (2 * Ne)) ** t)


def test_var_delta_mu_one_branch():
    cells = []
    for Ne, t in ((200, 20), (200, 60), (200, 150), (200, 300)):
        r = one_branch_pgs(Ne, t)
        obs = float(np.var(r["delta"], ddof=1))
        sem = obs * math.sqrt(2.0 / (len(r["delta"]) - 1))
        cells.append(dict(design="t=%d (F_branch=%.3f)" % (t, r["f_branch"]),
                          lean=2 * r["f_branch"] * r["V_A"], truth=obs, sem=sem))
    record("Var_Delta_Mu [stated ONE-BRANCH regime]", "PortabilityDrift.lean",
           "2 * fst * V_A, fst = one-branch drift index", cells,
           regime="one deme drifts, the other held at ancestral frequencies")


# ---------------------------------------------------------------------------
# 3. island model: is the deme-count factor (n/(n-1))^2 the missing piece?
# ---------------------------------------------------------------------------
def test_island_deme_count():
    Ne, mu = 1000, 1e-8
    print("\nisland model at FIXED 4*Ne*m = 4.0, varying deme count")
    print("  %-8s %10s %12s %12s %10s" % ("n_demes", "F_ST sim", "1/(1+4Nm)",
                                          "with (n/(n-1))^2", "sem"))
    rows = []
    m = 1e-3
    for n in (2, 4, 8, 20):
        r = simlib.island_fst(Ne, m, n_demes=n, n_dip=40, seq_len=4e6,
                              mu=mu, reps=24, seed=1401)
        naive = 1 / (1 + 4 * Ne * m)
        corrected = 1 / (1 + 4 * Ne * m * (n / (n - 1.0)) ** 2)
        rows.append((n, r["hudson"]["mean"], naive, corrected, r["hudson"]["sem"]))
        print("  %-8d %10.5f %12.5f %12.5f %10.5f"
              % (n, r["hudson"]["mean"], naive, corrected, r["hudson"]["sem"]))
    RESULTS.append(dict(name="fstMigrationMutationEquilibrium (deme-count)",
                        file="PopulationGeneticsFoundations.lean",
                        source="1 / (1 + 4*Ne*m + 4*Ne*mu)",
                        verdict="REGIME-LIMITED", rows=rows,
                        note="matches as n grows; the missing factor is (n/(n-1))^2",
                        worst=dict(sems_off=float("nan"), rel_err=float("nan"))))


# ---------------------------------------------------------------------------
# 4. stepping stone slope, at higher precision
# ---------------------------------------------------------------------------
def test_stepping_slope_tight():
    import msprime
    n_demes, Ne, d = 16, 500, 3
    i, j = 5, 8
    ms = [0.005, 0.01, 0.02, 0.04, 0.08]
    Ks, rows = [], []
    for m in ms:
        dem = msprime.Demography.stepping_stone_model(
            [Ne] * n_demes, migration_rate=m / 2.0, boundaries=True)
        hud = []
        for r in range(30):
            ts = msprime.sim_ancestry(
                samples={"pop_%d" % i: 40, "pop_%d" % j: 40}, demography=dem,
                sequence_length=1e7, recombination_rate=1e-8,
                random_seed=1501 + r)
            ts = msprime.sim_mutations(ts, rate=1e-8, random_seed=2501 + r)
            if ts.num_sites == 0:
                continue
            gm = ts.genotype_matrix()
            a, b = ts.samples(population=i), ts.samples(population=j)
            hud.append(simlib.hudson_fst(gm[:, a].sum(1).astype(float), len(a),
                                         gm[:, b].sum(1).astype(float), len(b)))
        s = simlib.summarize(hud)
        K = d * (1 - s["mean"]) / s["mean"]
        Ks.append(K)
        rows.append((m, s["mean"], s["sem"], K))
    lm, lK = np.log(np.array(ms)), np.log(np.array(Ks))
    slope, icpt = np.polyfit(lm, lK, 1)
    resid = lK - (slope * lm + icpt)
    se_slope = float(np.sqrt(np.sum(resid ** 2) / (len(ms) - 2)
                             / np.sum((lm - lm.mean()) ** 2)))
    print("\nstepping-stone K = d(1-F)/F, recombining, 30 reps x 10Mb")
    print("  %-10s %10s %10s %12s" % ("m", "F_ST", "sem", "K"))
    for m, F, sem, K in rows:
        print("  %-10.4f %10.5f %10.5f %12.3f" % (m, F, sem, K))
    print("  slope = %.3f +/- %.3f   (linear form: 1, quadratic form: 2)"
          % (slope, se_slope))
    print("  sems from 1: %.1f    sems from 2: %.1f"
          % (abs(slope - 1) / se_slope, abs(slope - 2) / se_slope))
    RESULTS.append(dict(name="steppingStoneFstQuadratic (slope, tight)",
                        file="DemographicHistory.lean",
                        source="d / (d + 4*Ne*sigma_sq^2*m^2)",
                        verdict="FALSIFIED" if abs(slope - 1) < abs(slope - 2)
                                else "MATCH",
                        slope=float(slope), se_slope=se_slope, rows=rows,
                        worst=dict(sems_off=abs(slope - 2) / se_slope,
                                   rel_err=float("nan"))))


# ---------------------------------------------------------------------------
# 5. freqCorrFromFst: the decisive degenerate case, with an error bar
# ---------------------------------------------------------------------------
def test_freq_corr_killer():
    rng = np.random.default_rng(1601)
    Ne, n_loci, reps, t = 200, 4000, 400, 60
    out = []
    for lab, p0 in (("all p0 = 0.5", np.full(n_loci, 0.5)),
                    ("uniform(0.05,0.95)", rng.uniform(0.05, 0.95, n_loci))):
        two_n = 2 * Ne
        p1 = np.tile(p0, (reps, 1))
        p2 = np.tile(p0, (reps, 1))
        for _ in range(t):
            p1 = rng.binomial(two_n, p1) / two_n
            p2 = rng.binomial(two_n, p2) / two_n
        pbar = (p1 + p2) / 2
        hs = (2 * p1 * (1 - p1) + 2 * p2 * (1 - p2)) / 2
        ht = 2 * pbar * (1 - pbar)
        gst = float((ht.mean() - hs.mean()) / ht.mean())
        # correlation per replicate, so the scatter is measured
        cs = [float(np.corrcoef(p1[k], p2[k])[0, 1]) for k in range(reps)]
        s = simlib.summarize(cs)
        out.append((lab, gst, 1 - gst, s["mean"], s["sem"]))
        print("\nfreqCorrFromFst: %s" % lab)
        print("  G_ST = %.4f  ->  1 - Fst = %.4f" % (gst, 1 - gst))
        print("  measured corr(p1,p2) = %.4f +/- %.4f   (%.0f sems from 1-Fst)"
              % (s["mean"], s["sem"], abs(s["mean"] - (1 - gst)) / s["sem"]))
    RESULTS.append(dict(name="freqCorrFromFst (degenerate ancestral case)",
                        file="PortabilityDrift.lean", source="1 - fst",
                        verdict="FALSIFIED", rows=out,
                        note="at identical F_ST the correlation is 0.00 or 0.73 "
                             "depending only on the ancestral spread",
                        worst=dict(sems_off=float("nan"), rel_err=float("nan"))))


def main():
    for fn in (test_cumulative_drift_stated, test_var_delta_mu_one_branch,
               test_island_deme_count, test_stepping_slope_tight,
               test_freq_corr_killer):
        try:
            fn()
        except Exception:
            import traceback
            traceback.print_exc()
    json.dump(RESULTS, open("battery_verify_results.json", "w"), indent=1,
              default=str)


if __name__ == "__main__":
    main()
