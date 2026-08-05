"""Battery: the three cells `battery_dis1.py` could not decide, redesigned.

  fstTransientAt   VOID there. The control -- that at zero migration the fitted
      decay base reproduces the known heterozygosity decay `1 + theta` -- missed
      by 22.8 sems, and the reason is a convention mismatch in the ORACLE, not
      in the definition: a biallelic two-way mutation model contracts the
      between-deme deviation by `(1 - 2 mu)^2` per generation, so its rate is
      `2 theta` in units of `1/(2Ne)`, while `hetDecayFromScaled` carries the
      INFINITE-ALLELES rate `theta`. Rather than build an infinite-alleles island
      engine to settle a claim that does not need one, mutation is switched OFF
      here. At `mu = 0` the two candidate decay bases differ ONLY by migration,
      which is the whole question, and the `M = 0` cell becomes a control that
      both candidates predict and that the pure-drift result `1/(2Ne)` fixes
      independently.

  asymmetricFst    NO POWER there. The sum candidate was right in every cell but
      the three cells all had the SAME sum, so the design could not have
      rejected it. Six designs spanning a factor of four in the sum.

  sourceBestLinearWeightsFromLD   never reported: `verdict.report` raises
      KeyError on any verdict `classify` returns before it computes `sems_off`,
      so SELF-TEST and GENERATIVE SELF-TEST crash the reporter. Guarded here.
"""
import math

import numpy as np

from battery_core import RESULTS, record


def island_transient_nomut(Ne, d, bigM, gens, n_loci=240, reps=10, seed=1):
    """Island model, NO mutation, started identical in every deme."""
    m = bigM / (4.0 * Ne)
    two_n = int(2 * Ne)
    rng = np.random.default_rng(seed)
    traj = np.zeros((reps, gens + 1))
    for r in range(reps):
        p0 = rng.uniform(0.15, 0.85, n_loci)
        p = np.tile(p0, (d, 1))
        for t in range(gens + 1):
            pbar = p.mean(axis=0)
            den = (pbar * (1 - pbar)).mean()
            traj[r, t] = (p.var(axis=0).mean() / den) if den > 0 else 0.0
            if t == gens:
                break
            p = (1 - m) * p + m * pbar[None, :]
            p = rng.binomial(two_n, np.clip(p, 0, 1)) / two_n
    return traj


def fit_R(traj, Ne, tau):
    """Fitted approach rate in units of 1/(2Ne), one value per replicate.

    The plateau is read over `[9 tau, 12 tau]`, which is after equilibration and
    before the slow global-fixation rise that has no plateau of its own; the
    exponential is fitted where the approach is 20 to 80 percent complete.
    """
    out = []
    n = traj.shape[1]
    lo, hi = int(9 * tau), min(int(12 * tau), n)
    for r in range(traj.shape[0]):
        f = traj[r]
        fstar = f[lo:hi].mean()
        if fstar <= 0:
            continue
        y = 1.0 - f[:lo] / fstar
        t = np.arange(len(y))
        ok = (y > 0.2) & (y < 0.8)
        if ok.sum() < 5:
            continue
        lam = math.exp(np.polyfit(t[ok], np.log(y[ok]), 1)[0])
        out.append((1.0 - lam) * 2 * Ne)
    return np.array(out)


def test_transient_rate_nomut():
    Ne, d = 100, 24
    cells_corpus, cells_cand = [], []
    control = None
    for bigM in (0.0, 2.0, 6.0, 16.0):
        rate = 1.0 + bigM * d / (d - 1.0)
        tau = 2 * Ne / rate
        gens = int(12 * tau) + 5
        traj = island_transient_nomut(Ne, d, bigM, gens, seed=8101 + int(bigM))
        R = fit_R(traj, Ne, tau)
        obs, sem = float(R.mean()), float(R.std(ddof=1) / math.sqrt(len(R)))
        lab = "M=%.1f" % bigM
        # hetDecayFactor at theta = 0 is the pure-drift factor 1 - 1/(2Ne),
        # so the corpus's transient approaches at R = 1 whatever the migration
        cells_corpus.append(dict(design=lab, lean=1.0, truth=obs, sem=sem))
        cells_cand.append(dict(design=lab, lean=rate, truth=obs, sem=sem))
        if bigM == 0.0:
            control = dict(design="M=0 vs the pure-drift rate 1/(2Ne)",
                           lean=1.0, truth=obs, sem=sem)
    reg = ("24-deme forward Wright-Fisher island model, NO mutation, started "
           "identical; the fitted per-generation decay base of F(t)/F(plateau) "
           "-- a shape, so invariant to the F_ST convention -- expressed as "
           "R = (1 - lam) * 2Ne")
    record("fstTransientAt [decay base = hetDecayFactor, which carries no "
           "migration: R = 1]", "PortabilityDrift.lean",
           "(1/(1+theta+bigM)) * (1 - hetDecayFactor^t)", cells_corpus,
           control=control, regime=reg)
    record("fstTransientAt [CANDIDATE: the equilibrium's own forces set the "
           "rate, R = 1 + bigM*d/(d-1)]", "PortabilityDrift.lean",
           "(1/(1+theta+bigM)) * (1 - (1 - (1+theta+bigM)/(2Ne))^t)",
           cells_cand, control=control, regime="same runs, same fits")


def two_deme_asym_fst(Ne, m12, m21, reps=24, seed=1):
    import msprime
    dem = msprime.Demography()
    dem.add_population(name="A", initial_size=Ne)
    dem.add_population(name="B", initial_size=Ne)
    dem.set_migration_rate(source="A", dest="B", rate=m12)
    dem.set_migration_rate(source="B", dest="A", rate=m21)
    vals = []
    for r in range(reps):
        ts = msprime.sim_ancestry(samples={"A": 25, "B": 25}, demography=dem,
                                  sequence_length=4e6, recombination_rate=1e-8,
                                  random_seed=seed + r)
        A, B = ts.samples(population=0), ts.samples(population=1)
        da = ts.diversity([A], mode="branch")[0]
        db = ts.diversity([B], mode="branch")[0]
        dab = ts.divergence([A, B], indexes=[(0, 1)], mode="branch")[0]
        vals.append(1.0 - 0.5 * (da + db) / dab)
    v = np.array(vals)
    return float(v.mean()), float(v.std(ddof=1) / math.sqrt(len(v)))


def test_asymmetric_fst_spanning():
    Ne = 1000
    designs = ((5.0e-4, 5.0e-4), (1.0e-3, 1.0e-3), (2.0e-3, 2.0e-3),
               (1.5e-3, 5.0e-4), (1.8e-3, 2.0e-4), (3.5e-3, 5.0e-4))
    cells_big, cells_small, cells_sum = [], [], []
    control = None
    for m12, m21 in designs:
        obs, sem = two_deme_asym_fst(Ne, m12, m21, seed=32001)
        lab = "m12=%.1e m21=%.1e" % (m12, m21)
        big, small = max(m12, m21), min(m12, m21)
        cells_big.append(dict(design=lab, lean=1 / (1 + 4 * Ne * big),
                              truth=obs, sem=sem))
        cells_small.append(dict(design=lab, lean=1 / (1 + 4 * Ne * small),
                                truth=obs, sem=sem))
        cells_sum.append(dict(design=lab, lean=1 / (1 + 4 * Ne * (m12 + m21)),
                              truth=obs, sem=sem))
        if m12 == m21 == 1.0e-3:
            control = dict(design="the symmetric cell vs the two-deme island "
                                  "value 1/(1 + 2*4Ne*m), validated "
                                  "independently in battery_correct.py",
                           lean=1 / (1 + 2 * 4 * Ne * m12), truth=obs, sem=sem)
    reg = ("two demes with asymmetric migration, Ne=1000, F_ST read as "
           "1 - E[T_within]/E[T_between] from branch lengths so no estimator "
           "convention enters, 24 replicates of 4 Mb; the SUM of the two rates "
           "spans a factor of four across the six designs, and three designs "
           "share a sum while differing in asymmetry, so a law depending on "
           "more than the sum would separate")
    record("asymmetricFst [m_into = the larger rate]", "PortabilityDrift.lean",
           "1 / (1 + 4*Ne*m_into)", cells_big, control=control, regime=reg)
    record("asymmetricFst [m_into = the smaller rate]", "PortabilityDrift.lean",
           "1 / (1 + 4*Ne*m_into)", cells_small, control=control,
           regime="same runs, the other reading of the single rate argument")
    record("asymmetricFst [CANDIDATE: 1/(1 + 4Ne(m12 + m21))]",
           "PortabilityDrift.lean", "1 / (1 + 4*Ne*(m12 + m21))", cells_sum,
           control=control, regime="same runs, the total-exchange reading")


def test_source_weights():
    n, c, t = 40000, 40, 12
    rng = np.random.default_rng(71001)
    L = rng.normal(0, 1, (c + t, c + t)) * 0.25 + np.eye(c + t)
    Sigma = L @ L.T
    X = rng.multivariate_normal(np.zeros(c + t), Sigma, n)
    X = (X - X.mean(0)) / X.std(0)
    S = X.T @ X / n
    beta_c = rng.normal(0, 1, c)
    y = X[:, :c] @ beta_c + rng.normal(0, 1, n)
    w_lean = np.linalg.solve(S[c:, c:], S[c:, :c] @ beta_c)
    A = X[:, c:]
    w_fit, *_ = np.linalg.lstsq(A, y, rcond=None)
    resid = y - A @ w_fit
    cov = np.linalg.inv(A.T @ A) * float(resid @ resid) / (n - t)
    se = np.sqrt(np.diag(cov))
    z = np.abs(w_lean - w_fit) / se
    k = int(np.argmax(z))
    cells = [dict(design="worst of %d coordinates" % t, lean=float(w_lean[k]),
                  truth=float(w_fit[k]), sem=float(se[k]))]
    cells += [dict(design="coordinate %d" % j, lean=float(w_lean[j]),
                   truth=float(w_fit[j]), sem=float(se[j]))
              for j in range(3)]
    record("sourceBestLinearWeightsFromLD", "DGP.lean",
           "sigmaTagSource^-1 * sigmaTagCausal * betaCausal", cells,
           selected_from=t,
           regime="least-squares weights from an explicit regression on "
                  "standardised dosages with 40 causal and 12 tag variants; "
                  "the first cell is the WORST of the twelve coordinates, "
                  "which is why the selection correction applies")


def main():
    for fn in (test_transient_rate_nomut, test_asymmetric_fst_spanning,
               test_source_weights):
        try:
            fn()
        except Exception:
            import traceback
            traceback.print_exc()
    import json
    with open("battery_dis2_results.json", "w") as f:
        json.dump(RESULTS, f, indent=1, default=float)


if __name__ == "__main__":
    main()
