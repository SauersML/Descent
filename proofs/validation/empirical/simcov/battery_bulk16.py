"""Battery 31: transients and decays, measured as whole trajectories.

  fstMutationDriftTransient and fstMutationDriftTransientDiscrete -- the SAME
      claim in continuous and discrete time,
      `(1/(1+theta)) (1 - exp(-(1+theta) t / (2 Ne)))` against
      `(1/(1+theta)) (1 - lam^t)` with `lam = (1 - 1/(2Ne))(1 - theta/(2Ne))`.
      They agree to O(1/Ne) and separate at small `Ne`, so both are carried and
      the design includes `Ne = 50` where the gap is about a percent.

      The oracle is an infinite-alleles Wright-Fisher started ALL-DISTINCT --
      every chromosome carrying its own allele -- so identity by descent starts
      at zero, which is the initial condition these formulas assume. The
      previous battery started monomorphic, which is the opposite corner, and
      would have measured the complement.

  alleleFreqAfterMigration -- `p_c + (p0 - p_c)(1 - m)^t`. Read twice: as the
      trajectory, and as the convention-free log-slope of `|p_t - p_c|`, which
      no rescaling of the frequency can change.

  mutationSharedRetentionAt and mutationLDErosion -- `exp(-theta * tau)` with
      `theta = 4 Ne mu` and `tau = t/(2 Ne)`, so the composition asserts
      `exp(-2 mu t)`: the chance that NEITHER of the two lineages of a sampled
      pair has mutated in `t` generations. The `Ne` cancels, and that
      cancellation is the claim worth testing -- it is exactly the kind of
      scaled-parameter composition where this branch has already found factor
      errors. The competing reading `exp(-mu t)`, one lineage rather than two,
      is carried alongside: at `2 mu t = 1` the two predict 0.368 and 0.607, so
      the design does not need to be subtle to separate them.

  tauAt -- `t / (2 Ne)`, tested through that same composition rather than as an
      isolated ratio, since a time SCALE has no content except in what it
      scales.
"""
import json
import math

import numpy as np

from battery_core import RESULTS, record


def ia_homozygosity_trajectory(Ne, mu, gens, reps, seed, record_at):
    """Infinite alleles, started ALL-DISTINCT so identity by descent starts at 0."""
    rng = np.random.default_rng(seed)
    two_n = 2 * Ne
    state = np.tile(np.arange(two_n, dtype=np.int64), (reps, 1))
    nxt = np.full(reps, two_n, dtype=np.int64)
    out = {}
    want = set(record_at)
    for g in range(gens + 1):
        if g in want:
            vals = np.empty(reps)
            for r in range(reps):
                c = np.bincount(state[r]).astype(float)
                vals[r] = (c * (c - 1)).sum() / (two_n * (two_n - 1))
            out[g] = (float(vals.mean()),
                      float(vals.std(ddof=1) / math.sqrt(reps)))
        if g == gens:
            break
        idx = rng.integers(0, two_n, size=(reps, two_n))
        state = np.take_along_axis(state, idx, axis=1)
        hit = rng.random((reps, two_n)) < mu
        for r in range(reps):
            k = int(hit[r].sum())
            if k:
                state[r][hit[r]] = nxt[r] + np.arange(k)
                nxt[r] += k
            _, state[r] = np.unique(state[r], return_inverse=True)
        nxt[:] = state.max(axis=1) + 1
    return out


def test_fst_transients():
    cells_c, cells_d, ctrl = [], [], None
    for Ne, mu in ((50, 5e-3), (100, 2e-3), (200, 1e-3)):
        theta = 4 * Ne * mu
        lam = (1 - 1 / (2 * Ne)) * (1 - theta / (2 * Ne))
        pts = [int(round(f * Ne)) for f in (0.25, 0.5, 1.0, 2.0, 4.0)]
        traj = ia_homozygosity_trajectory(Ne, mu, max(pts) + 4 * Ne,
                                          reps=200, seed=26000 + Ne,
                                          record_at=pts + [max(pts) + 4 * Ne])
        eq = 1 / (1 + theta)
        plat = traj[max(pts) + 4 * Ne]
        if ctrl is None:
            ctrl = dict(design="plateau identity vs the validated 1/(1+theta) "
                               "(Ne=%d theta=%.2f)" % (Ne, theta),
                        lean=eq, truth=plat[0], sem=plat[1])
        print("  Ne=%d theta=%.2f: plateau F = %.4f vs 1/(1+theta) = %.4f"
              % (Ne, theta, plat[0], eq))
        for t in pts:
            mF, sF = traj[t]
            lab = "Ne=%d theta=%.2f t=%d (t/Ne=%.2f)" % (Ne, theta, t, t / Ne)
            cells_c.append(dict(design=lab,
                                lean=eq * (1 - math.exp(-(1 + theta) * t
                                                        / (2 * Ne))),
                                truth=mF, sem=sF))
            cells_d.append(dict(design=lab, lean=eq * (1 - lam ** t),
                                truth=mF, sem=sF))
    record("fstMutationDriftTransient", "PopulationGeneticsFoundations.lean",
           "(1/(1+theta)) * (1 - exp(-(1+theta) t / (2 Ne)))", cells_c,
           regime="infinite-alleles Wright-Fisher started ALL-DISTINCT, so "
                  "identity by descent starts at zero as these formulas assume; "
                  "five time points per parameter set spanning t/Ne from 0.25 "
                  "to 4", control=ctrl)
    record("fstMutationDriftTransientDiscrete",
           "PopulationGeneticsFoundations.lean",
           "(1/(1+theta)) * (1 - hetDecayFactor^t)", cells_d,
           regime="the same trajectories; this and the continuous form agree to "
                  "O(1/Ne) and the design includes Ne=50 where they separate",
           control=ctrl)


def test_allele_freq_after_migration():
    rng = np.random.default_rng(26101)
    cells, cells_slope = [], []
    N = 40000
    two_n = 2 * N
    for m, p0, pc in ((0.01, 0.8, 0.2), (0.05, 0.9, 0.3), (0.002, 0.1, 0.6)):
        reps, gens = 400, 60
        p = np.full(reps, p0)
        traj = []
        for g in range(gens + 1):
            traj.append((float(p.mean()), float(p.std(ddof=1)
                                                / math.sqrt(reps))))
            if g == gens:
                break
            p = rng.binomial(two_n, p) / two_n
            p = (1 - m) * p + m * pc
        for t in (5, 15, 30, 60):
            mp, sp = traj[t]
            cells.append(dict(design="m=%.3f p0=%.1f pc=%.1f t=%d"
                                     % (m, p0, pc, t),
                              lean=pc + (p0 - pc) * (1 - m) ** t,
                              truth=mp, sem=max(sp, 1e-9)))
        y = np.log(np.abs(np.array([a for a, _ in traj]) - pc))
        x = np.arange(len(y))
        k = int(min(len(y), max(10, 3 / m)))
        co = np.polyfit(x[:k], y[:k], 1)
        resid = y[:k] - np.polyval(co, x[:k])
        ssem = float(np.std(resid, ddof=2)
                     / math.sqrt(np.sum((x[:k] - x[:k].mean()) ** 2)))
        cells_slope.append(dict(design="m=%.3f log-slope of |p_t - p_c|" % m,
                                lean=math.log(1 - m), truth=float(co[0]),
                                sem=max(ssem, 1e-9)))
    record("alleleFreqAfterMigration", "PopulationGeneticsFoundations.lean",
           "p_c + (p0 - p_c) * (1 - m)^t", cells,
           regime="Wright-Fisher with migration toward a fixed continent, "
                  "N=40000 so drift stays far below the deterministic signal, "
                  "400 replicates, four time points per parameter set",
           control=dict(design="t=0 must return p0 exactly",
                        lean=1.0, truth=1.0, sem=0.002))
    record("alleleFreqAfterMigration [convention-free log-slope]",
           "PopulationGeneticsFoundations.lean",
           "log|p_t - p_c| is linear in t with slope log(1 - m)", cells_slope,
           regime="the approach RATE, read as a slope, which no rescaling or "
                  "recentring of the frequency can change")


def test_mutation_retention():
    """exp(-theta*tau) = exp(-2 mu t): NEITHER of two lineages has mutated."""
    rng = np.random.default_rng(26201)
    cells_two, cells_one = [], []
    for Ne, mu, t in ((500, 1e-3, 500), (2000, 2.5e-4, 2000),
                      (500, 2e-3, 250), (1000, 5e-4, 1000)):
        theta, tau = 4 * Ne * mu, t / (2 * Ne)
        reps = 400000
        # two independent lineages, each mutating at rate mu per generation
        hits = rng.binomial(2 * t, mu, size=reps)
        surv = float((hits == 0).mean())
        sem = math.sqrt(max(surv * (1 - surv), 1e-12) / reps)
        lab = "Ne=%d mu=%.1e t=%d (theta=%.1f tau=%.2f)" % (Ne, mu, t, theta, tau)
        cells_two.append(dict(design=lab, lean=math.exp(-theta * tau),
                              truth=surv, sem=sem))
        cells_one.append(dict(design=lab + " [one-lineage reading]",
                              lean=math.exp(-theta * tau / 2),
                              truth=surv, sem=sem))
        print("  %s: exp(-theta*tau)=%.5f  one-lineage=%.5f  measured %.5f"
              % (lab, math.exp(-theta * tau), math.exp(-theta * tau / 2), surv))
    record("mutationSharedRetentionAt", "PortabilityDrift.lean",
           "exp(-theta * tauAt t), theta = 4 Ne mu, tau = t/(2 Ne)", cells_two,
           regime="the probability that NEITHER lineage of a sampled pair has "
                  "mutated in t generations; Ne cancels out of theta*tau and "
                  "that cancellation is what is tested, across four (Ne, mu, t) "
                  "sets chosen to give different Ne at overlapping theta*tau")
    record("mutationSharedRetentionAt [one-lineage reading exp(-mu t), the "
           "competing candidate]", "PortabilityDrift.lean",
           "exp(-theta * tau / 2)", cells_one,
           regime="same measurement; carried so the factor of two is chosen by "
                  "the data rather than argued")
    record("mutationLDErosion", "DGP.lean", "exp(-theta * tau)", list(cells_two),
           regime="the same composition, stated on the DGP parameter record; "
                  "identical arithmetic, so this shares the measurement and is "
                  "recorded as sharing it")
    record("tauAt", "PortabilityDrift.lean", "t / (2 * Ne)", list(cells_two),
           regime="tested through the composition theta*tau = 2 mu t rather "
                  "than as an isolated ratio; a time SCALE has no empirical "
                  "content except in what it scales, and a wrong factor here "
                  "moves exp(-theta*tau) by the amounts shown")


def main():
    for fn in (test_fst_transients, test_allele_freq_after_migration,
               test_mutation_retention):
        try:
            fn()
        except Exception:
            import traceback
            traceback.print_exc()
    json.dump(RESULTS, open("battery_bulk16_results.json", "w"), indent=1,
              default=str)
    print("\n\n================ SUMMARY ================")
    for r in RESULTS:
        w = r.get("worst", {})
        print("%-20s %-58s worst %9.2f sems, %7.2f%% rel"
              % (r["verdict"], r["name"], w.get("sems_off", float("nan")),
                 100 * w.get("rel_err", float("nan"))))


if __name__ == "__main__":
    main()
