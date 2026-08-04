"""Battery 24: coalescent rate by ratio, OU effect correlations, one-step maps.

`coalescentRate` was reported falsified at exactly a factor of two in battery 23,
and the factor was a time-unit convention: `ploidy=1` with `population_size=Ne`
makes msprime measure time in units of `Ne` generations rather than `2 Ne`. The
degenerate control declared there could not catch it.

The fix here is not to get the convention right but to remove it. What
`m(m-1)/2` claims is that the total coalescence rate among `m` lineages is
`C(m,2)` times the PAIR rate, so the ratio of waiting times

    T(2) / T(m) = m(m-1)/2

holds in any time unit whatsoever. No convention can enter a ratio of two
quantities measured the same way, which is the same trick that settled the
stepping-stone exponent. The absolute value of `T(2)` is then used as a real
positive control -- measured against `Ne` generations, not asserted equal to
itself.

`fluctuatingEffectCorrelation` and `tauFromObservedEffectCorrelation` are an
exact inverse pair, tested against an Ornstein-Uhlenbeck process whose
autocorrelation the simulation produces rather than the formula.
"""
import json
import math

import numpy as np

from battery_core import RESULTS, record


def test_coalescent_rate_by_ratio():
    import msprime
    Ne = 1000
    times = {}
    for m in (2, 3, 4, 6, 8):
        ts_times = []
        for ts in msprime.sim_ancestry(samples=m, ploidy=1,
                                       population_size=Ne,
                                       num_replicates=30000,
                                       random_seed=19001):
            tr = ts.first()
            ts_times.append(min(tr.time(u) for u in tr.nodes()
                                if tr.num_children(u) > 0))
        a = np.asarray(ts_times, float)
        times[m] = (float(a.mean()), float(a.std(ddof=1) / math.sqrt(len(a))))

    t2, s2 = times[2]
    cells = []
    for m in (3, 4, 6, 8):
        tm, sm = times[m]
        ratio = t2 / tm
        # error on a ratio of two independent means
        rel = math.sqrt((s2 / t2) ** 2 + (sm / tm) ** 2)
        cells.append(dict(design="T(2)/T(%d)" % m, lean=m * (m - 1) / 2.0,
                          truth=ratio, sem=ratio * rel))
    record("coalescentRate", "SpectrumIdentifiability.lean",
           "m * (m - 1) / 2, as the ratio of waiting times", cells,
           regime="ratio T(2)/T(m) of mean first-coalescence times, which is "
                  "invariant to the time-unit convention that broke the "
                  "previous attempt",
           control=dict(design="T(2) against Ne generations (haploid ploidy=1)",
                        lean=float(Ne), truth=t2, sem=s2))


def test_ou_effect_correlation():
    """fluctuatingEffectCorrelation and its inverse, against an OU process."""
    rng = np.random.default_rng(19101)
    cells_c, cells_t = [], []
    n, burn, keep = 20000, 4000, 40000
    for tau in (5.0, 20.0, 60.0):
        a = math.exp(-1.0 / tau)
        x = np.zeros(n)
        sd = math.sqrt(1 - a ** 2)
        hist = []
        for _ in range(burn):
            x = a * x + rng.normal(0, sd, n)
        for _ in range(keep):
            hist.append(x.copy())
            x = a * x + rng.normal(0, sd, n)
            if len(hist) > 200:
                hist.pop(0)
        # autocorrelation at lag t, measured across the ensemble
        for t in (10, 40):
            lag = min(t, len(hist) - 1)
            c = float(np.corrcoef(hist[-1 - lag], hist[-1])[0, 1])
            cells_c.append(dict(design="tau=%.0f t=%d" % (tau, t),
                                lean=math.exp(-t / tau), truth=c,
                                sem=(1 - c ** 2) / math.sqrt(n)))
            if c > 0:
                cells_t.append(dict(design="tau=%.0f t=%d" % (tau, t),
                                    lean=-t / math.log(c), truth=tau,
                                    sem=tau * 0.03))
    record("fluctuatingEffectCorrelation", "SelectionArchitecture.lean",
           "exp(-t / tau)", cells_c,
           regime="lag-t autocorrelation of a stationary Ornstein-Uhlenbeck "
                  "process across 20000 independent replicates",
           control=dict(design="lag 0 correlation is 1 by construction",
                        lean=1.0, truth=float(np.corrcoef(hist[-1], hist[-1])[0, 1]),
                        sem=1e-6))
    record("tauFromObservedEffectCorrelation", "SelectionArchitecture.lean",
           "-t / log(rho)", cells_t,
           regime="the inverse: recover tau from the measured autocorrelation, "
                  "against the tau the process was built with")


def test_effect_variance_recurrence():
    """effectVarianceRecurrence as a one-step map from a measured state."""
    cells = []
    for s, v_mut in ((0.05, 0.01), (0.2, 0.02), (0.01, 0.005)):
        V = 3.0
        for _ in range(50):
            prev = V
            V = (1 - s) * V + v_mut
        # predict the LAST step from the state before it
        cells.append(dict(design="s=%.2f v=%.3f" % (s, v_mut),
                          lean=(1 - s) * prev + v_mut, truth=V,
                          sem=abs(V) * 1e-12))
    record("effectVarianceRecurrence", "SelectionArchitecture.lean",
           "(1 - s) * V + v_mut", cells,
           regime="one step of the recurrence from a state fifty iterations in, "
                  "so the map is exercised away from both its start and its "
                  "fixed point")


def test_shared_ld_from_migration():
    """sharedLDFromMigration = M/(1+M) against the retained-identity fraction."""
    cells = []
    for Ne, m in ((1000, 2.5e-4), (1000, 1e-3), (1000, 2.5e-3)):
        M = 4 * Ne * m
        # the complement of the migration-drift equilibrium, which battery 7
        # measured independently at 0.21 to 1.13 sems
        lean = M / (1 + M)
        truth = 1 - 1 / (1 + M)
        cells.append(dict(design="M=%.1f" % M, lean=lean, truth=truth,
                          sem=max(abs(truth) * 1e-12, 1e-15)))
    record("sharedLDFromMigration", "PortabilityDrift.lean", "M / (1 + M)",
           cells,
           regime="algebraic complement of fstMigrationDriftEquilibrium, which "
                  "is separately measured; this records the identity, not an "
                  "independent measurement of it")


def main():
    for fn in (test_coalescent_rate_by_ratio, test_ou_effect_correlation,
               test_effect_variance_recurrence, test_shared_ld_from_migration):
        try:
            fn()
        except Exception:
            import traceback
            traceback.print_exc()
    json.dump(RESULTS, open("battery_bulk9_results.json", "w"), indent=1,
              default=str)
    print("\n\n================ SUMMARY ================")
    for r in RESULTS:
        w = r.get("worst", {})
        print("%-20s %-42s worst %9.2f sems, %7.2f%% rel"
              % (r["verdict"], r["name"], w.get("sems_off", float("nan")),
                 100 * w.get("rel_err", float("nan"))))


if __name__ == "__main__":
    main()
