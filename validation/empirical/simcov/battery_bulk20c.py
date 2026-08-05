"""Battery 20c: `ibdRecurrenceFixedPoint` and `admixtureLDDecay`, at a scale
where the discrimination is actually available.

Battery 20's group C swept `m` at `Ne = 100` across 40 demes and had to be
killed: at `m = 0.12` with 39 migration sources the structured coalescent spends
essentially all its time moving lineages between demes, and one cell had not
finished in twenty-five minutes.  It was also the wrong design for the question.
The exact fixed point

    (1-m)^2 / ((1-m)^2 + 2 Ne m (2-m))

and the diffusion form `1/(1 + 4 Ne m)` agree to first order in `m`, so what
separates them is `m` itself, NOT `4 Ne m`.  Holding `4 Ne m` fixed and shrinking
`Ne` therefore raises the discrimination and lowers the cost at the same time:
at `4 Ne m = 24`, `Ne = 100` puts the two forms 9% apart and takes half an hour a
cell, while `Ne = 25` puts them 33% apart and takes seconds.

So the sweep runs at small `Ne` with `m` large, which is exactly the corner the
diffusion approximation is not entitled to and the exact recurrence claims.
Both forms are carried on every cell so the data picks the body rather than the
name.  Control: the small-`m` cell, where `1/(1 + 4 Ne m)` is already VALIDATED
(`battery_core.py`, `fstMigrationMutationEquilibrium`) and the two forms agree,
so a design that cannot reproduce it has no standing to report a difference
where they diverge.

Group D is battery 20's admixture group unchanged; it never ran, because group C
was killed before reaching it.
"""
import json
import math

import numpy as np

import simlib
from battery_core import RESULTS, record

SEQ = 4e6
RHO = 1e-8


def group_c():
    import msprime

    n_demes = 30
    cells_exact, cells_diff = [], []
    control = None
    # (Ne, m): the first cell is the agreement corner and is the control; the
    # rest push m up at small Ne, where the two forms come apart.
    for Ne, m in ((400, 0.0025), (100, 0.02), (50, 0.06), (25, 0.16),
                  (15, 0.30)):
        dem = msprime.Demography.island_model(
            [Ne] * n_demes, migration_rate=m / (n_demes - 1.0))
        vals = []
        for r in range(32):
            ts = msprime.sim_ancestry(
                samples={"pop_0": 30, "pop_1": 30}, demography=dem,
                sequence_length=SEQ, recombination_rate=RHO,
                random_seed=91001 + r)
            A, B = ts.samples(population=0), ts.samples(population=1)
            da = ts.diversity([A], mode="branch")[0]
            db = ts.diversity([B], mode="branch")[0]
            dab = ts.divergence([A, B], indexes=[(0, 1)], mode="branch")[0]
            vals.append(1.0 - ((da + db) / 2.0) / dab)
        s = simlib.summarize(vals)
        exact = (1 - m) ** 2 / ((1 - m) ** 2 + 2 * Ne * m * (2 - m))
        diff = 1.0 / (1.0 + 4 * Ne * m)
        lab = "Ne=%d m=%.4f (4Nm=%.1f)" % (Ne, m, 4 * Ne * m)
        print("  %-28s F_ST = %.5f ± %.5f | exact %.5f  diffusion %.5f  "
              "(gap %.0f%%)"
              % (lab, s["mean"], s["sem"], exact, diff,
                 100 * abs(exact - diff) / max(exact, 1e-12)))
        cells_exact.append(dict(design=lab, lean=exact, truth=s["mean"],
                                sem=s["sem"]))
        cells_diff.append(dict(design=lab, lean=diff, truth=s["mean"],
                               sem=s["sem"]))
        if Ne == 400:
            control = dict(
                design=lab + " [1/(1+4Nm) at small m, already VALIDATED]",
                lean=diff, truth=s["mean"], sem=s["sem"])
    reg = ("symmetric island model, 30 demes so the many-deme limit both forms "
           "are written in actually holds; m is the TOTAL emigration rate, so "
           "each of the 29 sources gets m/29 -- msprime's migration_rate is "
           "per ordered pair and using it directly would rescale the "
           "prediction by 29; F_ST between two demes from branch-mode "
           "coalescence times over 4 Mb with recombination 1e-8, 32 replicates. "
           "4*Ne*m is swept only mildly; m itself is swept 120-fold, because "
           "m is what separates the two candidate forms")
    record("ibdRecurrenceFixedPoint / fstIslandMultiplicativeEquilibrium",
           "PortabilityDrift.lean",
           "(1-m)^2 / ((1-m)^2 + 2*Ne*m*(2-m))", cells_exact, regime=reg,
           control=control)
    record("fstMigrationDriftEquilibrium [diffusion form, competing]",
           "PortabilityDrift.lean", "1 / (1 + 4*Ne*m)", cells_diff,
           regime=reg, control=control)


def group_d():
    rng = np.random.default_rng(2020)
    Ne, alpha = 2000, 0.5
    pA1, pB1, pA2, pB2 = 0.8, 0.2, 0.75, 0.15
    n_hap = 2 * Ne
    reps = 400
    cells_decay, cells_boost = [], []
    control = None
    for r_rate in (0.005, 0.02, 0.05, 0.15):
        D0 = alpha * (1 - alpha) * (pA1 - pB1) * (pA2 - pB2)
        p1 = alpha * pA1 + (1 - alpha) * pB1
        p2 = alpha * pA2 + (1 - alpha) * pB2
        base = np.array([p1 * p2 + D0, p1 * (1 - p2) - D0,
                         (1 - p1) * p2 - D0, (1 - p1) * (1 - p2) + D0])
        H = np.tile(base, (reps, 1))
        traj = []
        for gen in range(41):
            f1 = H[:, 0] + H[:, 1]
            f2 = H[:, 0] + H[:, 2]
            D = H[:, 0] - f1 * f2
            traj.append(D.copy())
            H = H.copy()
            H[:, 0] -= r_rate * D
            H[:, 1] += r_rate * D
            H[:, 2] += r_rate * D
            H[:, 3] -= r_rate * D
            H = np.clip(H, 0, None)
            H /= H.sum(axis=1, keepdims=True)
            H = rng.multinomial(n_hap, H) / float(n_hap)
        traj = np.asarray(traj)
        for t in (10, 40):
            ratio = traj[t] / traj[0]
            truth = float(np.mean(ratio))
            sem = float(np.std(ratio, ddof=1) / math.sqrt(reps))
            lab = "r=%.3f t=%d" % (r_rate, t)
            lean = (1 - r_rate) ** t
            print("  %-18s retention %.5f ± %.5f  (lean %.5f)"
                  % (lab, truth, sem, lean))
            cells_decay.append(dict(design=lab, lean=lean, truth=truth,
                                    sem=sem))
            eq = 0.25
            cells_boost.append(dict(design=lab + " eq=0.25",
                                    lean=lean / eq, truth=truth / eq,
                                    sem=sem / eq))
            if r_rate == 0.005 and t == 10:
                control = dict(
                    design=lab + " [(1-r)^t (1-1/(2Ne))^t, the finite-Ne "
                                 "retention, independently derived]",
                    lean=((1 - r_rate) * (1 - 1.0 / (2 * Ne))) ** t,
                    truth=truth, sem=sem)
    reg = ("one-pulse 50/50 admixture into a Wright-Fisher population of "
           "Ne = 2000, then 40 generations of recombination and drift; the "
           "observable is E[D_t]/E[D_0] over 400 independent replicates")
    record("admixtureLDDecay", "PortabilityDrift.lean",
           "(1 - r) ^ generations_since", cells_decay, regime=reg,
           control=control)
    record("admixtureLDBoost", "PortabilityDrift.lean",
           "admixtureLDDecay r t_since / equilibrium_ld", cells_boost,
           regime=reg + "; equilibrium_ld held at 0.25, since it is an input "
                        "to the body and what is on trial is the ratio",
           control=control)


def main():
    for fn in (group_d, group_c):
        print("\n===== %s =====" % fn.__name__)
        try:
            fn()
        except Exception as e:
            print("*** %s RAISED %r" % (fn.__name__, e))
            import traceback
            traceback.print_exc()
    json.dump(RESULTS, open("battery_bulk20c_results.json", "w"), indent=1,
              default=str)
    print("\n================ SUMMARY ================")
    for r in RESULTS:
        w = r.get("worst", {})
        print("%-22s %-56s worst %8.2f sems, %6.2f%% rel"
              % (r["verdict"], r["name"], w.get("sems_off", float("nan")),
                 100 * w.get("rel_err", float("nan"))))


if __name__ == "__main__":
    main()
