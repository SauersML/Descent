"""Battery 24: the mutation-drift transient, tested on its RATE.

`MutationDriftModelAssumptions.fstTransient` is

    fstEquilibrium * (1 - exp(-(1 + theta) * t / (2 * Ne)))

and it makes two separable claims: a plateau `fstEquilibrium = 1/(1+theta)`, and
an approach with time constant `tau = 2*Ne/(1+theta)`. The plateau is
convention-bound -- whether it is Nei's G_ST, Hudson's F_ST or a per-branch
drift F changes it by factors of two and four, and this corpus has already lost
a factor of four to exactly that. The RATE is not: rescaling F_ST by any
constant leaves `tau` untouched.

So the design fits `A * (1 - exp(-t/tau))` to the measured trajectory, throws `A`
away, and puts `tau` on trial against `2*Ne/(1+theta)`. `Ne` and `theta` are
swept separately, so a body that got the `Ne` scaling right and the `theta`
scaling wrong separates from one that got both right.

Competing form carried: `tau = 2*Ne`, the drift-only time constant with no
mutation term. At `theta = 3` the two differ fourfold.

IDENTITY RISK, screened before running rather than after: none. The oracle is
msprime's coalescent with mutations, and the prediction is a closed-form
trajectory. No quantity fed into the prediction is derived from the measured
trajectory -- `Ne` and `theta` are simulation inputs, `tau` is fitted output.
Contrast `driftVariance` and `haplotypeHomozygosity`, where the "measurement"
was pinned to the body by algebra.
"""
import json
import math

import numpy as np
from scipy import optimize

import simlib
from battery_core import RESULTS, record

SEQ = 1e6
RHO = 1e-8


def trajectory(Ne, theta, times, reps, seed):
    """F_ST between two demes that split `t` generations ago, with mutation."""
    import msprime
    mu = theta / (4.0 * Ne)
    # Hold the EXPECTED MUTATION COUNT roughly fixed across cells. theta is set
    # by mu at fixed Ne, so a high-theta cell needs an absurd per-site rate; at
    # theta = 3 with Ne = 500 that is mu = 1.5e-3, five orders above realistic,
    # and a megabase of it produces a genotype matrix large enough to stall the
    # run. Scaling the sequence inversely to theta keeps every cell the same
    # size to simulate. The observable is a ratio of coalescence-time
    # functionals, so sequence length affects only the error bar.
    # Capped at BOTH ends: unbounded below it stalls on a huge genotype
    # matrix at high theta, unbounded above it stalls on a 25 Mb sequence
    # at the low-theta control.
    seq = int(min(max(SEQ * (0.5 / theta), 5e4), 2e6))
    out = []
    for t in times:
        dem = msprime.Demography()
        dem.add_population(name="A", initial_size=Ne)
        dem.add_population(name="B", initial_size=Ne)
        dem.add_population(name="ANC", initial_size=Ne)
        dem.add_population_split(time=t, derived=["A", "B"], ancestral="ANC")
        vals = []
        for r in range(reps):
            ts = msprime.sim_ancestry(
                samples={"A": 25, "B": 25}, demography=dem,
                sequence_length=seq, recombination_rate=RHO,
                random_seed=24001 + r + int(t))
            mts = msprime.sim_mutations(ts, rate=mu, random_seed=124001 + r)
            if mts.num_sites == 0:
                continue
            gm = mts.genotype_matrix()
            a, b = mts.samples(population=0), mts.samples(population=1)
            vals.append(simlib.hudson_fst(gm[:, a].sum(1).astype(float), len(a),
                                          gm[:, b].sum(1).astype(float), len(b)))
        s = simlib.summarize(vals)
        out.append((s["mean"], s["sem"]))
    return out


def fit_tau(times, means, sems):
    """Fit A * (1 - exp(-t/tau)); return tau and its standard error.

    `A` is a nuisance parameter and is discarded: it carries the whole F_ST
    convention, which is what this design is built to avoid depending on.
    """
    t = np.asarray(times, float)
    y = np.asarray(means, float)
    w = 1.0 / np.maximum(np.asarray(sems, float), 1e-12)

    def resid(p):
        A, tau = p
        return (A * (1 - np.exp(-t / max(tau, 1e-6))) - y) * w

    p0 = [max(y.max(), 1e-6), float(t.mean())]
    sol = optimize.least_squares(resid, p0, bounds=([0, 1.0], [5.0, 1e7]))
    # standard error on tau from the Jacobian at the solution
    J = sol.jac
    try:
        cov = np.linalg.inv(J.T @ J)
        se = float(np.sqrt(max(cov[1, 1], 0.0)))
    except np.linalg.LinAlgError:
        se = float("nan")
    return float(sol.x[1]), se, float(sol.x[0])


def main():
    cells_full, cells_drift = [], []
    control = None
    # theta is capped at 1. Testing the (1 + theta) factor wants theta large,
    # but under infinite sites theta is set by mu at fixed Ne, and theta = 3
    # at Ne = 500 means mu = 1.5e-3 per site: ~4e6 mutations and a genotype
    # matrix that cannot be built. Reaching large theta needs a finite-sites
    # model or branch-mode statistics, not this instrument. Leverage on the
    # theta term comes instead from the fiftyfold span 0.02 to 1.0.
    designs = ((500, 0.5), (500, 0.02), (1000, 0.5), (500, 1.0), (1000, 0.1))
    for Ne, theta in designs:
        tau_pred = 2.0 * Ne / (1.0 + theta)
        times = [int(round(f * tau_pred)) for f in (0.25, 0.5, 1.0, 1.75, 3.0)]
        obs = trajectory(Ne, theta, times, reps=12, seed=0)
        means = [m for m, _ in obs]
        sems = [s for _, s in obs]
        tau, se, A = fit_tau(times, means, sems)
        lab = "Ne=%d theta=%.1f" % (Ne, theta)
        print("  %-20s tau_fit = %.0f ± %.0f   (2Ne/(1+theta) = %.0f, "
              "2Ne = %d)   A = %.4f"
              % (lab, tau, se, tau_pred, 2 * Ne, A))
        print("      times %s" % times)
        print("      F_ST  %s" % ["%.4f" % m for m in means])
        cells_full.append(dict(design=lab, lean=tau_pred, truth=tau,
                               sem=max(se, 1e-6)))
        cells_drift.append(dict(design=lab, lean=2.0 * Ne, truth=tau,
                                sem=max(se, 1e-6)))
        if Ne == 1000 and theta == 0.1:
            # control: at theta -> 0 the two candidate rates coincide, and the
            # drift-only time constant 2*Ne is independently known. Run a
            # near-zero-theta cell on the same code path.
            obs0 = trajectory(500, 0.02, [int(round(f * 1000))
                                          for f in (0.25, 0.5, 1.0, 1.75, 3.0)],
                              reps=12, seed=0)
            tau0, se0, _ = fit_tau([int(round(f * 1000))
                                    for f in (0.25, 0.5, 1.0, 1.75, 3.0)],
                                   [m for m, _ in obs0], [s for _, s in obs0])
            control = dict(design="Ne=500 theta=0.02 [drift-only tau = 2Ne]",
                           lean=1000.0, truth=tau0, sem=max(se0, 1e-6))
            print("  control  tau_fit = %.0f ± %.0f  (2Ne = 1000)" % (tau0, se0))
    reg = ("two demes split from a common ancestor, no migration, mutation at "
           "theta = 4*Ne*mu; 1 Mb with recombination, 12 replicates per time "
           "point, five time points spanning 0.25 to 3 predicted time "
           "constants. The observable is the TIME CONSTANT of a fitted "
           "A*(1-exp(-t/tau)); the amplitude A is discarded because it carries "
           "the F_ST convention and tau does not. Ne and theta are swept "
           "separately so the two scalings are separately on trial")
    record("MutationDriftModelAssumptions.fstTransient [rate]",
           "PortabilityDrift.lean",
           "tau = 2*Ne/(1+theta), from fstEquilibrium*(1-exp(-(1+theta)*t/(2*Ne)))",
           cells_full, regime=reg, control=control)
    record("fstTransient [drift-only tau = 2*Ne, competing]",
           "PortabilityDrift.lean", "tau = 2*Ne", cells_drift, regime=reg,
           control=control)
    json.dump(RESULTS, open("battery_bulk24_results.json", "w"), indent=1,
              default=str)
    print("\n================ SUMMARY ================")
    for r in RESULTS:
        w = r.get("worst", {})
        print("%-22s %-56s worst %8.2f sems, %6.2f%% rel"
              % (r["verdict"], r["name"], w.get("sems_off", float("nan")),
                 100 * w.get("rel_err", float("nan"))))


if __name__ == "__main__":
    main()
