"""fstTransientAt, with a control the estimator can actually pass.

`battery_dis2.py` voided this claim: the `M = 0` control -- that the fitted decay
base reproduces the pure-drift rate `1/(2Ne)`, i.e. `R = 1` -- came out at
`0.972 +/- 0.006`, 4.7 sems low. The 3 percent is the estimator, not the model.
`F(t) = Var_demes(p) / pbar(1-pbar)` is a ratio of two quantities that BOTH move:
the numerator approaches its plateau at the fast eigenvalue of the island model
while the denominator decays at the slow metapopulation-drift one, and a single
exponential fitted to their ratio picks up a little of the slow mode. The two
modes are closest together at exactly `M = 0`, which is why the bias shows up
in the control cell and nowhere else.

The fix is to give the estimator a reference it can be held to. The island model
has an EXACT deterministic recursion in the two moments the estimator is built
from,

    S(t+1) = (1-m)^2 S(t) + (1 - 1/d) (T(t) - S(t)) / (2Ne)
    T(t+1) = T(t) - (T(t) - S(t)) / (2Ne d)

with `S = E[Var_demes(p)]` and `T = E[pbar(1-pbar)]`, and `F = S/T`. That
recursion is an independent derivation of the same model -- not the Lean formula
and not the simulation -- so running the IDENTICAL fitting code over it and
requiring the stochastic run to reproduce it is a control that can fail, and it
absorbs the estimator's own bias instead of charging it to the definition.

What is then under test is unchanged and is convention-free, since the fitted
base is a property of the SHAPE F(t)/F(plateau): does the approach rate depend
on migration? `fstTransientAt` uses `hetDecayFactor`, which is drift times
mutation, so at `theta = 0` it says `R = 1` for every migration rate.
"""
import math

import numpy as np

from battery_core import RESULTS, record
from battery_dis2 import island_transient_nomut, fit_R


def exact_traj(Ne, d, bigM, gens, p0mean=0.5):
    """The deterministic two-moment recursion, as an F(t) trajectory."""
    m = bigM / (4.0 * Ne)
    S, T = 0.0, p0mean
    out = np.zeros(gens + 1)
    for t in range(gens + 1):
        out[t] = S / T if T > 0 else 0.0
        U = T - S
        S, T = (1 - m) ** 2 * S + (1 - 1.0 / d) * U / (2 * Ne), \
            T - U / (2 * Ne * d)
    return out[None, :]


def test_transient():
    Ne, d = 100, 24
    cells_corpus, cells_cand = [], []
    control = None
    for bigM in (0.0, 2.0, 6.0, 16.0):
        tau = 2 * Ne / (1.0 + bigM)
        gens = int(12 * tau) + 5
        traj = island_transient_nomut(Ne, d, bigM, gens, seed=8101 + int(bigM))
        R = fit_R(traj, Ne, tau)
        obs, sem = float(R.mean()), float(R.std(ddof=1) / math.sqrt(len(R)))
        # the same fit, over the exact deterministic recursion
        p0mean = float(np.mean([p * (1 - p) for p in
                                np.random.default_rng(3).uniform(0.15, 0.85,
                                                                 100000)]))
        Rx = fit_R(exact_traj(Ne, d, bigM, gens, p0mean), Ne, tau)
        exact = float(Rx[0]) if len(Rx) else float("nan")
        lab = "M=%.1f (exact recursion %.3f)" % (bigM, exact)
        cells_corpus.append(dict(design=lab, lean=1.0, truth=obs, sem=sem))
        cells_cand.append(dict(design=lab, lean=1.0 + bigM -
                               bigM / (d * (1.0 + bigM)), truth=obs, sem=sem))
        if bigM == 0.0:
            control = dict(design="M=0: the stochastic run against the exact "
                                  "deterministic recursion, same fitting code",
                           lean=exact, truth=obs, sem=sem)
    reg = ("24-deme forward Wright-Fisher island model, NO mutation so no "
           "mutation-model convention enters, started identical; the fitted "
           "per-generation decay base of F(t)/F(plateau) -- a SHAPE, so "
           "invariant to the F_ST convention -- as R = (1 - lam) * 2Ne")
    record("fstTransientAt [its decay base carries no migration: R = 1]",
           "PortabilityDrift.lean",
           "(1/(1+theta+bigM)) * (1 - hetDecayFactor^t)", cells_corpus,
           control=control, regime=reg)
    record("fstTransientAt [CANDIDATE: the base carries every force the "
           "equilibrium does, R = 1 + bigM - bigM/(d(1+bigM))]",
           "PortabilityDrift.lean",
           "(1/(1+theta+bigM)) * (hetDecayFromScaled Ne theta * "
           "(1 - bigM/(2Ne)))^t", cells_cand, control=control,
           regime="same runs, same fits; the O(1/d) term is the finite-deme "
                  "correction the two-moment recursion carries")


def main():
    test_transient()
    import json
    with open("battery_dis3_results.json", "w") as f:
        json.dump(RESULTS, f, indent=1, default=float)


if __name__ == "__main__":
    main()
