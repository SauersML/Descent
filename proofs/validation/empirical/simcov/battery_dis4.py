"""fstTransientAt, on a design where BOTH candidates' predictions move.

`battery_dis3.py` fixed the control -- the stochastic run reproduces the exact
two-moment recursion at 1.80 sems -- and the candidate that carries migration in
the decay base then matched every cell at under 0.8 sems. But the corpus reading
was returned NO POWER rather than FALSIFIED, and correctly: `hetDecayFactor` has
no migration in it, so at `theta = 0` it predicts the SAME approach rate for
every migration rate in that design, and a design across which the prediction is
constant cannot reject it. That the measurement moved by a factor of seventeen
across the same cells is not something the power gate can see, and it should not
have to.

So the quantity is restated as the half-life in generations -- the generation at
which `F(t)` first reaches half its plateau -- and `Ne` is swept alongside the
migration rate. Now both candidates predict a moving number:

    corpus     t_half = ln2 * 2Ne          (drift alone sets the rate)
    candidate  t_half = ln2 * 2Ne / (1 + bigM)

and the design puts them in opposite directions, since `Ne` rises with `bigM`
across the cells. The half-life is read off the trajectory by interpolation, so
it is a property of the SHAPE and carries no F_ST convention, and the plateau it
is measured against is the same one both candidates share.
"""
import math

import numpy as np

from battery_core import RESULTS, record
from battery_dis2 import island_transient_nomut
from battery_dis3 import exact_traj


def half_life(f, tau):
    """First generation at which F reaches half its plateau, interpolated."""
    lo, hi = int(9 * tau), min(int(12 * tau), len(f))
    fstar = f[lo:hi].mean()
    if fstar <= 0:
        return float("nan")
    half = 0.5 * fstar
    idx = np.argmax(f >= half)
    if idx == 0:
        return float("nan")
    f0, f1 = f[idx - 1], f[idx]
    return (idx - 1) + (half - f0) / (f1 - f0)


def test_half_life():
    d = 24
    cells_corpus, cells_cand = [], []
    control = None
    for Ne, bigM in ((50, 0.0), (100, 2.0), (200, 6.0), (400, 16.0)):
        tau = 2 * Ne / (1.0 + bigM)
        gens = int(12 * tau) + 5
        traj = island_transient_nomut(Ne, d, bigM, gens, seed=8601 + Ne)
        hs = np.array([half_life(traj[r], tau) for r in range(traj.shape[0])])
        hs = hs[~np.isnan(hs)]
        obs, sem = float(hs.mean()), float(hs.std(ddof=1) / math.sqrt(len(hs)))
        p0mean = float(np.mean(np.array([p * (1 - p) for p in
                       np.random.default_rng(3).uniform(0.15, 0.85, 200000)])))
        exact = half_life(exact_traj(Ne, d, bigM, gens, p0mean)[0], tau)
        lab = "Ne=%d M=%.1f (exact recursion %.1f)" % (Ne, bigM, exact)
        cells_corpus.append(dict(design=lab, lean=math.log(2) * 2 * Ne,
                                 truth=obs, sem=sem))
        cells_cand.append(dict(design=lab,
                               lean=math.log(2) * 2 * Ne / (1 + bigM),
                               truth=obs, sem=sem))
        if bigM == 0.0:
            control = dict(design="Ne=50 M=0: the stochastic run against the "
                                  "exact deterministic recursion, same "
                                  "half-life estimator",
                           lean=exact, truth=obs, sem=sem)
    reg = ("24-deme forward Wright-Fisher island model, NO mutation so no "
           "mutation-model convention enters, started identical; the half-life "
           "of F(t) against its own plateau, read by interpolation, which is a "
           "property of the shape and so carries no F_ST convention")
    record("fstTransientAt [decay base = hetDecayFactor, which carries no "
           "migration]", "PortabilityDrift.lean",
           "(1/(1+theta+bigM)) * (1 - hetDecayFactor^t)", cells_corpus,
           control=control, regime=reg)
    record("fstTransientAt [CANDIDATE: the base carries every force the "
           "equilibrium does]", "PortabilityDrift.lean",
           "(1/(1+theta+bigM)) * (hetDecayFromScaled Ne theta * "
           "(1 - bigM/(2Ne)))^t", cells_cand, control=control,
           regime="same runs, same estimator")


def main():
    test_half_life()
    import json
    with open("battery_dis4_results.json", "w") as f:
        json.dump(RESULTS, f, indent=1, default=float)


if __name__ == "__main__":
    main()
