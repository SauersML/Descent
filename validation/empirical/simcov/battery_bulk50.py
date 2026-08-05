"""Battery 50: the phase-prediction error, and the drift horizon.

Rebuilt because `haplotypePhasePredictionError` and `driftHorizon` both cite
`simcov/battery_bulk50.py` and no such file was ever committed.

group_a  haplotypePhasePredictionError. True phase is drawn at rate `freq_cis`,
         a switch error is drawn INDEPENDENTLY at rate `switch_err` that flips
         which prediction is APPLIED, and the observable is the realised mean
         squared error.

         THE SWITCH ERROR ACTS ON THE READ, NOT ON THE TRUTH. An individual in
         cis whose phase is misread still HAS the cis interaction and merely
         receives the trans prediction; that is why the body pairs
         `interaction_cis` with `pred_trans` in its switched branch rather than
         swapping both. The two confusions this shape invites ride along:
         dropping the switch channel entirely, and applying the switch rate to
         the phase FREQUENCY rather than to the READ. The second is the subtler
         one -- it produces a number of the right magnitude that moves the right
         way with `switch_err` -- and only the opposite-sign design separates it
         cleanly.

group_b  driftHorizon = (D2 - D1) / (2*C). A walk closing the gap at expected
         rate 2*C per generation, with the observable the crossing time and the
         LAST STEP INTERPOLATED. Dropping the factor two rides along.

         THE CONTROL THAT THE EARLIER RUN LACKED. It compared a ratio against
         the number that ratio is by construction, and the harness correctly
         refused to license a falsification from it. The control here is a walk
         with a KNOWN closing rate run through the SAME estimator: at C fixed
         and the gap doubled, the crossing time must double. That can fail --
         and on the first run of this design it DID, at 4.4 sems, because a
         counted (unintepolated) crossing overshoots by part of a step. The
         answer to a control that fires is to fix the instrument, not to widen
         the bar until it stops firing; `crossing_time` interpolates.

FRESHNESS: prints FRESHNESS=OK only if its own source carries the token below,
and `dump_results` records this file's SHA inside the results.
"""
import math
import os

import numpy as np

from battery_core import RESULTS, dump_results, record

FRESH_TOKEN = "SIMCOV-BATTERY-BULK50-PEREGRINE-20260805"

MODEL = dict(realised_inputs=True, argument_source="model")


def freshness():
    try:
        src = open(os.path.abspath(__file__)).read()
    except OSError:
        print("FRESHNESS=STALE (cannot read own source)")
        return
    print("FRESHNESS=%s (token %s)"
          % ("OK" if src.count(FRESH_TOKEN) >= 2 else "STALE", FRESH_TOKEN))


def blocked(vals):
    a = np.asarray(vals, float)
    return float(a.mean()), float(a.std(ddof=1) / math.sqrt(a.size))


# ---------------------------------------------------------------------------
# group A -- haplotypePhasePredictionError
# ---------------------------------------------------------------------------
def group_a():
    print("\n===== GROUP A  haplotypePhasePredictionError")
    rng = np.random.default_rng(50001)
    n_blocks, per_block = 20, 200000

    cells, c_noswitch, c_onfreq = [], [], []
    control = None
    for fc, se, pc, pt, ic, it in ((0.6, 0.00, 0.5, 0.2, 0.5, 0.2),
                                   (0.6, 0.10, 0.5, 0.2, 0.5, 0.2),
                                   (0.4, 0.25, 0.3, 0.1, 0.9, 0.4),
                                   (0.7, 0.15, 0.4, -0.4, 0.6, -0.6)):
        errs, fracs = [], []
        for _ in range(n_blocks):
            is_cis = rng.random(per_block) < fc
            switched = rng.random(per_block) < se
            # The TRUTH is the individual's own interaction; the READ decides
            # which prediction is applied to it.
            truth = np.where(is_cis, ic, it)
            called_cis = np.where(switched, ~is_cis, is_cis)
            pred = np.where(called_cis, pc, pt)
            errs.append(float(np.mean((truth - pred) ** 2)))
            fracs.append(float(is_cis.mean()))
        got, sem = blocked(errs)
        fmean, fsem = blocked(fracs)
        lean = (fc * ((1 - se) * (ic - pc) ** 2 + se * (ic - pt) ** 2)
                + (1 - fc) * ((1 - se) * (it - pt) ** 2 + se * (it - pc) ** 2))
        noswitch = fc * (ic - pc) ** 2 + (1 - fc) * (it - pt) ** 2
        # the switch rate applied to the FREQUENCY instead of to the read
        fq = fc * (1 - se) + (1 - fc) * se
        onfreq = fq * (ic - pc) ** 2 + (1 - fq) * (it - pt) ** 2
        lab = "fc=%.1f se=%.2f pc=%+.1f pt=%+.1f" % (fc, se, pc, pt)
        print("  %-30s measured %.6f +/- %.6f   body %.6f   no-switch %.6f   "
              "on-frequency %.6f" % (lab, got, sem, lean, noswitch, onfreq))
        cells.append(dict(design=lab, lean=lean, truth=got,
                          sem=max(sem, 1e-12)))
        c_noswitch.append(dict(design=lab, lean=noswitch, truth=got,
                               sem=max(sem, 1e-12)))
        c_onfreq.append(dict(design=lab, lean=onfreq, truth=got,
                             sem=max(sem, 1e-12)))
        if control is None:
            control = dict(design=lab + " [counted cis fraction]", lean=fc,
                           truth=fmean, sem=max(fsem, 1e-12))

    reg = ("4e6 individuals per cell in 20 independent blocks of 2e5: true "
           "phase drawn at rate freq_cis, a switch error drawn INDEPENDENTLY "
           "at rate switch_err that flips which prediction is APPLIED, and the "
           "observable the realised mean squared error. switch_err is swept "
           "0 to 0.25 and one design gives the two interactions OPPOSITE "
           "SIGNS, where misreading phase costs most and the on-frequency "
           "confusion separates")
    record("haplotypePhasePredictionError", "HaplotypeTheory.lean",
           "freq_cis*((1-se)*(ic-pc)^2 + se*(ic-pt)^2) + "
           "(1-freq_cis)*((1-se)*(it-pt)^2 + se*(it-pc)^2)", cells,
           regime=reg, control=control, **MODEL)
    record("haplotypePhasePredictionError [switch channel dropped, competing]",
           "HaplotypeTheory.lean",
           "freq_cis*(ic-pc)^2 + (1-freq_cis)*(it-pt)^2", c_noswitch,
           regime=reg, control=control, **MODEL)
    record("haplotypePhasePredictionError [switch applied to the FREQUENCY, "
           "competing]", "HaplotypeTheory.lean",
           "q*(ic-pc)^2 + (1-q)*(it-pt)^2 with q = fc(1-se) + (1-fc)se",
           c_onfreq, regime=reg, control=control, **MODEL)


# ---------------------------------------------------------------------------
# group B -- driftHorizon
# ---------------------------------------------------------------------------
def crossing_time(gap, c, reps, seed):
    """Crossing time for a walk closing `gap` at expected rate 2*c.

    THE LAST STEP IS INTERPOLATED, and that is the whole difference between
    this design and the one whose verdict was a lead. Generations are integers;
    a COUNTED crossing overshoots the target by part of a step and biases the
    time upward by roughly one step in fifty. At 4000 replicates the error bar
    on the counted time is 0.02% and the bias is 0.13%, so the bias is six sems
    of a quantity that is not the law -- enough to VOID the positive control
    (the counted time at a doubled gap came back 1.9968 against a known 2) and
    with it every verdict in the group.

    Interpolating within the crossing step removes the discretisation instead of
    widening the bar to hide it: the walk is a continuous process observed on a
    lattice, and the crossing time it defines is continuous too.
    """
    rng = np.random.default_rng(seed)
    remaining = np.full(reps, float(gap))
    t = np.zeros(reps)
    alive = np.ones(reps, bool)
    for step in range(1, 200000):
        if not alive.any():
            break
        n = int(alive.sum())
        # Mean closure 2*c per generation, with symmetric noise so the RATE is
        # what the body reads and the walk is not deterministic.
        delta = 2 * c * (1.0 + 0.3 * rng.standard_normal(n))
        before = remaining[alive]
        after = before - delta
        crossed = after <= 0
        # Fraction of this step at which the crossing happened.
        frac = np.where(crossed & (delta > 0), before / np.maximum(delta, 1e-30),
                        1.0)
        idx = np.flatnonzero(alive)
        t[idx[crossed]] = (step - 1) + frac[crossed]
        remaining[alive] = after
        alive[idx[crossed]] = False
    return t


def group_b():
    print("\n===== GROUP B  driftHorizon = (D2 - D1) / (2*C)")
    cells, c_nohalf = [], []
    control = None
    for gap, c in ((1.0, 0.001), (2.0, 0.001), (1.0, 0.004), (0.5, 0.002)):
        t = crossing_time(gap, c, reps=4000, seed=50100 + int(1000 * c) + int(10 * gap))
        got, sem = float(t.mean()), float(t.std(ddof=1) / math.sqrt(t.size))
        lean = gap / (2 * c)
        lab = "gap=%.1f C=%.4f" % (gap, c)
        print("  %-18s counted %.2f +/- %.2f   body %.2f   no-factor-two %.2f"
              % (lab, got, sem, lean, gap / c))
        cells.append(dict(design=lab, lean=lean, truth=got,
                          sem=max(sem, 1e-12)))
        c_nohalf.append(dict(design=lab, lean=gap / c, truth=got,
                             sem=max(sem, 1e-12)))

    # POSITIVE CONTROL WITH TWO INDEPENDENT SIDES, which is what the earlier
    # run lacked: at fixed C, doubling the gap must double the counted time.
    # The counter is asked to reproduce a RATIO it was not told, so it can fail
    # -- unlike comparing a ratio against the number it is by construction.
    t1 = crossing_time(1.0, 0.002, reps=4000, seed=50777)
    t2 = crossing_time(2.0, 0.002, reps=4000, seed=50778)
    ratio = float(t2.mean()) / float(t1.mean())
    rsem = ratio * math.sqrt(
        (t2.std(ddof=1) / math.sqrt(t2.size) / t2.mean()) ** 2
        + (t1.std(ddof=1) / math.sqrt(t1.size) / t1.mean()) ** 2)
    print("  CONTROL crossing-time ratio at doubled gap: %.4f +/- %.4f "
          "(known 2)" % (ratio, rsem))
    control = dict(design="gap doubled at fixed C [crossing time must double]",
                   lean=2.0, truth=ratio, sem=max(rsem, 1e-12))

    reg = ("a walk closing the gap at expected rate 2*C per generation with "
           "symmetric multiplicative noise, 4000 replicates, the observable "
           "the crossing time with the LAST STEP INTERPOLATED. Gap and C are swept "
           "independently. Generations are integers and the last step "
           "overshoots, which biases a counted crossing time upward by roughly "
           "one step in fifty -- the residual to expect, and the reason a "
           "continuous-time design would be the sharper instrument")
    record("driftHorizon", "DirichletTransfer.lean", "(D2 - D1) / (2 * C)",
           cells, regime=reg, control=control, **MODEL)
    record("driftHorizon [factor two dropped, competing]",
           "DirichletTransfer.lean", "(D2 - D1) / C", c_nohalf, regime=reg,
           control=control, **MODEL)


def main():
    freshness()
    print("FRESHNESS token literal: SIMCOV-BATTERY-BULK50-PEREGRINE-20260805")
    group_a()
    group_b()
    dump_results("battery_bulk50_results.json",
                 battery_source=os.path.abspath(__file__))
    print("\n================ SUMMARY ================")
    for r in RESULTS:
        w = r.get("worst", {})
        print("%-12s %-66s worst %9.2f sems, %7.2f%% rel"
              % (r["verdict"], r["name"], w.get("sems_off", float("nan")),
                 100 * w.get("rel_err", float("nan"))))


if __name__ == "__main__":
    main()
