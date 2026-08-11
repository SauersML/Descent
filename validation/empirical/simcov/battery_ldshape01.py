"""Battery ldshape01: the AMPLITUDE the hyperbolic LD candidate commits to.

WHAT IS OWED AND BY WHOM.  `PortabilityDrift.ldCorrelationDecay` is FALSIFIED as
a shape in distance, and its record names a successor it refuses to install.  The
refusal is specifically about the amplitude, and the record says so:

    "Both fits carry a free amplitude, measured at 0.373 and 0.316.  This body is
     normalised to 1 at zero distance ... A hyperbolic with amplitude 1 is
     therefore NOT the curve that was fitted, and nothing in cell `I` bears on
     whether the corpus's normalisation survives once the amplitude is pinned."

and it names the one thing that would land the repair:

    "one cell fitting the amplitude-1 hyperbolic against measured `r²` normalised
     to its own zero-distance limit -- a re-analysis of cell `I`'s stored curve,
     not a new simulation."

This is that cell.  `ldCorrelationDecayHyperbolic` is the candidate written at the
falsified body's signature, and it is the one under test here.

NO NEW SIMULATION.  Every number comes from `popgensel/results.json` cell `I`,
the two stored msprime `r²` curves (Ne = 2000 over 4 Mb and Ne = 5000 over 2 Mb,
300 haplotypes, MAF 0.05, 12 and 14 distance bins with their own sems).  Their
`k·d` reaches 0.01 to 10 once a rate is fitted, which spans the range where the
candidate shape and its rivals part company, so the stored data suffice and a
fresh run would only re-draw them.

THE CANDIDATE IS NOT THE NAIVE HYPERBOLA, and the distinction is the point.
Cell `I` fitted `A/(1 + b·d)`.  `ldCorrelationDecayHyperbolic` is the
Ohta-Kimura form normalised at zero,

    f(rho) = 22·(10 + rho) / (10·(2 + rho)·(11 + rho)),   rho = lambda·sqrt(fstGap)·d

which is a ratio of quadratics and decays MORE SLOWLY than `1/(1+rho)` through
the middle of the range -- 0.672 against 0.500 at `rho = 1`, 0.175 against 0.091
at `rho = 10`.  So the naive hyperbola is carried here as a competitor and not as
a stand-in: cell `I`'s verdict on `A/(1+b·d)` is not a verdict on this body.

THE ZERO-DISTANCE LIMIT COMES FROM THE SHORTEST BINS ALONE, AND THAT IS WHAT
MAKES THIS A TEST.  Deriving the normalisation from the whole curve and then
checking that the whole curve is normalised would be circular.  So the anchor
`A0` is built from the THREE SHORTEST distance bins and nothing else -- a count
fixed before any curve was looked at -- while the RATE is fitted to the whole
curve.  A wrong shape makes those two disagree, and that disagreement is the
observable.  The curve is divided by `A0` and the candidate is then fitted with
ONE free parameter, the rate, its amplitude pinned at 1: the commitment the
record says is uncovered.  Cell `I`'s fits had TWO free parameters, so this is a
strictly harder test than the one that produced the standing evidence.

The anchor divides each of those three bins by the candidate's own value there
before averaging, and that correction is not a convenience: the bins sit at `rho`
of 0.01 to 0.15, where the shape has already fallen a few percent below one, so
an uncorrected mean of them lands BELOW the zero-distance limit and every
amplitude measured against it comes out high.  This battery's control measured
that bias at 4.0% and 12.8 sems before the correction was in -- larger than the
effect being reported, and caught by the control rather than by a reading of the
verdict.  Every candidate is anchored with ITSELF, so none is handicapped by
being normalised against a rival's limit.

THE ANCHOR'S OWN ERROR IS CARRIED INTO EVERY CELL, in quadrature, and it
dominates: the three shortest bins are the noisiest in each curve and `A0` lands
at 6.4% relative in both.  That term is COMMON to a curve's cells rather than
independent across them -- it slides the whole curve up or down instead of
scattering it -- so the per-cell bars here are conservative, and deliberately:
the failure this harness has paid for most often is a false falsification, and an
amplitude claim tested without the amplitude's own error bar is exactly that
waiting to happen.

WHAT THE TWO DESIGNS AGREE ABOUT, printed as a diagnostic.  Under the theory the
zero-distance plateau of binned `E[r²]` is set by the sample size and the MAF
filter, which both designs share, and NOT by `Ne`.  The two anchors are 0.3697
and 0.3731.  That they agree to 1% across a 2.5-fold change in `Ne` is evidence
that the plateau is a real measurable quantity rather than an artefact of
whichever curve is being fitted, which is what the anchor has to be for this
re-analysis to mean anything.

THE SCALE MISMATCH IS DECLARED AND IS NOT REPAIRED BY THIS RUN.  Ohta-Kimura is a
closed form for `sigma_d^2 = E[D²]/E[pq p'q']`, the ratio of expectations, and
these stored curves are binned means of `r²`, the expectation of the ratio.
`battery_sved01` established that the two are different numbers and that `E[r²]`
has no mutation-free equilibrium to measure.  Normalising each curve to its own
zero-distance limit is what makes the comparison a comparison of SHAPES, where
that mismatch cancels to the extent it is a common factor -- and it is not known
to cancel exactly.  So a MATCH here licenses the shape and the amplitude-1
normalisation, and does not license reading this body as a `sigma_d^2`.

CONTROL, and it gates on the pipeline rather than on the data: synthetic curves
drawn from a TRUE amplitude-1 candidate at the stored `x` with the stored
per-point sems, put through this file's own anchor recipe and fitter, must come
back with amplitude 1.  It fails if the three-bin anchor is biased by the shape's
droop across those bins, if the fitter's rate grid is too coarse or too narrow,
or if the weighting is wrong -- every way this re-analysis could manufacture its
own answer.  It is not a restatement of the claim, because the claim is about
MEASURED curves and the control is about synthetic ones whose truth is known.

FRESHNESS: prints FRESHNESS=OK only if its own source carries the token below,
and `dump_results` records this file's SHA inside the results.
"""
import json
import math
import os

import numpy as np

from battery_core import RESULTS, dump_results, record

FRESH_TOKEN = "SIMCOV-BATTERY-LDSHAPE01-SHRIKE-20260810"

LEAN_FILE = "PresentDayMetrics.lean"

# The stored cell-I curves, read and never regenerated.
SOURCE = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                      "..", "popgensel", "results.json")

N_ANCHOR = 3            # bins defining the zero-distance limit, fixed a priori
CTRL_REPS = 400
RATE_GRID = np.exp(np.linspace(math.log(1e1), math.log(1e7), 30000))


def freshness():
    try:
        src = open(os.path.abspath(__file__)).read()
    except OSError:
        print("FRESHNESS=STALE (cannot read own source)")
        return
    print("FRESHNESS=%s (token %s)"
          % ("OK" if src.count(FRESH_TOKEN) >= 2 else "STALE", FRESH_TOKEN))


# ---------------------------------------------------------------------------
# The shapes, each normalised to 1 at zero so the amplitude is not free.
# ---------------------------------------------------------------------------
def ok_normalised(rho):
    """`ldCorrelationDecayHyperbolic`, via `ldCorrelationDecayHyperbolic_closed`:
    `22*(10 + rho) / (10*(2 + rho)*(11 + rho))`."""
    return 22.0 * (10.0 + rho) / (10.0 * (2.0 + rho) * (11.0 + rho))


def naive_hyperbolic(rho):
    """`1 / (1 + rho)` -- the shape cell `I` actually fitted, amplitude pinned."""
    return 1.0 / (1.0 + rho)


def exponential(rho):
    """`ldCorrelationDecay`'s shape, `exp(-rho)`, amplitude pinned."""
    return np.exp(-rho)


# ---------------------------------------------------------------------------
def anchor(x, y, s, shape, rate, n=N_ANCHOR):
    """The zero-distance limit, from the `n` shortest bins and those alone.

    THE DROOP CORRECTION IS NOT OPTIONAL, and this battery's own control is what
    established that. A first version took the bare inverse-variance mean of the
    three shortest bins -- no shape anywhere in it, which read as the more honest
    choice. It is biased: those bins sit at `rho` of 0.01 to 0.15, where the
    candidate has already fallen a few percent below one, so the mean of them
    estimates the curve slightly BELOW its zero-distance limit and every
    amplitude measured against it comes out correspondingly high. Fed synthetic
    curves of KNOWN amplitude 1, that pipeline returned 1.0400 +/- 0.0031 -- a
    4% bias at 12.8 sems, which is the size of the effect this file exists to
    measure. The control caught it before the verdict did.

    So each bin is divided by the shape's own value there before averaging.
    Every candidate is anchored with ITSELF, never with a privileged one, so no
    shape is handicapped; the amplitude claim survives because the anchor still
    uses only the three shortest bins while the rate is fitted to the whole
    curve, and a wrong shape makes those two disagree.
    """
    x = np.asarray(x, float)[:n]
    y = np.asarray(y, float)[:n]
    s = np.asarray(s, float)[:n]
    f = shape(rate * x)
    # z_i = y_i / f_i estimates the amplitude, with variance (s_i / f_i)^2.
    w = (f / s) ** 2
    a = float((w * (y / f)).sum() / w.sum())
    return a, float(1.0 / math.sqrt(w.sum()))


def fit_rate(x, y, w, shape):
    """The one free parameter: the rate. Amplitude is pinned at 1."""
    base = shape(RATE_GRID[:, None] * x[None, :])
    sse = (w[None, :] * (y[None, :] - base) ** 2).sum(axis=1)
    i = int(np.argmin(sse))
    return float(RATE_GRID[i]), float(sse[i])


def fit_rate_and_amplitude(x, y, w, shape):
    """Both free, as cell `I` fitted them -- used only to report the amplitude
    the data want, against the 1 the body commits to."""
    base = shape(RATE_GRID[:, None] * x[None, :])
    num = (w[None, :] * y[None, :] * base).sum(axis=1)
    den = (w[None, :] * base * base).sum(axis=1)
    amp = num / np.maximum(den, 1e-300)
    sse = (w[None, :] * (y[None, :] - amp[:, None] * base) ** 2).sum(axis=1)
    i = int(np.argmin(sse))
    return float(amp[i]), float(RATE_GRID[i]), float(sse[i])


def load_curves():
    rows = json.load(open(SOURCE))["I"]["detail"]
    out = []
    for r in rows:
        x = np.asarray(r["x"], float)
        y = np.asarray(r["y"], float)
        s = np.asarray(r["sem"], float)
        out.append(dict(label="Ne=%d over %.0f Mb" % (r["Ne"], r["seqlen"] / 1e6),
                        x=x, y=y, sem=s,
                        cellI_hyp=r["hyp_params"], cellI_exp=r["exp_params"]))
    return out


SHAPES = (
    ("ldCorrelationDecayHyperbolic", ok_normalised,
     "22*(10 + rho)/(10*(2 + rho)*(11 + rho)), rho = lambda*sqrt(fstGap)*d",
     ""),
    ("ldCorrelationDecayHyperbolic [the NAIVE amplitude-1 hyperbola 1/(1+rho) "
     "in its place, the shape cell I actually fitted, competing]",
     naive_hyperbolic, "1 / (1 + rho)",
     "cell I's free-amplitude verdict was about THIS curve and not about the "
     "body; carried so the two are not conflated"),
    ("ldCorrelationDecayHyperbolic [the FALSIFIED exponential shape exp(-rho) "
     "in its place, competing]", exponential, "exp(-rho)",
     "the shape ldCorrelationDecay carries, FALSIFIED at 6.29 sems by "
     "battery_sved01 with a least-squares-fitted amplitude AND rate; carried "
     "so that a design in which it passed would be known to be broken"),
)


def main():
    freshness()
    print("FRESHNESS token literal: SIMCOV-BATTERY-LDSHAPE01-SHRIKE-20260810")

    curves = load_curves()

    def anchored(c, shape):
        """(A0, sem, rate). The rate comes from a FREE fit to the whole curve;
        the amplitude comes from the shortest bins alone, corrected for the
        shape's own droop across them."""
        w = 1.0 / np.asarray(c["sem"], float) ** 2
        _, rate, _ = fit_rate_and_amplitude(c["x"], c["y"], w, shape)
        a0, a0s = anchor(c["x"], c["y"], c["sem"], shape, rate)
        return a0, a0s, rate

    print("\nzero-distance anchors, from the %d shortest bins with the "
          "candidate's own droop across them divided out:" % N_ANCHOR)
    for c in curves:
        a0, a0s, _ = anchored(c, ok_normalised)
        c["a0"], c["a0_sem"] = a0, a0s
        print("  %-22s A0 = %.4f +/- %.4f (%.1f%%)   cell I's free-amplitude "
              "naive-hyperbolic fit wanted A = %.4f"
              % (c["label"], a0, a0s, 100 * a0s / a0, c["cellI_hyp"]["A"]))
    print("  DIAGNOSTIC: under the theory the plateau is set by the shared "
          "sample size and MAF filter, not by Ne, and the two agree to %.1f%% "
          "across a %.1f-fold change in Ne"
          % (100 * abs(curves[0]["a0"] - curves[1]["a0"])
             / max(curves[0]["a0"], curves[1]["a0"]), 5000 / 2000))

    # ---- DISCRIMINATION, on the statistic the anchor cannot reach ----------
    #
    # The recorded rows below normalise by the anchor and so carry its ~6%
    # uncertainty in every bar. That is the right bar for the AMPLITUDE claim
    # and it is the wrong one for telling two hyperbolas apart: the anchor term
    # is COMMON to both candidates, so it inflates both residuals equally and
    # buries the difference between the shapes under an error that cancels.
    #
    # So the shapes are also compared the way cell `I` compared its own two --
    # each fitted with a FREE amplitude and a free rate, chi-squared per point
    # against the measurement sems alone, no anchor anywhere. That statistic is
    # what gave cell `I` its 7x and 40x margins for hyperbolic over
    # exponential, and it is the one that can say whether the corpus's
    # Ohta-Kimura normalisation is preferred to the naive hyperbola or merely
    # tied with it.
    print("\nDISCRIMINATION: chi-squared per point, no anchor, each shape given "
          "a free amplitude AND a free rate (the statistic cell I used):")
    print("  %-22s %14s %14s %14s" % ("curve", "Ohta-Kimura", "naive 1/(1+r)",
                                      "exponential"))
    for c in curves:
        w = 1.0 / np.asarray(c["sem"], float) ** 2
        row = []
        for _, shape, _, _ in SHAPES:
            _, _, sse = fit_rate_and_amplitude(c["x"], c["y"], w, shape)
            row.append(sse / len(c["x"]))
        print("  %-22s %14.3f %14.3f %14.3f" % (c["label"], row[0], row[1],
                                                row[2]))
    print("  and with the amplitude PINNED at 1 against each curve's own "
          "anchor, which is the claim under test:")
    print("  %-22s %14s %14s %14s" % ("curve", "Ohta-Kimura", "naive 1/(1+r)",
                                      "exponential"))
    for c in curves:
        row = []
        for _, shape, _, _ in SHAPES:
            a0, _, _ = anchored(c, shape)
            yn = np.asarray(c["y"], float) / a0
            sn = np.asarray(c["sem"], float) / a0
            _, sse = fit_rate(c["x"], yn, 1.0 / sn ** 2, shape)
            row.append(sse / len(c["x"]))
        print("  %-22s %14.3f %14.3f %14.3f" % (c["label"], row[0], row[1],
                                                row[2]))

    # ---- THE RATE IS NOT FREE, AND THAT IS WHAT SEPARATES THE TWO HYPERBOLAS
    #
    # Everything above lets each shape choose its own rate, and with a free rate
    # the two hyperbolas are nearly degenerate over the measured range: one wins
    # on one curve, the other on the other, by 1.1x in chi-squared per point
    # against a precedent that called 7x and 40x decisive. A free rate is also
    # not what the theory offers. `rho = 4*Ne*c`, and both `Ne` and the genetic
    # distance are the simulation's OWN parameters -- these curves were run at
    # Ne = 2000 and 5000 with x already in Morgans -- so `rho = 4*Ne*x` is
    # computable and neither shape is entitled to a fitted constant.
    #
    # Pinned there, each candidate has ZERO free parameters: the amplitude comes
    # from its own three shortest bins and the rate from the simulation. The
    # ratio of the FITTED rate to `4*Ne` is reported beside it, because that
    # ratio is the effective Ne each shape implies and it is a physical quantity
    # a reader can check. Cell `I`'s record warns that this recovery carries a
    # known downward bias for r-squared off a finite sample -- it saw Ne_eff 563
    # against a true 1000 -- so the ABSOLUTE ratio is not a pass/fail; the two
    # shapes' ratios against each other, on the same curves and the same
    # estimator, are the comparison that bias is common to.
    print("\nTHE RATE PINNED AT ITS THEORETICAL 4*Ne, no free parameter left in "
          "either shape:")
    print("  %-22s %10s %24s %24s"
          % ("curve", "4*Ne", "Ohta-Kimura chi2/pt (Ne_eff)",
             "naive 1/(1+r) chi2/pt (Ne_eff)"))
    for c, ne in zip(curves, (2000.0, 5000.0)):
        x = np.asarray(c["x"], float)
        rho_true = 4.0 * ne * x
        out = []
        for _, shape, _, _ in SHAPES[:2]:
            a0, _, fitted = anchored(c, shape)
            yn = np.asarray(c["y"], float) / a0
            sn = np.asarray(c["sem"], float) / a0
            resid = (yn - shape(rho_true)) / sn
            chi2 = float((resid ** 2).sum() / len(x))
            out.append((chi2, fitted / 4.0))
        print("  %-22s %10.0f %14.3f (Ne_eff %6.0f) %14.3f (Ne_eff %6.0f)"
              % (c["label"], 4 * ne, out[0][0], out[0][1], out[1][0],
                 out[1][1]))

    # ---- CONTROL ---------------------------------------------------------
    # Synthetic curves of KNOWN amplitude 1, through this file's own anchor
    # recipe and fitter. The record's own control doctrine: feed the fitter a
    # curve whose shape is known and require it to recover that shape.
    rng = np.random.default_rng(20260810)
    amps = []
    for c in curves:
        x, s = c["x"], c["sem"]
        k_true = 1.0 / float(np.median(x))
        truth = c["a0"] * ok_normalised(k_true * x)
        for _ in range(CTRL_REPS // 2):
            yy = truth + rng.normal(0.0, s)
            w = 1.0 / s ** 2
            amp_full, rate, _ = fit_rate_and_amplitude(x, yy, w, ok_normalised)
            a0, _ = anchor(x, yy, s, ok_normalised, rate)
            amps.append(amp_full / a0)
    amps = np.asarray(amps, float)
    control = dict(
        design="synthetic amplitude-1 candidate at the stored x and sems: the "
               "amplitude the WHOLE curve wants, divided by the one the three "
               "shortest bins want, must be 1",
        lean=1.0, truth=float(amps.mean()),
        sem=max(float(amps.std(ddof=1) / math.sqrt(amps.size)), 1e-12))
    print("\n  CONTROL %s: predicted %.6f measured %.6f +/- %.6f"
          % (control["design"], control["lean"], control["truth"],
             control["sem"]))

    # ---- the amplitude the data want, reported per curve ------------------
    print("\namplitude the WHOLE curve wants, against the one the shortest bins "
          "want (the body commits to their ratio being 1):")
    for c in curves:
        a0, a0s, rate = anchored(c, ok_normalised)
        amp_full, _, _ = fit_rate_and_amplitude(
            c["x"], c["y"], 1.0 / np.asarray(c["sem"], float) ** 2,
            ok_normalised)
        print("  %-22s A_full = %.4f   A_short = %.4f +/- %.4f   ratio %.4f "
              "(rate %.4g)"
              % (c["label"], amp_full, a0, a0s, amp_full / a0, rate))

    # ---- the recorded groups ---------------------------------------------
    reg = (
        "a RE-ANALYSIS of the two stored msprime r-squared curves in "
        "popgensel/results.json cell I -- Ne=2000 over 4 Mb and Ne=5000 over "
        "2 Mb, 300 haplotypes, MAF 0.05, %d and %d distance bins with their own "
        "sems -- and no new simulation. Each curve is divided by its own "
        "zero-distance limit, built from its %d SHORTEST bins alone with the "
        "candidate's own droop across them divided out, while the RATE is "
        "fitted to the WHOLE curve: a wrong shape makes the two disagree, and "
        "each candidate is anchored with itself so none is handicapped. Each "
        "candidate is then fitted with ONE free parameter, the "
        "rate, its amplitude PINNED at 1, which is the commitment "
        "ldCorrelationDecay's falsification record says nothing in cell I "
        "covers; cell I's own fits carried TWO free parameters, so this is the "
        "harder test. Every cell's error bar carries the anchor's own (roughly "
        "6%%) "
        "relative uncertainty in quadrature with the bin's; that term is COMMON "
        "to a curve's cells rather than independent, so it slides the curve "
        "rather than scattering it and the bars are conservative. The measured "
        "curves are binned E[r-squared] while Ohta-Kimura is a closed form for "
        "sigma_d-squared, the ratio of expectations; normalising each curve to "
        "its own zero-distance limit is what makes this a comparison of SHAPES, "
        "and that mismatch is not known to cancel exactly, so a match here "
        "licenses the shape and the amplitude-1 normalisation and does not "
        "license reading this body as a sigma_d-squared"
        % (len(curves[0]["x"]), len(curves[1]["x"]), N_ANCHOR))

    for name, shape, source, note in SHAPES:
        cells = []
        for c in curves:
            x, y, s = c["x"], c["y"], c["sem"]
            # ANCHORED WITH ITSELF, so no shape is handicapped by being
            # normalised against a rival's zero-distance limit.
            a0, asem, _ = anchored(c, shape)
            yn = y / a0
            # the anchor term is common across the curve's cells; carried in
            # every bar because the claim under test is the level, not only the
            # shape.
            sn = np.sqrt((s / a0) ** 2 + (yn * asem / a0) ** 2)
            k, _ = fit_rate(x, yn, 1.0 / sn ** 2, shape)
            pred = shape(k * x)
            for xi, ti, si, pi in zip(x, yn, sn, pred):
                cells.append(dict(design="%s d=%.3g (rate %.4g)"
                                         % (c["label"], xi, k),
                                  lean=float(pi), truth=float(ti),
                                  sem=float(max(si, 1e-12))))
        record(name, LEAN_FILE, source, cells, regime=reg, control=control,
               note=note, realised_inputs=True)

    dump_results("battery_ldshape01_results.json",
                 battery_source=os.path.abspath(__file__))
    print("\n================ SUMMARY ================")
    for r in RESULTS:
        w = r.get("worst", {}) or {}
        print("%-34s %-64s worst %9.2f sems, %8.2f%% rel"
              % (r["verdict"], r["name"][:64], w.get("sems_off", float("nan")),
                 100 * w.get("rel_err", float("nan"))))


if __name__ == "__main__":
    main()
