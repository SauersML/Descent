"""Battery sved01: the withdrawn exponential, refuted on a second simulator.

WHY THIS EXISTS.  `Program.OpenQuestions.ldTaggingDecay` and its sibling
`PortabilityDrift.ldCorrelationDecay` are both `exp(-lambda*d)`, and both are
withdrawn: `popgensel/ldshapecell.py` fitted an exponential and a hyperbola to
the same binned msprime `r^2` curve, each with a free amplitude and a free rate,
and the hyperbola won by 7x and 40x in chi^2 per point while the exponential
missed at BOTH ends.  The withdrawal note names no replacement -- "no published
neutral two-locus theory in the corpus's reference set predicts an exponential
in genetic distance" -- and a falsified body with no successor leaves every
consumer holding the falsified shape.

WHAT THIS ADDS.  All of the existing evidence against the exponential comes from
ONE coalescent simulator and one fitting procedure.  This battery runs the same
question on a forward Wright-Fisher two-locus engine -- a different model class,
a different estimator, no msprime and no binning -- and asks whether the corpus
already contains the successor.  It does: `LDDecayTheory.ohtaKimuraSigmaDSq`.

THE THREE SHAPES, on one simulated curve at the same cells, with
`rho = 4*Ne*c`:

    Ohta-Kimura (1971)   (10 + rho)/((2 + rho)(11 + rho))   -- the corpus body
    Sved (1971)          1/(1 + rho)                        -- competing
    the withdrawn shape  A*exp(-k*rho), amplitude AND rate free

The exponential is fitted BY LEAST SQUARES TO THE VERY CURVE IT IS TESTED
AGAINST, on two free parameters.  That is the most generous possible treatment:
it is not asked to predict, only to describe.  The two hyperbolic forms are
given nothing -- no amplitude, no rate, no fitted constant.  A fitted
exponential that still loses to a parameter-free hyperbola settles the shape,
and no choice of `lambda` repairs the withdrawn bodies.

WHAT IS MEASURED, and it is `sigma_d^2` and not `E[r^2]`.

    sigma_d^2 = mean(D^2) / mean(p(1-p) q(1-q))

which is the ratio of expectations, and is the quantity Ohta-Kimura's closed
form is a closed form OF.  `E[r^2]`, the expectation of the ratio, is printed in
every cell as a diagnostic and NO VERDICT IS RECORDED ON IT, for a reason this
battery had to discover twice:

  * Sved's `1/(1 + rho)` was going to be added to the corpus as `svedExpectedR2`,
    on the reading that an `r^2` decay curve is a curve of `E[r^2]` and the
    corpus has no such quantity.  It is not supported.  Measured `E[r^2]` runs
    0.107 at `rho = 0.5` against Sved's 0.667, and the gap is not noise.
  * The reason is that `E[r^2]` HAS NO MUTATION-FREE EQUILIBRIUM TO MEASURE.  At
    the engine's own `mu = 1e-4` (`4*Ne*mu = 0.06`) the loci fix and 90% of
    replicates carry no polymorphism at all, so the average is over the remnant
    nearest to fixation.  Raising mutation to `4*Ne*mu = 1` keeps them
    polymorphic and destroys the thing being measured: mutation re-randomizes
    haplotypes, and the measured `sigma_d^2` falls from 0.358 to 0.143 against
    Ohta-Kimura's 0.365, so the setting that makes `E[r^2]` well defined breaks
    the drift-recombination equilibrium BOTH theories describe.
  * `sigma_d^2` is a ratio of means and is dominated by the replicates that are
    still segregating, which is why it survives the low-mutation setting and why
    the theory is stated in it.  This is the corpus's own position, in
    `ohtaKimuraSigmaDSq`'s docstring, arrived at here from the other direction.

So no `svedExpectedR2` is added.  The simulation was run to justify a new
definition and refused to.

CONTROL, exact and independent of all three shapes: with recombination switched
OFF, `E[D_t]` must decay by exactly `1 - 1/(2*Ne)` per generation.  Pinned by
drift alone, no equilibrium and no fitting, and it fails on any error in the
resampling, the haplotype bookkeeping or the replicate averaging.

The obvious dual -- drift OFF, so `E[D]` decays by exactly `(1-c)^t` -- was
written first and is DEGENERATE: with no drift the step is deterministic, every
replicate is the same trajectory, and the replicate sem is exactly zero.  The
harness voided the group, which is the right answer to a control that cannot
fail, and it is recorded here because it looked like the cleanest control in the
file.

CAN-FAIL.  The `rho` grid MUST reach below 10.  Ohta-Kimura and Sved agree to a
few percent by `rho = 100` and differ by nearly a factor of two as `rho -> 0`,
so a loosely-linked grid validates both and decides nothing.  This grid runs
`rho = 0.5` to `20`.

FRESHNESS: prints FRESHNESS=OK only if its own source carries the token below.
"""
import math
import os

import numpy as np

from battery_core import RESULTS, dump_results, record

FRESH_TOKEN = "SIMCOV-BATTERY-SVED01-GODWIT-20260806"

# The engine's own setting, kept deliberately: `4*Ne*mu = 0.06` at Ne = 150 is
# small enough that the equilibrium under test is drift-recombination and not
# mutation-drift.  See the module docstring for what raising it does.
MU = 1e-4
MAF = 0.05


def freshness():
    try:
        src = open(os.path.abspath(__file__)).read()
    except Exception:
        print("FRESHNESS=STALE (cannot read own source)")
        return
    print("FRESHNESS=%s (token %s)"
          % ("OK" if src.count(FRESH_TOKEN) >= 2 else "STALE", FRESH_TOKEN))


def wf_step(x, ne, c, rng, mutate=True):
    """One Wright-Fisher generation on four haplotype frequencies.

    Recombination, then mutation, then multinomial resampling; `x` is
    `(reps, 4)` over AB, Ab, aB, ab.  Transcribed from
    `differential/cluster/fam_ld_decay.py`, whose engine validated
    `ohtaKimuraSigmaDSq` -- the same engine on purpose, so a disagreement
    between that verdict and this one cannot be the simulator.
    """
    D = x[:, 0] * x[:, 3] - x[:, 1] * x[:, 2]
    x = x + c * np.stack([-D, D, D, -D], axis=1)
    if mutate:
        m = MU
        M = np.array([
            [(1 - m) ** 2, m * (1 - m), m * (1 - m), m * m],
            [m * (1 - m), (1 - m) ** 2, m * m, m * (1 - m)],
            [m * (1 - m), m * m, (1 - m) ** 2, m * (1 - m)],
            [m * m, m * (1 - m), m * (1 - m), (1 - m) ** 2],
        ])
        x = x @ M.T
    x = np.clip(x, 0.0, None)
    x /= x.sum(axis=1, keepdims=True)
    if ne is None:
        return x
    n = 2 * ne
    return rng.multinomial(n, x).astype(np.float64) / n


def d_of(x):
    return x[:, 0] * x[:, 3] - x[:, 1] * x[:, 2]


def measure(ne, c, burn, samples, reps, rng, thin=20):
    """Equilibrium `sigma_d^2`, the diagnostic `E[r^2]`, and what was dropped."""
    x = rng.multinomial(2 * ne, [0.25] * 4, size=reps).astype(np.float64) / (2 * ne)
    for _ in range(burn):
        x = wf_step(x, ne, c, rng)
    num, den, r2, kept, total = [], [], [], 0, 0
    for i in range(samples):
        x = wf_step(x, ne, c, rng)
        if i % thin:
            continue
        pa = x[:, 0] + x[:, 1]
        pb = x[:, 0] + x[:, 2]
        D = d_of(x)
        d4 = pa * (1 - pa) * pb * (1 - pb)
        num.append(D ** 2)
        den.append(d4)
        ok = ((np.minimum(pa, 1 - pa) >= MAF)
              & (np.minimum(pb, 1 - pb) >= MAF))
        total += len(d4)
        kept += int(ok.sum())
        if ok.any():
            r2.append((D[ok] ** 2) / d4[ok])
    num = np.concatenate(num)
    den = np.concatenate(den)
    r2 = np.concatenate(r2) if r2 else np.array([float("nan")])
    # sem of a ratio of means, to first order, from the sem of each mean.
    n = len(num)
    sn, sd = num.std(ddof=1) / math.sqrt(n), den.std(ddof=1) / math.sqrt(n)
    mn, md = float(num.mean()), float(den.mean())
    sig = mn / md
    sig_sem = abs(sig) * math.sqrt((sn / mn) ** 2 + (sd / md) ** 2) if mn > 0 else 0.0
    return sig, sig_sem, float(r2.mean()), 1.0 - kept / max(total, 1)


def fit_exponential(rho, y):
    """Least squares `A*exp(-k*rho)` in log space, both parameters free."""
    lg = np.log(np.maximum(y, 1e-12))
    k, a = np.polyfit(rho, lg, 1)
    return math.exp(a), -k


def main():
    freshness()
    print("FRESHNESS token literal: SIMCOV-BATTERY-SVED01-GODWIT-20260806")

    NE = 150
    RHOS = [0.5, 1.0, 2.0, 5.0, 10.0, 20.0]
    REPS, BURN, SAMPLES = 600, 6 * NE, 2000
    rng = np.random.default_rng(20260806)

    rows = []
    print("\n  %-14s %10s %10s %12s %10s %8s"
          % ("cell", "Ohta-Kim", "Sved", "sigma_d2 sim", "E[r2] diag", "MAF cut"))
    for rho in RHOS:
        c = rho / (4.0 * NE)
        sig, sig_sem, er2, lost = measure(NE, c, BURN, SAMPLES, REPS, rng)
        sved = 1.0 / (1.0 + rho)
        ok = (10.0 + rho) / ((2.0 + rho) * (11.0 + rho))
        print("  rho=%-10.1f %10.4f %10.4f %12.4f %10.4f %7.1f%%"
              % (rho, ok, sved, sig, er2, 100 * lost))
        rows.append(dict(rho=rho, sved=sved, ok=ok, sig=sig, sig_sem=sig_sem,
                         er2=er2, lost=lost))

    rho = np.array([r["rho"] for r in rows])
    amp, rate = fit_exponential(rho, np.array([r["sig"] for r in rows]))
    print("\n  exponential FITTED to this very curve, both parameters free: "
          "%.4f * exp(-%.4f * rho)" % (amp, rate))

    def cells(pred):
        return [dict(design="rho=%.1f (Ne=%d)" % (r["rho"], NE),
                     lean=pred(r), truth=r["sig"], sem=r["sig_sem"])
                for r in rows]

    ok_cells = cells(lambda r: r["ok"])
    sved_cells = cells(lambda r: r["sved"])
    exp_cells = cells(lambda r: amp * math.exp(-rate * r["rho"]))

    # ---- control: no recombination, so E[D] decays by (1 - 1/(2Ne)) --------
    gens, batches, per = 60, 6, 150
    retention = []
    for _ in range(batches):
        x = np.tile(np.array([0.5, 0.0, 0.0, 0.5]), (per, 1))
        traj = [float(np.mean(d_of(x)))]
        for _ in range(gens):
            x = wf_step(x, NE, 0.0, rng, mutate=False)
            traj.append(float(np.mean(d_of(x))))
        t = np.array(traj)
        keep = t > 1e-9
        slope = np.polyfit(np.arange(len(t))[keep], np.log(t[keep]), 1)[0]
        retention.append(math.exp(slope))
    control = dict(design="no recombination: E[D_t] must decay by "
                          "(1 - 1/(2Ne)) per generation",
                   lean=1.0 - 1.0 / (2.0 * NE),
                   truth=float(np.mean(retention)),
                   sem=float(np.std(retention, ddof=1) / math.sqrt(batches)))
    print("\n  CONTROL %s: predicted %.6f measured %.6f +/- %.6f"
          % (control["design"], control["lean"], control["truth"],
             control["sem"]))

    reg = ("neutral two-locus forward Wright-Fisher, Ne=150 diploids, 600 "
           "replicates, mutation mu=1e-4 both ways (4*Ne*mu = 0.06, so the "
           "equilibrium under test is drift-recombination and not "
           "mutation-drift), burn-in of 6*Ne generations then 2000 sampled "
           "every 20th. rho = 4*Ne*c runs 0.5 to 20, reaching below the "
           "rho=10 where Ohta-Kimura and Sved converge -- above it the grid "
           "would validate both and decide nothing. The observable is "
           "sigma_d^2 = mean(D^2)/mean(p(1-p)q(1-q)), the ratio of "
           "expectations, which is the quantity the Ohta-Kimura closed form is "
           "a closed form of. E[r^2], the expectation of the ratio, is printed "
           "per cell as a diagnostic and carries no verdict: it has no "
           "mutation-free equilibrium to measure here, and the mutation rate "
           "that makes it well defined destroys the equilibrium both theories "
           "describe. The exponential rival is fitted to this same curve with a "
           "free amplitude AND a free rate, so it is asked only to describe "
           "the data while the two hyperbolic forms are given no fitted "
           "constant at all")
    MODEL = dict(regime=reg, control=control, realised_inputs=True,
                 argument_source="model")

    record("ohtaKimuraSigmaDSq", "LDDecayTheory.lean",
           "(10 + rho) / ((2 + rho) * (11 + rho)), rho = 4*Ne*c",
           ok_cells, **MODEL)
    record("ohtaKimuraSigmaDSq [Sved's 1/(1+rho) in its place, competing]",
           "LDDecayTheory.lean", "1 / (1 + rho)", sved_cells, **MODEL)
    record("ohtaKimuraSigmaDSq [the withdrawn exponential shape, amplitude and "
           "rate fitted to this very curve, competing]", "LDDecayTheory.lean",
           "A * exp(-k * rho), A and k free", exp_cells, **MODEL)

    dump_results("battery_sved01_results.json")
    print("\n================ SUMMARY ================")
    for rec in RESULTS:
        w = rec.get("worst", {}) or {}
        print("%-30s %-56s worst %9.2f sems, %8.2f%% rel"
              % (rec["verdict"], rec["name"][:56],
                 w.get("sems_off", float("nan")),
                 100 * w.get("rel_err", float("nan"))))


if __name__ == "__main__":
    main()
