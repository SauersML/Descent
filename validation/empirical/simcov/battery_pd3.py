"""Battery pd3: the IM-equilibrium squared mean PGS difference, and its convention join.

WHAT IS UNDER TEST.  `expectedSqMeanPGSDiff_IMEquilibrium V_A M = Var_Delta_Mu V_A (2*delta)`
with `delta = twoDemeIMEquilibriumDelta M = 1/(2M+1)`.  Both components already
carry measurements and they are measurements of DIFFERENT CONVENTIONS:

  Var_Delta_Mu V_A f = 2 f V_A   is validated with `f` read as the SUM OF THE
      PER-BRANCH DRIFT INDICES.  Its docstring records that a two-branch design
      fed a pairwise value produced a factor-of-four false falsification twice.
  twoDemeIMEquilibriumDelta M    is validated as HUDSON's F_ST, 1 - ETss/ETst.

So the substitution `fstS + fstT |-> 2*delta` is the entire content of this body,
and it is a bridge between two conventions in the family this corpus has paid for
three times.  A docstring derivation put the exact join at

    A := E[dp^2] / E[pbar(1-pbar)]  =  2*delta / (1 - delta/2)

(from Hudson's denominator being 2*pbar(1-pbar) + dp^2/2), which makes the body
LOW by (1 - delta/2): 2.4% at M = 10 and 17% at M = 1.  That derivation is
algebra and was never checked against a simulation.  This checks it.

THE OBSERVABLE.  `A = E[dp^2] / E[pbar(1-pbar)]` is what `Var_Delta_Mu`'s slot
takes: variances add over independent branches, so for a pure split
E[dp^2] = (F_S + F_T) p0(1-p0), which is how `battery_verify.py` validated that
body.  Measuring A therefore measures the argument the corpus feeds, with no
V_A convention anywhere in it -- which matters, because V_A carries its own
factor-of-two conventions and `Var_Delta_Mu` is separately validated.

THREE CANDIDATES on the same cells, all evaluated at the simulation's own M:

    body          A = 2/(2M+1)
    derived       A = (2/(2M+1)) / (1 - 1/(2*(2M+1)))
    competitor    A = 1/(2M+1)            [the "pairwise IS per-branch" reading]

argument_source: MODEL.  M = 4*Ne*m is written into the update rule; no cell
takes its prediction from an estimate made on the replicates it scores.

CONTROLS, both able to fail:
  C1  PURE SPLIT, no migration, t generations from a common ancestor.  There
      A = F_S + F_T = 2*(1 - (1 - 1/(2*Ne))^t) exactly, a closed form owing
      nothing to the island model or to either candidate.  This is the control
      that gates: it exercises the same estimator and the same code path.
  C2  the measured Hudson F_ST against the closed form 1/(2M+1), reported
      rather than gated.  It pins the M convention EMPIRICALLY instead of by
      assumption, which is the step that would otherwise be an unchecked
      premise of the whole design.
"""
import json
import math
import os
from multiprocessing import Pool

import numpy as np

GUARD = "PD3-FRESHNESS-IM-DELTA-JOIN-v2"

REPS = 12


def two_deme_rep(args):
    """One replicate: returns (A, hudson) as ratios of averages over loci+generations."""
    N, m, L, gens, burn, mu, seed, split = args
    twoN = 2 * N
    rng = np.random.default_rng(seed)
    cnt = rng.binomial(twoN, 0.5, size=(2, L)).astype(np.int64)
    num_a = den_a = num_h = den_h = 0.0
    half = burn + (gens - burn) // 2
    h1n = h1d = h2n = h2d = 0.0
    for g in range(gens):
        p = cnt / twoN
        if split:
            pmix = p                      # no migration: two independent branches
        else:
            pmix = np.stack([(1.0 - m) * p[0] + m * p[1],
                             (1.0 - m) * p[1] + m * p[0]])
        if mu > 0.0:
            pmix = pmix * (1.0 - mu) + (1.0 - pmix) * mu
        cnt = rng.binomial(twoN, pmix)
        if g >= burn:
            q = cnt / twoN
            dp = q[0] - q[1]
            pbar = 0.5 * (q[0] + q[1])
            num_a += float((dp * dp).sum())
            den_a += float((pbar * (1.0 - pbar)).sum())
            num_h += float((dp * dp).sum())
            den_h += float((q[0] * (1 - q[1]) + q[1] * (1 - q[0])).sum())
            if g < half:
                h1n += float((dp * dp).sum())
                h1d += float((q[0] * (1 - q[1]) + q[1] * (1 - q[0])).sum())
            else:
                h2n += float((dp * dp).sum())
                h2d += float((q[0] * (1 - q[1]) + q[1] * (1 - q[0])).sum())
    early = h1n / h1d if h1d > 0 else float("nan")
    late = h2n / h2d if h2d > 0 else float("nan")
    return (num_a / den_a, num_h / den_h, early, late)


def summarize(v):
    v = np.asarray(v, float)
    return float(v.mean()), float(v.std(ddof=1) / math.sqrt(len(v)))


# (M, N)  --  m = M/(4N), kept small so the discrete/diffusion gap stays under the signal
CELLS = [(0.5, 250), (1.0, 250), (2.0, 250), (4.0, 250), (10.0, 250)]
L_LOCI = 4000
GENS, BURN = 2600, 1400
THETA = 0.02          # 4*N*mu, small against 2M+1 which runs 2 to 21

# the pure-split control: one ancestral population, two branches, t generations
SPLIT_N, SPLIT_T = 250, 200


def main():
    print("FRESHNESS_GUARD=%s" % GUARD)
    jobs = []
    for (M, N) in CELLS:
        m = M / (4.0 * N)
        mu = THETA / (4.0 * N)
        for r in range(REPS):
            jobs.append((N, m, L_LOCI, GENS, BURN, mu, 5100 + 313 * r + int(100 * M), False))
    for r in range(REPS):
        # no migration, no mutation: the closed form below assumes neither
        jobs.append((SPLIT_N, 0.0, L_LOCI, SPLIT_T, SPLIT_T - 1, 0.0, 8100 + 313 * r, True))

    pool = Pool(12)
    out = pool.map(two_deme_rep, jobs)
    pool.close()
    pool.join()

    k = 0
    rows = []
    for (M, N) in CELLS:
        vals = out[k:k + REPS]
        k += REPS
        a = summarize([v[0] for v in vals])
        h = summarize([v[1] for v in vals])
        e = summarize([v[2] for v in vals])
        l = summarize([v[3] for v in vals])
        rows.append((M, N, a, h, e, l))
        print("M=%-5.1f Ne=%d   A = %.5f +/- %.5f    Hudson = %.5f +/- %.5f   (closed form delta = %.5f)"
              % (M, N, a[0], a[1], h[0], h[1], 1.0 / (2 * M + 1)))

    sv = out[k:k + REPS]
    ctrl_a = summarize([v[0] for v in sv])
    # A is NOT 2F.  The denominator E[pbar(1-pbar)] is not p0(1-p0): pbar itself
    # drifts, Var(pbar) = F*p0(1-p0)/2, so E[pbar(1-pbar)] = p0(1-p0)*(1 - F/2)
    # and A = 2F/(1 - F/2).  The first version of this control omitted that factor
    # and missed by 32.3 sems -- against a simulation that was right.  The factor
    # is the SAME (1 - x/2) the island derivation predicts, which is why getting
    # it wrong here and right there would have been incoherent.
    _F = 1.0 - (1.0 - 1.0 / (2.0 * SPLIT_N)) ** SPLIT_T
    ctrl_pred = 2.0 * _F / (1.0 - _F / 2.0)
    print("\nCONTROL C1 pure split, Ne=%d, t=%d:  A predicted %.5f (= 2F/(1-F/2)), "
          "measured %.5f +/- %.5f, %.2f sems"
          % (SPLIT_N, SPLIT_T, ctrl_pred, ctrl_a[0], ctrl_a[1],
             abs(ctrl_a[0] - ctrl_pred) / ctrl_a[1]))
    print("\nIDENTITY CHECK  A against 2*d/(1-d/2) with d the MEASURED Hudson on the SAME")
    print("replicates. This is algebra between two estimators, not a claim about the world;")
    print("it is here to show the derivation is the right algebra.")
    for (M, N, a, h, e, l) in rows:
        pred = 2 * h[0] / (1 - h[0] / 2)
        print("   M=%-5.1f  identity %.5f  measured A %.5f   %.3f%% apart"
              % (M, pred, a[0], 100 * abs(pred - a[0]) / a[0]))

    print("\nDRIFT CHECK  Hudson over the first vs second half of the sampling window.")
    print("Two demes have no stationary distribution at 4*N*mu = %.2f, so a rising value is" % THETA)
    print("the quasi-equilibrium drifting up as loci fix -- the confound C2 would show.")
    for (M, N, a, h, e, l) in rows:
        print("   M=%-5.1f  early %.5f +/- %.5f   late %.5f +/- %.5f   %+.1f%%"
              % (M, e[0], e[1], l[0], l[1], 100 * (l[0] - e[0]) / e[0]))

    print("\nCONTROL C2 measured Hudson against 1/(2M+1), reported not gated:")
    for (M, N, a, h, e, l) in rows:
        d = 1.0 / (2 * M + 1)
        print("   M=%-5.1f  closed %.5f  measured %.5f +/- %.5f  %.2f sems  (%.1f%% rel)"
              % (M, d, h[0], h[1], abs(h[0] - d) / h[1], 100 * abs(h[0] - d) / d))

    control = dict(design="pure split Ne=%d t=%d, A = 2F/(1-F/2), F = 1-(1-1/(2Ne))^t" % (SPLIT_N, SPLIT_T),
                   lean=ctrl_pred, truth=ctrl_a[0], sem=ctrl_a[1])

    forms = [
        ("expectedSqMeanPGSDiff_IMEquilibrium [body: A = 2*delta]",
         lambda M: 2.0 / (2 * M + 1)),
        ("[derived] A = 2*delta/(1 - delta/2)",
         lambda M: (2.0 / (2 * M + 1)) / (1.0 - 1.0 / (2.0 * (2 * M + 1)))),
        ("[competing] A = delta, the pairwise-is-per-branch reading",
         lambda M: 1.0 / (2 * M + 1)),
    ]

    import verdict
    results = []
    for (name, fn) in forms:
        cells = [dict(design="M=%.1f (Ne=%d)" % (M, N), lean=float(fn(M)),
                      truth=a[0], sem=a[1]) for (M, N, a, h, e, l) in rows]
        v, note, worst = verdict.classify(cells, control=control,
                                          sem_source="replicates", rel_floor=0.03)
        regime = ("two-deme Wright-Fisher island model at migration-drift balance, Ne=250, "
                  "4*Ne*m swept 20-fold, %d unlinked loci, 4*Ne*mu = %.2f, %d generations "
                  "past a %d-generation burn-in, %d independent replicates, sem across "
                  "replicates. The observable is A = E[dp^2]/E[pbar(1-pbar)] as a ratio of "
                  "averages -- the argument Var_Delta_Mu's validated reading takes -- so no "
                  "V_A convention enters."
                  % (L_LOCI, THETA, GENS - BURN, BURN, REPS))
        verdict.report(name, "A against the closed form", cells, v, note, worst, regime=regime)
        preds = [c["lean"] for c in cells]
        results.append(dict(name=name, file="PortabilityDrift.lean", verdict=v, note=note,
                            regime=regime, cells=cells, worst=worst, guard=GUARD,
                            argument_source="model", sem_source="replicates",
                            oracle_independent=True,
                            span=(max(preds) - min(preds)) / max(abs(max(preds)), 1e-12)))

    results.append(dict(name="[controls]", guard=GUARD,
                        pure_split=dict(predicted=ctrl_pred, measured=ctrl_a[0], sem=ctrl_a[1]),
                        hudson_vs_closed=[dict(M=M, closed=1.0 / (2 * M + 1),
                                               measured=h[0], sem=h[1]) for (M, N, a, h, e, l) in rows]))
    json.dump(results, open("battery_pd3_results.json", "w"), indent=1)
    print("\nFRESHNESS_GUARD=%s DONE" % GUARD)


if __name__ == "__main__":
    main()
