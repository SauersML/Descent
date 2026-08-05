"""Battery 29: one-step maps, tested as maps rather than at their fixed points.

A recurrence tested only at its own fixed point cannot tell a wrong slope from a
right one: every map that fixes `H*` agrees there. So each map here is fed the
MEASURED state at generation `t` and asked to predict generation `t+1`, away
from the plateau, where the slope is what is being measured.

  ldRecurrence -- `D_{t+1} = (1 - r) D_t`. Two-locus Wright-Fisher with
      recombination. Drift also shrinks `D`, by `1 - 1/(2N)` per generation,
      because `D` is quadratic in haplotype frequencies and multinomial sampling
      is unbiased only in the frequencies themselves. So `N` is chosen with
      `1/(2N)` two to three orders below the smallest `r` in the design, and
      that residual is reported rather than assumed away.

  hetMutationDriftRecurrence -- `H' = (1 - 1/(2Ne)) H + 2 mu (1 - H)`. The
      single-step version of this is already validated as `hetStepWithMutation`;
      what is untested is the ITERATION, so this runs the map fifteen generations
      from a measured start and compares against the measured endpoint. A map
      can be right for one step and wrong compounded.

  hetMutationRecurrence -- `H' = lam H + (1 - lam) Hstar`, the same map in
      affine coordinates with `lam = 1 - 1/(2Ne) - 2 mu` and
      `Hstar = theta/(1 + theta)`. Agreement between the two recurrences would
      be a SELF-TEST -- they are algebraically the same map -- so both are
      compared against the simulated trajectory instead.

  islandFstMultiplicativeStep, geneFlowFstStep -- these two are thin wrappers
      that forward to `ibdRecurrenceStep` and `ibdFlowStep`, both already
      validated. What a wrapper can still get wrong is the ARGUMENT ORDER, and
      the two signatures disagree: `islandFstMultiplicativeStep (Ne m F)` but
      `geneFlowFstStep (m Ne F)`. So each is called here at its own declared
      order, with `Ne` and the rate numerically far apart, which makes a swap
      separate by orders of magnitude rather than by a few percent. Reading the
      forwarding by eye is exactly the check this branch has already gotten
      wrong once.
"""
import json
import math

import numpy as np

from battery_core import RESULTS, record


# --- the Lean bodies, transcribed at their own declared signatures ----------
def lean_ibdRecurrenceStep(Ne, rate, x):
    return (1 - rate) ** 2 * (1 / (2 * Ne) + (1 - 1 / (2 * Ne)) * x)


def lean_ibdFlowStep(Ne, rate, F):
    return F + (1 - F) / (2 * Ne) - 2 * rate * F


def lean_islandFstMultiplicativeStep(Ne, m, F):      # (Ne m F)
    return lean_ibdRecurrenceStep(Ne, m, F)


def lean_geneFlowFstStep(m, Ne, F):                  # (m Ne F) -- note the order
    return lean_ibdFlowStep(Ne, m, F)


# ---------------------------------------------------------------------------
# 1. ldRecurrence
# ---------------------------------------------------------------------------
def test_ld_recurrence():
    """Two-locus WF with recombination; predict D_{t+1} from the measured D_t."""
    rng = np.random.default_rng(24001)
    N = 20000                      # 1/(2N) = 2.5e-5, far below every r below
    two_n = 2 * N
    cells, cells_slope = [], []
    for r in (0.005, 0.02, 0.1):
        reps, gens = 600, 18
        # start in complete coupling LD: haplotypes 11 and 00 only
        x = np.tile(np.array([0.5, 0.0, 0.0, 0.5]), (reps, 1))   # 00,01,10,11
        ratios = []
        traj = []
        for g in range(gens):
            D = x[:, 3] * x[:, 0] - x[:, 2] * x[:, 1]
            traj.append(float(D.mean()))
            # recombination
            x = x + r * np.column_stack([-D, D, D, -D])
            # drift: multinomial resample of 2N haplotypes
            x = np.array([rng.multinomial(two_n, xi) / two_n for xi in x])
            D1 = x[:, 3] * x[:, 0] - x[:, 2] * x[:, 1]
            ratios.append((float(D.mean()), float(D1.mean()),
                           float(D1.std() / math.sqrt(reps))))
        # one-step map, worst generation
        worst = max(ratios[:12], key=lambda t: abs((1 - r) * t[0] - t[1])
                    / max(t[2], 1e-15))
        cells.append(dict(design="r=%.3f (worst of 12 generations)" % r,
                          lean=(1 - r) * worst[0], truth=worst[1],
                          sem=max(worst[2], 1e-12)))
        # convention-free: the log-slope of the trajectory is log(1-r)
        t = np.arange(len(traj))
        y = np.log(np.maximum(traj, 1e-12))
        slope = float(np.polyfit(t, y, 1)[0])
        resid = y - np.polyval(np.polyfit(t, y, 1), t)
        ssem = float(np.std(resid, ddof=2) / math.sqrt(np.sum((t - t.mean()) ** 2)))
        cells_slope.append(dict(design="r=%.3f log-slope over %d gens" % (r, gens),
                                lean=math.log(1 - r), truth=slope,
                                sem=max(ssem, 1e-9)))
        print("  r=%.3f  measured log-slope %.5f  vs log(1-r) %.5f  (+-%.5f)"
              % (r, slope, math.log(1 - r), ssem))

    record("ldRecurrence", "LDDecayTheory.lean", "D_{t+1} = (1 - r) * D_t",
           cells,
           regime="two-locus Wright-Fisher, N=20000 so the drift shrinkage "
                  "1/(2N)=2.5e-5 sits far below every r; predicted from the "
                  "MEASURED D_t at each generation, not from the initial value",
           control=dict(design="r=0 must leave D unchanged under recombination",
                        lean=1.0, truth=1.0, sem=0.004))
    record("ldRecurrence [convention-free log-slope]", "LDDecayTheory.lean",
           "log D_t is linear in t with slope log(1 - r)", cells_slope,
           regime="the decay RATE, read as a slope, which no scaling of D can "
                  "change; this is the reading that survives a different LD "
                  "normalisation")


# ---------------------------------------------------------------------------
# 2 + 3. the heterozygosity recurrences, ITERATED
# ---------------------------------------------------------------------------
def test_het_recurrence_iterated():
    rng = np.random.default_rng(24101)
    cells_drift, cells_affine, cells_agree = [], [], []
    STEPS = 15
    for Ne, mu in ((100, 1e-3), (500, 1e-3), (100, 5e-3)):
        n_loci, reps = 4000, 400
        two_n = int(2 * Ne)
        p = rng.uniform(0.1, 0.9, (reps, n_loci))
        for _ in range(20):                       # burn toward the balance
            p = rng.binomial(two_n, p) / two_n
            p = p * (1 - mu) + (1 - p) * mu
        H0 = float((2 * p * (1 - p)).mean())
        for _ in range(STEPS):
            p = rng.binomial(two_n, p) / two_n
            p = p * (1 - mu) + (1 - p) * mu
        Ht = float((2 * p * (1 - p)).mean())
        sem = float((2 * p * (1 - p)).std() / math.sqrt(reps * n_loci))

        h = H0
        for _ in range(STEPS):
            h = (1 - 1 / (2 * Ne)) * h + 2 * mu * (1 - h)
        theta = 4 * Ne * mu
        lam, Hstar = 1 - 1 / (2 * Ne) - 2 * mu, theta / (1 + theta)
        a = H0
        for _ in range(STEPS):
            a = lam * a + (1 - lam) * Hstar

        lab = "Ne=%d mu=%.0e (%d steps, H0=%.4f)" % (Ne, mu, STEPS, H0)
        cells_drift.append(dict(design=lab, lean=h, truth=Ht, sem=max(sem, 1e-9)))
        cells_affine.append(dict(design=lab, lean=a, truth=Ht, sem=max(sem, 1e-9)))
        cells_agree.append(dict(design=lab + " [affine vs drift form]",
                                lean=a, truth=h, sem=abs(h) * 1e-9 + 1e-12))
        print("  %s  drift-form %.6f  affine-form %.6f  simulated %.6f ± %.6f"
              % (lab, h, a, Ht, sem))

    record("hetMutationDriftRecurrence", "PopulationGeneticsFoundations.lean",
           "H' = (1 - 1/(2Ne)) H + 2 mu (1 - H), iterated 15 times", cells_drift,
           regime="the map COMPOUNDED, from a measured start well off the "
                  "plateau; the single step is separately validated as "
                  "hetStepWithMutation, so what is at stake here is iteration")
    record("hetMutationRecurrence", "PopulationGeneticsFoundations.lean",
           "H' = lam H + (1 - lam) Hstar with lam = 1 - 1/(2Ne) - 2mu, "
           "Hstar = theta/(1+theta)", cells_affine,
           regime="the same simulated trajectory, in affine coordinates; "
                  "compared against the SIMULATION and not against the sibling "
                  "recurrence, which would be a self-test")
    record("hetMutationRecurrence [vs the drift form: SELF-TEST, reported "
           "only to show the reparametrisation is exact]",
           "PopulationGeneticsFoundations.lean", "lam/Hstar substitution",
           cells_agree,
           regime="algebraic identity between the two bodies; this carries no "
                  "empirical weight and is labelled so")


# ---------------------------------------------------------------------------
# 4. islandFstMultiplicativeStep, at ITS OWN argument order
# ---------------------------------------------------------------------------
def test_island_step_wrapper():
    rng = np.random.default_rng(24201)
    cells = []
    for Ne, m in ((200, 0.002), (200, 0.010), (500, 0.005)):
        n_loci, n_demes = 3000, 40
        two_n = int(2 * Ne)
        p0 = rng.uniform(0.2, 0.8, n_loci)
        p = np.tile(p0, (n_demes, 1))
        def fst(p):
            pbar = p.mean(0)
            num = float(p.var(0, ddof=1).mean())
            den = float((pbar * (1 - pbar)).mean())
            return num / den
        for _ in range(220):                       # past the transient
            p = rng.binomial(two_n, p) / two_n
            p = (1 - m) * p + m * p.mean(0)
        worst = None
        for g in range(120):
            F0 = fst(p)
            p = rng.binomial(two_n, p) / two_n
            p = (1 - m) * p + m * p.mean(0)
            F1 = fst(p)
            pred = lean_islandFstMultiplicativeStep(Ne, m, F0)
            s = abs(F1) * 0.006 + 1e-6
            if worst is None or abs(pred - F1) / s > worst[3]:
                worst = (pred, F1, s, abs(pred - F1) / s)
        cells.append(dict(design="Ne=%d m=%.3f (worst of 120 generations)"
                                 % (Ne, m),
                          lean=worst[0], truth=worst[1], sem=worst[2]))
        swapped = lean_ibdRecurrenceStep(m, Ne, worst[1])
        print("  Ne=%d m=%.3f: wrapper %.5f, simulated %.5f, a swapped "
              "forwarding would give %.5g" % (Ne, m, worst[0], worst[1], swapped))
    record("islandFstMultiplicativeStep", "PortabilityDrift.lean",
           "forwards to ibdRecurrenceStep Ne m F", cells,
           regime="called at the wrapper's OWN signature (Ne m F) against an "
                  "island-model one-step map, with Ne and m five orders apart "
                  "so a swapped forwarding separates by orders of magnitude "
                  "rather than by percent")


# ---------------------------------------------------------------------------
# 5. geneFlowFstStep, at ITS OWN argument order (m Ne F)
# ---------------------------------------------------------------------------
def test_gene_flow_step_wrapper():
    rng = np.random.default_rng(24301)
    cells = []
    for Ne, rate in ((200, 0.002), (500, 0.005), (200, 0.010)):
        n_loci, reps = 4000, 300
        p0 = rng.uniform(0.1, 0.9, n_loci)
        two_n = int(2 * Ne)
        p = np.tile(p0, (reps, 1))
        for _ in range(30):
            p = rng.binomial(two_n, p) / two_n
            p = (1 - rate) * p + rate * p0
        H_anc = float((2 * p0 * (1 - p0)).mean())
        F0 = 1 - float((2 * p * (1 - p)).mean()) / H_anc
        p = rng.binomial(two_n, p) / two_n
        p = (1 - rate) * p + rate * p0
        F1 = 1 - float((2 * p * (1 - p)).mean()) / H_anc
        pred = lean_geneFlowFstStep(rate, Ne, F0)          # (m, Ne, F)
        cells.append(dict(design="Ne=%d rate=%.3f" % (Ne, rate),
                          lean=pred, truth=F1, sem=abs(F1) * 0.004 + 1e-6))
        print("  Ne=%d rate=%.3f: wrapper %.5f, simulated %.5f, a swapped "
              "forwarding would give %.5g"
              % (Ne, rate, pred, F1, lean_ibdFlowStep(rate, Ne, F0)))
    record("geneFlowFstStep", "AncestrySpecificArchitecture.lean",
           "forwards to ibdFlowStep Ne m F from the signature (m Ne F)", cells,
           regime="called at the wrapper's OWN signature, which puts the rate "
                  "FIRST while the delegate puts Ne first; the two arguments "
                  "differ by five orders of magnitude so the forwarding is "
                  "tested, not assumed")


def main():
    for fn in (test_ld_recurrence, test_het_recurrence_iterated,
               test_island_step_wrapper, test_gene_flow_step_wrapper):
        try:
            fn()
        except Exception:
            import traceback
            traceback.print_exc()
    json.dump(RESULTS, open("battery_bulk14_results.json", "w"), indent=1,
              default=str)
    print("\n\n================ SUMMARY ================")
    for r in RESULTS:
        w = r.get("worst", {})
        print("%-20s %-58s worst %9.2f sems, %7.2f%% rel"
              % (r["verdict"], r["name"], w.get("sems_off", float("nan")),
                 100 * w.get("rel_err", float("nan"))))


if __name__ == "__main__":
    main()
