"""#36: the tag-side monomorphic law across an n-SWEEP, on an ascertained spectrum.

`battery_fix36` put the law on trial at ONE sample size, n = 200, from known
initial frequencies. This battery does two things that one could not.

FIRST, IT SWEEPS n = 20, 50, 100, 200 on the SAME trajectories. That matters
because the gap between this law and the population-fixation quantity IS the
n-dependence: a sample of n can be monomorphic while the population still
segregates, and how often depends on how many ancestral lineages the sample has.
At n = 200 the two are 0.1 to 1.0 sems apart and the distinction is unmeasurable;
at n = 20 it is 5 to 9 sems and the distinction is the measurement. Chasing that
separation with more SITES buys 1/sqrt(N) on the error bar; shrinking n moves the
EFFECT. The sweep is the cheap axis.

SECOND, IT DRAWS ITS FREQUENCIES FROM AN ASCERTAINED PANEL rather than from a
designed list, and carries an UNASCERTAINED arm beside it. Ascertainment enters
the law only through `p0`, so predicting both arms correctly is the law getting a
large effect right that it was never told about -- the two arms differ 6.3-fold in
median MAF here, and their monomorphic fractions differ by 0.42 at the shallowest
cell.

THE FOUR RIVALS, ALL ON THE SAME CELLS.

  POPULATION FIXATION -- the confusion actually present in the corpus, and the
  reason this body exists. `stillSegregatingProb` is a POPULATION quantity with no
  sample size in its signature and it has been pointed at as the tag-loss term
  twice in this program. Its prediction here needs no separate machinery: the
  rival's claim is exactly that the SAMPLE monomorphic fraction equals the
  POPULATION fixed fraction, and this run measures both on the same trajectories.
  So its `lean` is the realised population-fixed fraction and its `truth` is the
  realised sample-monomorphic fraction -- a rival stated in the currency of the
  confusion rather than in a reconstruction of it.

  BETA CLOSURE (Balding-Nichols matching the first two moments exactly) -- it has
  no atoms at 0 and 1, and the monomorphic probability IS the atom mass. Its
  verdict is n-DEPENDENT and the sweep is built to show that: it is
  indistinguishable from the law at n = 20 and refuted at n = 200. A competitor
  row whose verdict flips across the sweep is not an inconsistency here, it is the
  result.

  TAU/2 -- one wrong constant, reading Tavare's N as the diploid size.

  NO DRIFT -- the tau = 0 reading, `p0^n + (1-p0)^n`. Trivially refuted on the
  ascertained arm, where the MAF floor makes it ~0, and sharply refuted on the
  unascertained arm. Carried anyway rather than dropped: hiding the trivial half
  would flatter the comparison.

THE READABILITY RULE FOR THE POPULATION RIVAL IS DECLARED PER CELL AND FIXED IN
ADVANCE: a cell can speak to that distinction only where the predicted gap clears
2 prediction-side sems. Seven of the twenty-four cells qualify and seventeen do
not, and the seventeen are PRINTED with their gaps rather than dropped, so a null
there reads as a design property rather than as evidence.

THE LAW AND THE PMF MACHINERY ARE IMPORTED FROM `battery_fix36` rather than
retyped, so the two batteries cannot drift apart. That module's own self-check --
uniformization against an independently written ODE predictor -- runs there.

TEMPLATE CHECKS: `p0_panel` names the ascertainment the frequencies came from;
the estimand is the unweighted fraction of PANEL SITES whose SAMPLE of n is
monomorphic, stated in the regime; the denominator is the site count, unweighted;
each cell prints its floor beside its measurement; config travels in the regime;
and the two arms' site sets are drawn once and handed to every row.
"""
import math
import os

import numpy as np

from battery_core import dump_results, record, run_groups
from battery_fix36 import block_counting_pmf, p_mono, p_mono_beta

FRESH_TOKEN = "SIMCOV-BATTERY-FIX36B-NSWEEP-20260811"
LEAN_FILE = "Coalescent/Duality.lean"

NE_DIP = 1500.0
TWO_NE = int(2 * NE_DIP)
TIMES = (250, 750, 2000)
N_GRID = (20, 50, 100, 200)
N_HAP_T0 = 400
SEQ = 20e6
REC = 1.1e-8
MU = 1.1e-8
MAF = 0.05
N_CAUSAL = 300
N_SITES = 400
SEED = 360137


def freshness():
    return FRESH_TOKEN


def panels():
    """The two arms' initial frequencies, from one ascertainment. Deterministic."""
    import msprime
    ts = msprime.sim_ancestry(
        samples=N_HAP_T0 // 2, population_size=NE_DIP, sequence_length=SEQ,
        recombination_rate=REC, ploidy=2, random_seed=SEED)
    ts = msprime.sim_mutations(ts, rate=MU, random_seed=SEED + 11)
    hap = ts.genotype_matrix()
    # p0_panel: the t=0 PANEL frequency the ascertainment was defined on. Not a
    # population frequency, which is unobservable and is not what was ascertained.
    p0_panel = hap.mean(1)
    seg = np.flatnonzero((p0_panel > 0) & (p0_panel < 1))
    rng = np.random.default_rng(SEED + 77)
    maf0 = np.minimum(p0_panel, 1 - p0_panel)
    elig = seg[maf0[seg] >= MAF]
    causal = rng.choice(elig, size=N_CAUSAL, replace=False)
    beta = rng.standard_normal(N_CAUSAL)
    dos = hap.reshape(hap.shape[0], -1, 2).sum(2).astype(np.float64)
    gv = dos[causal].T @ beta
    gc = dos - dos.mean(1, keepdims=True)
    yc = gv - gv.mean()
    v = (gc ** 2).sum(1)
    b = np.zeros(dos.shape[0])
    ok = v > 0
    b[ok] = (gc[ok] @ yc) / v[ok]
    rank = np.zeros(dos.shape[0])
    rank[ok] = np.abs(b[ok]) * np.sqrt(v[ok] / dos.shape[1])
    asc = np.sort(elig[np.argsort(-rank[elig])][:N_SITES])
    unasc = np.sort(rng.choice(seg, size=N_SITES, replace=False))
    return p0_panel[asc], p0_panel[unasc]


def cell(design, lean, truth, sem):
    return dict(design=design, lean=float(lean), truth=float(truth),
                sem=float(max(sem, 1e-12)))


def group_sweep():
    print("\n== the monomorphic law across n = 20/50/100/200, two ascertainments")
    p_asc, p_unasc = panels()
    print("  ascertained   MAF median %.4f   unascertained MAF median %.4f"
          % (float(np.median(np.minimum(p_asc, 1 - p_asc))),
             float(np.median(np.minimum(p_unasc, 1 - p_unasc)))))
    rng = np.random.default_rng(SEED + 991)

    cells, c_pop, c_beta, c_half, c_nodrift, ctrl = [], [], [], [], [], []
    skipped = []
    print("  %-24s %9s %9s %9s %9s %8s"
          % ("cell", "law", "measured", "popfix", "gap/sem", "readable"))
    for arm, p0 in (("asc", p_asc), ("unasc", p_unasc)):
        for t in TIMES:
            tau = t / TWO_NE
            p = p0.astype(np.float64).copy()
            for _ in range(t):
                p = rng.binomial(TWO_NE, p) / TWO_NE
            # THE POPULATION quantity, measured on the same trajectories: the
            # fraction of sites actually fixed. This is the rival's currency.
            pop_fixed = float(np.mean((p <= 0.0) | (p >= 1.0)))
            for n in N_GRID:
                pmf = block_counting_pmf(n, tau)
                pred = float(np.mean(p_mono(p0, n, tau, pmf=pmf)))
                k = rng.binomial(n, p)
                meas = float(np.mean((k == 0) | (k == n)))
                sem = math.sqrt(max(pred * (1 - pred), 1e-12) / p0.size)
                lab = "%s t=%d n=%d" % (arm, t, n)
                gap = abs(pred - pop_fixed) / sem
                readable = gap > 2.0
                print("  %-24s %9.5f %9.5f %9.5f %9.2f %8s"
                      % (lab, pred, meas, pop_fixed, gap,
                         "yes" if readable else "NO"))
                cells.append(cell(lab, pred, meas, sem))
                c_beta.append(cell(lab, float(np.mean(
                    p_mono_beta(p0, n, 1.0 - math.exp(-tau)))), meas, sem))
                c_half.append(cell(lab, float(np.mean(
                    p_mono(p0, n, tau / 2.0))), meas, sem))
                c_nodrift.append(cell(lab, float(np.mean(
                    p0 ** n + (1.0 - p0) ** n)), meas, sem))
                if readable:
                    # THE PAIRED SEM, because the two events are NESTED: a fixed
                    # population makes every sample from it monomorphic, so the
                    # difference is a single count -- the sites monomorphic in
                    # the sample while the population still segregates -- and its
                    # variance is that of one proportion, not of a difference of
                    # two loose ones. The marginal sem used in the first version
                    # overstated the bar and understated the separation.
                    dd = meas - pop_fixed
                    sem_d = math.sqrt(max(dd * (1.0 - dd), 1e-12) / p0.size)
                    c_pop.append(cell(lab, pop_fixed, meas, sem_d))
                else:
                    skipped.append((lab, gap))
            # CONTROL, per arm and time: the mean frequency is a martingale under
            # neutral drift, so E[p_t] = mean(p0) whatever the sample size. It
            # involves no coalescent quantity and no sample at all, and it fails
            # if the drift step or the trajectory bookkeeping is wrong.
            ctrl.append(cell("mean frequency is a martingale, %s t=%d" % (arm, t),
                             float(np.mean(p0)), float(np.mean(p)),
                             float(np.std(p, ddof=1) / math.sqrt(p.size))))

    print("\n  CELLS THAT CANNOT SPEAK TO THE POPULATION DISTINCTION (gap < 2 sem),")
    print("  declared before the run and printed rather than dropped:")
    for lab, gap in skipped:
        print("    %-24s gap %.2f sem" % (lab, gap))

    reg = ("exact Wright-Fisher binomial drift on 2Ne=%d gene copies from an "
           "ASCERTAINED panel of %d sites per arm, drawn once by msprime at seed "
           "%d: the ascertained arm is MAF >= %.2f then top-ranked by |b|*sd, the "
           "unascertained arm is random segregating sites with no floor and no "
           "ranking. Samples of n = %s haplotypes drawn binomially (WITH "
           "replacement) from the same trajectories at t = %s. The estimand is the "
           "unweighted fraction of PANEL SITES whose sample of n is monomorphic -- "
           "a proportion over sites, not a per-site probability averaged and not a "
           "population fixation probability. Error bars are prediction-side, "
           "sqrt(sum P(1-P))/N_sites. The law and its pmf are imported from "
           "battery_fix36 rather than retyped"
           % (TWO_NE, N_SITES, SEED, MAF, N_GRID, TIMES))
    control = ctrl[len(ctrl) // 2]

    record("tagSampleMonomorphicProb", LEAN_FILE,
           "sum_k P(N_tau = k | n) * (p^k + (1-p)^k), swept over n",
           cells, regime=reg, control=control,
           realised_inputs=True, argument_source="model",
           note="twenty-four cells over four sample sizes and two ascertainments; "
                "the n-sweep both tests the n-dependence and extends the validated "
                "regime to n = 20, 50 and 100, which had no verdict before")
    record("tagSampleMonomorphicProb [POPULATION FIXATION used where sample "
           "monomorphism belongs, competing]", LEAN_FILE,
           "the realised fraction of sites FIXED IN THE POPULATION, which a "
           "sample-free quantity like stillSegregatingProb reports",
           c_pop, regime=reg, control=control,
           realised_inputs=True, argument_source="model",
           note="THE SIGN OF THIS ROW IS FORCED AND IS NOT A FINDING: a fixed "
                "population makes every sample drawn from it monomorphic, so the "
                "sample-monomorphic event CONTAINS the population-fixed one site "
                "by site and the difference is non-negative in every realisation. "
                "What the row measures is the MAGNITUDE of a gap already known to "
                "be positive, and the substantive claim under test is therefore "
                "ADEQUACY AS AN APPROXIMATION -- whether the population quantity "
                "can stand in for the sample one -- which is the confusion the "
                "corpus committed and is n-DEPENDENT: negligible at n = 200, not "
                "negligible at n = 20. The error bar is the PAIRED one, since the "
                "nesting makes the difference a single count. Recorded only on "
                "cells whose predicted gap clears 2 sems, the rest printed")
    record("tagSampleMonomorphicProb [beta closure matching the first two moments, "
           "competing]", LEAN_FILE, "Balding-Nichols E[X^n] + E[(1-X)^n]",
           c_beta, regime=reg, control=control,
           realised_inputs=True, argument_source="model",
           note="no atoms at 0 and 1, where the monomorphic probability lives. Its "
                "separation from the law is n-DEPENDENT: indistinguishable at "
                "n = 20 and refuted at n = 200, which is the sweep working rather "
                "than an inconsistency")
    record("tagSampleMonomorphicProb [tau/2 convention, competing]", LEAN_FILE,
           "the same law with tau = t/(4 Ne)",
           c_half, regime=reg, control=control,
           realised_inputs=True, argument_source="model",
           note="one wrong constant, reading Tavare's N as the diploid size")
    record("tagSampleMonomorphicProb [no drift, the tau = 0 reading, competing]",
           LEAN_FILE, "p0^n + (1-p0)^n",
           c_nodrift, regime=reg, control=control,
           realised_inputs=True, argument_source="model",
           note="trivially refuted on the ascertained arm, where the MAF floor "
                "makes it near zero, and sharply refuted on the unascertained one; "
                "carried rather than dropped because hiding the trivial half "
                "would flatter the comparison")


def main():
    print(freshness())
    failed = run_groups(group_sweep)
    here = os.path.dirname(os.path.abspath(__file__))
    sha = dump_results(os.path.join(here, "battery_fix36b_results.json"),
                       failed_groups=failed)
    print("\nbattery sha %s" % sha)


if __name__ == "__main__":
    main()
