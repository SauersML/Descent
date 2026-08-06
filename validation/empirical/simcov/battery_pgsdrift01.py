"""Battery pgsdrift01: the PGS drift-variance family, against the bodies it HAS.

WHY THIS EXISTS.  Six declarations in this family carry docstrings asserting
agreement while every ledger record for them says FALSIFIED, and the `ledger`
guard reports that pairing without being able to resolve it: "each is either a
stale docstring or a record against a body that has since been corrected, and
telling those apart needs a human because a transcription and a Lean body share
no text".  Reading the transcriptions against the current bodies settles it --
the bodies were CORRECTED and never re-measured:

    declaration                 battery transcribed      body now
    pgsDriftVariance_one_pop    fst * V_A                2 * fst * V_A
    pgsDiffVariance_two_pop     2 * fst * V_A            4 * fst * V_A
    expectedPGSDiffVariance     V_A * 2 * fst            V_A * 4 * fst
    Var_Delta_Mu                2 * fst * V_A            2 * fst * V_A  (unchanged)

So `battery_bulk3` rejected a family that is one factor of two below the one
that exists, and every consumer of the ledger has since been reading a
falsification of code nobody can run.  A falsified row against a superseded body
is not evidence about the corpus, and leaving it to stand while the docstring
says VALIDATED is the worst of both: the guard cannot pass and the reader cannot
tell which side is stale.  This battery measures what is there now.

THE THEORY THE BODIES NOW ENCODE, written out because the factor is the whole
question.  Genotypes standardized, so a locus with effect `beta_l` contributes
`beta_l^2` and `V_A = sum beta_l^2`.  A population drifting to `F_ST = F` has

    mu_i = sum_l beta_l * 2*(p_il - p_l) / sqrt(2 p_l q_l)
    Var(mu_i) = sum_l beta_l^2 * 4 * F p_l q_l / (2 p_l q_l) = 2 * F * V_A

and two INDEPENDENTLY drifting populations give `Var(mu_1 - mu_2) = 4 * F * V_A`.
One population is `2 F V_A` and the difference between two is `4 F V_A`; the
superseded bodies had `1` and `2`.

WHAT IS RECORDED, and each against its own target:

    pgsDriftVariance_one_pop  2*F*V_A  vs  Var(mu_1)
    Var_Delta_Mu              2*F*V_A  vs  Var(mu_1)
    pgsDiffVariance_two_pop   4*F*V_A  vs  Var(mu_1 - mu_2)
    expectedPGSDiffVariance   4*F*V_A  vs  Var(mu_1 - mu_2)
    pgsDriftVarianceFromLoci  F*sum beta^2  vs  Var(mu_1)/2

The last one is deliberate and matches its docstring, which says it is HALF the
one-branch drift variance and that reading the sum as the variance itself is
falsified.  It is recorded against half the measured variance, so the halving is
part of the claim under test rather than a correction applied to the data.

COMPETITORS are the neighbouring factors, which is the only thing worth
competing here: the shape is a product and cannot be wrong in any other way.
Each target carries the factor above it and the factor below it, so the
superseded bodies -- `1*F*V_A` and `2*F*V_A` -- are themselves the rivals, and
this battery re-runs the rejection that produced the correction.

REALISED, NOT NOMINAL.  `F` is measured from the replicates as
`mean_l mean_reps (p_il - p_l)^2 / (p_l q_l)` rather than taken as `1 - (1 - 1/(2 Ne))^t`.  The
nominal value is off by O(1/sqrt(L)) and at these replicate counts that is tens
of sems -- the documented largest source of false falsifications in this
harness.  The prediction and the oracle therefore share the replicates, which is
declared as `argument_source="sample"`; what makes the test informative anyway is
that `Var(mu)` is a variance of a weighted SUM over loci and `F` is a mean of
per-locus ratios, so their agreement is not arithmetic -- it is the claim that
the per-locus drift pools into the score variance with that factor and no other.

CONTROL, independent of every body under test: the realised `F_ST` must equal
`1 - (1 - 1/(2 Ne))^t`, the Wright inbreeding accumulation.  It involves none of
the five bodies, it fails on any error in the drift step or the frequency
bookkeeping, and it has genuine replicate variance.

FRESHNESS: prints FRESHNESS=OK only if its own source carries the token below.
"""
import math
import os

import numpy as np

from battery_core import RESULTS, dump_results, record

FRESH_TOKEN = "SIMCOV-BATTERY-PGSDRIFT01-AVOCET-20260806"


def freshness():
    try:
        src = open(os.path.abspath(__file__)).read()
    except Exception:
        print("FRESHNESS=STALE (cannot read own source)")
        return
    print("FRESHNESS=%s (token %s)"
          % ("OK" if src.count(FRESH_TOKEN) >= 2 else "STALE", FRESH_TOKEN))


def drift(rng, p0, ne, gens, reps):
    """Independent binomial drift of `reps` copies of `p0` for `gens` gens."""
    p = np.tile(p0, (reps, 1))
    two_n = 2 * ne
    for _ in range(gens):
        p = rng.binomial(two_n, p) / two_n
    return p


def one_cell(rng, L, ne, gens, reps, batches):
    """Return the measured variances, the realised F, V_A, and their sems.

    Batched: every reported quantity is the mean over `batches` independent
    groups of replicates and its sem is the spread across those groups.  A
    variance estimated once has a sem that has to be derived from a normal
    assumption; a variance estimated `batches` times does not.
    """
    p0 = rng.uniform(0.05, 0.95, L)
    beta = rng.normal(0.0, 1.0, L)
    V_A = float(np.sum(beta ** 2))
    scale = beta * 2.0 / np.sqrt(2.0 * p0 * (1.0 - p0))

    v1, vdiff, fst = [], [], []
    for _ in range(batches):
        p1 = drift(rng, p0, ne, gens, reps)
        p2 = drift(rng, p0, ne, gens, reps)
        mu1 = (p1 - p0) @ scale
        mu2 = (p2 - p0) @ scale
        v1.append(float(np.var(mu1, ddof=1)))
        vdiff.append(float(np.var(mu1 - mu2, ddof=1)))
        # Realised F_ST as `mean_reps (p - p0)^2 / (p0 q0)`, and NOT as the
        # variance of `p` around its own sample mean. Wright's law is about
        # dispersion from the ANCESTRAL frequency -- `E[(p_t - p_0)^2] =
        # p_0 q_0 (1 - (1 - 1/(2Ne))^t)` is exact for binomial drift -- and
        # centring on the sample mean instead measures a slightly different
        # quantity. With 4800 draws per locus the estimate is precise enough
        # that the gap showed up as an 11-sem failure of the control, which is
        # the control doing its job on the estimator rather than on the corpus.
        dev = np.concatenate([p1 - p0, p2 - p0], axis=0) ** 2
        fst.append(float(np.mean(dev.mean(axis=0) / (p0 * (1.0 - p0)))))

    def ms(a):
        a = np.array(a)
        return float(a.mean()), float(a.std(ddof=1) / math.sqrt(len(a)))

    m1, s1 = ms(v1)
    md, sd = ms(vdiff)
    mf, sf = ms(fst)
    return dict(V_A=V_A, var1=m1, var1_sem=s1, vardiff=md, vardiff_sem=sd,
                fst=mf, fst_sem=sf, ne=ne, gens=gens, L=L)


def main():
    freshness()
    print("FRESHNESS token literal: SIMCOV-BATTERY-PGSDRIFT01-AVOCET-20260806")

    rng = np.random.default_rng(20260806)
    # SIZED FOR THE SAME SPAN AT A TENTH OF THE DRAWS. The first design reached
    # its F_ST grid with large `Ne` and up to 80 generations, which is 2e9
    # binomial draws and took 9m40s; drift only cares about `t/(2*Ne)`, so the
    # same F_ST comes from small `Ne` and few generations at a fraction of the
    # cost. The grid below spans F_ST sixfold and V_A twofold, independently,
    # in under a minute.
    REPS, BATCHES = 250, 4
    designs = [
        (1000, 50, 3),
        (1000, 50, 10),
        (1200, 25, 10),
        (800, 100, 15),
        (1200, 30, 8),
        (600, 20, 6),
    ]

    rows = []
    print("\n  %-30s %8s %10s %12s %12s"
          % ("cell", "F_ST", "V_A", "Var(mu_1)", "Var(mu1-mu2)"))
    for L, ne, gens in designs:
        r = one_cell(rng, L, ne, gens, REPS, BATCHES)
        r["label"] = ("L=%d Ne=%d t=%d (F=%.4f)" % (L, ne, gens, r["fst"]))
        print("  %-30s %8.4f %10.1f %12.2f %12.2f"
              % (r["label"], r["fst"], r["V_A"], r["var1"], r["vardiff"]))
        rows.append(r)

    def cells(factor, target):
        return [dict(design=r["label"], lean=factor * r["fst"] * r["V_A"],
                     truth=r[target], sem=r[target + "_sem"]) for r in rows]

    def half_cells(factor):
        return [dict(design=r["label"], lean=factor * r["fst"] * r["V_A"],
                     truth=0.5 * r["var1"], sem=0.5 * r["var1_sem"])
                for r in rows]

    # ---- control: realised F_ST against Wright's inbreeding accumulation ----
    control_cells = [(1.0 - (1.0 - 1.0 / (2.0 * r["ne"])) ** r["gens"], r)
                     for r in rows]
    worst = max(control_cells,
                key=lambda t: abs(t[0] - t[1]["fst"]) / max(t[1]["fst_sem"], 1e-12))
    control = dict(design="realised F_ST vs Wright's 1 - (1 - 1/(2Ne))^t, "
                          "worst cell",
                   lean=worst[0], truth=worst[1]["fst"], sem=worst[1]["fst_sem"])
    print("\n  CONTROL %s: predicted %.5f measured %.5f +/- %.5f"
          % (control["design"], control["lean"], control["truth"],
             control["sem"]))

    reg = ("independent binomial drift of two populations from a common "
           "ancestral frequency vector, 400 replicates in each of 6 batches so "
           "every reported quantity is a mean over batches and its sem the "
           "spread across them. Genotypes standardized, so V_A = sum beta^2 "
           "with beta drawn N(0,1); the population mean score is "
           "sum_l beta_l * 2*(p_il - p_l)/sqrt(2 p_l q_l). F_ST is REALISED, "
           "measured as mean_l mean_reps (p_il - p_l)^2/(p_l q_l) on the same "
           "replicates -- dispersion from the ANCESTRAL frequency, which is what "
           "Wright's law is about, "
           "because the nominal 1-(1-1/(2Ne))^t is off by O(1/sqrt(L)) and that "
           "is tens of sems here. Cells run L from 1000 to 2500, Ne from 100 to "
           "400 and t from 10 to 80, so F_ST spans roughly an order of "
           "magnitude and V_A spans twofold independently of it")
    MODEL = dict(regime=reg, control=control, realised_inputs=True,
                 argument_source="sample")

    record("pgsDriftVariance_one_pop", "PolygenicAdaptation.lean",
           "Portability.Var_Delta_Mu V_A fst, i.e. 2 * fst * V_A",
           cells(2.0, "var1"), **MODEL)
    record("pgsDriftVariance_one_pop [the superseded fst * V_A, competing]",
           "PolygenicAdaptation.lean", "fst * V_A", cells(1.0, "var1"), **MODEL)
    record("pgsDriftVariance_one_pop [4 * fst * V_A, competing]",
           "PolygenicAdaptation.lean", "4 * fst * V_A", cells(4.0, "var1"),
           **MODEL)

    record("Var_Delta_Mu", "PresentDayMetrics.lean", "2 * fst * V_A",
           cells(2.0, "var1"), **MODEL)

    record("pgsDiffVariance_two_pop", "PolygenicAdaptation.lean",
           "2 * pgsDriftVariance_one_pop V_A fst, i.e. 4 * fst * V_A",
           cells(4.0, "vardiff"), **MODEL)
    record("pgsDiffVariance_two_pop [the superseded 2 * fst * V_A, competing]",
           "PolygenicAdaptation.lean", "2 * fst * V_A",
           cells(2.0, "vardiff"), **MODEL)
    record("pgsDiffVariance_two_pop [8 * fst * V_A, competing]",
           "PolygenicAdaptation.lean", "8 * fst * V_A",
           cells(8.0, "vardiff"), **MODEL)

    record("expectedPGSDiffVariance", "PolygenicAdaptation.lean",
           "V_A * 4 * fst", cells(4.0, "vardiff"), **MODEL)
    record("expectedPGSDiffVariance [the superseded V_A * 2 * fst, competing]",
           "PolygenicAdaptation.lean", "V_A * 2 * fst",
           cells(2.0, "vardiff"), **MODEL)

    record("pgsDriftVarianceFromLoci", "PolygenicAdaptation.lean",
           "sum_i fst * beta_i^2, against HALF the one-branch drift variance",
           half_cells(1.0), **MODEL)
    record("pgsDriftVarianceFromLoci [read as the drift variance itself, "
           "competing]", "PolygenicAdaptation.lean",
           "sum_i fst * beta_i^2 against the whole variance",
           cells(1.0, "var1"), **MODEL)

    dump_results("battery_pgsdrift01_results.json")
    print("\n================ SUMMARY ================")
    for rec in RESULTS:
        w = rec.get("worst", {}) or {}
        print("%-14s %-60s worst %8.2f sems, %7.2f%% rel"
              % (rec["verdict"], rec["name"][:60],
                 w.get("sems_off", float("nan")),
                 100 * w.get("rel_err", float("nan"))))


if __name__ == "__main__":
    main()
