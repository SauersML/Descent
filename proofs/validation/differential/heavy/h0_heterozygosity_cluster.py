#!/usr/bin/env python3
"""HEAVY 0 -- the heterozygosity cluster. HIGHEST YIELD. BARE NUMPY ONLY.

Runs on numpy alone (>=1.17 for default_rng). No scipy, no msprime, no SLiM.

WHAT THIS DECIDES
-----------------
The corpus's worst defect cluster, now precisely localized. These definitions
are all exact functions of the single number (1 - 1/(2 Ne))^t:

    Calibrator.hetRecurrence                  PopulationGeneticsFoundations.lean:1186   ROOT
    Calibrator.fstDerived                     PopulationGeneticsFoundations.lean:1212
    Calibrator.heterozygosityLossFromDrift    PopulationGeneticsFoundations.lean:454
    Calibrator.wrightFisherDriftRetention     PortabilityDrift.lean:710
    Calibrator.wrightFisherHeterozygosityLoss PortabilityDrift.lean:730
    Calibrator.cumulativeDrift                DemographicHistory.lean:506    (vector form)
    Calibrator.fstVariableNe                  DemographicHistory.lean:510    (vector form)
    Calibrator.targetHetFromFst               PortabilityDrift.lean:653      (consumer)

The extraction layer already localized the fault precisely: the mutation-drift
map is FINE -- hetMutationDriftRecurrence(Ne=1000, mu=1e-4, H0=0, t=20000)
= 0.28571405 against hetEquilibrium = 0.28571429, seven figures. The fault is
in `hetRecurrence`, which carries NO mutation term and decays to zero, and in
everything routing through it.

None of these is algebraically wrong. Every one follows correctly from the
premise of a CLOSED POPULATION WITH NO MUTATION. This run measures whether that
premise holds for the population they are cited about.

WHAT TO SIMULATE
    Infinite-alleles Wright-Fisher, diploid size Ne, per-generation per-copy
    mutation rate mu, every mutation a brand-new allele. Exact, not diffusion.

WHAT TO MEASURE
    Heterozygosity H(t) = 1 - sum_i p_i^2 over allele labels, and the RETENTION
    RATIO H(t)/H(0), which is scale-free and is what the definitions predict.

WHAT THE DEFINITIONS PREDICT
    retention = (1 - 1/(2 Ne))^t, i.e. 0.9048 / 0.6065 / 0.1353 at
    t = 200 / 1000 / 4000 with Ne = 1000. Those three numbers are quoted in the
    Lean docstring as its VALIDATED evidence. They contain no mutation term, so
    they are invariant in mu.

WHAT THEORY PREDICTS
    Started AT mutation-drift equilibrium, retention is 1.0 at every t, for
    every mu > 0. Mutation replenishes exactly what drift removes; that is what
    equilibrium means.

    Separation at t = 4000: 0.135 versus 1.000, a factor of 7.4.

=============================================================================
THE TWO THEORY-PINNED CONTROLS  (mandatory; both fixed by theorems, not by
                                 simulation, so a broken run cannot masquerade
                                 as a refutation)
=============================================================================
CONTROL 1 -- MUTATION OFF.  Set mu = 0 and the SAME simulator must reproduce
    (1 - 1/(2 Ne))^t to within Monte Carlo error at every checkpoint. This
    value is pinned by a theorem (`hetRecurrence_closed_form`), not fitted.
    It is the corpus's own claim, and under its own premise it is CORRECT.
    If control 1 fails, the simulator is broken and NOTHING else in this run
    may be reported. This is the control that distinguishes "my simulation is
    wrong" from "the claim is wrong".

CONTROL 2 -- EQUILIBRIUM LEVEL.  With mu > 0, the stationary heterozygosity
    must equal theta/(1+theta), theta = 4*Ne*mu, to within Monte Carlo error
    (Kimura & Crow 1964; it is also `Calibrator.hetEquilibrium`, and the
    extraction layer already confirmed the corpus's own recurrence converges to
    it to seven figures). Pinned by theory. If control 2 fails, the burn-in was
    too short and the "equilibrium" start is not one, which would make the test
    ratio meaningless in the direction that FAVOURS the definitions.

Only if BOTH controls pass may the test result be read.

=============================================================================
CAN-FAIL CLAUSE  (what the design must contain so a wrong answer shows up)
=============================================================================
1.  t MUST reach order 2*Ne.  Both hypotheses give retention ~ 1 - t/(2Ne) for
    t << Ne, so at short times they agree to under 1% and the test cannot
    discriminate. The t = 4000 row at Ne = 1000 (t = 2*Ne*2) is the decisive
    one; t = 200 is included precisely to show the region where the test has
    NO power, so nobody later mistakes agreement there for confirmation.

2.  mu MUST be varied at fixed Ne and t, over at least two orders of
    magnitude. The definitions have no mu argument, so their prediction is a
    horizontal line in mu. Any measured mu-dependence falsifies them outright
    and no fitted constant can absorb it. A single-mu grid could always be
    rescued by claiming the wrong mu was chosen.

3.  The mu = 0 control MUST be run with the identical code path, not a
    separate branch. A control that shares no machinery with the test controls
    nothing.

4.  RETENTION RATIOS, not raw H.  Raw H depends on theta and would let a
    disagreement be explained away as a calibration of mu. The ratio is
    dimensionless and both hypotheses make sharp, different predictions for it.

WHAT WOULD MAKE THIS TEST WRONG RATHER THAN THE DEFINITIONS
    If control 1 fails -> simulator bug, report nothing else.
    If control 2 fails -> burn-in too short, extend and rerun.
    If the measured retention at mu > 0 came out near 0.135, the definitions
    would be VINDICATED and the corpus's model premise correct. That is a real
    possible outcome of this design, which is what makes it a test.

EXPECTED RUNTIME
    ~8 min on 1 core; trivially parallel over the 8 cells. 200 replicates x
    4000 generations x 2000 gene copies, vectorised over replicates.
    Memory < 100 MB.

DEPENDENCIES
    numpy only.  Verified against the numpy 1.19 API surface (default_rng,
    integers, random) -- no scipy, no rng.multinomial on 2-D, nothing exotic.
"""

import json
import sys

import numpy as np

NE = 1000            # diploid; 2*NE gene copies
CHECKPOINTS = [0, 200, 1000, 4000]
REPS = 200
BURNIN_MULT = 10     # burn-in generations = BURNIN_MULT * 2 * NE

# mu = 0 is CONTROL 1. The rest are the test, spanning three orders of
# magnitude at fixed Ne and t (can-fail clause 2).
MUS = [0.0, 1e-6, 1e-5, 1e-4]


def heterozygosity(pop):
    """H = 1 - sum_i p_i^2 per replicate, over integer allele labels."""
    out = np.empty(pop.shape[0])
    for r in range(pop.shape[0]):
        _, counts = np.unique(pop[r], return_counts=True)
        p = counts / pop.shape[1]
        out[r] = 1.0 - np.sum(p * p)
    return out


def evolve(pop, mu, gens, rng, next_label):
    """Wright-Fisher resampling + infinite-alleles mutation, in place."""
    reps, n = pop.shape
    rows = np.arange(reps)[:, None]
    for _ in range(gens):
        idx = rng.integers(0, n, size=(reps, n))
        pop = pop[rows, idx]
        if mu > 0.0:
            hit = rng.random((reps, n)) < mu
            k = int(hit.sum())
            if k:
                pop[hit] = np.arange(next_label, next_label + k)
                next_label += k
    return pop, next_label


def main():
    rng = np.random.default_rng(20260802)
    n = 2 * NE
    results = []

    for mu in MUS:
        # Start every copy distinct so H(0) is maximal, then burn in. With
        # mu = 0 the burn-in is skipped: a closed no-mutation population has no
        # stationary state to reach, and burning it in would drive H to 0 and
        # destroy the control.
        pop = np.arange(n, dtype=np.int64)[None, :].repeat(REPS, axis=0)
        next_label = n

        if mu > 0.0:
            pop, next_label = evolve(pop, mu, BURNIN_MULT * 2 * NE, rng, next_label)

        h0 = heterozygosity(pop)
        theta = 4.0 * NE * mu
        row = {
            "mu": mu,
            "theta": theta,
            "H0_measured": float(h0.mean()),
            "H0_sem": float(h0.std() / np.sqrt(REPS)),
            # CONTROL 2: pinned by Kimura & Crow, not fitted.
            "H_equilibrium_theory": (theta / (1.0 + theta)) if mu > 0 else None,
            "role": "CONTROL 1 (mu=0)" if mu == 0.0 else "test",
            "checkpoints": [],
        }

        cur = pop
        prev_t = 0
        for t in CHECKPOINTS:
            if t > prev_t:
                cur, next_label = evolve(cur, mu, t - prev_t, rng, next_label)
                prev_t = t
            h = heterozygosity(cur)
            ratio = h / np.where(h0 == 0, np.nan, h0)
            row["checkpoints"].append({
                "t": t,
                "retention_measured": float(np.nanmean(ratio)),
                "retention_sem": float(np.nanstd(ratio) / np.sqrt(REPS)),
                # What the cluster predicts. No mu term: identical across rows.
                "retention_predicted_by_cluster": float((1.0 - 1.0 / (2.0 * NE)) ** t),
                # What equilibrium theory predicts for mu > 0.
                "retention_predicted_by_theory": None if mu == 0.0 else 1.0,
            })
        results.append(row)
        print(json.dumps(row), flush=True)

    # ---- verdicts -------------------------------------------------------
    ctrl1 = next(r for r in results if r["mu"] == 0.0)
    c1_ok = all(
        abs(c["retention_measured"] - c["retention_predicted_by_cluster"])
        < 4 * max(c["retention_sem"], 1e-6)
        for c in ctrl1["checkpoints"]
    )
    c2 = [
        (r["mu"], r["H0_measured"], r["H_equilibrium_theory"],
         abs(r["H0_measured"] - r["H_equilibrium_theory"])
         < 4 * max(r["H0_sem"], 1e-6))
        for r in results if r["mu"] > 0
    ]
    c2_ok = all(x[3] for x in c2)

    summary = {
        "control_1_mutation_off_reproduces_closed_form": c1_ok,
        "control_2_equilibrium_level_matches_theory": c2_ok,
        "controls_pinned_by": [
            "hetRecurrence_closed_form (theorem)",
            "Kimura & Crow 1964 theta/(1+theta) == Calibrator.hetEquilibrium",
        ],
        "control_2_detail": [
            {"mu": m, "H_measured": h, "H_theory": th, "ok": ok}
            for m, h, th, ok in c2
        ],
        "READ_THE_TEST": c1_ok and c2_ok,
        "note": (
            "If either control is False the test rows are uninterpretable and "
            "must NOT be reported as a falsification of anything."
        ),
    }
    if c1_ok and c2_ok:
        summary["test"] = [
            {
                "mu": r["mu"],
                "t": c["t"],
                "retention_measured": c["retention_measured"],
                "cluster_predicts": c["retention_predicted_by_cluster"],
                "theory_predicts": c["retention_predicted_by_theory"],
            }
            for r in results if r["mu"] > 0
            for c in r["checkpoints"] if c["t"] == max(CHECKPOINTS)
        ]
    print(json.dumps({"summary": summary}, indent=1))
    json.dump({"cells": results, "summary": summary},
              open("h0_results.json", "w"), indent=1)
    return 0 if (c1_ok and c2_ok) else 1


if __name__ == "__main__":
    sys.exit(main())
