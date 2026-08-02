#!/usr/bin/env python3
"""Family simulators: SPLIT F_ST and ISLAND-MIGRATION F_ST.

Run with the popgen venv:
    /projects/standard/hsiehph/sauer354/popgenv/bin/python fam_coalescent.py

WHY BY FAMILY
    One simulator per model family covers many statements, because the shared
    modelling choice lives in the family rather than in any one definition. The
    island family alone has 8 definitions across 5 files that all compute
    1/(1 + 4 Ne m); none of them says it is the infinite-island limit.

METHOD -- match on what the definition reads, differ in the truth, measure
whether it notices. Each family fixes the parameters a definition takes,
varies something it does NOT take, and asks whether the measured quantity moves
while the prediction cannot.

FAMILY 1 -- SPLIT F_ST
    Covers coalFst, fstFromGenerations, fstFromTau, coalescentTau,
    hudsonFstFromCoalescenceTimes, pairwiseFstFromBranchTaus,
    pairwiseFstFromBranches.
    Simulate a clean split, measure branch-mode Hudson F_ST (no mutational
    noise; the mutation rate cancels in the ratio).
    THE DIFFERENCE THE DEFINITIONS CANNOT SEE: daughter population sizes.
    coalFst takes one Ne, so it predicts the same F_ST whether the daughters
    are equal or 16-fold apart. The simulator varies exactly that.
    CONTROL pinned by definition: t = 0 gives F_ST = 0 identically.

FAMILY 2 -- ISLAND MIGRATION F_ST
    Covers islandModelFst, asymmetricFst, fstMigDriftEquil,
    fstMigrationDriftEquilibrium, equilibriumFst, sharedLD_from_equilibrium,
    neutralAFBenchmarkFromRecurrence, fstDriftMigration.
    Simulate d demes at symmetric migration m, measure F_ST between two demes.
    THE DIFFERENCE THE DEFINITIONS CANNOT SEE: the NUMBER OF DEMES. Every one
    of the eight takes only (Ne, m), so all predict 1/(1+4 Ne m) at d = 2 and
    at d = 40 alike. The finite-deme theory says 1/(1 + 4 Ne m (d/(d-1))^2),
    which at d = 2 is four times more migration-scaled than at d = infinity.
    CONTROL pinned by theory: as m grows the demes panmict and F_ST -> 0.

WHY THIS DESIGN CAN FAIL
    If measured F_ST were flat in d, the infinite-island formula would be
    vindicated at every deme count and the CONDITIONALLY VALID annotations
    would be too weak rather than too strong. The d axis is the whole test; a
    single-d run cannot fail and would be a fitted constant.

SPEED
    Branch-mode statistics on short sequences: no mutations simulated, so a few
    megabases and a handful of replicates give tight estimates. Whole script is
    under two minutes. Replicates are deliberately small -- get signal first.
"""

import json
import sys

import msprime
import numpy as np

# Sized for SIGNAL FIRST. A first attempt at 2 Mb x 6 replicates x 12 island
# cells did not finish in two minutes, which is a design problem rather than a
# compute problem: branch-mode statistics carry no mutational noise, so
# precision comes from independent trees, and 200 kb at rho=1e-8 already gives
# thousands. Deep low-migration island trees over 40 demes were the real cost.
SEQ = 200_000
RHO = 1e-8
REPS = 3


def hudson_branch_fst(ts, sa, sb):
    dxy = ts.divergence([sa, sb], mode="branch")
    pa = ts.diversity(sa, mode="branch")
    pb = ts.diversity(sb, mode="branch")
    return 1.0 - 0.5 * (pa + pb) / dxy


# ---------------------------------------------------------------------------
def family_split():
    out = []
    NA = 1000
    cells = []
    for t in (0, 500, 2000, 8000):
        for (n1, n2, tag) in ((NA, NA, "equal"),
                              (NA // 4, 4 * NA, "16x apart")):
            cells.append((t, n1, n2, NA, tag))

    for (t, n1, n2, na, tag) in cells:
        vals = []
        for r in range(REPS):
            d = msprime.Demography()
            d.add_population(name="A", initial_size=n1)
            d.add_population(name="B", initial_size=n2)
            d.add_population(name="ANC", initial_size=na)
            if t > 0:
                d.add_population_split(time=t, derived=["A", "B"], ancestral="ANC")
            else:
                d.add_population_split(time=1e-9, derived=["A", "B"], ancestral="ANC")
            ts = msprime.sim_ancestry(
                samples={"A": 10, "B": 10}, demography=d,
                sequence_length=SEQ, recombination_rate=RHO, random_seed=100 + r)
            vals.append(hudson_branch_fst(
                ts, ts.samples(population=0), ts.samples(population=1)))
        m = float(np.mean(vals))
        s = float(np.std(vals) / np.sqrt(len(vals)))
        out.append({
            "t": t, "N1": n1, "N2": n2, "N_anc": na, "sizes": tag,
            "fst_measured": m, "fst_sem": s,
            # every definition in the family takes ONE Ne; this is what they say
            "coalFst_prediction": t / (t + 2.0 * na),
        })
        print("  t=%-5d %-10s N1=%-5d N2=%-5d  measured %.5f +-%.5f   coalFst %.5f"
              % (t, tag, n1, n2, m, s, t / (t + 2.0 * na)), flush=True)
    return out


# ---------------------------------------------------------------------------
def family_island():
    out = []
    NE = 500
    for m in (0.01, 0.002):
        for d in (2, 5, 20):
            vals = []
            for r in range(REPS):
                dem = msprime.Demography.island_model([NE] * d, migration_rate=m)
                ts = msprime.sim_ancestry(
                    samples={("pop_%d" % i): (10 if i < 2 else 0) for i in range(d)},
                    demography=dem, sequence_length=SEQ,
                    recombination_rate=RHO, random_seed=500 + r)
                vals.append(hudson_branch_fst(
                    ts, ts.samples(population=0), ts.samples(population=1)))
            mu_ = float(np.mean(vals))
            se = float(np.std(vals) / np.sqrt(len(vals)))
            inf_island = 1.0 / (1.0 + 4.0 * NE * m)
            finite = 1.0 / (1.0 + 4.0 * NE * m * (d / (d - 1.0)) ** 2)
            out.append({
                "Ne": NE, "m": m, "d": d,
                "fst_measured": mu_, "fst_sem": se,
                "islandModelFst_prediction": inf_island,
                "finite_deme_theory": finite,
                "rel_err_infinite_island": (inf_island - mu_) / mu_ if mu_ else None,
                "rel_err_finite_deme": (finite - mu_) / mu_ if mu_ else None,
            })
            print("  m=%-6g d=%-3d measured %.5f +-%.5f | 1/(1+4Nm) %.5f (%+.1f%%) "
                  "| finite-d %.5f (%+.1f%%)"
                  % (m, d, mu_, se, inf_island,
                     100 * (inf_island - mu_) / mu_ if mu_ else float("nan"),
                     finite, 100 * (finite - mu_) / mu_ if mu_ else float("nan")),
                  flush=True)
    return out


def main():
    res = {}
    print("FAMILY 1 -- SPLIT F_ST  (difference the definitions cannot see: "
          "daughter sizes)")
    res["split"] = family_split()

    zero = [r for r in res["split"] if r["t"] == 0]
    c1 = all(abs(r["fst_measured"]) < 5e-3 for r in zero)
    print("  CONTROL t=0 gives F_ST=0: %s (%s)"
          % ("PASS" if c1 else "FAIL",
             ", ".join("%.5f" % r["fst_measured"] for r in zero)))

    print("")
    print("FAMILY 2 -- ISLAND F_ST  (difference the definitions cannot see: "
          "number of demes)")
    res["island"] = family_island()

    hi = [r for r in res["island"] if r["m"] == 0.01 and r["d"] == 20]
    lo = [r for r in res["island"] if r["m"] == 0.002 and r["d"] == 20]
    c2 = bool(hi and lo and hi[0]["fst_measured"] < lo[0]["fst_measured"])
    print("  CONTROL F_ST decreases with migration: %s" % ("PASS" if c2 else "FAIL"))

    res["controls"] = {"split_t0_zero": bool(c1), "island_monotone_in_m": c2}
    res["READ_THE_TEST"] = bool(c1 and c2)
    fh = open("fam_coalescent_results.json", "w")
    json.dump(res, fh, indent=1)
    fh.close()
    print("")
    print("READ_THE_TEST: %s   -> fam_coalescent_results.json"
          % res["READ_THE_TEST"])
    return 0 if res["READ_THE_TEST"] else 1


if __name__ == "__main__":
    sys.exit(main())
