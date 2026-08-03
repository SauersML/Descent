"""Tabulate check_defs.py output: Lean definition vs simulated ground truth.

    /projects/standard/hsiehph/sauer354/popgen_venv/bin/python report.py defs.json

That interpreter is the only working one on this cluster; check_defs.py's header
records why the three obvious alternatives are not.

READING THIS REPORT.  Agreement between a Lean formula and a simulation is only
evidence about the NAME if the simulation was written from the name.  CHECK 5
below is the one to read first: it reports the same definition against two
different ground truths on purpose, because agreeing with one of them is exactly
what a misnamed definition does.
"""
from __future__ import annotations

import json
import sys
from collections import defaultdict

import numpy as np


def agg(rows, keys, cols):
    g = defaultdict(list)
    for r in rows:
        g[tuple(r[k] for k in keys)].append(r)
    out = []
    for k in sorted(g):
        rec = dict(zip(keys, k))
        for c in cols:
            vals = [r[c] for r in g[k] if r[c] == r[c]]
            rec[c] = float(np.mean(vals)) if vals else float("nan")
        out.append(rec)
    return out


def main(path):
    recs = json.load(open(path))
    by = defaultdict(list)
    for r in recs:
        by[r["check"]].append(r)

    print("=" * 78)
    print("CHECK 1  split Fst:  coalFst t/(t+2Ne)  vs msprime between-population Fst")
    print("         the `fstDrift` column is RETIRED: `Calibrator.fstFromDrift` is")
    print("         no longer in the corpus, so that column grades nothing.")
    print("=" * 78)
    print(f"{'Ne':>6} {'t':>6} {'sim':>9} {'coalFst':>9} {'err%':>7} "
          f"{'fstDrift':>9} {'err%':>7}")
    for r in agg(by["split_fst"], ["Ne", "t"], ["sim", "lean_coalFst", "lean_fstFromDrift"]):
        e1 = 100 * (r["lean_coalFst"] - r["sim"]) / r["sim"]
        e2 = 100 * (r["lean_fstFromDrift"] - r["sim"]) / r["sim"]
        print(f"{r['Ne']:6.0f} {r['t']:6.0f} {r['sim']:9.5f} "
              f"{r['lean_coalFst']:9.5f} {e1:7.1f} {r['lean_fstFromDrift']:9.5f} {e2:7.1f}")

    print("\n" + "=" * 78)
    print("CHECK 2  island model:  1/(1+4*Ne*m)")
    print("         RETIRED: `Calibrator.islandModelFst` is no longer in the corpus.")
    print("=" * 78)
    print(f"{'demes':>6} {'Nm':>6} {'sim':>9} {'lean':>9} {'err%':>8} {'sim/lean':>9}")
    for r in agg(by["island_fst"], ["ndemes", "Nm"], ["sim", "lean"]):
        e = 100 * (r["lean"] - r["sim"]) / r["sim"]
        print(f"{r['ndemes']:6.0f} {r['Nm']:6.2f} {r['sim']:9.5f} {r['lean']:9.5f} "
              f"{e:8.1f} {r['sim']/r['lean']:9.3f}")

    print("\n" + "=" * 78)
    print("CHECK 3  singleton proportion:  1 - log N0 / log N1")
    print("         RETIRED: `Calibrator.singletonProportion` is not in the corpus.")
    print("=" * 78)
    print(f"{'N0':>8} {'N1':>9} {'nsamp':>6} {'sim':>8} {'lean':>8} "
          f"{'const-size theory':>18}")
    for r in agg(by["singletons"], ["N0", "N1", "nsamp"],
                 ["sim", "lean", "neutral_constant_size"]):
        print(f"{r['N0']:8.0f} {r['N1']:9.0f} {r['nsamp']:6.0f} {r['sim']:8.4f} "
              f"{r['lean']:8.4f} {r['neutral_constant_size']:18.4f}")

    print("\n" + "=" * 78)
    print("CHECK 4  LD decay:  ldAfterGenerations = D0*((1-r)(1-1/2Ne))^t")
    print("=" * 78)
    print(f"{'N':>6} {'r':>7} {'t':>5} {'E[D]/D0':>9} {'E[D^2]/D0^2':>12} "
          f"{'lean':>9} {'(1-r)^t':>9}")
    for r in agg(by["ld_decay"], ["N", "r", "t"],
                 ["sim_ED_ratio", "sim_ED2_ratio",
                  "lean_ldAfterGenerations_ratio", "pure_recombination"]):
        print(f"{r['N']:6.0f} {r['r']:7.4f} {r['t']:5.0f} {r['sim_ED_ratio']:9.4f} "
              f"{r['sim_ED2_ratio']:12.4f} {r['lean_ldAfterGenerations_ratio']:9.4f} "
              f"{r['pure_recombination']:9.4f}")


    rows = by.get("founder_fst", [])
    if rows:
        print("\n" + "=" * 78)
        print("CHECK 5  founderFst k t = 1 - (1 - 1/(2k))^t")
        print("         THE NAME SAYS F_ST.  Compared against BOTH the quantity the")
        print("         body computes and the quantity the name asserts.")
        print("=" * 78)
        print(f"{'k':>6} {'t':>5} {'founderFst':>11} {'hetLoss':>10} {'err':>9} "
              f"{'Fst':>10} {'err':>9}")
        for r in agg(rows, ["k", "t"],
                     ["lean_founderFst", "truth_hetloss", "truth_fst",
                      "err_vs_hetloss", "err_vs_fst"]):
            print(f"{r['k']:6.0f} {r['t']:5.0f} {r['lean_founderFst']:11.5f} "
                  f"{r['truth_hetloss']:10.5f} {r['err_vs_hetloss']:+9.5f} "
                  f"{r['truth_fst']:10.5f} {r['err_vs_fst']:+9.5f}")
        mh = max(abs(r["err_vs_hetloss"]) for r in rows)
        mf = max(abs(r["err_vs_fst"]) for r in rows)
        ratio = np.mean([r["lean_founderFst"] / r["truth_fst"]
                         for r in rows if r["truth_fst"] > 1e-6])
        print(f"\n  max |err| vs heterozygosity loss (the BODY) : {mh:.5f}")
        print(f"  max |err| vs between-population Fst (the NAME): {mf:.5f}")
        print(f"  mean founderFst / simulated Fst              : {ratio:.3f}")
        print("  VERDICT: the formula is the heterozygosity loss, not an F_ST.")

    rows = by.get("hudson_vs_neigst", [])
    if rows:
        print("\n" + "=" * 78)
        print("CHECK 6  REGRESSION: hudsonFst = 2*G/(1+G), G = neiGstFromFrequencies")
        print("         These two have been renamed across each other before; the")
        print("         correction was recorded in a docstring, which cannot fail.")
        print("=" * 78)
        print(f"{'p1':>6} {'p2':>6} {'neiGst':>10} {'hudsonFst':>11} "
              f"{'2G/(1+G)':>11} {'rel err':>10}")
        for r in sorted(rows, key=lambda r: (r["p1"], r["p2"])):
            print(f"{r['p1']:6.2f} {r['p2']:6.2f} {r['neiGst']:10.6f} "
                  f"{r['hudsonFst']:11.6f} {r['from_identity']:11.6f} "
                  f"{r['rel_err']:10.2e}")
        worst = max(r["rel_err"] for r in rows)
        print(f"\n  worst relative error over {len(rows)} cells: {worst:.3e}")
        if worst > 1e-12:
            print("  REGRESSION FAILED: the two definitions no longer satisfy the "
                  "conversion identity.")
        else:
            print("  ok: the identity holds; the two names are not swapped.")


if __name__ == "__main__":
    main(sys.argv[1] if len(sys.argv) > 1 else "defs.json")
